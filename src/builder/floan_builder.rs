// use log::*;
// use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt::{Debug};
use std::{hash::Hash};
use rustc_hir::def_id::{DefId};
use rustc_middle::ty::{Region, Ty, TyCtxt};
// use rustc_data_structures::intern::Interned;
use rustc_data_structures::{
    graph::{iterate::reverse_post_order, scc::Sccs, vec_graph::VecGraph},
    intern::Interned,
  };
use crate::util::{borrowck_util};

use crate::util::place::PlaceExt;
use rustc_middle::mir::Place;
use crate::util::place::UNKNOWN_REGION;
use rustc_index::{
    bit_set::{HybridBitSet, SparseBitMatrix},
    IndexVec,
  };
use rustc_data_structures::fx::FxHashSet as HashSet;
use rustc_middle::{
    mir::*,
    ty::{GenericArgKind, RegionKind, RegionVid},
};
use crate::util::body::BodyExt;

use rustc_middle::mir::visit::Visitor;
pub type LoanSet<'tcx> = HashSet<(Place<'tcx>, Mutability)>;
type LoanMap<'tcx> = HashMap<RegionVid, LoanSet<'tcx>>;
pub type PlaceLoanMap<'tcx> = HashMap<Place<'tcx>, (Mutability, LoanSet<'tcx>)>;

#[derive(Default, Debug)]
struct GatherBorrows<'tcx> {
  borrows: Vec<(RegionVid, BorrowKind, Place<'tcx>)>,
}

macro_rules! region_pat {
    ($name:ident) => {
      Region(Interned(RegionKind::ReVar($name), _))
    };
  }
rustc_index::newtype_index! {
    #[orderable]
    #[debug_format = "rs{}"]
    struct RegionSccIndex {}
}


impl<'tcx> Visitor<'tcx> for GatherBorrows<'tcx> {
    fn visit_assign(
      &mut self,
      _place: &Place<'tcx>,
      rvalue: &Rvalue<'tcx>,
      _location: Location,
    ) {
      if let Rvalue::Ref(region_pat!(region), kind, borrowed_place) = rvalue {
        self.borrows.push((*region, *kind, *borrowed_place));
      }
    }
  }


pub struct FuncLoanBuilder<'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
}



impl<'tcx> FuncLoanBuilder<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> Self {
        Self { tcx, def_id }
    }

    pub fn compute_loans(&self) -> PlaceLoanMap<'tcx> {
        let tcx = self.tcx;
        let def_id = self.def_id;
        let local_def_id = def_id.expect_local();
        // println!("local_def_id: {local_def_id:#?}", local_def_id = local_def_id);
        let body_with_facts = borrowck_util::get_bodies(tcx, local_def_id);
        // println!("body_with_facts: {body_with_facts:#?}", body_with_facts = body_with_facts.body);
        let static_region = RegionVid::from_usize(0);
        // let start = Instant::now();
        // println!("func_id: {:?}", def_id);
        // println!("input_facts: {:?}", body_with_facts.input_facts);
        let subset_base = &body_with_facts
                .input_facts
                .as_ref()
                .unwrap()
                .subset_base
                .iter()
                .cloned()
                .collect::<Vec<_>>();
        // println!("subset_base: {:?}", subset_base);
        
    
        let all_pointers = body_with_facts.body
        .local_decls
        .indices()
        .flat_map(|local| {
            Place::from_local(local, tcx).interior_pointers(tcx, &body_with_facts.body, def_id)
        })
        .collect::<Vec<_>>();
    
        // let all_pointers_hash = all_pointers.iter().map(|(r, _)| *r).collect();
    
        // println!("all_pointers: {:?}", all_pointers);
        let max_region = all_pointers
        .iter()
        .map(|(region, _)| *region)
        .chain(subset_base.iter().flat_map(|(r1, r2, _)| [*r1, *r2]))
        .filter(|r| *r != UNKNOWN_REGION)
        .max()
        .unwrap_or(static_region);
    
        let hashmap: HashMap<_, _> = all_pointers.clone()
        .into_iter()
        .filter(|(key, _)| *key != UNKNOWN_REGION)
        .collect();
    
        // println!("hashmap: {:?}", hashmap);
    
        let num_regions = max_region.as_usize() + 1;
        let all_regions = (0 .. num_regions).map(RegionVid::from_usize);
    
        let mut subset = SparseBitMatrix::new(num_regions);
    
        let async_hack = AsyncHack::new(tcx, &body_with_facts.body, def_id);
        let ignore_regions = async_hack.ignore_regions();
    
        // subset('a, 'b) :- subset_base('a, 'b, _).
        for (a, b, _) in subset_base {
            if ignore_regions.contains(a) || ignore_regions.contains(b) {
            continue;
            }
            subset.insert(*a, *b);
        }
    
        // subset('static, 'a).
        for a in all_regions.clone() {
            subset.insert(static_region, a);
        }
    
        let mut contains: LoanMap<'tcx> = HashMap::default();
        let mut definite: HashMap<RegionVid, (Ty<'tcx>, Vec<PlaceElem<'tcx>>)> =
          HashMap::default();
    
        // For all e = &'a x.q in body:
        //   contains('a, p).
        //   If p = p^[* p2]: definite('a, ty(p2), p2^[])
        //   Else:            definite('a, ty(p),  p^[]).
        let mut gather_borrows = GatherBorrows::default();
        gather_borrows.visit_body(&body_with_facts.body);
        // println!("gather_borrows={gather_borrows:#?}", gather_borrows = gather_borrows.borrows);
        for (region, kind, place) in gather_borrows.borrows {
            // println!("gather_borrows.borrows region={region:?}, kind={kind:?}, place={place:?}");
            if place.is_direct(&body_with_facts.body) {
                // println!("place is direct");
                contains
                .entry(region)
                .or_default()
                .insert((place, kind.to_mutbl_lossy()));
            }
          
            let def = match place.refs_in_projection().next() {
                Some((ptr, proj)) => {
                    // println!("ptr={ptr:?}, proj={proj:#?}", ptr = ptr, proj = proj);
                    // println!("ptr.projection: {:?}", ptr.projection);
                    let ptr_ty = ptr.ty(body_with_facts.body.local_decls(), tcx).ty;
                    // println!("ptr_ty: {:?}", ptr_ty);
                    (ptr_ty.builtin_deref(true).unwrap().ty, proj.to_vec())
                    }
                    None => {
                    // println!("place is none, place: {:?}", place);
                    (body_with_facts.body.local_decls()[place.local].ty,
                    place.projection.to_vec())
                }
            };
            // println!("def={def:#?}", def = def);
            definite.insert(region, def);
        }
        // For all args p : &'a ω T where 'a is abstract: contains('a, *p, ω).
        for arg in body_with_facts.body.args_iter() {
            for (region, places) in
                Place::from_local(arg, tcx).interior_pointers(tcx, &body_with_facts.body, def_id)
            {
                let region_contains = contains.entry(region).or_default();
                // println!("region={region:?}, places={places:#?}, region_contains={region_contains:#?}", region = region, places = places, region_contains = region_contains);
                for (place, mutability) in places {
                // WARNING / TODO: this is a huge hack (that is conjoined w/ all_args).
                // Need a way to limit the number of possible pointers for functions with
                // many pointers in the input. This is almost certainly not sound, but hopefully
                // it works for most cases.
                if place.projection.len() <= 2 {
                    // println!("place={place:?}, mutability={mutability:?}");
                    region_contains.insert((tcx.mk_place_deref(place), mutability));
                }
                }
            }
        }
    
        // For all places p : *T or p : Box<T>: contains('UNK, *p, mut).
        let unk_contains = contains.entry(UNKNOWN_REGION).or_default();
        // println!("unk_contains={unk_contains:#?}", unk_contains = unk_contains);
        for (region, places) in &all_pointers {
          if *region == UNKNOWN_REGION {
            for (place, _) in places {
            //   println!("UNKNOWN_REGION place={place:?}");
              unk_contains.insert((tcx.mk_place_deref(*place), Mutability::Mut));
            }
          }
        }
        // println!("Initial contains: {contains:#?}");
        // println!("Definite: {definite:#?}");
        // println!("Subset: {subset:#?}", subset = subset);
    
        let edge_pairs = subset
            .rows()
            .flat_map(|r1| subset.iter(r1).map(move |r2| (r1, r2)))
            .collect::<Vec<_>>();
        let subset_graph = VecGraph::new(num_regions, edge_pairs);
        let subset_sccs = Sccs::<RegionVid, RegionSccIndex>::new(&subset_graph);
        let mut scc_to_regions =
        IndexVec::from_elem_n(HybridBitSet::new_empty(num_regions), subset_sccs.num_sccs());
        for r in all_regions.clone() {
            let scc = subset_sccs.scc(r);
            scc_to_regions[scc].insert(r);
        }
        let scc_order = reverse_post_order(&subset_sccs, subset_sccs.scc(static_region));
        // elapsed("relation construction", start);
    
        // let start = Instant::now();
        for r in all_regions {
        contains.entry(r).or_default();
        }
        for scc_idx in scc_order {
        // println!("scc_idx={scc_idx:?}");
        loop {
            let mut changed = false;
            let scc = &scc_to_regions[scc_idx];
            // println!("scc={scc:#?}", scc = scc);
            for a in scc.iter() {
            for b in subset.iter(a) {
                // println!("    b={b:?}");
                if a == b {
                continue;
                }
                // SAFETY: a != b
                let a_contains =
                unsafe { &*(contains.get(&a).unwrap() as *const LoanSet<'tcx>) };
                let b_contains =
                unsafe { &mut *(contains.get_mut(&b).unwrap() as *mut LoanSet<'tcx>) };
                
                // println!("    a_contains={a_contains:#?}, b_contains={b_contains:#?}", a_contains = a_contains, b_contains = b_contains);
    
                let cyclic = scc.contains(b);
                
                match definite.get(&b) {
                Some((ty, proj)) if !cyclic => {
                    for (p, mutability) in a_contains.iter() {
                    let p_ty = p.ty(body_with_facts.body.local_decls(), tcx).ty;
                    // println!("      ty={ty:?}, proj={proj:#?}, p_ty={p_ty:?}", ty = *ty, proj = proj, p_ty = p_ty);
                    let p_proj = if *ty == p_ty {
                        let mut full_proj = p.projection.to_vec();
                        full_proj.extend(proj);
                        // println!("      full_proj={full_proj:#?}", full_proj = full_proj);
                        Place::make(p.local, tcx.mk_place_elems(&full_proj), tcx)
                    } else {
                        // println!("      p_ty != ty, *p={p:?}, *ty={ty:?}", p = p, ty = *ty);
                        *p
                    };
    
                    changed |= b_contains.insert((p_proj, *mutability));
                    // println!("      p={p:?}, mutability={mutability:?}, p_ty={p_ty:?}, p_proj={p_proj:?}, changed={changed:?}, b_contains={b_contains:#?}", p = p, mutability = mutability, p_ty = p_ty, p_proj = p_proj, changed = changed, b_contains = b_contains);
                    }
                }
                _ => {
                    let orig_len = b_contains.len();
                    b_contains.extend(a_contains);
                    changed |= b_contains.len() != orig_len;
                    // println!("      changed={changed:?}, b_contains={b_contains:#?}", changed = changed, b_contains = b_contains);
                }
                }
            }
            }
    
            if !changed {
            break;
            }
        }
        }
        // println!("Final contains: {contains:#?}", contains = contains);
        // elapsed("fixpoint", start);
        let mut func_loans: PlaceLoanMap<'tcx> = HashMap::default();
        for (region, contain) in contains {
            if contain.is_empty() {
                continue;
            }
            if let Some(region_var) = hashmap.get(&region) {
                // println!("region={region:?}, region_var={region_var:#?}", region = region, region_var = region_var);
                for (path, mutability) in region_var{
                    func_loans.insert(*path, (*mutability, contain.clone()));
                }
            }
        }
        // println!("func_loans: {func_loans:#?}", func_loans = func_loans);
        func_loans 
    
    }
}




pub(crate) struct AsyncHack<'tcx> {
    context_ty: Option<Ty<'tcx>>,
    // tcx: TyCtxt<'tcx>,
    // body: &'a Body<'tcx>,
  }
  
impl<'tcx> AsyncHack<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, def_id: DefId) -> Self {
        let context_ty = body.async_context(tcx, def_id);
        AsyncHack {
            context_ty,
            // tcx,
            // body,
        }
    }

    pub fn ignore_regions(&self) -> HashSet<RegionVid> {
        match self.context_ty {
        Some(context_ty) => context_ty
            .walk()
            .filter_map(|part| match part.unpack() {
            GenericArgKind::Lifetime(r) => match r.kind() {
                RegionKind::ReVar(rv) => Some(rv),
                _ => None,
            },
            _ => None,
            })
            .collect::<HashSet<_>>(),
        None => HashSet::default(),
        }
    }

    // pub fn ignore_place(&self, place: Place<'tcx>) -> bool {
    //     match self.context_ty {
    //     Some(context_ty) => {
    //         self
    //         .tcx
    //         .erase_regions(place.ty(&self.body.local_decls, self.tcx).ty)
    //         == self.tcx.erase_regions(context_ty)
    //     }
    //     None => false,
    //     }
    // }
}