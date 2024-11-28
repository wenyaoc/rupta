
// use std::{hash::Hash, time::Instant};
// use crate::mir::place::PlaceExt;
// use log::{debug, info};
// use rustc_borrowck::consumers::BodyWithBorrowckFacts;
// use rustc_data_structures::{
//   fx::{FxHashMap as HashMap, FxHashSet as HashSet},
//   graph::{iterate::reverse_post_order, scc::Sccs, vec_graph::VecGraph},
//   intern::Interned,
// };
// use rustc_hir::def_id::DefId;
// use rustc_index::{
//   bit_set::{HybridBitSet, SparseBitMatrix},
//   IndexVec,
// };
// use rustc_middle::{
//   mir::{visit::Visitor, *},
//   ty::{Region, RegionKind, RegionVid, Ty, TyCtxt, TyKind, TypeAndMut},
// };
// // use rustc_utils::{mir::place::UNKNOWN_REGION, timer::elapsed, PlaceExt};
// /// Used to describe aliases of owned and raw pointers.cd 
// pub const UNKNOWN_REGION: RegionVid = RegionVid::MAX;


// type LoanSet<'tcx> = HashSet<(Place<'tcx>, Mutability)>;
// type LoanMap<'tcx> = HashMap<RegionVid, LoanSet<'tcx>>;
// type BorrowckLocationIndex =
//   <rustc_borrowck::consumers::RustcFacts as crate::polonius_engine::FactTypes>::Point;


// pub struct FuncLoans<'a, 'tcx> {
//     tcx: TyCtxt<'tcx>,
//     body: &'a Body<'tcx>,
//     pub(super) loans: LoanMap<'tcx>,
// }

// rustc_index::newtype_index! {
//   #[orderable]
//   #[debug_format = "rs{}"]
//   struct RegionSccIndex {}
// }

// impl<'a, 'tcx> FuncLoans<'a, 'tcx> {
//   /// Runs the alias analysis on a given `body_with_facts`.
//   pub fn build(
//     tcx: TyCtxt<'tcx>,
//     def_id: DefId,
//     body_with_facts: &'a BodyWithBorrowckFacts<'tcx>,
//   ) -> Self {
//     let loans = Self::compute_loans(tcx, def_id, body_with_facts, |_, _, _| true);
//     FuncLoans {
//       tcx,
//       body: &body_with_facts.body,
//       loans,
//     }
//   }

//   fn compute_loans(
//     tcx: TyCtxt<'tcx>,
//     def_id: DefId,
//     body_with_facts: &'a BodyWithBorrowckFacts<'tcx>,
//     constraint_selector: impl Fn(RegionVid, RegionVid, BorrowckLocationIndex) -> bool,
//   ) -> LoanMap<'tcx> {
//     let start = Instant::now();
//     let body = &body_with_facts.body;
//     let static_region = RegionVid::from_usize(0);
//     let subset_base = &body_with_facts
//       .input_facts
//       .as_ref()
//       .unwrap()
//       .subset_base
//       .iter()
//       .cloned()
//       .filter(|(r1, r2, i)| constraint_selector(*r1, *r2, *i))
//       .collect::<Vec<_>>();

//     let all_pointers = body
//       .local_decls()
//       .indices()
//       .flat_map(|local| {
//         Place {
//           local,
//           projection: tcx.mk_place_elems(&[]),
//         }.interior_pointers(tcx, body, def_id)
//       })
//       .collect::<Vec<_>>();
//     let max_region = all_pointers
//       .iter()
//       .map(|(region, _)| *region)
//       .chain(subset_base.iter().flat_map(|(r1, r2, _)| [*r1, *r2]))
//       .filter(|r| *r != UNKNOWN_REGION)
//       .max()
//       .unwrap_or(static_region);
//     let num_regions = max_region.as_usize() + 1;
//     let all_regions = (0 .. num_regions).map(RegionVid::from_usize);

//     let mut subset = SparseBitMatrix::new(num_regions);

//     let async_hack = AsyncHack::new(tcx, body, def_id);
//     let ignore_regions = async_hack.ignore_regions();

//     // subset('a, 'b) :- subset_base('a, 'b, _).
//     for (a, b, _) in subset_base {
//       if ignore_regions.contains(a) || ignore_regions.contains(b) {
//         continue;
//       }
//       subset.insert(*a, *b);
//     }

//     // subset('static, 'a).
//     for a in all_regions.clone() {
//       subset.insert(static_region, a);
//     }

//     if is_extension_active(|mode| mode.pointer_mode == PointerMode::Conservative) {
//       // for all p1 : &'a T, p2: &'b T: subset('a, 'b).
//       let mut region_to_pointers: HashMap<_, Vec<_>> = HashMap::default();
//       for (region, places) in &all_pointers {
//         if *region != UNKNOWN_REGION {
//           region_to_pointers
//             .entry(*region)
//             .or_default()
//             .extend(places);
//         }
//       }

//       let constraints = generate_conservative_constraints(
//         tcx,
//         &body_with_facts.body,
//         &region_to_pointers,
//       );

//       for (a, b) in constraints {
//         subset.insert(a, b);
//       }
//     }

//     let mut contains: LoanMap<'tcx> = HashMap::default();
//     let mut definite: HashMap<RegionVid, (Ty<'tcx>, Vec<PlaceElem<'tcx>>)> =
//       HashMap::default();

//     // For all e = &'a x.q in body:
//     //   contains('a, p).
//     //   If p = p^[* p2]: definite('a, ty(p2), p2^[])
//     //   Else:            definite('a, ty(p),  p^[]).
//     let mut gather_borrows = GatherBorrows::default();
//     gather_borrows.visit_body(&body_with_facts.body);
//     for (region, kind, place) in gather_borrows.borrows {
//       if place.is_direct(body) {
//         contains
//           .entry(region)
//           .or_default()
//           .insert((place, kind.to_mutbl_lossy()));
//       }

//       let def = match place.refs_in_projection().next() {
//         Some((ptr, proj)) => {
//           let ptr_ty = ptr.ty(body.local_decls(), tcx).ty;
//           (ptr_ty.builtin_deref(true).unwrap().ty, proj.to_vec())
//         }
//         None => (
//           body.local_decls()[place.local].ty,
//           place.projection.to_vec(),
//         ),
//       };
//       definite.insert(region, def);
//     }

//     // For all args p : &'a ω T where 'a is abstract: contains('a, *p, ω).
//     for arg in body.args_iter() {
//       for (region, places) in
//         Place::make(arg, &[], tcx).interior_pointers(tcx, body, def_id)
//       {
//         let region_contains = contains.entry(region).or_default();
//         for (place, mutability) in places {
//           // WARNING / TODO: this is a huge hack (that is conjoined w/ all_args).
//           // Need a way to limit the number of possible pointers for functions with
//           // many pointers in the input. This is almost certainly not sound, but hopefully
//           // it works for most cases.
//           if place.projection.len() <= 2 {
//             region_contains.insert((tcx.mk_place_deref(place), mutability));
//           }
//         }
//       }
//     }

//     // For all places p : *T or p : Box<T>: contains('UNK, *p, mut).
//     let unk_contains = contains.entry(UNKNOWN_REGION).or_default();
//     for (region, places) in &all_pointers {
//       if *region == UNKNOWN_REGION {
//         for (place, _) in places {
//           unk_contains.insert((tcx.mk_place_deref(*place), Mutability::Mut));
//         }
//       }
//     }

//     info!(
//       "Initial places in loan set: {}, total regions {}, definite regions: {}",
//       contains.values().map(|set| set.len()).sum::<usize>(),
//       contains.len(),
//       definite.len()
//     );

//     debug!("Initial contains: {contains:#?}");
//     debug!("Definite: {definite:#?}");

//     // Compute a topological sort of the subset relation.
//     let edge_pairs = subset
//       .rows()
//       .flat_map(|r1| subset.iter(r1).map(move |r2| (r1, r2)))
//       .collect::<Vec<_>>();
//     let subset_graph = VecGraph::new(num_regions, edge_pairs);
//     let subset_sccs = Sccs::<RegionVid, RegionSccIndex>::new(&subset_graph);
//     let mut scc_to_regions =
//       IndexVec::from_elem_n(HybridBitSet::new_empty(num_regions), subset_sccs.num_sccs());
//     for r in all_regions.clone() {
//       let scc = subset_sccs.scc(r);
//       scc_to_regions[scc].insert(r);
//     }
//     let scc_order = reverse_post_order(&subset_sccs, subset_sccs.scc(static_region));
//     elapsed("relation construction", start);

//     // Subset implies containment: l ∈ 'a ∧ 'a ⊆ 'b ⇒ l ∈ 'b
//     // i.e. contains('b, l) :- contains('a, l), subset('a, 'b).
//     //
//     // contains('b, p2^[p], ω) :-
//     //   contains('a, p, ω), subset('a, 'b),
//     //   definite('b, T, p2^[]), !subset('b, 'a), p : T.
//     //
//     // If 'a is from a borrow expression &'a proj[*p'], then we add proj to all inherited aliases.
//     // See interprocedural_field_independence for an example where this matters.
//     // But we only do this if:
//     //   * !subset('b, 'a) since otherwise projections would be added infinitely.
//     //   * if p' : &T, then p : T since otherwise proj[p] is not well-typed.
//     //
//     // Note that it's theoretically more efficient to compute the transitive closure of `subset`
//     // and then do the pass below in one step rather than to a fixpoint. But this negates the added
//     // precision from propagating projections. For example, in the program:
//     //   a = &'0 mut (0, 0)
//     //   b = &'1 mut a.0
//     //   c = &'2 mut *b
//     //   *c = 1;
//     // then '0 :> '1 :> '2. By propagating projections, then '1 = {a.0}. However if we see '0 :> '2
//     // to insert contains('0) into contains('2), then contains('2) = {a, a.0} which defeats the purpose!
//     // Then *c = 1 is considered to be a mutation to anything within a.
//     //
//     // Rather than iterating over the entire subset relation, we only do local fixpoints
//     // within each strongly-connected component.
//     let start = Instant::now();
//     for r in all_regions {
//       contains.entry(r).or_default();
//     }
//     for scc_idx in scc_order {
//       loop {
//         let mut changed = false;
//         let scc = &scc_to_regions[scc_idx];
//         for a in scc.iter() {
//           for b in subset.iter(a) {
//             if a == b {
//               continue;
//             }

//             // SAFETY: a != b
//             let a_contains =
//               unsafe { &*(contains.get(&a).unwrap() as *const LoanSet<'tcx>) };
//             let b_contains =
//               unsafe { &mut *(contains.get_mut(&b).unwrap() as *mut LoanSet<'tcx>) };

//             let cyclic = scc.contains(b);
//             match definite.get(&b) {
//               Some((ty, proj)) if !cyclic => {
//                 for (p, mutability) in a_contains.iter() {
//                   let p_ty = p.ty(body.local_decls(), tcx).ty;
//                   let p_proj = if *ty == p_ty {
//                     let mut full_proj = p.projection.to_vec();
//                     full_proj.extend(proj);
//                     Place::make(p.local, tcx.mk_place_elems(&full_proj), tcx)
//                   } else {
//                     *p
//                   };

//                   changed |= b_contains.insert((p_proj, *mutability));
//                 }
//               }
//               _ => {
//                 let orig_len = b_contains.len();
//                 b_contains.extend(a_contains);
//                 changed |= b_contains.len() != orig_len;
//               }
//             }
//           }
//         }

//         if !changed {
//           break;
//         }
//       }
//     }
//     elapsed("fixpoint", start);

//     info!(
//       "Final places in loan set: {}",
//       contains.values().map(|set| set.len()).sum::<usize>()
//     );
//     contains
//   }
// }