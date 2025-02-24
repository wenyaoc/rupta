// use std::sync::atomic::{AtomicBool, Ordering};

use rustc_borrowck::consumers::{BodyWithBorrowckFacts, ConsumerOptions};
// use rustc_data_structures::fx::FxHashSet as HashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{BorrowCheckResult},
    ty::TyCtxt,
    util::Providers,
};
use std::{cell::RefCell, hash::Hash, pin::Pin};
use rustc_span::sym::external;

pub struct Cache<In, Out>(RefCell<HashMap<In, Option<Pin<Box<Out>>>>>);
use rustc_data_structures::fx::FxHashMap as HashMap;

impl<In, Out> Cache<In, Out>
where
  In: Hash + Eq + Clone,
{
    /// Size of the cache
    pub fn len(&self) -> usize {
        self.0.borrow().len()
    }
    /// Returns the cached value for the given key, or runs `compute` if
    /// the value is not in cache.
    ///
    /// # Panics
    ///
    /// If this is a recursive invocation for this key.
    pub fn get(&self, key: In, compute: impl FnOnce(In) -> Out) -> &Out {
        self
          .get_maybe_recursive(key, compute)
          .unwrap_or_else(recursion_panic)
    }
    /// Returns the cached value for the given key, or runs `compute` if
    /// the value is not in cache.
    ///
    /// Returns `None` if this is a recursive invocation of `get` for key `key`.
    pub fn get_maybe_recursive<'a>(
      &'a self,
      key: In,
      compute: impl FnOnce(In) -> Out,
    ) -> Option<&'a Out> {
        if !self.0.borrow().contains_key(&key) {
            self.0.borrow_mut().insert(key.clone(), None);
            let out = Box::pin(compute(key.clone()));
            self.0.borrow_mut().insert(key.clone(), Some(out));
        }

        let cache = self.0.borrow();
        // Important here to first `unwrap` the `Option` created by `get`, then
        // propagate the potential option stored in the map.
        let entry = cache.get(&key).expect("invariant broken").as_ref()?;

        // SAFETY: because the entry is pinned, it cannot move and this pointer will
        // only be invalidated if Cache is dropped. The returned reference has a lifetime
        // equal to Cache, so Cache cannot be dropped before this reference goes out of scope.
        Some(unsafe { std::mem::transmute::<&'_ Out, &'a Out>(&**entry) })
    }
}

// static SIMPLIFY_MIR: AtomicBool = AtomicBool::new(false);
fn recursion_panic<A>() -> A {
    panic!("Recursion detected! The computation of a value tried to retrieve the same from the cache. Using `get_maybe_recursive` to handle this case gracefully.")
}

impl<In, Out> Default for Cache<In, Out> {
    fn default() -> Self {
        Cache(RefCell::new(HashMap::default()))
    }
}
// Since mir_borrowck does not have access to any other state, we need to use a
// thread-local for storing the obtained MIR bodies.
//
// Note: We are using 'static lifetime here, which is in general unsound.
// Unfortunately, that is the only lifetime allowed here. Our use is safe
// because we cast it back to `'tcx` before using.
// https://github.com/rust-lang/rust/blob/485ced56b8753ec86936903f2a8c95e9be8996a1/src/test/run-make-fulldeps/obtain-borrowck/driver.rs
thread_local! {
    static MIR_BODIES: Cache<LocalDefId, BodyWithBorrowckFacts<'static>> = Cache::default();
}

use rustc_session::Session;
pub fn override_queries(_session: &Session, provider: &mut Providers) {
    provider.mir_borrowck = mir_borrowck;
    // provider.extern_queries.mir_borrowck = mir_borrowck;
}

fn mir_borrowck(tcx: TyCtxt<'_>, def_id: LocalDefId) -> &BorrowCheckResult<'_> {
    let body_with_facts = rustc_borrowck::consumers::get_body_with_borrowck_facts(
      tcx,
      def_id,
      ConsumerOptions::PoloniusInputFacts,
    );
    // SAFETY: The reader casts the 'static lifetime to 'tcx before using it.
    let body_with_facts: BodyWithBorrowckFacts<'static> = unsafe { std::mem::transmute(body_with_facts) };


    MIR_BODIES.with(|cache| {
      cache.get(def_id, |_| body_with_facts);
    });
    let mut providers = Providers::default();
    rustc_borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}


#[allow(clippy::needless_lifetimes)]
pub fn get_bodies<'tcx>(
  tcx: TyCtxt<'tcx>,
  def_id: LocalDefId,
) -> &'tcx BodyWithBorrowckFacts<'tcx> {
    let _ = tcx.mir_borrowck(def_id);
    MIR_BODIES.with(|cache| {
        let body = cache.get(def_id, |_| panic!("mir_borrowck override should have stored body for item: {def_id:?}. Are you sure you registered borrowck_facts::override_queries?"));
        unsafe {
            std::mem::transmute::<
              &BodyWithBorrowckFacts<'static>,
              &'tcx BodyWithBorrowckFacts<'tcx>,
            >(body)
        }
    })
}




use rustc_index::IndexSlice;
use rustc_middle::mir::Body;
use rustc_middle::mir::Promoted;
use rustc_hir::def_id::DefId;
use std::borrow::Borrow;
use rustc_index::IndexVec;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_infer::infer::{
    InferCtxt, NllRegionVariableOrigin, RegionVariableOrigin, TyCtxtInferExt,
};
use rustc_middle::ty;
// use rustc_borrowck::{BorrowckInferCtxt};
use rustc_middle::ty::ParamEnv;
use rustc_middle::ty::RegionVid;
use rustc_data_structures::fx::FxIndexMap;
use rustc_span::Symbol;
use rustc_span::symbol::kw;
use rustc_middle::mir::Location;
use rustc_middle::mir::visit::{MutVisitor, TyContext};
use rustc_middle::span_bug;
use rustc_middle::mir::VarDebugInfoContents;
use rustc_hir::BodyOwnerKind;
use rustc_middle::ty::{GenericArgs, InlineConstArgs, InlineConstArgsParts, GenericArgsRef, Ty};
use crate::util::renumber::BorrowckInferCtxt;
use crate::util::renumber;
use crate::util::type_check;
use crate::util::universal_regions::UniversalRegions;
use rustc_middle::mir::dump_mir;
use rustc_middle::mir::Local;
use rustc_middle::mir::LocalDecl;
use rustc_middle::mir::LocalKind;
use rustc_middle::mir::Statement;
use rustc_middle::mir::StatementKind;
use rustc_middle::mir::ConstraintCategory;
use rustc_middle::mir::ReturnConstraint;
use rustc_middle::mir::LocalInfo;


// use rustc_middle::ty::{self, ParamEnv, RegionVid, TypingMode};
pub fn my_mir_borrowck(tcx: TyCtxt<'_>, def_id: DefId) {
    // let def_id = def_id.to_def_id();
    println!("LOCAL_CRATE: {:?}, CURRENT_CRATE: {:?}", LOCAL_CRATE, def_id.krate);
    println!("my_mir_borrowck: {:?}, index: {:?}, krate: {:?}", def_id, def_id.index, def_id.krate);
    let input_body = tcx.optimized_mir(def_id);
    let promoted = tcx.promoted_mir(def_id);

    let input_body: &Body<'_> = &input_body.borrow();
    if input_body.should_skip() || input_body.tainted_by_errors.is_some() {
        println!("Skipping borrowck because of injected body or tainted body");
        // TODO: https://doc.rust-lang.org/stable/nightly-rustc/src/rustc_borrowck/lib.rs.html#1-2562
        // return tcx.arena.alloc(Bo
    }
    let input_promoted: &IndexSlice<_, _> = &promoted.borrow();
    // println!("input_body: {:?}, input_promoted: {:?}", input_body, input_promoted);
    my_do_mir_borrowck(tcx, input_body, input_promoted, None);

    // tcx.arena.alloc(borrowck_result)

}

const FR: NllRegionVariableOrigin = NllRegionVariableOrigin::FreeRegion;
fn my_do_mir_borrowck<'tcx>(
    tcx: TyCtxt<'tcx>,
    input_body: &Body<'tcx>,
    input_promoted: &IndexSlice<Promoted, Body<'tcx>>,
    consumer_options: Option<ConsumerOptions>,
) {
    let def_id = input_body.source.def_id();
    let parent_def_id = tcx.parent(def_id);
    println!("def_id: {:?}, parent_def_id: {:?}", def_id, parent_def_id);
    // println!("input_body: {:?}, input_promoted: {:?}", input_body, input_promoted);

    let borrowck_infcx = tcx.infer_ctxt().build();  //TODO: Check if this is correct
    let param_env = tcx.param_env(def_id);
    let infcx = BorrowckInferCtxt { infcx: borrowck_infcx, reg_var_to_origin: RefCell::new(Default::default()), param_env };

    let mut local_names = IndexVec::from_elem(None, &input_body.local_decls);

    for var_debug_info in &input_body.var_debug_info {
        // println!("var_debug_info: {:?}", var_debug_info);
        if let VarDebugInfoContents::Place(place) = var_debug_info.value {
            if let Some(local) = place.as_local() {
                if let Some(prev_name) = local_names[local]
                    && var_debug_info.name != prev_name
                {   
                    // TODO: check why there are multiple names for the same local
                    // span_bug!(
                    //     var_debug_info.source_info.span,
                    //     "local {:?} has many names (`{}` vs `{}`)",
                    //     local,
                    //     prev_name,
                    //     var_debug_info.name
                    // );
                }
                local_names[local] = Some(var_debug_info.name);
            }
        }
    }
    // let diags = &mut diags::BorrowckDiags::new(); check this
    if let Some(e) = input_body.tainted_by_errors {
        
        // TODO: infcx.set_tainted_by_errors(e);
        println!("tainted_by_errors: {:?}", e);
    }

    // // Create the "global" region that is always free in all contexts: 'static.
    // let fr_static = infcx.next_nll_region_var(FR, || RegionCtxt::Free(kw::Static)).as_var();
    // println!("fr_static: {:?}", fr_static);

    // // We've now added all the global regions. The next ones we
    // // add will be external.
    // let first_extern_index = infcx.infcx.num_region_vars();
    let universal_regions = UniversalRegions::new(&infcx, def_id, param_env);
    let mut body_owned = input_body.clone();
    let mut promoted = input_promoted.to_owned();
    // println!("hir: {:?}", tcx.hir().krate(def_id.krate));
    renumber::renumber_mir(&infcx, &mut body_owned, &mut promoted);
    dump_mir(infcx.infcx.tcx, false, "renumber", &0, &mut body_owned, |_, _| Ok(()));

    // let is_polonius_legacy_enabled = infcx.infcx.tcx.sess.opts.unstable_opts.polonius.is_legacy_enabled();
    // let polonius_input = consumer_options.map(|_| true).unwrap_or_default()
    //     || is_polonius_legacy_enabled;

    type_check::type_check(
                &infcx,
                param_env, 
                &body_owned, 
                &promoted, 
                universal_regions,
                // location_table,
                // borrow_set,
                // &mut polonius_facts,
                // flow_inits,
                // move_data, 
                // Rc::clone(&location_map),
    );


    // println!("polonius_input: {:?}", polonius_input);
    // let MirTypeckResults {
    //     constraints,
    //     universal_region_relations,
    //     opaque_type_values,
    //     polonius_context,
    // } = type_check::type_check();
    // let mut polonius_facts = (polonius_input || PoloniusFacts::enabled(infcx.tcx)).then_some(PoloniusFacts::default());


    // let location_table = PoloniusLocationTable::new(body); 


}

// fn typeck_mir<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, universal_regions: &UniversalRegions<'tcx>) {
//     let mut last_span = body.span;
//     println!("last_span: {:?}", last_span);
    

//     for (local, local_decl) in body.local_decls.iter_enumerated() {
//         check_local(body, local, local_decl);
//     }

//     for (block, block_data) in body.basic_blocks.iter_enumerated() {
//         let mut location = Location { block, statement_index: 0 };
//         for stmt in &block_data.statements {
//             if !stmt.source_info.span.is_dummy() {
//                 last_span = stmt.source_info.span;
//             }
//             check_stmt(tcx, body, stmt, location, &universal_regions);
//             location.statement_index += 1;
//         }

//         // use rustc_middle::mir::Place;
//         // use crate::util::place::PlaceExt;
//         // let all_pointers = body
//         // .local_decls
//         // .indices()
//         // .flat_map(|local| {
//         //     // println!("local: {:?}", local);
//         //     Place::from_local(local, tcx).interior_pointers(tcx, &body, body.source.def_id())
//         // })
//         // .collect::<Vec<_>>();
//         // println!("all_pointers: {:?}", all_pointers);
//         // self.check_terminator(body, block_data.terminator(), location);
//         // self.check_iscleanup(body, block_data);
//     }
// }

// fn check_local<'tcx>(body: &Body<'tcx>, local: Local, local_decl: &LocalDecl<'tcx>) {
//     match body.local_kind(local) {
//         LocalKind::ReturnPointer | LocalKind::Arg => {
//             // return values of normal functions are required to be
//             // sized by typeck, but return values of ADT constructors are
//             // not because we don't include a `Self: Sized` bounds on them.
//             //
//             // Unbound parts of arguments were never required to be Sized
//             // - maybe we should make that a warning.
//             return;
//         }
//         LocalKind::Temp => {}
//     }

//     // TODO: finish this
//     // When `unsized_fn_params` or `unsized_locals` is enabled, only function calls
//     // and nullary ops are checked in `check_call_dest`.
//     // if !self.unsized_feature_enabled() {
//     //     let span = local_decl.source_info.span;
//     //     let ty = local_decl.ty;
//     //     self.ensure_place_sized(ty, span);
//     // }
// }


// fn check_stmt<'tcx>(
//             tcx: TyCtxt<'tcx>, 
//             body: &Body<'tcx>, 
//             stmt: &Statement<'tcx>, 
//             location: Location,
//             universal_regions: &UniversalRegions<'tcx>) {
//     // let tcx = self.tcx();
//     // debug!("stmt kind: {:?}", stmt.kind);
//     match &stmt.kind {
//         StatementKind::Assign(box (place, rv)) => {
//             // Assignments to temporaries are not "interesting";
//             // they are not caused by the user, but rather artifacts
//             // of lowering. Assignments to other sorts of places *are* interesting
//             // though.
//             let category = match place.as_local() {
//                 Some(RETURN_PLACE) => {
//                     let defining_ty = universal_regions.defining_ty;
//                     if defining_ty.is_const() {
//                         if tcx.is_static(defining_ty.def_id()) {
//                             ConstraintCategory::UseAsStatic
//                         } else {
//                             ConstraintCategory::UseAsConst
//                         }
//                     } else {
//                         ConstraintCategory::Return(ReturnConstraint::Normal)
//                     }
//                 }
//                 Some(l)
//                     if matches!(body.local_decls[l].local_info(), LocalInfo::AggregateTemp) =>
//                 {
//                     ConstraintCategory::Usage
//                 }
//                 Some(l) if !body.local_decls[l].is_user_variable() => {
//                     ConstraintCategory::Boring
//                 }
//                 _ => ConstraintCategory::Assignment,
//             };

//             // println!("category: {:?}", category);
//             // debug!(
//             //     "assignment category: {:?} {:?}",
//             //     category,
//             //     place.as_local().map(|l| &body.local_decls[l])
//             // );

//             // let place_ty = place.ty(body, tcx).ty;
//             // // debug!(?place_ty);
//             // let place_ty = self.normalize(place_ty, location);
//             // println!("place_ty normalized: {:?}", place_ty);
//             // let rv_ty = rv.ty(body, tcx);
//             // // debug!(?rv_ty);
//             // let rv_ty = self.normalize(rv_ty, location);
//             // println!("normalized rv_ty: {:?}", rv_ty);
//             // if let Err(terr) =
//             //     self.sub_types(rv_ty, place_ty, location.to_locations(), category)
//             // {
//             //     span_mirbug!(
//             //         self,
//             //         stmt,
//             //         "bad assignment ({:?} = {:?}): {:?}",
//             //         place_ty,
//             //         rv_ty,
//             //         terr
//             //     );
//             // }

//             // if let Some(annotation_index) = self.rvalue_user_ty(rv) {
//             //     if let Err(terr) = self.relate_type_and_user_type(
//             //         rv_ty,
//             //         ty::Invariant,
//             //         &UserTypeProjection { base: annotation_index, projs: vec![] },
//             //         location.to_locations(),
//             //         ConstraintCategory::TypeAnnotation(AnnotationSource::GenericArg),
//             //     ) {
//             //         let annotation = &self.user_type_annotations[annotation_index];
//             //         span_mirbug!(
//             //             self,
//             //             stmt,
//             //             "bad user type on rvalue ({:?} = {:?}): {:?}",
//             //             annotation,
//             //             rv_ty,
//             //             terr
//             //         );
//             //     }
//             // }

//             // self.check_rvalue(body, rv, location);
//             // if !self.unsized_feature_enabled() {
//             //     let trait_ref = ty::TraitRef::new(
//             //         tcx,
//             //         tcx.require_lang_item(LangItem::Sized, Some(self.last_span)),
//             //         [place_ty],
//             //     );
//             //     self.prove_trait_ref(
//             //         trait_ref,
//             //         location.to_locations(),
//             //         ConstraintCategory::SizedBound,
//             //     );
//             // }
//         }
//         StatementKind::AscribeUserType(..)
//         | StatementKind::Intrinsic(..)
//         | StatementKind::FakeRead(..)
//         | StatementKind::StorageLive(..)
//         | StatementKind::StorageDead(..)
//         | StatementKind::Retag { .. }
//         | StatementKind::Coverage(..)
//         | StatementKind::ConstEvalCounter
//         | StatementKind::PlaceMention(..)
//         | StatementKind::Nop => {}
//         StatementKind::Deinit(..) | StatementKind::SetDiscriminant { .. } => {
//             println!("Statement not allowed in this MIR phase")
//         }
//     }
// }
