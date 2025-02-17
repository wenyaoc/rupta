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

pub fn override_queries(_session: &rustc_session::Session, local: &mut Providers) {
    local.mir_borrowck = mir_borrowck;
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
    println!("original_mir_borrowck: {:?}", original_mir_borrowck);
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
use crate::util::universal_regions::UniversalRegions;


// pub(crate) struct MyBorrowckInferCtxt<'tcx> {
//     pub(crate) infcx: InferCtxt<'tcx>,
//     pub(crate) reg_var_to_origin: RefCell<FxIndexMap<RegionVid, RegionCtxt>>,
//     pub(crate) param_env: ParamEnv<'tcx>,
// }


// impl<'tcx> MyBorrowckInferCtxt<'tcx> {

//     pub(crate) fn next_region_var<F>(
//         &self,
//         origin: RegionVariableOrigin,
//         get_ctxt_fn: F,
//     ) -> ty::Region<'tcx>
//     where
//         F: Fn() -> RegionCtxt,
//     {
//         let next_region = self.infcx.next_region_var(origin);
//         let vid = next_region.as_var();

//         if cfg!(debug_assertions) {
//             println!("inserting vid {:?} with origin {:?} into var_to_origin", vid, origin);
//             let ctxt = get_ctxt_fn();
//             let mut var_to_origin = self.reg_var_to_origin.borrow_mut();
//             assert_eq!(var_to_origin.insert(vid, ctxt), None);
//         }

//         next_region
//     }

//     // #[instrument(skip(self, get_ctxt_fn), level = "debug")]
//     pub(crate) fn next_nll_region_var<F>(
//         &self,
//         origin: NllRegionVariableOrigin,
//         get_ctxt_fn: F,
//     ) -> ty::Region<'tcx>
//     where
//         F: Fn() -> RegionCtxt,
//     {
//         let next_region = self.infcx.next_nll_region_var(origin);
//         let vid = next_region.as_var();

//         if cfg!(debug_assertions) {
//             println!("inserting vid {:?} with origin {:?} into var_to_origin", vid, origin);
//             let ctxt = get_ctxt_fn();
//             let mut var_to_origin = self.reg_var_to_origin.borrow_mut();
//             assert_eq!(var_to_origin.insert(vid, ctxt), None);
//         }

//         next_region
//     }
// }

// // #[extension(trait InferCtxtExt<'tcx>)]
// // impl<'tcx> MyBorrowckInferCtxt<'tcx> {
// //     #[instrument(skip(self), level = "debug")]
// //     fn replace_free_regions_with_nll_infer_vars<T>(
// //         &self,
// //         origin: NllRegionVariableOrigin,
// //         value: T,
// //     ) -> T
// //     where
// //         T: TypeFoldable<TyCtxt<'tcx>>,
// //     {
// //         fold_regions(self.infcx.tcx, value, |region, _depth| {
// //             let name = region.get_name_or_anon();
// //             debug!(?region, ?name);

// //             self.next_nll_region_var(origin, || RegionCtxt::Free(name))
// //         })
// //     }

// //     #[instrument(level = "debug", skip(self, indices))]
// //     fn replace_bound_regions_with_nll_infer_vars<T>(
// //         &self,
// //         all_outlive_scope: LocalDefId,
// //         value: ty::Binder<'tcx, T>,
// //         indices: &UniversalRegionIndices<'tcx>,
// //     ) -> T
// //     where
// //         T: TypeFoldable<TyCtxt<'tcx>>,
// //     {
// //         let (value, _map) = self.tcx.instantiate_bound_regions(value, |br| {
// //             debug!(?br);
// //             let kind = ty::LateParamRegionKind::from_bound(br.var, br.kind);
// //             let liberated_region =
// //                 ty::Region::new_late_param(self.tcx, all_outlive_scope.to_def_id(), kind);
// //             ty::Region::new_var(self.tcx, indices.to_region_vid(liberated_region))
// //         });
// //         value
// //     }
// // }


// /// The "defining type" for this MIR. The key feature of the "defining
// /// type" is that it contains the information needed to derive all the
// /// universal regions that are in scope as well as the types of the
// /// inputs/output from the MIR. In general, early-bound universal
// /// regions appear free in the defining type and late-bound regions
// /// appear bound in the signature.
// #[derive(Copy, Clone, Debug)]
// pub(crate) enum MyDefiningTy<'tcx> {
//     /// The MIR is a closure. The signature is found via
//     /// `ClosureArgs::closure_sig_ty`.
//     Closure(DefId, GenericArgsRef<'tcx>),

//     /// The MIR is a coroutine. The signature is that coroutines take
//     /// no parameters and return the result of
//     /// `ClosureArgs::coroutine_return_ty`.
//     Coroutine(DefId, GenericArgsRef<'tcx>),

//     /// The MIR is a special kind of closure that returns coroutines.
//     ///
//     /// See the documentation on `CoroutineClosureSignature` for details
//     /// on how to construct the callable signature of the coroutine from
//     /// its args.
//     // CoroutineClosure(DefId, GenericArgsRef<'tcx>),

//     /// The MIR is a fn item with the given `DefId` and args. The signature
//     /// of the function can be bound then with the `fn_sig` query.
//     FnDef(DefId, GenericArgsRef<'tcx>),

//     /// The MIR represents some form of constant. The signature then
//     /// is that it has no inputs and a single return value, which is
//     /// the value of the constant.
//     Const(DefId, GenericArgsRef<'tcx>),

//     /// The MIR represents an inline const. The signature has no inputs and a
//     /// single return value found via `InlineConstArgs::ty`.
//     InlineConst(DefId, GenericArgsRef<'tcx>),
// }

// impl<'tcx> MyDefiningTy<'tcx> {
//     /// Returns a list of all the upvar types for this MIR. If this is
//     /// not a closure or coroutine, there are no upvars, and hence it
//     /// will be an empty list. The order of types in this list will
//     /// match up with the upvar order in the HIR, typesystem, and MIR.
//     pub(crate) fn upvar_tys(self) -> &'tcx ty::List<Ty<'tcx>> {
//         match self {
//             MyDefiningTy::Closure(_, args) => args.as_closure().upvar_tys(),
//             // MyDefiningTy::CoroutineClosure(_, args) => args.as_coroutine_closure().upvar_tys(),
//             MyDefiningTy::Coroutine(_, args) => args.as_coroutine().upvar_tys(),
//             MyDefiningTy::FnDef(..) | MyDefiningTy::Const(..) | MyDefiningTy::InlineConst(..) => {
//                 ty::List::empty()
//             }
//         }
//     }

//     /// Number of implicit inputs -- notably the "environment"
//     /// parameter for closures -- that appear in MIR but not in the
//     /// user's code.
//     pub(crate) fn implicit_inputs(self) -> usize {
//         match self {
//             MyDefiningTy::Closure(..)
//             | MyDefiningTy::CoroutineClosure(..)
//             | MyDefiningTy::Coroutine(..) => 1,
//             MyDefiningTy::FnDef(..) | MyDefiningTy::Const(..) | MyDefiningTy::InlineConst(..) => 0,
//         }
//     }

//     pub(crate) fn is_fn_def(&self) -> bool {
//         matches!(*self, MyDefiningTy::FnDef(..))
//     }

//     pub(crate) fn is_const(&self) -> bool {
//         matches!(*self, MyDefiningTy::Const(..) | MyDefiningTy::InlineConst(..))
//     }

//     pub(crate) fn def_id(&self) -> DefId {
//         match *self {
//             MyDefiningTy::Closure(def_id, ..)
//             | MyDefiningTy::CoroutineClosure(def_id, ..)
//             | MyDefiningTy::Coroutine(def_id, ..)
//             | MyDefiningTy::FnDef(def_id, ..)
//             | MyDefiningTy::Const(def_id, ..)
//             | MyDefiningTy::InlineConst(def_id, ..) => def_id,
//         }
//     }
// }

// #[derive(PartialEq)]
// #[derive(Debug)]
// pub(crate) enum RegionCtxt {
//     Location(Location),
//     TyContext(TyContext),
//     Free(Symbol),
//     LateBound(Symbol),
//     Existential(Option<Symbol>),
//     Placeholder(Symbol),
//     Unknown,
// }

// /// Returns the "defining type" of the current MIR;
// /// see `MyDefiningTy` for details.
// fn defining_ty<'tcx>(infcx: &MyBorrowckInferCtxt<'tcx>, mir_def: DefId) -> MyDefiningTy<'tcx> {
//     let tcx = infcx.tcx;
//     let typeck_root_def_id = tcx.typeck_root_def_id(mir_def);

//     match tcx.hir().body_owner_kind(mir_def) {
//         BodyOwnerKind::Closure | BodyOwnerKind::Fn => {
//             let defining_ty = tcx.type_of(mir_def).instantiate_identity();

//             println!("defining_ty (pre-replacement): {:?}", defining_ty);

//             let defining_ty = infcx.replace_free_regions_with_nll_infer_vars(FR, defining_ty);

//             match *defining_ty.kind() {
//                 ty::Closure(def_id, args) => MyDefiningTy::Closure(def_id, args),
//                 ty::Coroutine(def_id, args) => MyDefiningTy::Coroutine(def_id, args),
//                 // ty::CoroutineClosure(def_id, args) => {
//                 //     MyDefiningTy::CoroutineClosure(def_id, args)
//                 // }
//                 ty::FnDef(def_id, args) => MyDefiningTy::FnDef(def_id, args),
//                 _ => span_bug!(
//                     tcx.def_span(mir_def),
//                     "expected defining type for `{:?}`: `{:?}`",
//                     mir_def,
//                     defining_ty
//                 ),
//             }
//         }

//         BodyOwnerKind::Const { .. } | BodyOwnerKind::Static(..) => {
//             let identity_args = GenericArgs::identity_for_item(tcx, typeck_root_def_id);
//             if mir_def == typeck_root_def_id {
//                 let args =
//                     infcx.replace_free_regions_with_nll_infer_vars(FR, identity_args);
//                     MyDefiningTy::Const(mir_def, args)
//             } else {
//                 // FIXME this line creates a dependency between borrowck and typeck.
//                 //
//                 // This is required for `AscribeUserType` canonical query, which will call
//                 // `type_of(inline_const_def_id)`. That `type_of` would inject erased lifetimes
//                 // into borrowck, which is ICE #78174.
//                 //
//                 // As a workaround, inline consts have an additional generic param (`ty`
//                 // below), so that `type_of(inline_const_def_id).args(args)` uses the
//                 // proper type with NLL infer vars.
//                 let ty = tcx
//                     .typeck(mir_def)
//                     .node_type(tcx.local_def_id_to_hir_id(mir_def));
//                     // .is_typeck_child(mir_def) // https://doc.rust-lang.org/nightly/nightly-rustc/src/rustc_middle/query/mod.rs.html#2513
//                     // .node_type(tcx.local_def_id_to_hir_id(mir_def));
//                 let args = InlineConstArgs::new(tcx, InlineConstArgsParts {
//                     parent_args: identity_args,
//                     ty,
//                 })
//                 .args;
//                 let args = infcx.replace_free_regions_with_nll_infer_vars(FR, args);
//                 MyDefiningTy::InlineConst(mir_def, args)
//             }
//         }
//     }
// }


// use rustc_middle::ty::{self, ParamEnv, RegionVid, TypingMode};
pub fn my_mir_borrowck(tcx: TyCtxt<'_>, def_id: DefId) {
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
    println!("input_body: {:?}, input_promoted: {:?}", input_body, input_promoted);

    let borrowck_infcx = tcx.infer_ctxt().build();  //TODO: Check if this is correct
    let param_env = tcx.param_env(def_id);
    let infcx = BorrowckInferCtxt { infcx: borrowck_infcx, reg_var_to_origin: RefCell::new(Default::default()), param_env };

    let mut local_names = IndexVec::from_elem(None, &input_body.local_decls);
    println!("local_names: {:?}", local_names);
    for var_debug_info in &input_body.var_debug_info {
        println!("var_debug_info: {:?}", var_debug_info);
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

    let mut body_owned = input_body.clone();
    let mut promoted = input_promoted.to_owned();
    let universal_regions = UniversalRegions::new(&infcx, def_id, param_env);
    // let free_regions = nll::replace_regions_in_mir(&infcx, &mut body_owned, &mut promoted);
    // let result = BorrowCheckResult {
    //     concrete_opaque_types: opaque_type_values,
    //     closure_requirements: opt_closure_req,
    //     used_mut_upvars: mbcx.used_mut_upvars,
    //     tainted_by_errors,
    // };

    // (None, None)
}