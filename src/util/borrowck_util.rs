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