// Copyright (c) 2024 <Wei Li>.
//
// This source code is licensed under the GNU license found in the
// LICENSE file in the root directory of this source tree.

use std::collections::HashSet;
use std::fmt::{Debug, Formatter, Result};
use std::rc::Rc;
use std::time::Duration;

use rustc_middle::ty::TyCtxt;

use super::propagator::propagator::Propagator;
use super::PointerAnalysis;
use super::strategies::stack_filtering::StackFilter;
use crate::graph::call_graph::CallGraph;
use crate::graph::func_pag::FuncPAG;
use crate::mir::call_site::{CallSite, BaseCallSite, CallType, AssocCallGroup};
use crate::mir::function::FuncId;
use crate::mir::analysis_context::AnalysisContext;
use crate::mir::path::Path;
use crate::pta::*;
use crate::rta::rta::RapidTypeAnalysis;
use crate::util::chunked_queue;
use crate::util::pta_statistics::AndersenStat;
use crate::util::results_dumper;
use std::collections::HashMap;
use crate::builder::fpag_builder::{FuncLoanMap, PathLoanMap};
use crate::builder::loan_builder::LoanBuilder;

pub struct AndersenPTA<'pta, 'tcx, 'compilation> {
    /// The analysis context
    pub(crate) acx: &'pta mut AnalysisContext<'tcx, 'compilation>,
    /// Points-to data
    pub(crate) pt_data: DiffPTDataTy,
    /// Pointer Assignment Graph
    pub(crate) pag: PAG<Rc<Path>>,
    /// Call graph
    pub call_graph: CallGraph<FuncId, BaseCallSite>,

    /// Records the functions that have been processed
    pub(crate) processed_funcs: HashSet<FuncId>,

    /// Iterator for reachable functions
    rf_iter: chunked_queue::IterCopied<FuncId>,

    /// Iterator for address_of edges in pag
    addr_edge_iter: chunked_queue::IterCopied<EdgeId>,

    // Inter-procedure edges created for dynamic calls, which will be iterated
    // as initial constraints in propagator
    inter_proc_edges_queue: chunked_queue::ChunkedQueue<EdgeId>,

    assoc_calls: AssocCallGroup<NodeId, FuncId, Rc<Path>>,

    pub stack_filter: Option<StackFilter<FuncId>>,
    pub pre_analysis_time: Duration,

    pub loans: HashMap<FuncId, FuncLoanMap>,
}

impl<'pta, 'compilation, 'tcx> Debug for AndersenPTA<'pta, 'compilation, 'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "AndersenPTA".fmt(f)
    }
}

/// Constructor
impl<'pta, 'tcx, 'compilation> AndersenPTA<'pta, 'tcx, 'compilation> {
    pub fn new(acx: &'pta mut AnalysisContext<'tcx, 'compilation>) -> Self {
        let call_graph = CallGraph::new();
        let rf_iter = call_graph.reach_funcs_iter();
        let pag = PAG::new();
        let addr_edge_iter = pag.addr_edge_iter();
        AndersenPTA {
            acx,
            pt_data: DiffPTDataTy::new(),
            pag,
            call_graph,
            processed_funcs: HashSet::new(),
            rf_iter,
            addr_edge_iter,
            inter_proc_edges_queue: chunked_queue::ChunkedQueue::new(),
            assoc_calls: AssocCallGroup::new(),
            stack_filter: None,
            pre_analysis_time: Duration::ZERO,
            loans: HashMap::default(),
        }
    }

    #[inline]
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.acx.tcx
    }

    /// Process statements in reachable functions.
    fn process_reach_funcs(&mut self) {
        while let Some(func_id) = self.rf_iter.next() {
            if !self.processed_funcs.contains(&func_id) {
                let func_ref = self.acx.get_function_reference(func_id);
                info!(
                    "Processing function {:?} {}", func_id, func_ref.to_string(),
                );
                if self.pag.build_func_pag(self.acx, func_id) {
                    self.add_fpag_edges(func_id);
                    self.process_calls_in_fpag(func_id);
                    self.get_loans(func_id);
                }
            }
        }
    }
    pub fn get_loans(&mut self, func_id: FuncId) {
        let fpag = unsafe { &*(self.pag.func_pags.get(&func_id).unwrap() as *const FuncPAG) };
        let loans = &fpag.func_loans;
        self.loans.insert(func_id, loans.clone());
    }

    // pub fn compute_loans(&mut self, func_id: FuncId) {
        
    //     let def_id = self.acx.get_function_reference(func_id).def_id;
    //     // let mut loans = FuncLoanMap::default();
    //     if let Some(_local_def_id) = def_id.as_local() {
    //         // Self::compute_loans(acx.tcx, def_id);
    //         let loan_builder = LoanBuilder::new(self.acx.tcx, def_id);
    //         let loans = loan_builder.compute_loans();
    //         // self.loans.insert(func_id, loans.clone());
    //     }
    // }

    /// Adds internal edges of a function pag to the whole program's pag.
    /// The function pag for the given def_id should be built before calling this function.
    pub fn add_fpag_edges(&mut self, func_id: FuncId) {
        if self.processed_funcs.contains(&func_id) {
            return;
        }

        let fpag = unsafe { &*(self.pag.func_pags.get(&func_id).unwrap() as *const FuncPAG) };
        let edges_iter = fpag.internal_edges_iter();
        for (src, dst, kind) in edges_iter {
            if let Some(edge_id) = self.pag.add_edge(src, dst, kind.clone()) {
                if src.is_promoted_constant() || src.is_static_variable() {
                    self.inter_proc_edges_queue.push(edge_id);
                }
            }
        }

        // add edges in the promoted functions
        if let Some(promoted_funcs) = self.pag.promoted_funcs_map.get(&func_id) {
            let promoted_funcs = unsafe { &*(promoted_funcs as *const HashSet<FuncId>) };
            for promoted_func in promoted_funcs {
                self.add_fpag_edges(*promoted_func);
            }
        }
        // add edges in the related static functions
        if let Some(static_funcs) = self.pag.involved_static_funcs_map.get(&func_id) {
            let static_funcs = unsafe { &*(static_funcs as *const HashSet<FuncId>) };
            for static_func in static_funcs {
                self.add_fpag_edges(*static_func);
            }
        }

        self.processed_funcs.insert(func_id);
    }

    fn process_calls_in_fpag(&mut self, func_id: FuncId) {
        let fpag = unsafe { &*(self.pag.get_func_pag(&func_id).unwrap() as *const FuncPAG) };
        // For static dispatch callsites, the call target can be resolved directly.
        for (callsite, callee) in &fpag.static_dispatch_callsites {
            self.add_call_edge(callsite, callee);
            self.call_graph.set_callsite_type(callsite.into(), CallType::StaticDispatch);
        }

        // For special callsites, we have summary the effects. Therefore we only add call edge
        // for the callsite without adding arg --> param and ret --> dst edges.
        for (callsite, callee) in &fpag.special_callsites {
            self.call_graph.add_edge(callsite.into(), func_id, *callee);
            // To fix: this may classify some special dynamic calls into static calls
            self.call_graph.set_callsite_type(callsite.into(), CallType::StaticDispatch);
        }

        let mut dyn_node_id = |dyn_obj: &Rc<Path>| {
           self.pag.get_or_insert_node(dyn_obj)
        };

        // For std::ops::call, dynamic and fnptr callsites, add them to the dynamic_calls and fnptr_calls maps.
        for (dyn_fn_obj, callsite) in &fpag.dynamic_fntrait_callsites {
            self.assoc_calls.add_dynamic_fntrait_call(dyn_node_id(dyn_fn_obj), callsite.clone());
            self.call_graph.set_callsite_type(callsite.into(), CallType::DynamicFnTrait);
        }
        for (dyn_var, callsite) in &fpag.dynamic_dispatch_callsites {
            self.assoc_calls.add_dynamic_dispatch_call(dyn_node_id(dyn_var), callsite.clone());
            self.call_graph.set_callsite_type(callsite.into(), CallType::DynamicDispatch);
        }
        for (fn_ptr, callsite) in &fpag.fnptr_callsites {
            self.assoc_calls.add_fnptr_call(self.pag.get_or_insert_node(fn_ptr), callsite.clone());
            self.call_graph.set_callsite_type(callsite.into(), CallType::FnPtr);
        }
    }

    // Add new call edges to pag
    fn process_new_calls(&mut self, new_calls: &Vec<(Rc<CallSite>, FuncId)>) {
        for (callsite, callee_id) in new_calls {
            self.add_call_edge(callsite, callee_id);
        }
        self.process_reach_funcs();
    }

    fn process_new_call_instances(&mut self, new_call_instances: &Vec<(Rc<CallSite>, Rc<Path>, FuncId)>) {
        for (callsite, _instance, callee_id) in new_call_instances {
            self.add_call_edge(callsite, callee_id);
        }
        self.process_reach_funcs();
    }

    fn add_call_edge(&mut self, callsite: &Rc<CallSite>, callee: &FuncId) {
        let caller = callsite.func;
        if !self.call_graph.add_edge(callsite.into(), caller, *callee) {
            return; 
        }
        let new_inter_proc_edges = self.pag.add_inter_procedural_edges(self.acx, callsite, *callee);
        for edge in new_inter_proc_edges {
            self.inter_proc_edges_queue.push(edge);
            self.add_page_edge_func(edge, callsite.func);
        }
    }

    fn add_page_edge_func(&mut self, edge: EdgeId, func: FuncId) {
        if let Some(sf) = &mut self.stack_filter {
            sf.add_pag_edge_in_func(edge, func);
        }
    }

    #[inline]
    pub fn get_pt_data(&self) -> &DiffPTDataTy {
        &self.pt_data
    }

}

impl<'pta, 'tcx, 'compilation> PointerAnalysis<'tcx, 'compilation> for AndersenPTA<'pta, 'tcx, 'compilation> {
    fn pre_analysis(&mut self) {
        if !self.acx.analysis_options.stack_filtering {
            return;
        }
        info!("Start pre-analysis");
        let mut rta = RapidTypeAnalysis::new(&mut self.acx);
        rta.analyze();
        self.pre_analysis_time += rta.analysis_time;
        self.stack_filter = Some(StackFilter::new(rta.call_graph));
        self.pre_analysis_time += self.stack_filter.as_ref().unwrap().fra_time();
        println!("Pre-analysis time {}", 
            humantime::format_duration(self.pre_analysis_time).to_string()
        );
    }

    /// Initialize the analysis.
    fn initialize(&mut self) {
        // add the entry point to the call graph
        let entry_point = self.acx.entry_point;
        let entry_func_id = self.acx.get_func_id(entry_point, self.tcx().mk_args(&[]));
        self.call_graph.add_node(entry_func_id);

        // process statements of reachable functions
        self.process_reach_funcs();
    }

    /// Solve the worklist problem using Propagator.
    fn propagate(&mut self) {
        let mut iter_proc_edge_iter = self.inter_proc_edges_queue.iter_copied();
        // Solve until no new call relationship is found.
        loop {
            let mut new_calls: Vec<(Rc<CallSite>, FuncId)> = Vec::new();
            let mut new_call_instances: Vec<(Rc<CallSite>, Rc<Path>, FuncId)> = Vec::new();
            let mut propagator = Propagator::new(
                self.acx,
                &mut self.pt_data,
                &mut self.pag,
                &mut new_calls,
                &mut new_call_instances,
                &mut self.addr_edge_iter,
                &mut iter_proc_edge_iter,
                &mut self.assoc_calls,
                self.stack_filter.as_mut(),
                &self.loans,
            );
            propagator.solve_worklist();

            if new_calls.is_empty() && new_call_instances.is_empty() {
                break;
            } else {
                self.process_new_calls(&new_calls);
                self.process_new_call_instances(&new_call_instances);
            }
        }
    }

    /// Finalize the analysis.
    fn finalize(&self) {
        // dump call graph, points-to results
        results_dumper::dump_results(self.acx, &self.call_graph, &self.pt_data, &self.pag);

        // dump pta statistics
        let pta_stat = AndersenStat::new(self);
        pta_stat.dump_stats();
    }

}
