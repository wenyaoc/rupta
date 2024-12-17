// Copyright (c) 2024 <Wei Li>.
//
// This source code is licensed under the GNU license found in the
// LICENSE file in the root directory of this source tree.

//! Analysis options.

use itertools::Itertools;

use clap::{Arg, Command};
use clap::error::ErrorKind;
use rustc_tools_util::VersionInfo;


use crate::pta::PTAType;

const RUPTA_USAGE: &str = r#"pta [OPTIONS] INPUT -- [RUSTC OPTIONS]"#;

/// The version information from Cargo.toml.
fn version() -> &'static str {
    let version_info = rustc_tools_util::get_version_info!();
    let version = format!("v{}.{}.{}", version_info.major, version_info.minor, version_info.patch);
    Box::leak(version.into_boxed_str())
}

/// Creates the clap::Command metadata for argument parsing.
fn make_options_parser() -> Command<'static> {
    // We could put this into lazy_static! with a Mutex around, but we really do not expect
    // to construct this more then once per regular program run.
    let parser = Command::new("rupta")
        .no_binary_name(true)
        .override_usage(RUPTA_USAGE)
        .version(version())
        .arg(Arg::new("entry-func-name")
            .long("entry-func")
            .takes_value(true) 
            .help("The name of entry function from which the pointer analysis begins."))
        .arg(Arg::new("entry-func-id")
            .long("entry-id")
            .takes_value(true)
            .value_parser(clap::value_parser!(u32))
            .help("The def_id of entry function from which the pointer analysis begins."))
        .arg(Arg::new("pta-type")
            .long("pta-type")
            .takes_value(true)
            .value_parser(["andersen", "ander", "callsite-sensitive", "cs"])
            .default_value("callsite-sensitive")
            .help("The type of pointer analysis.")
            .long_help("Andersen and callsite-sensitive pointer analyses are supported now."))
        .arg(Arg::new("context-depth")
            .long("context-depth")
            .takes_value(true)
            .value_parser(clap::value_parser!(u32))
            .default_value("1")
            .help("The context depth limit for a context-sensitive pointer analysis."))
        .arg(Arg::new("no-cast-constraint")
            .long("no-cast-constraint")
            .takes_value(false)
            .hide(true)
            .help("Disable the cast optimization that constrains an object cast from a simple pointer type."))
        .arg(Arg::new("stack-filtering")
            .long("stack-filtering")
            .takes_value(false)
            .help("Enable stack filtering in pointer analysis."))
        .arg(Arg::new("compute-loans")
            .long("compute-loans")
            .takes_value(false)
            .help("Compute loans in the analysis."))
        .arg(Arg::new("dump-stats")
            .long("dump-stats")
            .takes_value(false)
            .help("Dump the statistics of the analysis results."))
        .arg(Arg::new("call-graph-output")
            .long("dump-call-graph")
            .takes_value(true)
            .help("Dump the call graph in DOT format to the output file."))
        .arg(Arg::new("pts-output")
            .long("dump-pts")
            .takes_value(true)
            .help("Dump points-to results to the output file."))
        .arg(Arg::new("mir-output")
            .long("dump-mir")
            .takes_value(true)
            .help("Dump the mir of reachable functions to the output file."))
        .arg(Arg::new("unsafe-stats-output")
            .long("dump-unsafe-stats")
            .takes_value(true)
            .help("Dump the statistics of unsafe functions in the analyzed program."))
        .arg(Arg::new("dyn-calls-output")
            .long("dump-dyn-calls")
            .takes_value(true)
            .hide(true)
            .hide(true)
            .help("Dump resolved dynamic callsites with their corresponding call targets.")
            .long_help("Including both calls on dynamic trait objects and calls via function pointers"))
        .arg(Arg::new("type-indices-output")
            .long("dump-type-indices")
            .takes_value(true)
            .hide(true)
            .help("Dump type indices for debugging."))
        .arg(Arg::new("INPUT")
            .multiple(true)
            .help("The input file to be analyzed.")
        );
    parser
}

#[derive(Clone, Debug)]
pub struct AnalysisOptions {
    pub entry_func: String,
    pub entry_def_id: Option<u32>,
    pub pta_type: PTAType,
    // options for context-sensitive analysis
    pub context_depth: u32,
    // options for handling cast propagation
    pub cast_constraint: bool,
    pub stack_filtering: bool,
    pub compute_loans: bool,
    pub dump_stats: bool,
    pub call_graph_output: Option<String>,
    pub pts_output: Option<String>,
    pub mir_output: Option<String>,
    pub type_indices_output: Option<String>,
    pub dyn_calls_output: Option<String>,
    pub unsafe_stat_output: Option<String>,
    pub func_ctxts_output: Option<String>, 
}

impl Default for AnalysisOptions {
    fn default() -> Self {
        Self {
            entry_func: String::new(),
            entry_def_id: None,
            pta_type: PTAType::CallSiteSensitive,
            context_depth: 1,
            cast_constraint: true,
            stack_filtering: false,
            compute_loans: false,
            dump_stats: true,
            call_graph_output: None,
            pts_output: None,
            mir_output: None,
            type_indices_output: None,
            dyn_calls_output: None,
            unsafe_stat_output: None,
            func_ctxts_output: None,
        }
    }
}

impl AnalysisOptions {
    /// Parses options from a list of strings. Any content beyond the leftmost `--` token
    /// will be returned (excluding this token).
    pub fn parse_from_args(&mut self, args: &[String], from_env: bool) -> Vec<String> {
        let mut pta_args_end = args.len();
        let mut rustc_args_start = 0;
        if let Some((p, _)) = args.iter().find_position(|s| s.as_str() == "--") {
            pta_args_end = p;
            rustc_args_start = p + 1;
        }
        let pta_args = &args[0..pta_args_end];
        let matches = if !from_env && rustc_args_start == 0 {
            // The arguments may not be intended for RUPTA and may get here via some tool, so do not 
            // report errors here, but just assume that the arguments were not meant for RUPTA.
            match make_options_parser().try_get_matches_from(pta_args.iter())
            {
                Ok(matches) => {
                    // Looks like these are RUPTA options after all and there are no rustc options.
                    rustc_args_start = args.len();
                    matches
                }
                Err(e) => match e.kind() {
                    ErrorKind::DisplayHelp => {
                        eprintln!("{e}");
                        return args.to_vec();
                    }
                    ErrorKind::UnknownArgument => {
                        // Just send all of the arguments to rustc.
                        // Note that this means that RUPTA options and rustc options must always
                        // be separated by --. I.e. any RUPTA options present in arguments list
                        // will stay unknown to RUPTA and will make rustc unhappy.
                        return args.to_vec();
                    }
                    _ => {
                        e.exit();
                    }
                },
            }
        } else {
            // This will display error diagnostics for arguments that are not valid for RUPTA.
            match make_options_parser().try_get_matches_from(pta_args.iter()) {
                Ok(matches) => {
                    if rustc_args_start == 0 {
                        rustc_args_start = args.len();
                    }
                    matches
                }
                Err(e) => {
                    e.exit();
                }
            }
        };

        if let Some(s) = matches.get_one::<String>("entry-func-name") {
            self.entry_func = s.clone();
        }
        self.entry_def_id = matches.get_one::<u32>("entry-func-id").cloned();

        if matches.contains_id("pta-type") {
            self.pta_type = match matches.get_one::<String>("pta-type").unwrap().as_str() {
                "andersen" | "ander" => PTAType::Andersen,
                "callsite-sensitive" | "cs" => PTAType::CallSiteSensitive,
                _ => unreachable!(),
            }
        }
        
        if let Some(depth) = matches.get_one::<u32>("context-depth") {
            self.context_depth = *depth;
        }

        self.cast_constraint = !matches.contains_id("no-cast-constraint");
        self.stack_filtering = matches.contains_id("stack-filtering");
        self.compute_loans = matches.contains_id("compute-loans");
        self.dump_stats = matches.contains_id("dump-stats");
        self.call_graph_output = matches.get_one::<String>("call-graph-output").cloned();
        self.pts_output = matches.get_one::<String>("pts-output").cloned();
        self.mir_output = matches.get_one::<String>("mir-output").cloned();
        self.unsafe_stat_output = matches.get_one::<String>("unsafe-stats-output").cloned();
        self.dyn_calls_output = matches.get_one::<String>("dyn-calls-output").cloned();
        self.type_indices_output = matches.get_one::<String>("type-indices-output").cloned();

        // If the user provide the input source code file path before the `--` token, 
        // add it to the rustc arguments.
        let mut rustc_args = args[rustc_args_start..].to_vec();
        if let Some(input) = matches.get_many::<String>("INPUT") {
            rustc_args.extend(input.cloned())
        } 
        
        rustc_args
    }

}
