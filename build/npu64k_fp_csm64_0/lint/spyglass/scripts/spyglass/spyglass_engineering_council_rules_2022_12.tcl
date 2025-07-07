#===============================================================================
# SYNOPSYS CONFIDENTIAL - This is an unpublished, confidential and proprietary
# work of Synopsys, Inc., and may be subject to patent, copyright, trade secret,
# and/or other intellectual property or contractual protection.This work may
# only be used in accordance with the terms and conditions of a written license
# agreement with Synopsys, Inc.  All other use or distribution of this work is
# strictly prohibited.
#-------------------------------------------------------------------------------
# Versions     :
# 2015.12 December 17th, 2015
#   First Release
# 2016.02 February 24th, 2016
#   Remove invalid ignorerules (rules can't be disabled)
#   Disable Clock-Reset-Detail report (may consume too much disk space)
# 2016.07 June 7th, 2016
#   Linting Mandatory rules update.
# 2017.01 January 25th, 2017
#   Unwaived 5 GW2016.06 rules.
#   Disable automatic qualifier detection in synchronization schemes
# 2017.07 June 25th, 2017
#   No longer ignore rules included in default GuideWare
#   Review rules added to lint/lint_rtl
# 2018.03 March 23th, 2018
#   Lint:
#     4 rules added: DisallowCaseX-ML; NoGenLabel-ML; NoTab; STARC05-1.1.1.1
#     4 parameters updated: report_flop_reset_loop; strict=CombLoop; handle_equivalent_drivers; handle_const_expressions
#   Add new rules to cdc/cdc_verify_struct
#     Ar_converge02
#     Ar_glitch01
#     Ac_glitch02
#     Ac_glitch04
#     Reset_info09b
#   Disallow combinational logic in CDC paths
#   Disable propagation of CDC qualifiers
#   Remove "remove_overlap" from reset_reduce_pessimism parameter
#   Remove rule ignore of dftMandatory_Constraint_Check (requires waiver)
#   Ignore inferred nets in DFT TA_09 rule
#   Disable Reactive mode in TXV MCP analysis
#   Review default parametrization of TXV goal
#   Improve global options for hierarchical analysis
#   Set handlememory option
#   Make project read only
# 2019.01 January 29th, 2019
#   Global:
#     Set parameter show_all_sdc_violations=yes
#   Lint:
#     17 rules added: OneModule-ML; sim_race07; STARC05-2.2.3.1; UndrivenNet-ML; UndrivenOutTermNLoaded-ML; W146; W164a; W241; W287a; W401;
#                     W402b; W464; W468; W497; W527; W552; W576
#     1 rule removed: W484 --> W164a
#     2 parameters updated: check_dup_label; genlabeltype
#     lint/design_audit: Add Clock_info15 rule
#   CDC:
#     cdc/cdc_verify_struct: Set parameter ignore_bus_resets=no
#     cdc/cdc_verify_struct: Remove override allow_combo_logic=no
# 2019.01-1 May 19th, 2019
#   Lint:
#     1 parameters corrected: nocheckoverflow (turned off for W164a).
# 2019.09 September 23rd, 2019
#   Lint:
#     3 rules added: AutomaticFuncTask-ML, ImproperRangeIndex-ML, InstPortConnType-ML.
#   CDC:
#     Include "all_potential_resets" in reset_reduce_pessimism parameter
# 2020.05 May 26th, 2020
#   Improve support for SystemVerilog RTL:
#     Enable option synthesize_logic_inside_sv_interface
#   CDC:
#     Reduce convergance analysis propagation to a single sequential level
# 2020.05-1 September 24th, 2020
#   CDC:
#     Disable automatic qualifier detection in clock gating synchronization scheme
# 2021.03 March 11th, 2021
#   No changes. Only change in Spyglass Version and Guideware Version
# 2021.11 November 22nd, 2021
#   Lint:
#     Remove duplicate STARC05-2.8.3.3
#   RDC:
#     Enable report_cgc_dest_rdc
# 2022.12 November 29th, 2022
#   Lint:
#     Added: lint_rtl_enhanced correction (ignoring some rules and changing some parameters).
#   RDC:
#     Disable report_cgc_dest_rdc due to having worse results
#===============================================================================

################################################################################################################################################################
# Global configuration

# Automatically handle memory management when inferred RAM is above mthresh
set_option handlememory                yes
# Include interface information in abstracts and use them in hierarchical flow
set_option include_block_interface     abstract
set_option use_block_interface         yes
# Do not include references to project's internal constraints files
set_option decompile_block_constraints yes
# Do not allow core.prj to be written
set_option project_read_only           yes
# Synthesize logic of interface statements
set_option synthesize_logic_inside_sv_interface 1

# Show all detected violations during SDC parsing
set_parameter show_all_sdc_violations  yes

################################################################################################################################################################
# Lint configuration
current_goal lint/lint_rtl
set_goal_option addrules        AutomaticFuncTask-ML;           # Use automatic functions/tasks in modules and interfaces.
set_goal_option addrules        DisallowCaseX-ML;               # Do not use casex constructs in the design.
set_goal_option addrules        ImproperRangeIndex-ML;          # Possible discrepancy in the range index or slice of an array.
set_goal_option addrules        InstPortConnType-ML;            # Output and inout port connection in instantiation should not be of type reg.
set_goal_option addrules        infiniteloop;                   # While/forever loop has no break control.
set_goal_option addrules        mixedsenselist;                 # Mixed conditions in sensitivity list may not be synthesizable.
set_goal_option addrules        NoGenLabel-ML;                  # Unnamed generate block or duplicate generate block names used in module.
set_goal_option addrules        NoTab;                          # Tab detected in design.
set_goal_option addrules        OneModule-ML;                   # At most one module per file.
set_goal_option addrules        ReserveName;                    # A reserve name has been used.
set_goal_option addrules        ReserveNameSystemVerilog-ML;    # System Verilog IEEE-1800 reserved word used.
set_goal_option addrules        SameControlNDataNet-ML;         # Control (set/reset) signal used as data for the same flop.
set_goal_option addrules        SelfDeterminedExpr-ML;          # Self determined expression present in the design.
set_goal_option addrules        SetBeforeRead-ML;               # Signal is read before being set.
set_goal_option addrules        sim_race07;                     # Non-blocking assignment should not be used in clock or enable path.
#reuse-pragma startSub module_name [IncludeIf {[get_design_prefix] eq "" && [get_file_prefix] eq ""} %subText]
set_goal_option addrules        STARC05-1.1.1.1;                # Source file name should be same as the name of the module in the file.
#reuse-pragma endSub module_name
set_goal_option addrules        STARC05-2.10.1.4a;              # Signals must not be compared with X or Z.
set_goal_option addrules        STARC05-2.10.1.4b;              # Signals must not be compared with values containing X or Z.
set_goal_option addrules        STARC05-2.2.3.1;                # Non-blocking assignment should not be used in combinational always blocks.
set_goal_option addrules        STARC05-2.3.4.1;                # Do not specify flip-flop initial value using initial construct.
set_goal_option addrules        STARC05-2.5.1.7;                # Do not use tristate output in the conditional expression of an if statement.
set_goal_option addrules        STARC05-2.5.1.9;                # Do not enter a tristate output in the selection expression of casex and casez statement.
set_goal_option addrules        STARC05-2.8.1.3;                # case constructs should not have overlapping clause conditions.
set_goal_option addrules        STARC05-2.8.1.5;                # Do not use the full_case directive.
set_goal_option addrules        STARC05-2.8.3.3;                # Do not use  //synopsys full_case pragma when all conditions are not described as case clause or the default clause is missing.
set_goal_option addrules        STARC05-2.8.5.1;                # Do not use the parallel_case directive.
set_goal_option addrules        STARC05-2.9.1.2a;               # Loop variable of "for" construct must have constant initial value.
set_goal_option addrules        STARC05-2.9.1.2b;               # Terminating condition of "for" constructs must be a constant.
set_goal_option addrules        STARC-2.3.4.3;                  # A flip-flop should have an asynchronous set or an asynchronous Reset.
set_goal_option addrules        UndrivenNet-ML;                 # Undriven but loaded net is detected in the design.
set_goal_option addrules        UndrivenOutPort-ML;             # Undriven but loaded output port of a module detected.
set_goal_option addrules        UnrecSynthDir-ML;               # Synthesis directive is not recognized.
set_goal_option addrules        W127;                           # Delay values should not contain X(unknown value) or Z(high-impedance state).
set_goal_option addrules        W146;                           # Use named-association rather than positional association to connect to an instance.
set_goal_option addrules        W156;                           # Do not connect busses in reverse order.
set_goal_option addrules        W163;                           # Truncation of bits in constant integer conversion.
set_goal_option addrules        W164a;                          # Identifies assignments in which the LHS width is less than the RHS width.
set_goal_option addrules        W167;                           # Module has no input or output ports.
set_goal_option addrules        W188;                           # Do not write to input ports.
set_goal_option addrules        W193;                           # Empty statement.
set_goal_option addrules        W239;                           # Hierarchical references may not be synthesizable.
set_goal_option addrules        W241;                           # Output is never set.
set_goal_option addrules        W263;                           # Case clause labels whose widths do not match the width of the corresponding case construct selector.
set_goal_option addrules        W287a;                          # Module instances where nets connected to input ports are not driven.
set_goal_option addrules        W391;                           # Design has a clock driving it on both edges.
set_goal_option addrules        W401;                           # Clock signal is not an input to the design unit
set_goal_option addrules        W402b;                          # Asynchronous set/reset signal is not an input to the module
set_goal_option addrules        W423;                           # A port with a range is redeclared with a different range.
set_goal_option addrules        W468;                           # Index variable is too short.
set_goal_option addrules        W464;                           # Unrecognized synthesis directive used in the design.
set_goal_option addrules        W479;                           # Loop step statement is incorrect.
set_goal_option addrules        W497;                           # Bus signals that are not completely set in the design.
set_goal_option addrules        W527;                           # Dangling else in sequence of if conditions. Make sure nesting is correct.
set_goal_option addrules        W552;                           # Different bits of a bus are driven in different sequential blocks.
set_goal_option addrules        W576;                           # Logical operation on a vector.
set_goal_option addrules        WRN_47;                         # Zero or negative repetition multiplier used in multiple concatenation.

set_goal_option ignorerules     NoFeedThrus-ML;                 # Block should not contain feed-throughs.

set_parameter        check_dup_label            yes;            # Used by NoGenLabel-ML.
set_parameter        genlabeltype               all;            # Used by NoGenLabel-ML.
set_parameter        handle_const_expressions   yes;            # Used by SelfDeterminedExpr-ML.
set_parameter        handle_equivalent_drivers  yes;            # Used by W415.
set_parameter        report_flop_reset_loop     yes;            # Used by CombLoop.
set_parameter        strict                     CombLoop;       # Used by CombLoop.
set_parameter        nocheckoverflow            W116,W164b,W164c,W110,W486,W263,W362,AsgnOverflow-ML,STARC-2.1.3.1,STARC-2.8.1.6,STARC-2.10.3.1,STARC-2.10.3.2a,STARC-2.10.3.2b,STARC-2.10.3.2c,STARC-3.2.3.2,STARC02-2.1.3.1,STARC02-2.8.1.6,STARC02-2.10.3.1,STARC02-2.10.3.2a,STARC02-2.10.3.2b,STARC02-2.10.3.2c,STARC02-3.2.3.2,STARC05-2.1.3.1,STARC05-2.8.1.6,STARC05-2.10.3.1,STARC05-2.10.3.2a,STARC05-2.10.3.2b,STARC05-2.10.3.2c,STARC05-3.2.3.2;


################################################################################################################################################################
# Lint RTL Enhanced goal configuration
current_goal lint/lint_rtl_enhanced
set_goal_option ignorerules     STARC05-1.1.1.1;
set_goal_option ignorerules     CMD_overloadrule01;
set_goal_option ignorerules     HdlLibDuCheck_03;
set_goal_option ignorerules     W339;
set_parameter                   checkfullbus            yes;
set_goal_option ignorerules     W316;
set_goal_option ignorerules     PragmaComments-ML;
set_parameter                   nocheckoverflow            W116,W110,W263,W362,STARC05-2.1.3.1,STARC05-2.8.1.6,STARC05-2.10.3.2a;

################################################################################################################################################################
# Lint design_audit goal configuration
current_goal lint/design_audit
set_goal_option addrules        Clock_info15;                   # Want this to be enabled in this goal as needed for the clock extraction

################################################################################################################################################################
# CDC verify_struct goal configuration
current_goal cdc/cdc_verify_struct

proc cdc_common_parameters {} {
  set_parameter reset_reduce_pessimism same_data_reset_flop,all_potential_resets; # Remove "remove_overlap" included by default in GuideWare
                                                                                  # Add "all_potential_resets"
}

set_parameter conv_sync_seq_depth    1;                         # Number of sequential elements that a synchronized signal can be propagated through during convergence analysis
set_parameter cdc_qualifier_depth    0;                         # Number of sequential elements between the qualifier point till the point of synchronization
set_parameter enable_sync            no;                        # Disable automatic qualifier detection in Synchronized Enable synchronization scheme
set_parameter enable_and_sync        no;                        # Disable automatic qualifier detection in AND Gate synchronization scheme
set_parameter enable_mux_sync        none;                      # Disable automatic qualifier detection in MUX-Select Sync synchronization scheme
set_parameter enable_multiflop_sync  no;                        # Disable automatic qualifier detection in Multi-Flop synchronization scheme
set_parameter enable_clock_gate_sync no;                        # Disable automatic qualifier detection in Clock Gating synchronization scheme
set_parameter ignore_bus_resets      no;                        # Don't ignore resets just because they are an index of a bus
set_goal_option addrules Ar_converge02;                         # Reports a reset signal which converges on data and reset pin of same flop
set_goal_option addrules Ar_glitch01;                           # Reports unsynchronized clock domain crossings subject to glitches because of glitch-prone MUX implementations
set_goal_option addrules Ac_glitch02;                           # Reports clock domain crossings that are subject to glitches because of a reconverging source
set_goal_option addrules Ac_glitch04;                           # Reports glitches on synchronized data path crossings or unsynchronized crossings
set_goal_option addrules Reset_info09b;                         # Reports asynchronous reset nets that are tied to a constant value
set_goal_option overloadrules Reset_info09b+severity=Warning
cdc_common_parameters

################################################################################################################################################################
# CDC abstract goal configuration
current_goal cdc/cdc_abstract

cdc_common_parameters

################################################################################################################################################################
# RDC verify_struct goal configuration
current_goal rdc/rdc_verify_struct

################################################################################################################################################################
# DFT dft_best_practices goal configuration
current_goal dft/dft_best_practice

set_parameter dft_TA_09_ignore_generated_nets on;               # Inferred nets will not exist in final netlist and can be ignored during DFT analysis (decreases number of false TA_09 errors)

################################################################################
# TXV fp_mcp_verification configuration
current_goal txv_verification/fp_mcp_verification

set_parameter txv_mcp_enable_type        flop_en,dp_mux;        # Specifies the type of enable to be considered for MCP verification
set_parameter txv_mcp_common_enable_only no;                    # Include all enables present in data path instead of only common data path enables in MCP verification
set_parameter txv_mcp_enable_grouping    no;                    # Enables grouping of multiple partitions of a multicycle path constraint based on the common source or destination enable
set_parameter txv_mcp_reactive_flow      no;                    # Disable Reactive mode in Multicycle Path verification
set_parameter txv_solver_run_time        10h;                   # Runtime limit of the formal engines for functional analysis of a single sdc_data
set_goal_option overloadrules Txv_InitState01+severity=Info;    # Reduce severity to Info

################################################################################################################################################################
# Global configurations
current_goal none

