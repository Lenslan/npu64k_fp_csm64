puts "Info: Running script [info script]\n"
set start_time [date]

source -echo ./setup/setup.tcl

set_user_units -type power -value 1W

###############################################################################
# Library creation
###############################################################################

if {[file exists ${DESIGN_LIBRARY}]} {
    puts "Warning: Design library '${DESIGN_LIBRARY}' already existed, deleting..."
    file delete -force ${DESIGN_LIBRARY}
}

puts "Info: search_path is=\n${search_path}"

if {[file exists [which ${TECH_FILE}]]} {
    # Preferred : use tech file
    create_lib ${DESIGN_LIBRARY} -ref_libs ${REFERENCE_LIBRARY} -technology ${TECH_FILE}
} elseif {${TECH_LIB} != ""} {
    # Else use Tech NDM lim
    create_lib ${DESIGN_LIBRARY} -ref_libs ${REFERENCE_LIBRARY} -use_technology_lib ${TECH_LIB}
} else {
    # No target technology, we see worst timing
    create_lib ${DESIGN_LIBRARY} -ref_libs ${REFERENCE_LIBRARY}
}

###############################################################################
# Read in the RTL Design, analyze, elaborate and link
###############################################################################

#Enable DMM
#Disabling for showing the violations
if {${ENABLE_DMM}} {
    set_current_mismatch_config auto_fix
}
get_current_mismatch_config

#set_app_options -name hdlin.elaborate.ff_infer_async_set_reset -value true
if {${RTLA_PDM_UPF}} {
    puts "Enable UPF ..."
    set_app_options -name hdlin.naming.upf_compatible -value true
}

set_app_options -name hdlin.autoread.sverilog_extensions -value {.sv .svh .sverilog}
#set_app_options -name hdlin.autoread.verilog_extensions  -value {.def}
set_app_options -name hdlin.autoread.verilog_extensions  -value {.v .vh .def}
set_app_options -name hdlin.naming.upf_compatible        -value true
set_app_options -name hdlin.naming.sverilog_union_member -value true
puts "sverilog_extensions = [get_app_option_value -name hdlin.autoread.sverilog_extensions]"
puts "verilog_extensions  = [get_app_option_value -name hdlin.autoread.verilog_extensions]"
puts "exclude_extensions  = [get_app_option_value -name hdlin.autoread.exclude_extensions]"

analyze -autoread -recursive \
    -output_script ${DESIGN_NAME}_fm_read_verilog.tcl \
    ${RTL_SOURCE_FILES}

# Adding '-top' to 'analyze -autoread' causes problems with SystemVerilog packages
# without the '-top' argument all files will be analysed to resolve dependencies
# before giving up
#   -top ${DESIGN_NAME}

#analyze -format sverilog -top ${DESIGN_NAME} -vcs {<VCS_args>}

elaborate ${DESIGN_NAME}
set_top_module ${DESIGN_NAME}
saif_map -start
source -echo ./scripts/rtla_app_opts.tcl

redirect -tee -file ${rptpfx}.design_mismatch.rpt       {report_design_mismatch -verbose}
redirect -tee -file ${rptpfx}.design_hier.rpt           {report_design -hierarchical}

set done_elab_time [date]
echo $done_elab_time > ${WORK_DIR}/done.elab

save_lib -all

###############################################################################
# Checking for combinational loops
###############################################################################

if { ! (($SDC_ONLY==2 || $ELAB_ONLY==2) && $DESIGN_NAME=="npu_top") } {

  redirect -compress -file check_timing.rpt.gz {check_timing -all}

  if { [catch {exec zgrep "TCK-011" check_timing.rpt.gz}] == "0" } {
    puts "Error-NPU: Combinational loop detected: [exec zgrep "TCK-011" check_timing.rpt.gz]"
    puts "Exiting RTLA due to Combinational loop error!! See check_timing.rpt.gz for more details"
    exit 1
  } else {
    puts "Info: No combinational loop detected"
  }
} else {
  puts "Skipping check_timing ($ELAB_ONLY , $DESIGN_NAME)"
}

###############################################################################

if { $ELAB_ONLY > 0 } {
    puts "Stopping after elaboration"
    if { $ELAB_ONLY == 2 } {
        gui_start
        return
    } else {
        exit 0
    }
}

###############################################################################
# Apply Design Constraints
###############################################################################

set_technology -list
if { ${TECHNOLOGY} eq "03"} {
    puts "Info: technology_node mega switch set for N3E"
    set_technology -node "3e"
} elseif { ${TECHNOLOGY} eq "05"} {
    puts "Info: technology_node mega switch set for N5"
    set_technology -node "5"
} elseif { ${TECHNOLOGY} eq "07"} {
    # FIXME: options '7' and '7+' exists, need to decide which we use by default
    puts "Warning: not selecting between N7 and N7+ yet..."
    #puts "Info: technology_node mega switch set for N7"
    #set_technology -node 7
} elseif { ${TECHNOLOGY} eq "12"} {
    puts "Info: technology_node mega switch set for N12"
    set_technology -node "12"
}
get_attribute [current_block] technology_node


report_ref_libs

if {${DONT_USE_LIST} eq ""} {
    puts "Info: Use all cells (DONT_USE_LIST is empty)"
} else {
    if {${SVT_ONLY}} {
      puts "Info: Use SVT ONLY for the synthesize"
      lappend DONT_USE_LIST */*LVT*
    }

    puts "Info: DONT_USE_LIST: ${DONT_USE_LIST}"
    set_attribute [get_lib_cells ${DONT_USE_LIST}] dont_use true
    report_target_library_subset
}

set sdc_start [date]
echo "SDC Reading start Time $sdc_start"

#  Parasitic and Multi-Corner setup
if {[file exists $TCL_PARASITIC_SETUP_FILE]} {
   puts "Info : Loading TCL_PARASITIC_SETUP_FILE = $TCL_PARASITIC_SETUP_FILE"
   source -echo $TCL_PARASITIC_SETUP_FILE
} else {
    puts "Info: Parasitic file not found (TCL_PARASITIC_SETUP_FILE=$TCL_PARASITIC_SETUP_FILE)"
}
if {[file exists ${TCL_MCMM_SETUP_FILE}]} {
    puts "Info: Loading TCL_MCMM_SETUP_FILE = ${TCL_MCMM_SETUP_FILE}"
    source -echo ${TCL_MCMM_SETUP_FILE}
} else {
    # Read the SDC file (single corner)
    #read_sdc ${CONSTRAINTS_INPUT_FILE}
    source -echo -verbose ${CONSTRAINTS_INPUT_FILE}
}

write_sdc -nosplit -output constraints_flat.sdc
set done_sdc_time [date]
echo "SDC Reading Finish Time $done_sdc_time"
echo $done_sdc_time > ${WORK_DIR}/done.sdc

if { ${TECHNOLOGY} eq "12"} {
    set_app_options -list {plan.flow.target_site_def unit}
}

# Either use a manual/existing floorplan or create one automatically for the RTL_OPT mode
if {${MODE} eq "RTL_OPT"} {
    if {${FLOORPLAN} eq "auto"} {
        set_app_options -name compile.auto_floorplan.enable -value true
        set_auto_floorplan_constraints -core_utilization  ${UTILIZATION_RATIO}
        if {$pin_constraint_sides!=""} {
            set_block_pin_constraints -side $pin_constraint_sides
        }
        report_auto_floorplan_constraints
    } elseif {${FLOORPLAN} eq "def"} {
        read_def ${FLOORPLAN_FILE}
    } elseif {${FLOORPLAN} eq "tcl"} {
        source -echo -verbose ${FLOORPLAN_FILE}
    } else {
        puts "Warning: Specify a value for FLOORPLAN"
    }
}

###############################################################################
# Enables ideal clock transition and network latency for clock-to-data interface pins.
###############################################################################

# enabled to avoid huge timing violation in clock gate paths, where the tool used
# the actual propagated clock # latency and transition time at the clock-to-data pin.

set_app_options -list { time.enable_clock_to_data_analysis true }

###############################################################################
# Register retiming
###############################################################################

# for Flat Implementation  it is only set for the VPX VFPU
if {${REGISTER_RETIME} eq "true"} {
    set_optimize_registers -modules [get_modules *fpu32*]
}

# Register retiming , for Hierarchical Implementation
#Inside mapping_file.tcl,we have to give the setting as:
#alb_cpu_top CONDITIONING_SETTING alb_cpu_top_retiming.tcl
#
#And alb_cpu_top_retiming.tcl has below commands:
#set_app_options -name compile.retiming.group_chained_retiming_modules -value false
#set_optimize_registers -modules [get_modules *fpu32*]
#And change the rtl_opt command to the following
#rtl_opt -host_options khost -block_instances ${BLOCK_INSTANCES} -mapping_file mapping_file.tcl


###############################################################################
# zbuf switches to Bypass error and produce the results,
# Note :- Results might be inaccurate if you bypass the errors.
###############################################################################
if {${BYP_ERR}} {
    #open_block work/archipelago.dlib:archipelago/block_estimation
    #link_block
    set_app_options -name shell.common.monitor_cpu_memory -value true
    set_app_options -list { top_level.continue_flow_on_check_hier_design_errors true }
    ##report_editability -blocks [get_blocks -hier ]
    ##report_editability -blocks [get_blocks -hier -all]
    ##report_editability -blocks [get_blocks]
    ##report_editability -blocks [get_blocks -all ]
    check_hier_design -stage pre_placement
    report_app_options -non_default -hidden
    set zbuf_debug 3
    set zbuf_enable_hfs_multithread false
    set_flow fc/initial_place/physicalInitial/initialPlaceStopHere -tcl { save_block -as initial_place } -after
}

###############################################################################
# App options
###############################################################################
if {${MODE} eq "RTL_OPT"} {
    set_app_options -list { rtl_opt.flow.save_design all_stages  }
    # budget options as Kannan mentioned it will available in built from 0615 versions.
    #set_app_options -list { rtl_opt.conditioning.use_write_budgets true }
    set_app_options -as_user_default -list {naboConverter.supportSkip 7 }
}

#To fix  Low fanout nets  large delay
set_app_options -list { time.analysis_design_delay_calculation_style pdm_physical }

# in 28nm we are seeing huge leakage power numbers so for leakage power improvement
set_app_options -name compile.flow.fast_run_npo_sec_mode -value 2

# For high area optimization
#set_app_options -name compile.flow.high_effort_area  -value true

# Disk space issue in the /tmp/ directory
file mkdir ./TMP
set_app_options -list { shell.common.tmp_dir_path ./TMP }

###############################################################################
#To fix  Low fanout nets  large delay (only for hierarchical runs )
###############################################################################
#High fanout causing huge timing failure in hierarchical design, (on reset_bar net). Follow these steps
#1) Open_block archipelago/budgeting  or archipelago/floorplanning (whichever is available in the list_blocks).
#2) set_host_options -max_cores 16 -submit_command sh -name host
#
#3) rtl_opt -mapping_file mapping.tcl -from block_estimation -host_options host.
#
#/u/abilla/RTLA_makeflow_main/high_fanout_net_mapping.tcl
#
# /u/abilla/RTLA_makeflow_main/mpn.tcl
#
#4) Please copy high_fanout_net_mapping.tcl and mpn.tcl in your area and edit according to your design and then the design


###############################################################################
# Setup UPF in design that have power domains enabled
###############################################################################
if {${RTLA_PDM_UPF}} {
  if {[file exists $UPF_FILE]} {
      load_upf ${NPU_HOME_RLS}/syn/constraints/${DESIGN_NAME}.upf
      commit_upf
  }
}

###############################################################################
# Add VT restrictions
###############################################################################
if {${RTLA_LVT_RATIO} > 0} {
  set_threshold_voltage_group_type -type low_vt {LVT08 LVT11}
  set_multi_vth_constraint -low_vt_percentage ${RTLA_LVT_RATIO}
}


###############################################################################

save_block -as b4_rtlopt
if {${DFT}} {
    #source -echo -verbose scan.tcl
}

if {${USE_MESH}} {
    create_port VDD -direction inout
    create_port VSS -direction inout
    create_net -power VDD
    create_net -ground VSS
    connect_net -net VSS [get_ports VSS]
    connect_net -net VDD [get_ports VDD]
}

save_lib -all

set done_constr_time [date]
echo $done_constr_time > ${WORK_DIR}/done.constraint

report_clocks

if { $SDC_ONLY > 0 } {
    puts "Stopping after applying constraints"
    if { $SDC_ONLY == 2 } {
        gui_start
        return
    } else {
        exit 0
    }
}

###############################################################################
# Synthesize the design in RTL_OPT or Exploration mode
###############################################################################

if {${MODE} eq "RTL_OPT"} {
    if {${IMPLEMENTATION} eq "flat"} {
        if {${USE_MESH}} {
            rtl_opt -to conditioning -host_options khost
            connect_pg_net -automatic
            save_lib -all
            source ${ARC_PRJ_DIR}/scripts/supportFunctions.tcl
            source ${ARC_PRJ_DIR}/scripts/icc2_rm/rm_setup/icc2_common_setup.tcl
            source ${ARC_PRJ_DIR}/scripts/icc2_rm/rm_icc2_flat_scripts/pns_strategies.tcl
            source ${ARC_PRJ_DIR}/scripts/icc2_rm/rm_icc2_flat_scripts/pns_compile.tcl
            rtl_opt -from estimation -host_options khost
        } else {
            rtl_opt -host_options khost
        }
    } elseif {${IMPLEMENTATION} eq "hier"} {
        set_budget_options -add_blocks ${BLOCK_INSTANCES}
        rtl_opt -host_options khost -block_instances ${BLOCK_INSTANCES}
    }
} elseif {${MODE} eq "EXPLORATION"} {
    set explore_cmd "set_explore_design_options"
    set_rtl_power_analysis_options -pwr_shell $PWR_SHELL

    if { ${exp_utilization}!="" } {
        append explore_cmd " -utilization {${exp_utilization}}"
    }
    if { ${exp_aspect_ratio} != "" } {
        append explore_cmd " -aspect_ratio {${exp_aspect_ratio}}"
    }
    if { ${exp_supply_voltage}!="" } {
        append explore_cmd " -supply_voltage {${exp_supply_voltage}}"
    }
    if { ${exp_library}!=""} {
        append explore_cmd " -library {${exp_library}}"
    }
    puts "$explore_cmd"
    eval $explore_cmd
    explore_design -host_options khost
    report_explore_design_result
}

if { ${MODE} eq "RTL_OPT" && ${FLOORPLAN} eq "auto" } {
    set auto_fp_out "${WORK_DIR}/floorplan_auto"
    # Save the automatically generated floorplan
    if {[file exists $auto_fp_out]} { [ exec rm -rf "$auto_fp_out" ] }
    # Large file !
    #write_floorplan -output :$auto_fp_out"
}

set done_rtlopt_time [date]
echo $done_rtlopt_time > ${WORK_DIR}/done.rtl_opt

save_lib -all

###############################################################################
#To fix  Low fanout nets  large delay (only for hierarchical runs )
###############################################################################
#High fanout causing huge timing failure in hierarchical design, (on reset_bar net). Follow these steps
#1) Open_block archipelago/budgeting  or archipelago/floorplanning (whichever is available in the list_blocks).
if { ${IMPLEMENTATION} eq "hier" } {
    set_app_options -list {time.analysis_design_delay_calculation_style pdm_physical}
}

###############################################################################
# Compute Metrics for RTL_OPT mode
###############################################################################

redirect -file ${rptpfx}.clock_gating.rpt {report_clock_gating -nosplit -ungated -gated}
#redirect -file ${rptpfx}.check_netlist.rpt {check_netlist -summary}

if { ${MODE} eq "RTL_OPT" } {
    #current_scenario  functional::typ
    #compute_metrics -congestion -timing

    current_scenario  functional::wc
    compute_metrics -congestion -timing

    set nw 10
    # ---- Basic ----
    redirect -compress ${rptpfx}.check_timing.rpt.gz   {check_timing -all}
    redirect ${rptpfx}.design_all.rpt            {report_design -all}
    redirect ${rptpfx}.clock.rpt                 {report_clock}
    redirect ${rptpfx}.constraints.rpt           {report_constraints}
    redirect ${rptpfx}.threshold_volt_groups.rpt {report_threshold_voltage_groups}

    # ---- Area ----
    redirect ${rptpfx}.area.rpt                  {report_area}
    redirect -append ${rptpfx}.area.rpt          {report_reference}
    redirect ${rptpfx}.area_hier.rpt             {report_area -hierarchy -nosplit}
    redirect -append ${rptpfx}.area_hier.rpt     {report_reference -hierarchical}
    redirect ${rptpfx}.utilization.rpt           {report_utilization}
    redirect ${rptpfx}.report_qor.rpt            {report_qor}

    # ---- Timing ----
    redirect ${rptpfx}.global_timing.rpt                {report_global_timing}
    redirect ${rptpfx}.metrics.timing                   {report_metrics  -timing }
    redirect ${rptpfx}.timing_per_scenario.rpt          {report_metrics -timing -scenario [get_scenarios * -filter "active==true"] -table}
    foreach_in_col sc [get_scenarios -f "active==true"] {
      set sn [get_attr $sc name]
      redirect ${rptpfx}.timing_top500_paths.${sn}.rpt   {report_timing -max_paths 500 -nworst 1 -nets -derate -scenario $sc }
    }
    # Nworst R2R wns
    redirect ${rptpfx}.metrics.timing.nworst_tim_wns_r2r.rpt    {get_metrics -nworst $nw -metric metrics_tim_wns_r2r -local}
    # Nworst R2R tns
    redirect ${rptpfx}.metrics.timing.nworst_tim_tns_r2r.rpt    {get_metrics -nworst $nw -metric metrics_tim_tns_r2r -local}
    # Nworst R2R nvp
    redirect ${rptpfx}.metrics.timing.nworst_tim_nvp_r2r.rpt    {get_metrics -nworst $nw -metric metrics_tim_nvp_r2r -local}

    # ---- Congestion ----
    redirect ${rptpfx}.congestion.rpt                             {report_congestion}
    redirect ${rptpfx}.metrics.congestion.rpt                     {report_metrics -congestion}
    # Nworst Congested Hierarchies
    redirect ${rptpfx}.metrics.congestion.nworst_hier.rpt         {get_metrics -nworst $nw -metric metrics_cong_number_cells -local}
    # Nworst Logic Congested Hierarchies (Logic-Structure Induced Congestion)
    redirect ${rptpfx}.metrics.congestion.nworst_logic_hier.rpt   {get_metrics -nworst $nw -metric metrics_cong_number_cells_in_cong_area -local}
    # Nworst Channel Congested Hierarchies (Narrow Channel or Floorplan Congestion)
    redirect ${rptpfx}.metrics.congestion.nworst_channel_hier.rpt {get_metrics -nworst $nw -metric metrics_cong_number_cells_in_cong_channel -local}
    # Nworst RTL lines which generates most congested cells
    redirect ${rptpfx}.metrics.congestion.rtl_worst_lines.rpt     {get_metrics -metric metrics_cong_number_cells_in_cong_area -rtl_worst_lines $nw }

    # ---- Screenshots -----
    gui_start

    gui_explore_logic_hierarchy -remove
    set layout_w [gui_create_window -type Layout -show_state maximize]
    gui_set_active_window -window $layout_w

    gui_write_window_image -file "${rptpfx}.floorplan.png" -window $layout_w
    #change_selection [gui_explore_logic_hierarchy -expand]
    gui_explore_logic_hierarchy -expand
    gui_write_window_image -file "${rptpfx}.floorplan_hier.png" -window $layout_w

    #gui_set_setting -window [gui_get_current_window -types Layout -mru]  -setting hatchCellNormalHier -value Dense7Pattern

    gui_show_map -map globalCongestionMap -show true -window $layout_w
    change_selection [gui_explore_logic_hierarchy -expand]
    gui_write_window_image -file "${rptpfx}.global_congestion.png" -window $layout_w

    gui_set_layout_layer_visibility [get_layers] -toggle       
    gui_execute_menu_item -menu "View->Map->Cell Density"
    gui_set_map_option  -map cellDensityMap -option min_threshold -value 0.6
    gui_set_map_option  -map cellDensityMap -option max_threshold -value 1.0
    gui_load_cell_density_mm
    gui_write_window_image -file "${rptpfx}.cell_density.png"

    gui_set_layout_layer_visibility [get_layers] -toggle       
    gui_execute_menu_item -menu "View->Map->Pin Density"
    gui_load_pin_density_mm
    gui_write_window_image -file "${rptpfx}.cell_density.png"

    gui_stop

    # ---- Power ----
        # Please check run_power.tcl
}

set done_metrics_time [date]
echo $done_metrics_time > ${WORK_DIR}/done.metrics

save_block
save_lib -all

###############################################################################
# Latch check
###############################################################################
set latchrpt [open "${REPORTS_DIR}/rtla_latches.txt" w+]
set latch_in_design [get_cells -hierarchical  -filter "is_positive_level_sensitive==true || is_negative_level_sensitive==true"]
if {$latch_in_design != ""} {
    tee_puts ${latchrpt} "Error-NPU: LATCHES FOUND IN THE DESIGN"
    tee_puts ${latchrpt} "Error-NPU: Please check the names below:"
    set lst [collection_to_list $latch_in_design -newline -name]
	tee_puts ${latchrpt} "$lst"
} else {
    tee_puts ${latchrpt} "Info: No latch found in the design"
}
close ${latchrpt}

write_sdc -nosplit -output constraints_flat_final.sdc

set end_time [date]
puts "Done.\n  Start: $start_time\n  Elab done: $done_elab_time\n  SDC done: $done_sdc_time\n  RTL Opt done: $done_rtlopt_time\n  Metrics done: $done_metrics_time\n\n"

if {${RTLA_KEEP_OPEN}} {
  puts "Keeping RTLA open for interactive use\n\n"
} else {
  exit
}
