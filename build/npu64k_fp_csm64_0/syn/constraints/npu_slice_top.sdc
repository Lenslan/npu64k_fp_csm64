# Copyright (C) 2021-2023 Synopsys, Inc. All rights reserved.
#
# SYNOPSYS CONFIDENTIAL - This is an unpublished, confidential, and
# proprietary work of Synopsys, Inc., and may be subject to patent,
# copyright, trade secret, and other legal or contractual protection.
# This work may be used only pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# distribution, or disclosure of this work is strictly prohibited.
#
# The entire notice above must be reproduced on all authorized copies.
#
# =============================================================================
# Constraints for the npu_slice_top module 
# =============================================================================
set npu_lint_virt_clk 0
if { [info exists ::env(NPU_LINT_VIRT_CLK)] } {
    set npu_lint_virt_clk $::env(NPU_LINT_VIRT_CLK)
}
set npu_syn_replace_clkg 1
if { [info exists ::env(NPU_SYN_REPLACE_CLKG)] } {
    set npu_syn_replace_clkg $::env(NPU_SYN_REPLACE_CLKG)
}
set clk_gate0_Q "clk_gate0/Q"
if {("$npu_lint_virt_clk" ne "0") || ("$npu_syn_replace_clkg" eq "0")} {
  set clk_gate0_Q "clk_out"
}
#Note: npu_flatten_sdc=1 by default for npu_slice_top synthesis
set npu_flatten_sdc 1

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------
# -- Clocks uncertainty (setup and hold)
#
set clk_unc_setup 0.200
if { [info exists ::env(NPU_CLK_UNC_SETUP)] } {
  set clk_unc_setup $::env(NPU_CLK_UNC_SETUP)
}
set clk_unc_hold  0.050
if { [info exists ::env(NPU_CLK_UNC_HOLD)] } {
  set clk_unc_hold $::env(NPU_CLK_UNC_HOLD)
}
puts "Info: npu_slice_top  clk_unc_setup = $clk_unc_setup clk_unc_hold = $clk_unc_hold"

# -- Defautl cell from the library to use to estimate the driving capability of the ports
#
if {![info exists TECHNOLOGY]} {
  set TECHNOLOGY undef
}
if {"$TECHNOLOGY" eq "03"} {
  set default_drive_cell HDMDBSVT03_BUF_8
} elseif {"$TECHNOLOGY" eq "05"} {
  set default_drive_cell HDBSVT06_BUF_CA3Q_8
} elseif {"$TECHNOLOGY" eq "07"} {
  set default_drive_cell HDBSVT08_BUF_8
} elseif {"$TECHNOLOGY" eq "12"} {
  set default_drive_cell EDBSVT16_BUF_8
} else {
  set default_drive_cell "none"
}

# Clock ratio with the external axi interconnect
set axi_clk_ratio 1

# -- NPU slice search path in the hierarchy
set nslhier "u_npu_slice"
set l1hier "${nslhier}*u_npu_l1_arc"

# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------
# --- main ---
set slice_clock_name "clk"
set slice_virt_clock_name "async_vclk"
set slice_clock_freq 1000
if { [info exists ::env(NPU_FMAX)] } {
  set slice_clock_freq $::env(NPU_FMAX)
}
set slice_clock_per  [expr 1000.0 / $slice_clock_freq] ; # Period in ns
set slice_clock_port [get_ports $slice_clock_name]
set slice_clock_Teff [expr $slice_clock_per - $clk_unc_setup]
create_clock -name $slice_clock_name -period ${slice_clock_per} ${slice_clock_port}
set_drive 0 $slice_clock_name
set_clock_uncertainty -setup $clk_unc_setup $slice_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $slice_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${slice_clock_per}] -rise_from $slice_clock_name -fall_to $slice_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${slice_clock_per}] -fall_from $slice_clock_name -rise_to $slice_clock_name
set_clock_transition 0.1 $slice_clock_name
set_dont_touch_network   $slice_clock_name
set slice_clock_obj [get_clocks $slice_clock_name]
puts "info: npu_slice  clock $slice_clock_name created @ $slice_clock_freq mhz"

set slice_wdt_clock_name "wdt_clk"
set slice_wdt_clock_freq 50
if { [info exists ::env(WDT_NPU_FMAX)] } {
  set slice_wdt_clock_freq $::env(WDT_NPU_FMAX)
}
set slice_wdt_clock_per  [expr 1000.0 / $slice_wdt_clock_freq] ; # Period in ns
set slice_wdt_clock_port [get_ports $slice_wdt_clock_name]
create_clock -name $slice_wdt_clock_name -period ${slice_wdt_clock_per} ${slice_wdt_clock_port}
set_drive 0 $slice_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $slice_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $slice_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${slice_wdt_clock_per}] -rise_from $slice_wdt_clock_name -fall_to $slice_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${slice_wdt_clock_per}] -fall_from $slice_wdt_clock_name -rise_to $slice_wdt_clock_name
set_clock_transition 0.1 $slice_wdt_clock_name
set_dont_touch_network   $slice_wdt_clock_name
set slice_wdt_clock_obj [get_clocks $slice_wdt_clock_name]
puts "Info: npu_slice  clock $slice_wdt_clock_name created @ $slice_wdt_clock_freq MHz"


# -----------------------------------------------------------------------------
# Generated Clocks
# We recommend replacing architectural clock gating modules in the RTL by a
# wrapper (with same port names) containing a technology specific ICG cell
# before running synthesis. In that case, if the ICG instance is called
# ck_gate0, all you need to possibly modify in the incoming SDC is the name
# of the output pin (Q) of the ICG cell
# -----------------------------------------------------------------------------
# Create a generated clock for the ARC HS SRAMS. The clock is at 1/2 the frequency of the HS.
#   name       : the generated clock name
#   ckg_module : the clock gate cell used to generate a half rate clock in the design
#
# All generated clock names are appended to string l1arc_hs_gclocks
#
# IMPORTANT:
# Replace the '/Q' in the search patter if the replacement clock gate cell from the library uses another output pin name
set  l1arc_hs_gclocks ""
proc l1arc_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable slice_clock_obj
    variable slice_clock_port
    variable l1hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable l1arc_hs_gclocks
    variable clk_gate0_Q
    # Slow search
    #   get_pins * -hier -filter "@full_name=~*${nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*$clk_gate0_Q"
    # Faster search
    #   get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*"
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${l1hier}*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${slice_clock_obj} -source ${slice_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append l1arc_hs_gclocks " $name"
    puts "Info: npu_slice_top  L1 ARC HS generated clock '$name' from ICG $ckg_full_name with edges $ck_edges"
}

set l1pfx "nl1_"
l1arc_hs_generated_clock "${l1pfx}ic_data_bank0_gclk"        "uic_data_bank0_clkgate"  {1 2 5}
l1arc_hs_generated_clock "${l1pfx}ic_data_bank1_gclk"        "uic_data_bank1_clkgate"  {1 2 5}
l1arc_hs_generated_clock "${l1pfx}ic_tag_w0_gclk"            "uic_tag_w0_clkgate"      {1 2 5}
l1arc_hs_generated_clock "${l1pfx}ic_tag_w1_gclk"            "uic_tag_w1_clkgate"      {1 2 5}
l1arc_hs_generated_clock "${l1pfx}ic_tag_w2_gclk"            "uic_tag_w2_clkgate"      {1 2 5}
l1arc_hs_generated_clock "${l1pfx}ic_tag_w3_gclk"            "uic_tag_w3_clkgate"      {1 2 5}
l1arc_hs_generated_clock "${l1pfx}bc_ram0_gclk"              "u_bc0_clkgate"           {1 2 5}
l1arc_hs_generated_clock "${l1pfx}bc_ram1_gclk"              "u_bc1_clkgate"           {1 2 5}
l1arc_hs_generated_clock "${l1pfx}pt_ram0_gclk"              "u_pt0_clkgate"           {1 2 5}
l1arc_hs_generated_clock "${l1pfx}pt_ram1_gclk"              "u_pt1_clkgate"           {1 2 5}
l1arc_hs_generated_clock "${l1pfx}dccm_bank0_lo_gclk"        "u_clkgate_dccm_0_lo"     {1 2 5}
l1arc_hs_generated_clock "${l1pfx}dccm_bank0_hi_gclk"        "u_clkgate_dccm_0_hi"     {1 2 5}
l1arc_hs_generated_clock "${l1pfx}dccm_bank1_lo_gclk"        "u_clkgate_dccm_1_lo"     {1 2 5}
l1arc_hs_generated_clock "${l1pfx}dccm_bank1_hi_gclk"        "u_clkgate_dccm_1_hi"     {1 2 5}
l1arc_hs_generated_clock "${l1pfx}data_even_lo_gclk"         "u_clkgate_data_even_lo"  {1 2 5}
l1arc_hs_generated_clock "${l1pfx}data_even_hi_gclk"         "u_clkgate_data_even_hi"  {1 2 5}
l1arc_hs_generated_clock "${l1pfx}data_odd_lo_gclk"          "u_clkgate_data_odd_lo"   {1 2 5}
l1arc_hs_generated_clock "${l1pfx}data_odd_hi_gclk"          "u_clkgate_data_odd_hi"   {1 2 5}
l1arc_hs_generated_clock "${l1pfx}ntlb_pd0_gclk"             "u_ntlb_pd0_clkgate"      {1 2 7}
l1arc_hs_generated_clock "${l1pfx}ntlb_pd1_gclk"             "u_ntlb_pd1_clkgate"      {1 2 5}

# GTOA core runs at half the frequency
create_generated_clock -name "gtoa_half_gclk" -edges {1 2 5} -add -master_clock ${slice_clock_obj} -source ${slice_clock_port} [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${nslhier}*u_npu_gtoa*u_l2_clkgate_half_inst*"]
set_dont_touch_network "gtoa_half_gclk"
set_clock_uncertainty -setup $clk_unc_setup "gtoa_half_gclk"
set_clock_uncertainty -hold  $clk_unc_hold  "gtoa_half_gclk"

group_path -name $slice_clock_name-to-$slice_clock_name -from $slice_clock_name -to $slice_clock_name
group_path -name gtoa_half_gclk-to-$slice_clock_name    -from gtoa_half_gclk    -to $slice_clock_name
group_path -name $slice_clock_name-to-gtoa_half_gclk    -from $slice_clock_name -to gtoa_half_gclk
group_path -name gtoa_half_gclk-to-gtoa_half_gclk       -from gtoa_half_gclk    -to gtoa_half_gclk

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name $slice_virt_clock_name -period 1.000
set scg_cmd "set_clock_groups -asynchronous -group {$slice_wdt_clock_name} -group {$slice_clock_name $l1arc_hs_gclocks gtoa_half_gclk} -group {$slice_virt_clock_name}"
} else {
set scg_cmd "set_clock_groups -asynchronous -group {$slice_wdt_clock_name} -group {$slice_clock_name $l1arc_hs_gclocks gtoa_half_gclk}"
}
echo $scg_cmd
eval $scg_cmd

set slice_all_non_gen_clks      [get_clocks * -filter {@is_generated == false}]
set slice_all_non_gen_virt_clks $slice_all_non_gen_clks
if {"$npu_lint_virt_clk" ne "0"} {
  set slice_all_non_gen_virt_clks [remove_from_collection $slice_all_non_gen_clks [get_clocks $slice_virt_clock_name]]
}

set top_reset_name "rst_a"
set top_reset [get_ports ${top_reset_name} -filter {@port_direction == in}]

#------------------------------------------------------------------------------
# Input Constraints
#------------------------------------------------------------------------------
set gclk_col [get_clocks -quiet *_gclk]

# If the  configuration you have  built does not have generated  clocks, then this constraint is superflous and an
# error referring to non-existent *_gclk can be ignored
foreach_in_collection gclkname ${gclk_col} { remove_input_delay -clock $gclkname [get_ports * -filter {@port_direction == in}] }

# Default value
set ALL_INPUTS_EXC_MAIN_CLK       [remove_from_collection [all_inputs] [get_ports $slice_clock_name]]
set ALL_INPUTS_EXC_MAIN_WDT_CLK   [remove_from_collection $ALL_INPUTS_EXC_MAIN_CLK [get_ports $slice_wdt_clock_name]]
set_input_delay [expr 0.25 * ${slice_clock_per}] -clock ${slice_clock_obj} [get_ports $ALL_INPUTS_EXC_MAIN_WDT_CLK -filter {@port_direction == in}]

# Per input pin type
set_input_delay [expr 0.25 * ${slice_wdt_clock_per}] -clock ${slice_wdt_clock_obj} [get_ports wdt_* -filter {@port_direction == in}]
##set_input_delay [expr 0.25 * ${slice_clock_per}] -clock ${slice_clock_obj} [get_ports arcnum* -filter {@port_direction == in}] -add
##set_input_delay [expr 0.25 * ${slice_clock_per}] -clock ${slice_clock_obj} [get_ports clusternum* -filter {@port_direction == in}]
##set_input_delay [expr 0.25 * ${slice_clock_per}] -clock ${slice_clock_obj} [get_ports test_mode -filter {@port_direction == in}]
##set_input_delay [expr 0.25 * ${slice_clock_per}] -clock ${slice_clock_obj} ${top_reset}
##set_input_delay [expr 0.25 * ${slice_clock_per}] -clock ${slice_clock_obj} ${top_reset} -add
##Set input delay for GALS interface
set_input_delay  [expr 0.25*$slice_clock_Teff] -clock ${slice_clock_obj} [get_ports *axi_gals_*_rdpnt* -filter {@port_direction == in}]
set_input_delay  [expr 0.9 *$slice_clock_Teff] -clock ${slice_clock_obj} [get_ports *axi_gals_*_data -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *$slice_clock_Teff] -clock ${slice_clock_obj} [get_ports *axi_gals*_rpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *$slice_clock_Teff] -clock ${slice_clock_obj} [get_ports *axi_gals*_wpnt_a -filter {@port_direction == in}]
##Set input delay for APB async interface
set_input_delay  [expr 0.8 *$slice_clock_Teff] -clock ${slice_clock_obj} [get_ports dbg_as_req_a -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *$slice_clock_Teff] -clock ${slice_clock_obj} [get_ports dbg_as_pcmd -filter {@port_direction == in}]

remove_input_delay [get_ports [get_object_name $slice_all_non_gen_virt_clks]]

if {"$npu_lint_virt_clk" ne "0"} {
  foreach_in_collection clkname $slice_all_non_gen_virt_clks {
    remove_input_delay  -clock $clkname [get_ports ${top_reset_name} -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports arct_rst_an -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports *arc_halt_req_a -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports *arc_run_req_a -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports *arc_irq_a -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports *l2_event_a* -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports *l1_peer_event_a* -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports dbg_* -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $slice_virt_clock_name] period]] -clock [get_clocks $slice_virt_clock_name] [get_ports ${top_reset_name} -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $slice_virt_clock_name] period]] -clock [get_clocks $slice_virt_clock_name] [get_ports arct_rst_an -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $slice_virt_clock_name] period]] -clock [get_clocks $slice_virt_clock_name] [get_ports *arc_halt_req_a -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $slice_virt_clock_name] period]] -clock [get_clocks $slice_virt_clock_name] [get_ports *arc_run_req_a -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $slice_virt_clock_name] period]] -clock [get_clocks $slice_virt_clock_name] [get_ports *arc_irq_a -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $slice_virt_clock_name] period]] -clock [get_clocks $slice_virt_clock_name] [get_ports *l2_event_a* -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $slice_virt_clock_name] period]] -clock [get_clocks $slice_virt_clock_name] [get_ports *l1_peer_event_a* -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $slice_virt_clock_name] period]] -clock [get_clocks $slice_virt_clock_name] [get_ports dbg_* -filter {@port_direction == in}]
}

if {"$default_drive_cell" eq "none"} {
  set_input_transition 0.1 [remove_from_collection [get_ports * -filter {@port_direction == in}] [get_ports [get_object_name $slice_all_non_gen_virt_clks]]]
} else {
  set_driving_cell -lib_cell $default_drive_cell -pin X [get_ports * -filter {@port_direction == in}]
  remove_driving_cell [get_ports [get_object_name $slice_all_non_gen_virt_clks]]
}

#------------------------------------------------------------------------------
# Output Constraints
#------------------------------------------------------------------------------
# Default value
set_output_delay [expr 0.25 * ${slice_clock_per}] -clock ${slice_clock_obj} [get_ports * -filter {@port_direction == out}]
##Set output delay for GALS interface
set_output_delay [expr 0.9 *$slice_clock_Teff] -clock ${slice_clock_obj} [get_ports *axi_gals_*_rdpnt* -filter {@port_direction == out}]
set_output_delay [expr 0.25*$slice_clock_Teff] -clock ${slice_clock_obj} [get_ports *axi_gals_*_data -filter {@port_direction == out}]
set_output_delay [expr 0.7 *$slice_clock_Teff] -clock ${slice_clock_obj} [get_ports *axi_gals*_rpnt -filter {@port_direction == out}]
set_output_delay [expr 0.7 *$slice_clock_Teff] -clock ${slice_clock_obj} [get_ports *axi_gals*_wpnt -filter {@port_direction == out}]
##Set output delay for APB async interface
set_output_delay [expr 0.8 *$slice_clock_Teff] -clock ${slice_clock_obj} [get_ports dbg_as_ack_a -filter {@port_direction == out}]
set_output_delay [expr 0.8 *$slice_clock_Teff] -clock ${slice_clock_obj} [get_ports dbg_as_presp -filter {@port_direction == out}]
##Set output delay for SWE interface (pulse + data)
set_output_delay [expr 0.8 *$slice_clock_Teff] -clock ${slice_clock_obj} [get_ports rtt_swe_val  -filter {@port_direction == out}]
set_output_delay [expr 0.8 *$slice_clock_Teff] -clock ${slice_clock_obj} [get_ports rtt_swe_data -filter {@port_direction == out}]
set_output_delay [expr 0.8 *$slice_clock_Teff] -clock ${slice_clock_obj} [get_ports rtt_swe_ext  -filter {@port_direction == out}]

set_output_delay [expr 0.25 * ${slice_wdt_clock_per}] -clock ${slice_wdt_clock_obj} [get_ports wdt_* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${slice_clock_per}] -clock ${slice_clock_obj} [get_ports wdt_reset -filter {@port_direction == out}]




#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------
set_false_path -from [get_ports *clusternum* -filter {@port_direction == in}]
set_false_path -from [get_ports *arct_dbgen* -filter {@port_direction == in}]
set_false_path -from [get_ports *arct_niden* -filter {@port_direction == in}]
set_false_path -from [get_ports *arcnum* -filter {@port_direction == in}]
set_false_path -from [get_ports *intvbase_in -filter {@port_direction == in}]
set_false_path -from [get_ports *clk_en_a -filter {@port_direction == in}]
set_false_path -from [get_ports *arct_rst_an* -filter {@port_direction == in}]
set_false_path -from [get_ports *arct_dbg_prot_sel* -filter {@port_direction == in}]
if {"$npu_lint_virt_clk" eq "0"} {
  set_false_path -from [get_ports *arc_halt_req_a -filter {@port_direction == in}]
  set_false_path -from [get_ports *arc_run_req_a -filter {@port_direction == in}]
  set_false_path -from [get_ports *arc_irq_a -filter {@port_direction == in}]
  set_false_path -from [get_ports *l2_event_a* -filter {@port_direction == in}]
  set_false_path -from [get_ports *l1_peer_event_a* -filter {@port_direction == in}]
  set_false_path -from [get_ports dbg_* -filter {@port_direction == in}]
}
set_false_path -to   [get_ports dbg_* -filter {@port_direction == out}]
set_false_path -to   [get_ports *l2_send_event* -filter {@port_direction == out}]
set_false_path -to   [get_ports *l1_peer_send_event* -filter {@port_direction == out}]
set_false_path -from [get_ports vmid -filter {@port_direction == in}]
set_false_path -from [get_ports *isolate*  -filter {@port_direction == in}]
set_false_path -from [get_ports *pd_logic  -filter {@port_direction == in}]
set_false_path -from [get_ports *pd_mem    -filter {@port_direction == in}]


if {"$npu_flatten_sdc" eq 1} {
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${l1hier}*ialb_cpu_top*"]
set_false_path -through [get_pins {*dbg_prot_sel} -hier -filter "@full_name=~*${l1hier}*ialb_cpu_top*"]
}

set_false_path -from ${top_reset} -through [get_pins -hier * -filter "@full_name=~*${l1hier}*ialb_cpu_top*reset_ctrl*sample_*"]
set_false_path -from ${top_reset} -through [get_pins -hier * -filter "@full_name=~*icc_top*reset_ctrl*sample_*"]
set_false_path -through [get_pins -hier * -filter "@full_name=~*icc_top*u_cc_aon_wrap*u_cc_clock_ctrl/l1_clk_enable"]
set_false_path -from ${top_reset} -through [get_pins -hier * -filter "@full_name=~*icc_top*u_biu_top*reset_ctrl*sample_*"]

# NPU CDC synchronizers
set_false_path -from ${top_reset} -through [get_pins -hier * -filter "@full_name=~*u_*cdc_sync*sample_*"]

if {"$npu_flatten_sdc" eq 1} {
#------------------------------------------------------------------------------
# False Paths  - multi-through
#------------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Multicycle paths
# -----------------------------------------------------------------------------
# ARC HS PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1

if {$axi_clk_ratio eq 2} {
  set_multicycle_path -end   -from [get_ports *axi* -filter {@port_direction == in}]  -setup 2 -comment reg2reg_mc2
  set_multicycle_path -end   -from [get_ports *axi* -filter {@port_direction == in}]  -hold  1
  set_multicycle_path -start   -to [get_ports *axi* -filter {@port_direction == out}] -setup 2 -comment reg2reg_mc2
  set_multicycle_path -start   -to [get_ports *axi* -filter {@port_direction == out}] -hold  1
}

# Conv 2 cycle checker for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${nslhier}*u_npu_conv*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${nslhier}*u_npu_conv*"] -hold 1
if {"$npu_lint_virt_clk" eq "0"} {
  # Do not merge redundant registers for timing in synthesis
  set_register_merging [get_cells * -hier -filter "@full_name=~*_nomerge_r*"]  false
}

# GTOA 2 cycle checker, the generated clock inside GTOA is 1/2 the frequency of the main clock
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${nslhier}*u_npu_gtoa*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${nslhier}*u_npu_gtoa*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${nslhier}*u_npu_gtoa*"] -start -setup 2 -comment reg2reg_mc2f2s
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${nslhier}*u_npu_gtoa*"] -start -hold 1
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${nslhier}*u_npu_gtoa*"] -end -setup 2 -comment reg2reg_mc2s2f
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${nslhier}*u_npu_gtoa*"] -end -hold 1
# GTOA 3 cycle path for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${nslhier}*u_npu_gtoa*"] -start -setup 3 -comment reg2reg_mc3f2s
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${nslhier}*u_npu_gtoa*"] -start -hold 2

}

# -----------------------------------------------------------------------------
# Source synchronous data_check
# -----------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Case analysis
# -----------------------------------------------------------------------------

set_case_analysis 0 [get_ports test_mode]


# -----------------------------------------------------------------------------
# Ideal network
# -----------------------------------------------------------------------------
