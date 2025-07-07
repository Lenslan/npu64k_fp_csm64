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


# -----------------------------------------------------------------------------
# Constraints for the npu_core module
# Includes the HS3 archipelago.sdc constraints for the L2 control core

set npu_lint_virt_clk 0
if { [info exists ::env(NPU_LINT_VIRT_CLK)] } {
  set npu_lint_virt_clk $::env(NPU_LINT_VIRT_CLK)
}

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# Information from npu_config.v

# NPU Slices      = 16
# NPU NoC ports   = 5
# NPU DMI ports   = 1
# NPU HAS MMU     = 1
# NPU HAS TRC     = 1
# NPU ARC SFT     = 0
# NPU HAS PDM     = 1
# NPU GRP NUM     = 4

# CLN DEV   = 5
# CLN CCM   = 0
# CLN DBANK = 8

# -- Clock pin name
#
set ncore_clock_name "npu_core_clk"
set apb_clock_name   "arct_clk"
set noc_clock_name   "npu_noc_clk"
set cfg_clock_name   "npu_cfg_clk"
set arc0_wdt_clock_name "nl2arc0_wdt_clk"
set arc1_wdt_clock_name "nl2arc1_wdt_clk"
set ncore_virt_clock_name "npu_core_async_vclk"

# -- Target frequency, in MHz
#
set ncore_clock_freq 1000
set noc_clock_freq   1000
set cfg_clock_freq   1000
if { [info exists ::env(NPU_FMAX)] } {
  set ncore_clock_freq $::env(NPU_FMAX)
  set noc_clock_freq   $::env(NPU_FMAX)
  set cfg_clock_freq   $::env(NPU_FMAX)
}

set ncore_wdt_clock_freq 50
if { [info exists ::env(WDT_NPU_FMAX)] } {
  set ncore_wdt_clock_freq $::env(WDT_NPU_FMAX)
}
set npu_syn_replace_clkg 1
if { [info exists ::env(NPU_SYN_REPLACE_CLKG)] } {
    set npu_syn_replace_clkg $::env(NPU_SYN_REPLACE_CLKG)
}
set clk_gate0_Q "clk_gate0/Q"
if {("$npu_lint_virt_clk" ne "0") || ("$npu_syn_replace_clkg" eq "0")} {
  set clk_gate0_Q "clk_out"
}

set apb_clock_freq [expr $ncore_clock_freq / 2]; # Frequency in MHz. Default: 50% of Ncore Freq.

# -- Clocks uncertainty (setup and hold)
#
#set clk_unc_setup 0.200
#set clk_unc_hold  0.050
set clk_unc_setup 0.200
if { [info exists ::env(NPU_CLK_UNC_SETUP)] } {
  set clk_unc_setup $::env(NPU_CLK_UNC_SETUP)
}
set clk_unc_hold  0.050
if { [info exists ::env(NPU_CLK_UNC_HOLD)] } {
  set clk_unc_hold $::env(NPU_CLK_UNC_HOLD)
}
puts "Info: npu_core  clk_unc_setup = $clk_unc_setup clk_unc_hold = $clk_unc_hold"

# -- NPU core search path in the hierarchy
#
set ncorehier ""
# -- L2 ARC controller
#
# naming prefix and path in the hierarchy
set l2pfx "nl2_"
set l2hier "${ncorehier}*u_npu_l2_arc"


# -- Defautl cell from the library to use to estimate the driving capability of the ports
#    Adapt this value to your specific cell library
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


# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------

set ncore_clock_per  [expr 1000.0 / $ncore_clock_freq] ; # Period in ns
set noc_clock_per    [expr 1000.0 / $noc_clock_freq] ; # Period in ns
set cfg_clock_per    [expr 1000.0 / $cfg_clock_freq] ; # Period in ns

set ncore_clock_Teff [expr $ncore_clock_per - $clk_unc_setup]
set noc_clock_Teff   [expr $noc_clock_per - $clk_unc_setup]
set cfg_clock_Teff   [expr $cfg_clock_per - $clk_unc_setup]

# Main Clock of npu_core
set ncore_clock_port [get_ports $ncore_clock_name]
create_clock -name $ncore_clock_name -period ${ncore_clock_per} ${ncore_clock_port}
set_drive 0 $ncore_clock_name
set_clock_uncertainty -setup $clk_unc_setup $ncore_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $ncore_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${ncore_clock_per}] -rise_from $ncore_clock_name -fall_to $ncore_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${ncore_clock_per}] -fall_from $ncore_clock_name -rise_to $ncore_clock_name
set_clock_transition 0.1 $ncore_clock_name
set_dont_touch_network $ncore_clock_name
puts "Info: npu_core clock $ncore_clock_name created @ $ncore_clock_freq MHz"
set ncore_clock_obj [get_clocks $ncore_clock_name]

set apb_clock_per  [expr 1000.0 / $apb_clock_freq] ;
set apb_clock_Teff [expr $apb_clock_per - $clk_unc_setup]
set apb_clock_port [get_ports $apb_clock_name]
create_clock -name $apb_clock_name -period ${apb_clock_per} ${apb_clock_port}
set_drive 0 $apb_clock_name
set_clock_uncertainty -setup $clk_unc_setup $apb_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $apb_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${apb_clock_per}] -rise_from $apb_clock_name -fall_to $apb_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${apb_clock_per}] -fall_from $apb_clock_name -rise_to $apb_clock_name
set_clock_transition 0.1 $apb_clock_name
set_dont_touch_network $apb_clock_name
set apb_clock_obj [get_clocks $apb_clock_name]
puts "Info: npu_core clock $apb_clock_name created @ $ncore_clock_freq MHz"


set noc_clock_port [get_ports $noc_clock_name]
create_clock -name $noc_clock_name -period ${noc_clock_per} ${noc_clock_port}
set_drive 0 $noc_clock_name
set_clock_uncertainty -setup $clk_unc_setup $noc_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $noc_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${ncore_clock_per}] -rise_from $noc_clock_name -fall_to $noc_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${ncore_clock_per}] -fall_from $noc_clock_name -rise_to $noc_clock_name
set_clock_transition 0.1 $noc_clock_name
set_dont_touch_network $noc_clock_name
set noc_clock_obj [get_clocks $noc_clock_name]
puts "Info: npu_core clock $noc_clock_name created @ $noc_clock_freq MHz"

set cfg_clock_port [get_ports $cfg_clock_name]
create_clock -name $cfg_clock_name -period ${cfg_clock_per} ${cfg_clock_port}
set_drive 0 $cfg_clock_name
set_clock_uncertainty -setup $clk_unc_setup $cfg_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $cfg_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${ncore_clock_per}] -rise_from $cfg_clock_name -fall_to $cfg_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${ncore_clock_per}] -fall_from $cfg_clock_name -rise_to $cfg_clock_name
set_clock_transition 0.1 $cfg_clock_name
set_dont_touch_network $cfg_clock_name
set cfg_clock_obj [get_clocks $cfg_clock_name]
puts "Info: npu_core clock $cfg_clock_name created @ $cfg_clock_freq MHz"

set wdt_clock_per  [expr 1000.0 / $ncore_wdt_clock_freq] ; # Period in ns
set arc0_wdt_clock_port [get_ports $arc0_wdt_clock_name]
create_clock -name $arc0_wdt_clock_name -period ${wdt_clock_per} ${arc0_wdt_clock_port}
set_drive 0 $arc0_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $arc0_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $arc0_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${wdt_clock_per}] -rise_from $arc0_wdt_clock_name -fall_to $arc0_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${wdt_clock_per}] -fall_from $arc0_wdt_clock_name -rise_to $arc0_wdt_clock_name
set_clock_transition 0.1 $arc0_wdt_clock_name
set_dont_touch_network $arc0_wdt_clock_name
set arc0_wdt_clock_obj [get_clocks $arc0_wdt_clock_name]
puts "Info: npu_core clock $arc0_wdt_clock_name created @ $ncore_clock_freq MHz"

set arc1_wdt_clock_port [get_ports $arc1_wdt_clock_name]
create_clock -name $arc1_wdt_clock_name -period ${wdt_clock_per} ${arc1_wdt_clock_port}
set_drive 0 $arc1_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $arc1_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $arc1_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${wdt_clock_per}] -rise_from $arc1_wdt_clock_name -fall_to $arc1_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${wdt_clock_per}] -fall_from $arc1_wdt_clock_name -rise_to $arc1_wdt_clock_name
set_clock_transition 0.1 $arc1_wdt_clock_name
set_dont_touch_network $arc1_wdt_clock_name
set arc1_wdt_clock_obj [get_clocks $arc1_wdt_clock_name]
puts "Info: npu_core clock $arc1_wdt_clock_name created @ $ncore_clock_freq MHz"

# -----------------------------------------------------------------------------
# Generated Clocks
# We recommend replacing architectural clock gating modules in the RTL by a
# wrapper (with same port names) containing a technology specific ICG cell
# before running synthesis. In that case, if the ICG instance is called
# ck_gate0, all you need to possibly modify in the incoming SDC is the name
# of the output pin (Q) of the ICG cell
# -----------------------------------------------------------------------------

# +++++++++++
# ARC HS (L2)
# +++++++++++

# Create a generated clock for the ARC HS SRAMS. The clock is at 1/2 the frequency of the HS.
#   name       : the generated clock name
#   ckg_module : the clock gate cell used to generate a half rate clock in the design
#
# All generated clock names are appended to string l2arc_hs_gclocks
#
# IMPORTANT:
# Replace the '/Q' in the search pattern if the replacement clock gate cell from the library uses another output pin name
#
set l2arc0_hs_gclocks ""
proc l2arc0_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable ncore_clock_obj
    variable ncore_clock_port
    variable l2hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable l2arc0_hs_gclocks
    variable clk_gate0_Q
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${l2hier}0*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${ncore_clock_obj} -source ${ncore_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append l2arc0_hs_gclocks " $name"
    puts "Info: L2 ARC HS generated clock '$name' from $ckg_full_name with edges $ck_edges"
}

l2arc0_hs_generated_clock "${l2pfx}arc0_ic_data_bank0_gclk"    "uic_data_bank0_clkgate"  {1 2 5}
l2arc0_hs_generated_clock "${l2pfx}arc0_ic_data_bank1_gclk"    "uic_data_bank1_clkgate"  {1 2 5}
l2arc0_hs_generated_clock "${l2pfx}arc0_ic_tag_w0_gclk"        "uic_tag_w0_clkgate"      {1 2 5}
l2arc0_hs_generated_clock "${l2pfx}arc0_ic_tag_w1_gclk"        "uic_tag_w1_clkgate"      {1 2 5}
l2arc0_hs_generated_clock "${l2pfx}arc0_ic_tag_w2_gclk"        "uic_tag_w2_clkgate"      {1 2 5}
l2arc0_hs_generated_clock "${l2pfx}arc0_ic_tag_w3_gclk"        "uic_tag_w3_clkgate"      {1 2 5}
l2arc0_hs_generated_clock "${l2pfx}arc0_bc_ram0_gclk"          "u_bc0_clkgate"           {1 2 5}
l2arc0_hs_generated_clock "${l2pfx}arc0_bc_ram1_gclk"          "u_bc1_clkgate"           {1 2 5}
l2arc0_hs_generated_clock "${l2pfx}arc0_pt_ram0_gclk"          "u_pt0_clkgate"           {1 2 5}
l2arc0_hs_generated_clock "${l2pfx}arc0_pt_ram1_gclk"          "u_pt1_clkgate"           {1 2 5}
l2arc0_hs_generated_clock "${l2pfx}arc0_dccm_bank0_lo_gclk"    "u_clkgate_dccm_0_lo"     {1 2 5}
l2arc0_hs_generated_clock "${l2pfx}arc0_dccm_bank0_hi_gclk"    "u_clkgate_dccm_0_hi"     {1 2 5}
l2arc0_hs_generated_clock "${l2pfx}arc0_dccm_bank1_lo_gclk"    "u_clkgate_dccm_1_lo"     {1 2 5}
l2arc0_hs_generated_clock "${l2pfx}arc0_dccm_bank1_hi_gclk"    "u_clkgate_dccm_1_hi"     {1 2 5}
l2arc0_hs_generated_clock "${l2pfx}arc0_data_even_lo_gclk"     "u_clkgate_data_even_lo"  {1 2 5}
l2arc0_hs_generated_clock "${l2pfx}arc0_data_even_hi_gclk"     "u_clkgate_data_even_hi"  {1 2 5}
l2arc0_hs_generated_clock "${l2pfx}arc0_data_odd_lo_gclk"      "u_clkgate_data_odd_lo"   {1 2 5}
l2arc0_hs_generated_clock "${l2pfx}arc0_data_odd_hi_gclk"      "u_clkgate_data_odd_hi"   {1 2 5}
l2arc0_hs_generated_clock "${l2pfx}arc0_ntlb_pd0_gclk"         "u_ntlb_pd0_clkgate"      {1 2 7}
l2arc0_hs_generated_clock "${l2pfx}arc0_ntlb_pd1_gclk"         "u_ntlb_pd1_clkgate"      {1 2 5}
set l2arc1_hs_gclocks ""
proc l2arc1_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable ncore_clock_obj
    variable ncore_clock_port
    variable l2hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable l2arc1_hs_gclocks
    variable clk_gate0_Q
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${l2hier}1*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${ncore_clock_obj} -source ${ncore_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append l2arc1_hs_gclocks " $name"
    puts "Info: L2 ARC HS generated clock '$name' from $ckg_full_name with edges $ck_edges"
}

l2arc1_hs_generated_clock "${l2pfx}arc1_ic_data_bank0_gclk"    "uic_data_bank0_clkgate"  {1 2 5}
l2arc1_hs_generated_clock "${l2pfx}arc1_ic_data_bank1_gclk"    "uic_data_bank1_clkgate"  {1 2 5}
l2arc1_hs_generated_clock "${l2pfx}arc1_ic_tag_w0_gclk"        "uic_tag_w0_clkgate"      {1 2 5}
l2arc1_hs_generated_clock "${l2pfx}arc1_ic_tag_w1_gclk"        "uic_tag_w1_clkgate"      {1 2 5}
l2arc1_hs_generated_clock "${l2pfx}arc1_ic_tag_w2_gclk"        "uic_tag_w2_clkgate"      {1 2 5}
l2arc1_hs_generated_clock "${l2pfx}arc1_ic_tag_w3_gclk"        "uic_tag_w3_clkgate"      {1 2 5}
l2arc1_hs_generated_clock "${l2pfx}arc1_bc_ram0_gclk"          "u_bc0_clkgate"           {1 2 5}
l2arc1_hs_generated_clock "${l2pfx}arc1_bc_ram1_gclk"          "u_bc1_clkgate"           {1 2 5}
l2arc1_hs_generated_clock "${l2pfx}arc1_pt_ram0_gclk"          "u_pt0_clkgate"           {1 2 5}
l2arc1_hs_generated_clock "${l2pfx}arc1_pt_ram1_gclk"          "u_pt1_clkgate"           {1 2 5}
l2arc1_hs_generated_clock "${l2pfx}arc1_dccm_bank0_lo_gclk"    "u_clkgate_dccm_0_lo"     {1 2 5}
l2arc1_hs_generated_clock "${l2pfx}arc1_dccm_bank0_hi_gclk"    "u_clkgate_dccm_0_hi"     {1 2 5}
l2arc1_hs_generated_clock "${l2pfx}arc1_dccm_bank1_lo_gclk"    "u_clkgate_dccm_1_lo"     {1 2 5}
l2arc1_hs_generated_clock "${l2pfx}arc1_dccm_bank1_hi_gclk"    "u_clkgate_dccm_1_hi"     {1 2 5}
l2arc1_hs_generated_clock "${l2pfx}arc1_data_even_lo_gclk"     "u_clkgate_data_even_lo"  {1 2 5}
l2arc1_hs_generated_clock "${l2pfx}arc1_data_even_hi_gclk"     "u_clkgate_data_even_hi"  {1 2 5}
l2arc1_hs_generated_clock "${l2pfx}arc1_data_odd_lo_gclk"      "u_clkgate_data_odd_lo"   {1 2 5}
l2arc1_hs_generated_clock "${l2pfx}arc1_data_odd_hi_gclk"      "u_clkgate_data_odd_hi"   {1 2 5}
l2arc1_hs_generated_clock "${l2pfx}arc1_ntlb_pd0_gclk"         "u_ntlb_pd0_clkgate"      {1 2 7}
l2arc1_hs_generated_clock "${l2pfx}arc1_ntlb_pd1_gclk"         "u_ntlb_pd1_clkgate"      {1 2 5}

set dbank_gclocks ""
# dbank clocks, generated from a clock gate with 25% duty cycle
# Group 0 , CSM dbank 0 , Sub-bank 0
set name "grp0_dbank0_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group0/*u_dbank0_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 0 , CSM dbank 0 , Sub-bank 1
set name "grp0_dbank0_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group0/*u_dbank0_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 0 , CSM dbank 1 , Sub-bank 0
set name "grp0_dbank1_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group0/*u_dbank1_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 0 , CSM dbank 1 , Sub-bank 1
set name "grp0_dbank1_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group0/*u_dbank1_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 0 , CSM dbank 2 , Sub-bank 0
set name "grp0_dbank2_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group0/*u_dbank2_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 0 , CSM dbank 2 , Sub-bank 1
set name "grp0_dbank2_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group0/*u_dbank2_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 0 , CSM dbank 3 , Sub-bank 0
set name "grp0_dbank3_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group0/*u_dbank3_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 0 , CSM dbank 3 , Sub-bank 1
set name "grp0_dbank3_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group0/*u_dbank3_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 0 , CSM dbank 4 , Sub-bank 0
set name "grp0_dbank4_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group0/*u_dbank4_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 0 , CSM dbank 4 , Sub-bank 1
set name "grp0_dbank4_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group0/*u_dbank4_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 0 , CSM dbank 5 , Sub-bank 0
set name "grp0_dbank5_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group0/*u_dbank5_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 0 , CSM dbank 5 , Sub-bank 1
set name "grp0_dbank5_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group0/*u_dbank5_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 0 , CSM dbank 6 , Sub-bank 0
set name "grp0_dbank6_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group0/*u_dbank6_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 0 , CSM dbank 6 , Sub-bank 1
set name "grp0_dbank6_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group0/*u_dbank6_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 0 , CSM dbank 7 , Sub-bank 0
set name "grp0_dbank7_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group0/*u_dbank7_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 0 , CSM dbank 7 , Sub-bank 1
set name "grp0_dbank7_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group0/*u_dbank7_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 1 , CSM dbank 0 , Sub-bank 0
set name "grp1_dbank0_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group1/*u_dbank0_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 1 , CSM dbank 0 , Sub-bank 1
set name "grp1_dbank0_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group1/*u_dbank0_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 1 , CSM dbank 1 , Sub-bank 0
set name "grp1_dbank1_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group1/*u_dbank1_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 1 , CSM dbank 1 , Sub-bank 1
set name "grp1_dbank1_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group1/*u_dbank1_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 1 , CSM dbank 2 , Sub-bank 0
set name "grp1_dbank2_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group1/*u_dbank2_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 1 , CSM dbank 2 , Sub-bank 1
set name "grp1_dbank2_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group1/*u_dbank2_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 1 , CSM dbank 3 , Sub-bank 0
set name "grp1_dbank3_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group1/*u_dbank3_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 1 , CSM dbank 3 , Sub-bank 1
set name "grp1_dbank3_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group1/*u_dbank3_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 1 , CSM dbank 4 , Sub-bank 0
set name "grp1_dbank4_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group1/*u_dbank4_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 1 , CSM dbank 4 , Sub-bank 1
set name "grp1_dbank4_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group1/*u_dbank4_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 1 , CSM dbank 5 , Sub-bank 0
set name "grp1_dbank5_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group1/*u_dbank5_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 1 , CSM dbank 5 , Sub-bank 1
set name "grp1_dbank5_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group1/*u_dbank5_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 1 , CSM dbank 6 , Sub-bank 0
set name "grp1_dbank6_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group1/*u_dbank6_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 1 , CSM dbank 6 , Sub-bank 1
set name "grp1_dbank6_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group1/*u_dbank6_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 1 , CSM dbank 7 , Sub-bank 0
set name "grp1_dbank7_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group1/*u_dbank7_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 1 , CSM dbank 7 , Sub-bank 1
set name "grp1_dbank7_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group1/*u_dbank7_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 2 , CSM dbank 0 , Sub-bank 0
set name "grp2_dbank0_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group2/*u_dbank0_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 2 , CSM dbank 0 , Sub-bank 1
set name "grp2_dbank0_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group2/*u_dbank0_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 2 , CSM dbank 1 , Sub-bank 0
set name "grp2_dbank1_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group2/*u_dbank1_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 2 , CSM dbank 1 , Sub-bank 1
set name "grp2_dbank1_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group2/*u_dbank1_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 2 , CSM dbank 2 , Sub-bank 0
set name "grp2_dbank2_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group2/*u_dbank2_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 2 , CSM dbank 2 , Sub-bank 1
set name "grp2_dbank2_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group2/*u_dbank2_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 2 , CSM dbank 3 , Sub-bank 0
set name "grp2_dbank3_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group2/*u_dbank3_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 2 , CSM dbank 3 , Sub-bank 1
set name "grp2_dbank3_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group2/*u_dbank3_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 2 , CSM dbank 4 , Sub-bank 0
set name "grp2_dbank4_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group2/*u_dbank4_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 2 , CSM dbank 4 , Sub-bank 1
set name "grp2_dbank4_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group2/*u_dbank4_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 2 , CSM dbank 5 , Sub-bank 0
set name "grp2_dbank5_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group2/*u_dbank5_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 2 , CSM dbank 5 , Sub-bank 1
set name "grp2_dbank5_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group2/*u_dbank5_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 2 , CSM dbank 6 , Sub-bank 0
set name "grp2_dbank6_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group2/*u_dbank6_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 2 , CSM dbank 6 , Sub-bank 1
set name "grp2_dbank6_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group2/*u_dbank6_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 2 , CSM dbank 7 , Sub-bank 0
set name "grp2_dbank7_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group2/*u_dbank7_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 2 , CSM dbank 7 , Sub-bank 1
set name "grp2_dbank7_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group2/*u_dbank7_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 3 , CSM dbank 0 , Sub-bank 0
set name "grp3_dbank0_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group3/*u_dbank0_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 3 , CSM dbank 0 , Sub-bank 1
set name "grp3_dbank0_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group3/*u_dbank0_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 3 , CSM dbank 1 , Sub-bank 0
set name "grp3_dbank1_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group3/*u_dbank1_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 3 , CSM dbank 1 , Sub-bank 1
set name "grp3_dbank1_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group3/*u_dbank1_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 3 , CSM dbank 2 , Sub-bank 0
set name "grp3_dbank2_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group3/*u_dbank2_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 3 , CSM dbank 2 , Sub-bank 1
set name "grp3_dbank2_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group3/*u_dbank2_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 3 , CSM dbank 3 , Sub-bank 0
set name "grp3_dbank3_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group3/*u_dbank3_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 3 , CSM dbank 3 , Sub-bank 1
set name "grp3_dbank3_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group3/*u_dbank3_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 3 , CSM dbank 4 , Sub-bank 0
set name "grp3_dbank4_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group3/*u_dbank4_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 3 , CSM dbank 4 , Sub-bank 1
set name "grp3_dbank4_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group3/*u_dbank4_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 3 , CSM dbank 5 , Sub-bank 0
set name "grp3_dbank5_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group3/*u_dbank5_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 3 , CSM dbank 5 , Sub-bank 1
set name "grp3_dbank5_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group3/*u_dbank5_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 3 , CSM dbank 6 , Sub-bank 0
set name "grp3_dbank6_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group3/*u_dbank6_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 3 , CSM dbank 6 , Sub-bank 1
set name "grp3_dbank6_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group3/*u_dbank6_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 3 , CSM dbank 7 , Sub-bank 0
set name "grp3_dbank7_sub0_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group3/*u_dbank7_top*/u_dbank_ck_distrib/clkgate_BLK\[0\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"
# Group 3 , CSM dbank 7 , Sub-bank 1
set name "grp3_dbank7_sub1_gclk"
create_generated_clock -name $name -edges {1 2 5} -add -master ${ncore_clock_obj} -source ${ncore_clock_port} \
    [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~${ncorehier}*u_npu_group3/*u_dbank7_top*/u_dbank_ck_distrib/clkgate_BLK\[1\]*"]
set_dont_touch_network $name
set_clock_uncertainty -setup $clk_unc_setup $name
set_clock_uncertainty -hold  $clk_unc_hold  $name
append dbank_gclocks " $name"


if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name $ncore_virt_clock_name -period 1.000
}

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
set scg_cmd "set_clock_groups -asynchronous -allow_paths -group {$ncore_clock_name $l2arc0_hs_gclocks $l2arc1_hs_gclocks $dbank_gclocks}  -group {$arc0_wdt_clock_name} -group {$arc1_wdt_clock_name} -group {$apb_clock_name} -group {$noc_clock_name} -group {$cfg_clock_name} -group {$ncore_virt_clock_name} "
} else {
set scg_cmd "set_clock_groups -asynchronous -allow_paths -group {$ncore_clock_name $l2arc0_hs_gclocks $l2arc1_hs_gclocks $dbank_gclocks}  -group {$arc0_wdt_clock_name} -group {$arc1_wdt_clock_name} -group {$apb_clock_name} -group {$noc_clock_name} -group {$cfg_clock_name} "
}

echo "Info: clock groups"
echo $scg_cmd
eval $scg_cmd

#------------------------------------------------------------------------------
# Input Constraints
#------------------------------------------------------------------------------
set arc0_wdt_clock_obj [get_clocks $arc0_wdt_clock_name]
set arc1_wdt_clock_obj [get_clocks $arc1_wdt_clock_name]

set top_reset     [get_ports nl2_rst_a -filter {@port_direction == in}]
set cfg_reset     [get_ports npu_cfg_rst_a -filter {@port_direction == in}]
set noc_reset     [get_ports npu_noc_rst_a -filter {@port_direction == in}]
set core_reset    [get_ports npu_core_rst_a -filter {@port_direction == in}]
set apb_reset     [get_ports arct_rst_an   -filter {@port_direction == in}]

set arc0_reset [get_ports "nl2arc0_rst_a" -filter {@port_direction == in}]
set arc1_reset [get_ports "nl2arc1_rst_a" -filter {@port_direction == in}]

set grp0_reset [get_ports "grp0_rst_a" -filter {@port_direction == in}]
set grp1_reset [get_ports "grp1_rst_a" -filter {@port_direction == in}]
set grp2_reset [get_ports "grp2_rst_a" -filter {@port_direction == in}]
set grp3_reset [get_ports "grp3_rst_a" -filter {@port_direction == in}]

set gclk_col [get_clocks -quiet *_gclk]

# Default value for all inputs
set ALL_INPUTS_EXC_CLK   [remove_from_collection [all_inputs] [get_ports *_clk]]
set_input_delay [expr 0.25 * ${ncore_clock_per}] -clock ${ncore_clock_obj} [get_ports $ALL_INPUTS_EXC_CLK -filter {@port_direction == in}]
set_input_delay [expr 0.25 * ${apb_clock_per}] -clock ${apb_clock_obj} [get_ports arct_*  -filter {@port_direction == in}]
set_input_delay [expr 0.25 * ${apb_clock_per}] -clock ${apb_clock_obj} [get_ports arct0_* -filter {@port_direction == in}]



# async reset
set_input_delay [expr 0.25 * ${ncore_clock_per}] -clock ${ncore_clock_obj} ${top_reset}
set_input_delay [expr 0.25 * ${ncore_clock_per}] -clock ${cfg_clock_obj}   ${cfg_reset}
set_input_delay [expr 0.25 * ${ncore_clock_per}] -clock ${noc_clock_obj}   ${noc_reset}
set_input_delay [expr 0.25 * ${ncore_clock_per}] -clock ${ncore_clock_obj} ${core_reset}
set_input_delay [expr 0.25 * ${apb_clock_per}] -clock ${apb_clock_obj}   ${apb_reset}

set_input_delay [expr 0.25 * ${ncore_clock_per}] -clock ${ncore_clock_obj} ${arc0_reset}
set_input_delay [expr 0.25 * ${ncore_clock_per}] -clock ${ncore_clock_obj} ${arc1_reset}
set_input_delay [expr 0.25 * ${ncore_clock_per}] -clock ${ncore_clock_obj} ${grp0_reset}
set_input_delay [expr 0.25 * ${ncore_clock_per}] -clock ${ncore_clock_obj} ${grp1_reset}
set_input_delay [expr 0.25 * ${ncore_clock_per}] -clock ${ncore_clock_obj} ${grp2_reset}
set_input_delay [expr 0.25 * ${ncore_clock_per}] -clock ${ncore_clock_obj} ${grp3_reset}

## Async Constraints
# NPU Master AXI
# L2 ARC NoC
set_input_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${noc_clock_obj} [get_ports npu_mst0_axi_* -filter {@port_direction == in}]

# GRP NoC
set_input_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${noc_clock_obj} [get_ports npu_mst1_axi_* -filter {@port_direction == in}]
set_input_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${noc_clock_obj} [get_ports npu_mst2_axi_* -filter {@port_direction == in}]
set_input_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${noc_clock_obj} [get_ports npu_mst3_axi_* -filter {@port_direction == in}]
set_input_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${noc_clock_obj} [get_ports npu_mst4_axi_* -filter {@port_direction == in}]

##Set input delay for GALS interface
##sl::`j::nl1arc_dev_gals_* & sl::`j::nl1arc_ccm_gals*
set_input_delay  [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl0nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == in}]
set_input_delay  [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl0nl1arc_*_axi_gals_*_data -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl0nl1arc_*_axi_gals*_rpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl0nl1arc_*_axi_gals*_wpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl1nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == in}]
set_input_delay  [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl1nl1arc_*_axi_gals_*_data -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl1nl1arc_*_axi_gals*_rpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl1nl1arc_*_axi_gals*_wpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl2nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == in}]
set_input_delay  [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl2nl1arc_*_axi_gals_*_data -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl2nl1arc_*_axi_gals*_rpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl2nl1arc_*_axi_gals*_wpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl3nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == in}]
set_input_delay  [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl3nl1arc_*_axi_gals_*_data -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl3nl1arc_*_axi_gals*_rpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl3nl1arc_*_axi_gals*_wpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl4nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == in}]
set_input_delay  [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl4nl1arc_*_axi_gals_*_data -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl4nl1arc_*_axi_gals*_rpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl4nl1arc_*_axi_gals*_wpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl5nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == in}]
set_input_delay  [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl5nl1arc_*_axi_gals_*_data -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl5nl1arc_*_axi_gals*_rpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl5nl1arc_*_axi_gals*_wpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl6nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == in}]
set_input_delay  [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl6nl1arc_*_axi_gals_*_data -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl6nl1arc_*_axi_gals*_rpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl6nl1arc_*_axi_gals*_wpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl7nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == in}]
set_input_delay  [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl7nl1arc_*_axi_gals_*_data -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl7nl1arc_*_axi_gals*_rpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl7nl1arc_*_axi_gals*_wpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl8nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == in}]
set_input_delay  [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl8nl1arc_*_axi_gals_*_data -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl8nl1arc_*_axi_gals*_rpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl8nl1arc_*_axi_gals*_wpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl9nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == in}]
set_input_delay  [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl9nl1arc_*_axi_gals_*_data -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl9nl1arc_*_axi_gals*_rpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl9nl1arc_*_axi_gals*_wpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl10nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == in}]
set_input_delay  [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl10nl1arc_*_axi_gals_*_data -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl10nl1arc_*_axi_gals*_rpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl10nl1arc_*_axi_gals*_wpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl11nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == in}]
set_input_delay  [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl11nl1arc_*_axi_gals_*_data -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl11nl1arc_*_axi_gals*_rpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl11nl1arc_*_axi_gals*_wpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl12nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == in}]
set_input_delay  [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl12nl1arc_*_axi_gals_*_data -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl12nl1arc_*_axi_gals*_rpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl12nl1arc_*_axi_gals*_wpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl13nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == in}]
set_input_delay  [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl13nl1arc_*_axi_gals_*_data -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl13nl1arc_*_axi_gals*_rpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl13nl1arc_*_axi_gals*_wpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl14nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == in}]
set_input_delay  [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl14nl1arc_*_axi_gals_*_data -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl14nl1arc_*_axi_gals*_rpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl14nl1arc_*_axi_gals*_wpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl15nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == in}]
set_input_delay  [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl15nl1arc_*_axi_gals_*_data -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl15nl1arc_*_axi_gals*_rpnt_a -filter {@port_direction == in}]
set_input_delay  [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl15nl1arc_*_axi_gals*_wpnt_a -filter {@port_direction == in}]
##Set input delay for APB async interface
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl0nl1arc_dbg_ack_a -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl0nl1arc_dbg_presp -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl1nl1arc_dbg_ack_a -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl1nl1arc_dbg_presp -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl2nl1arc_dbg_ack_a -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl2nl1arc_dbg_presp -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl3nl1arc_dbg_ack_a -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl3nl1arc_dbg_presp -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl4nl1arc_dbg_ack_a -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl4nl1arc_dbg_presp -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl5nl1arc_dbg_ack_a -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl5nl1arc_dbg_presp -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl6nl1arc_dbg_ack_a -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl6nl1arc_dbg_presp -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl7nl1arc_dbg_ack_a -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl7nl1arc_dbg_presp -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl8nl1arc_dbg_ack_a -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl8nl1arc_dbg_presp -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl9nl1arc_dbg_ack_a -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl9nl1arc_dbg_presp -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl10nl1arc_dbg_ack_a -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl10nl1arc_dbg_presp -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl11nl1arc_dbg_ack_a -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl11nl1arc_dbg_presp -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl12nl1arc_dbg_ack_a -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl12nl1arc_dbg_presp -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl13nl1arc_dbg_ack_a -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl13nl1arc_dbg_presp -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl14nl1arc_dbg_ack_a -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl14nl1arc_dbg_presp -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl15nl1arc_dbg_ack_a -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl15nl1arc_dbg_presp -filter {@port_direction == in}]
##Set input delay for SWE interface (pulse + data)
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl0_rtt_swe_val  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl0_rtt_swe_data -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl0_rtt_swe_ext  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl1_rtt_swe_val  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl1_rtt_swe_data -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl1_rtt_swe_ext  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl2_rtt_swe_val  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl2_rtt_swe_data -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl2_rtt_swe_ext  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl3_rtt_swe_val  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl3_rtt_swe_data -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl3_rtt_swe_ext  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl4_rtt_swe_val  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl4_rtt_swe_data -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl4_rtt_swe_ext  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl5_rtt_swe_val  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl5_rtt_swe_data -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl5_rtt_swe_ext  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl6_rtt_swe_val  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl6_rtt_swe_data -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl6_rtt_swe_ext  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl7_rtt_swe_val  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl7_rtt_swe_data -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl7_rtt_swe_ext  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl8_rtt_swe_val  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl8_rtt_swe_data -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl8_rtt_swe_ext  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl9_rtt_swe_val  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl9_rtt_swe_data -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl9_rtt_swe_ext  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl10_rtt_swe_val  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl10_rtt_swe_data -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl10_rtt_swe_ext  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl11_rtt_swe_val  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl11_rtt_swe_data -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl11_rtt_swe_ext  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl12_rtt_swe_val  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl12_rtt_swe_data -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl12_rtt_swe_ext  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl13_rtt_swe_val  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl13_rtt_swe_data -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl13_rtt_swe_ext  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl14_rtt_swe_val  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl14_rtt_swe_data -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl14_rtt_swe_ext  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl15_rtt_swe_val  -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl15_rtt_swe_data -filter {@port_direction == in}]
set_input_delay  [expr 0.8 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl15_rtt_swe_ext  -filter {@port_direction == in}]

# NPU Slave AXI
# DMIs
set_input_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${noc_clock_obj} [get_ports npu_dmi0_axi_* -filter {@port_direction == in}]

# CFG DMI Slave AXI
set_input_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${cfg_clock_obj} [get_ports npu_cfg_axi_* -filter {@port_direction == in}]



if {"$npu_lint_virt_clk" ne "0"} {
  foreach_in_collection clkname [get_clocks -quiet * -filter {@is_generated == false}] {
    remove_input_delay  -clock $clkname [get_ports nl2*_a -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports grp*_a -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports npu_cfg_rst_a -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports npu_noc_rst_a -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports npu_core_rst_a -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports arct_rst_an -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports at_rst_an   -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $ncore_virt_clock_name] period]] -clock [get_clocks $ncore_virt_clock_name] [get_ports nl2*_a -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $ncore_virt_clock_name] period]] -clock [get_clocks $ncore_virt_clock_name] [get_ports grp*_a -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $ncore_virt_clock_name] period]] -clock [get_clocks $ncore_virt_clock_name] [get_ports npu_cfg_rst_a -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $ncore_virt_clock_name] period]] -clock [get_clocks $ncore_virt_clock_name] [get_ports npu_noc_rst_a -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $ncore_virt_clock_name] period]] -clock [get_clocks $ncore_virt_clock_name] [get_ports npu_core_rst_a -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $ncore_virt_clock_name] period]] -clock [get_clocks $ncore_virt_clock_name] [get_ports arct_rst_an -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $ncore_virt_clock_name] period]] -clock [get_clocks $ncore_virt_clock_name] [get_ports at_rst_an -filter {@port_direction == in}]
}

if {"$default_drive_cell" eq "none"} {
  if {"$npu_lint_virt_clk" eq "0"} {
    set_input_transition 0.1 [remove_from_collection [get_ports * -filter {@port_direction == in}] [get_ports [get_object_name [get_clocks * -filter {@is_generated == false}]]]]
  } else {
    set ALL_CLKS_EXC_GEN       [get_clocks * -filter {@is_generated == false}]
    set ALL_CLKS_EXC_GEN_VIRT  [remove_from_collection $ALL_CLKS_EXC_GEN [get_clocks *_async_vclk -filter {@is_generated == false}]]
    set_input_transition 0.1   [remove_from_collection [get_ports * -filter {@port_direction == in}] [get_ports [get_object_name $ALL_CLKS_EXC_GEN_VIRT]]]
  }
} else {
  set_driving_cell -lib_cell $default_drive_cell -pin X [get_ports * -filter {@port_direction == in}]
  remove_driving_cell [get_ports [get_object_name [get_clocks * -filter {@is_generated == false}]]]
}

#------------------------------------------------------------------------------
# Output Constraints
#------------------------------------------------------------------------------
# Default value
set_output_delay [expr 0.25 * ${ncore_clock_per}] -clock ${ncore_clock_obj} [get_ports * -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${apb_clock_per}] -clock ${apb_clock_obj} [get_ports arct_* -filter {@port_direction == out}]


# NPU Master AXI
set_output_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${noc_clock_obj} [get_ports npu_mst0_axi_*  -filter {@port_direction == out}]

# GRP NoC
set_output_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${noc_clock_obj} [get_ports npu_mst1_axi_*  -filter {@port_direction == out}]
set_output_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${noc_clock_obj} [get_ports npu_mst2_axi_*  -filter {@port_direction == out}]
set_output_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${noc_clock_obj} [get_ports npu_mst3_axi_*  -filter {@port_direction == out}]
set_output_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${noc_clock_obj} [get_ports npu_mst4_axi_*  -filter {@port_direction == out}]

##Set output delay for GALS interface
##sl0nl1arc_dev_gals_* & sl0nl1arc_ccm_gals*
set_output_delay [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl0nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == out}]
set_output_delay [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl0nl1arc_*_axi_gals_*_data -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl0nl1arc_*_axi_gals*_rpnt -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl0nl1arc_*_axi_gals*_wpnt -filter {@port_direction == out}]
##Set output delay for GALS interface
##sl1nl1arc_dev_gals_* & sl1nl1arc_ccm_gals*
set_output_delay [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl1nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == out}]
set_output_delay [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl1nl1arc_*_axi_gals_*_data -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl1nl1arc_*_axi_gals*_rpnt -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl1nl1arc_*_axi_gals*_wpnt -filter {@port_direction == out}]
##Set output delay for GALS interface
##sl2nl1arc_dev_gals_* & sl2nl1arc_ccm_gals*
set_output_delay [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl2nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == out}]
set_output_delay [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl2nl1arc_*_axi_gals_*_data -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl2nl1arc_*_axi_gals*_rpnt -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl2nl1arc_*_axi_gals*_wpnt -filter {@port_direction == out}]
##Set output delay for GALS interface
##sl3nl1arc_dev_gals_* & sl3nl1arc_ccm_gals*
set_output_delay [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl3nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == out}]
set_output_delay [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl3nl1arc_*_axi_gals_*_data -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl3nl1arc_*_axi_gals*_rpnt -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl3nl1arc_*_axi_gals*_wpnt -filter {@port_direction == out}]
##Set output delay for GALS interface
##sl4nl1arc_dev_gals_* & sl4nl1arc_ccm_gals*
set_output_delay [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl4nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == out}]
set_output_delay [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl4nl1arc_*_axi_gals_*_data -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl4nl1arc_*_axi_gals*_rpnt -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl4nl1arc_*_axi_gals*_wpnt -filter {@port_direction == out}]
##Set output delay for GALS interface
##sl5nl1arc_dev_gals_* & sl5nl1arc_ccm_gals*
set_output_delay [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl5nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == out}]
set_output_delay [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl5nl1arc_*_axi_gals_*_data -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl5nl1arc_*_axi_gals*_rpnt -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl5nl1arc_*_axi_gals*_wpnt -filter {@port_direction == out}]
##Set output delay for GALS interface
##sl6nl1arc_dev_gals_* & sl6nl1arc_ccm_gals*
set_output_delay [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl6nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == out}]
set_output_delay [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl6nl1arc_*_axi_gals_*_data -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl6nl1arc_*_axi_gals*_rpnt -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl6nl1arc_*_axi_gals*_wpnt -filter {@port_direction == out}]
##Set output delay for GALS interface
##sl7nl1arc_dev_gals_* & sl7nl1arc_ccm_gals*
set_output_delay [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl7nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == out}]
set_output_delay [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl7nl1arc_*_axi_gals_*_data -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl7nl1arc_*_axi_gals*_rpnt -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl7nl1arc_*_axi_gals*_wpnt -filter {@port_direction == out}]
##Set output delay for GALS interface
##sl8nl1arc_dev_gals_* & sl8nl1arc_ccm_gals*
set_output_delay [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl8nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == out}]
set_output_delay [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl8nl1arc_*_axi_gals_*_data -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl8nl1arc_*_axi_gals*_rpnt -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl8nl1arc_*_axi_gals*_wpnt -filter {@port_direction == out}]
##Set output delay for GALS interface
##sl9nl1arc_dev_gals_* & sl9nl1arc_ccm_gals*
set_output_delay [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl9nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == out}]
set_output_delay [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl9nl1arc_*_axi_gals_*_data -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl9nl1arc_*_axi_gals*_rpnt -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl9nl1arc_*_axi_gals*_wpnt -filter {@port_direction == out}]
##Set output delay for GALS interface
##sl10nl1arc_dev_gals_* & sl10nl1arc_ccm_gals*
set_output_delay [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl10nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == out}]
set_output_delay [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl10nl1arc_*_axi_gals_*_data -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl10nl1arc_*_axi_gals*_rpnt -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl10nl1arc_*_axi_gals*_wpnt -filter {@port_direction == out}]
##Set output delay for GALS interface
##sl11nl1arc_dev_gals_* & sl11nl1arc_ccm_gals*
set_output_delay [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl11nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == out}]
set_output_delay [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl11nl1arc_*_axi_gals_*_data -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl11nl1arc_*_axi_gals*_rpnt -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl11nl1arc_*_axi_gals*_wpnt -filter {@port_direction == out}]
##Set output delay for GALS interface
##sl12nl1arc_dev_gals_* & sl12nl1arc_ccm_gals*
set_output_delay [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl12nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == out}]
set_output_delay [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl12nl1arc_*_axi_gals_*_data -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl12nl1arc_*_axi_gals*_rpnt -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl12nl1arc_*_axi_gals*_wpnt -filter {@port_direction == out}]
##Set output delay for GALS interface
##sl13nl1arc_dev_gals_* & sl13nl1arc_ccm_gals*
set_output_delay [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl13nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == out}]
set_output_delay [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl13nl1arc_*_axi_gals_*_data -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl13nl1arc_*_axi_gals*_rpnt -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl13nl1arc_*_axi_gals*_wpnt -filter {@port_direction == out}]
##Set output delay for GALS interface
##sl14nl1arc_dev_gals_* & sl14nl1arc_ccm_gals*
set_output_delay [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl14nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == out}]
set_output_delay [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl14nl1arc_*_axi_gals_*_data -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl14nl1arc_*_axi_gals*_rpnt -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl14nl1arc_*_axi_gals*_wpnt -filter {@port_direction == out}]
##Set output delay for GALS interface
##sl15nl1arc_dev_gals_* & sl15nl1arc_ccm_gals*
set_output_delay [expr 0.9 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl15nl1arc_*_axi_gals_*_rdpnt* -filter {@port_direction == out}]
set_output_delay [expr 0.25*${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl15nl1arc_*_axi_gals_*_data -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl15nl1arc_*_axi_gals*_rpnt -filter {@port_direction == out}]
set_output_delay [expr 0.7 *${ncore_clock_Teff}] -clock ${ncore_clock_obj} [get_ports sl15nl1arc_*_axi_gals*_wpnt -filter {@port_direction == out}]
##Set output delay for APB async interface
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl0nl1arc_dbg_req_a -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl0nl1arc_dbg_pcmd -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl1nl1arc_dbg_req_a -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl1nl1arc_dbg_pcmd -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl2nl1arc_dbg_req_a -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl2nl1arc_dbg_pcmd -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl3nl1arc_dbg_req_a -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl3nl1arc_dbg_pcmd -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl4nl1arc_dbg_req_a -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl4nl1arc_dbg_pcmd -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl5nl1arc_dbg_req_a -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl5nl1arc_dbg_pcmd -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl6nl1arc_dbg_req_a -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl6nl1arc_dbg_pcmd -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl7nl1arc_dbg_req_a -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl7nl1arc_dbg_pcmd -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl8nl1arc_dbg_req_a -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl8nl1arc_dbg_pcmd -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl9nl1arc_dbg_req_a -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl9nl1arc_dbg_pcmd -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl10nl1arc_dbg_req_a -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl10nl1arc_dbg_pcmd -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl11nl1arc_dbg_req_a -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl11nl1arc_dbg_pcmd -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl12nl1arc_dbg_req_a -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl12nl1arc_dbg_pcmd -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl13nl1arc_dbg_req_a -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl13nl1arc_dbg_pcmd -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl14nl1arc_dbg_req_a -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl14nl1arc_dbg_pcmd -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl15nl1arc_dbg_req_a -filter {@port_direction == out}]
set_output_delay  [expr 0.8 *${apb_clock_Teff}] -clock ${apb_clock_obj} [get_ports sl15nl1arc_dbg_pcmd -filter {@port_direction == out}]

# NPU Slave AXI
set_output_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${noc_clock_obj} [get_ports npu_dmi0_axi_* -filter {@port_direction == out}]

# CFG DMI Slave AXI
set_output_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${cfg_clock_obj} [get_ports npu_cfg_axi_* -filter {@port_direction == out}]

set_output_delay [expr 0.25 * ${ncore_clock_per}] -clock ${arc0_wdt_clock_obj} [get_ports nl2arc0_wdt* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${ncore_clock_per}] -clock ${ncore_clock_obj} [get_ports nl2arc0_wdt_reset_error -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${ncore_clock_per}] -clock ${arc1_wdt_clock_obj} [get_ports nl2arc1_wdt* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${ncore_clock_per}] -clock ${ncore_clock_obj} [get_ports nl2arc1_wdt_reset_error -filter {@port_direction == out}]


#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


## GALS WIRES PATHs
## GALS path max_delay should be constrainted to Teff = "MIN(src_clk_period, dst_clk_period) - clock_uncertainty"
## L2 NoC max_delay should be constraints to Teff = "MIN(noc_clk_period, npu_core_clk_period) - clock_uncertainty"
if {("$ncore_clock_per" < "$noc_clock_per")} {
  set noc_Teff ${ncore_clock_Teff}
} else {
  set noc_Teff ${noc_clock_Teff}
}
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${noc_Teff}                                    -through [get_pins {*l2arc_noc_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                              -through [get_pins {*l2arc_noc_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency ${noc_Teff}                                    -through [get_pins {*l2arc_noc_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                              -through [get_pins {*l2arc_noc_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${noc_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core_aon* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*l2arc_noc_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                              -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core_aon* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*l2arc_noc_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core_aon*"]
## CFG DMI max_delay should be constraints to Teff = "MIN(cfg_clk_period, npu_core_clk_period) - clock_uncertainty"
if {("$ncore_clock_per" < "$cfg_clock_per")} {
  set cfg_Teff ${ncore_clock_Teff}
} else {
  set cfg_Teff ${cfg_clock_Teff}
}
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${cfg_Teff}                                    -through [get_pins {*cfg_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                              -through [get_pins {*cfg_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency ${cfg_Teff}                                    -through [get_pins {*cfg_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                              -through [get_pins {*cfg_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${cfg_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core_aon* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*cfg_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                              -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core_aon* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*cfg_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core_aon*"]
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*npu_grp0_noc_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*npu_grp0_noc_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*npu_grp0_noc_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*npu_grp0_noc_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core_aon* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*npu_grp0_noc_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core_aon* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*npu_grp0_noc_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core_aon*"]
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*npu_grp1_noc_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*npu_grp1_noc_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*npu_grp1_noc_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*npu_grp1_noc_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core_aon* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*npu_grp1_noc_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core_aon* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*npu_grp1_noc_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core_aon*"]
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*npu_grp2_noc_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*npu_grp2_noc_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*npu_grp2_noc_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*npu_grp2_noc_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core_aon* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*npu_grp2_noc_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core_aon* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*npu_grp2_noc_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core_aon*"]
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*npu_grp3_noc_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*npu_grp3_noc_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*npu_grp3_noc_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*npu_grp3_noc_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core_aon* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*npu_grp3_noc_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core_aon* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*npu_grp3_noc_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core_aon*"]
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
## NPU DMI max_delay should be constraints to Teff = "MIN(noc_clk_period, npu_core_clk_period) - clock_uncertainty"
set_max_delay -ignore_clock_latency ${noc_Teff}                                    -through [get_pins {*dmi0_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                              -through [get_pins {*dmi0_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency ${noc_Teff}                                    -through [get_pins {*dmi0_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                              -through [get_pins {*dmi0_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core_aon*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${noc_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core_aon* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*dmi0_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                              -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core_aon* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*dmi0_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core_aon*"]

## APB WIRES PATHs
## APB debug max_delay should be constraints to Teff = "MIN(apb_clk_period, npu_core_clk_period) - clock_uncertainty"
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*nl2arc0_req*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*nl2arc0_req*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*nl2arc0_ack*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*nl2arc0_ack*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*nl2arc0_presp*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*nl2arc0_presp*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*nl2arc0_pcmd*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*nl2arc0_pcmd*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*nl2arc1_req*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*nl2arc1_req*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*nl2arc1_ack*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*nl2arc1_ack*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*nl2arc1_presp*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*nl2arc1_presp*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*nl2arc1_pcmd*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*nl2arc1_pcmd*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*arct_syn_req*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*arct_syn_req*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*arct_syn_ack*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*arct_syn_ack*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*arct_syn_presp*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*arct_syn_presp*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*arct_syn_pcmd*} -hier -filter "@full_name=~*u_npu_core_aon*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*arct_syn_pcmd*} -hier -filter "@full_name=~*u_npu_core_aon*"]


#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------
set_false_path -from [get_ports *_a -filter {@port_direction == in}]
set_false_path -from [get_ports npu_csm_base -filter {@port_direction == in}]
set_false_path -from [get_ports *clusternum* -filter {@port_direction == in}]
set_false_path -from [get_ports *dbgen* -filter {@port_direction == in}]
set_false_path -from [get_ports *niden* -filter {@port_direction == in}]
set_false_path -from [get_ports *intvbase_in -filter {@port_direction == in}]
set_false_path -from [get_ports *_isolate* -filter {@port_direction == in}]
set_false_path -from [get_ports *pd_logic  -filter {@port_direction == in}]
set_false_path -from [get_ports *pd_mem    -filter {@port_direction == in}]
set_false_path -from [get_ports arct_dbg_prot_sel -filter {@port_direction == in}]
set_false_path -from [get_ports *_dbg_resp -filter {@port_direction == in}]

# npu_group reset sync
set all_rst_ctl [get_pins -hier * -filter "@full_name=~*${ncorehier}*reset_ctrl*sample_meta* || @full_name=~*${ncorehier}*reset_ctrl*sample_sync*"]

set_false_path -from ${arc0_reset} -through [filter_coll $all_rst_ctl "@full_name=~*${l2hier}0*ialb_cpu_top**reset_ctrl*sample_*"]
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${l2hier}0*ialb_cpu_top*"]
set_false_path -from ${arc1_reset} -through [filter_coll $all_rst_ctl "@full_name=~*${l2hier}1*ialb_cpu_top**reset_ctrl*sample_*"]
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${l2hier}1*ialb_cpu_top*"]

set_false_path -from ${arc0_reset} -through [filter_coll $all_rst_ctl "@full_name=~*${l2hier}0*icc_top**reset_ctrl*sample_*"]
set_false_path -through [get_pins -hier * -filter "@full_name=~*${l2hier}0*icc_top*u_cc_aon_wrap*u_cc_clock_ctrl/l1_clk_enable"]
set_false_path -from ${arc0_reset} -through [filter_coll $all_rst_ctl "@full_name=~*${l2hier}0*icc_top*u_biu_top**reset_ctrl*sample_*"]
set_false_path -from ${arc1_reset} -through [filter_coll $all_rst_ctl "@full_name=~*${l2hier}1*icc_top**reset_ctrl*sample_*"]
set_false_path -through [get_pins -hier * -filter "@full_name=~*${l2hier}1*icc_top*u_cc_aon_wrap*u_cc_clock_ctrl/l1_clk_enable"]
set_false_path -from ${arc1_reset} -through [filter_coll $all_rst_ctl "@full_name=~*${l2hier}1*icc_top*u_biu_top**reset_ctrl*sample_*"]
set_false_path -from ${top_reset} -through [get_pins -hier * -filter "@full_name=~*u_*cdc_sync*sample_*"]

set_false_path -from ${arc0_reset} -through [get_pins -hier * -filter "@full_name=~*u_*cdc_sync*sample_*"]
set_false_path -from ${arc0_reset} -through [get_pins -hier * -filter "@full_name=~**reset_ctrl*sample_*"]
set_false_path -from ${arc1_reset} -through [get_pins -hier * -filter "@full_name=~*u_*cdc_sync*sample_*"]
set_false_path -from ${arc1_reset} -through [get_pins -hier * -filter "@full_name=~**reset_ctrl*sample_*"]

set_false_path -from ${grp0_reset} -through [filter_coll $all_rst_ctl "@full_name=~*${ncorehier}*u_sync_grp_rst*sample_*"]
set_false_path -from ${grp1_reset} -through [filter_coll $all_rst_ctl "@full_name=~*${ncorehier}*u_sync_grp_rst*sample_*"]
set_false_path -from ${grp2_reset} -through [filter_coll $all_rst_ctl "@full_name=~*${ncorehier}*u_sync_grp_rst*sample_*"]
set_false_path -from ${grp3_reset} -through [filter_coll $all_rst_ctl "@full_name=~*${ncorehier}*u_sync_grp_rst*sample_*"]

set_false_path -through [get_pins {*grp_clk_en_a} -hier -filter "@full_name=~*u_npu_core_pd*u_npu_group*"]
set_false_path -through [get_pins {*u_axi_ingrs_tgt0/clk_req} -hier -filter "@full_name=~*u_npu_core_pd*u_npu_group*"]
set_false_path -through [get_pins {*u_axi_ingrs_tgt1/clk_req} -hier -filter "@full_name=~*u_npu_core_pd*u_npu_group*"]
set_false_path -through [get_pins {*u_axi_ingrs_tgt2/clk_req} -hier -filter "@full_name=~*u_npu_core_pd*u_npu_group*"]
set_false_path -through [get_pins {*u_axi_tgt0/clk_req_a} -hier -filter "@full_name=~*u_npu_core_pd*u_npu_group*"]
set_false_path -through [get_pins {*u_axi_tgt1/clk_req_a} -hier -filter "@full_name=~*u_npu_core_pd*u_npu_group*"]
set_false_path -through [get_pins {*u_axi_tgt2/clk_req_a} -hier -filter "@full_name=~*u_npu_core_pd*u_npu_group*"]
set_false_path -through [get_pins {*u_axi_tgt3/clk_req_a} -hier -filter "@full_name=~*u_npu_core_pd*u_npu_group*"]
set_false_path -through [get_pins {*u_axi_mst_tgt/clk_req} -hier -filter "@full_name=~*u_npu_core_pd*u_npu_group*"]
set_false_path -through [get_pins {*u_axi_cfg_sync_tgt/clk_req} -hier -filter "@full_name=~*u_npu_core_pd*u_npu_group*"]

#------------------------------------------------------------------------------
# False Paths  - multi-through
#------------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Multicycle paths
# -----------------------------------------------------------------------------
# ARC HS0 PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${l2hier}0*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${l2hier}0*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${l2hier}0*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${l2hier}0*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1
# ARC HS1 PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${l2hier}1*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${l2hier}1*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${l2hier}1*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${l2hier}1*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1


set_multicycle_path -end -setup  2  -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*u_scm_dbank_sram_all*u_scm_dbank_sram*" ]
set_multicycle_path -end -hold   1  -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*u_scm_dbank_sram_all*u_scm_dbank_sram*" ]


## MCP will cover 2-cycle path constraint for safety in previous, they are as expected and no side effects.
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in} -hier -filter "@full_name=~*u_npu_group0*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in} -hier -filter "@full_name=~*u_npu_group0*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in} -hier -filter "@full_name=~*u_npu_group1*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in} -hier -filter "@full_name=~*u_npu_group1*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in} -hier -filter "@full_name=~*u_npu_group2*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in} -hier -filter "@full_name=~*u_npu_group2*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in} -hier -filter "@full_name=~*u_npu_group3*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in} -hier -filter "@full_name=~*u_npu_group3*"] -hold 1

set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in} -hier -filter "@full_name=~*u_l2arc_grp*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in} -hier -filter "@full_name=~*u_l2arc_grp*"] -hold 1


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

