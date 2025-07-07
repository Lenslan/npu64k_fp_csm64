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
# Constraints for the npu_top module

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# Information from npu_config.v
# NPU Slices        = 16
# NPU NoC ports     = 5
# NPU DMI ports     = 1
# NPU STU Chan      = 8
# NPU HAS MMU       = 1
# NPU HAS PDM       = 1
# NPU HAS Safety    = 0
# NPU Group Number  = 4

# CLN DEV   = 5
# CLN CCM   = 0
# CLN DBANK = 8


# -- Target frequency, in MHz
#
if { [info exists ::env(NPU_FMAX)] } {
    # Take value fron the environment
    set main_clock_freq $::env(NPU_FMAX)
} else {
    set main_clock_freq 1000
}

if { [info exists ::env(WDT_NPU_FMAX)] } {
    # Take value fron the environment
    set ncore_wdt_clock_freq $::env(WDT_NPU_FMAX)
} else {
    set ncore_wdt_clock_freq 50
}

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
# Note: npu_flatten_sdc flag is to control npu_slice_top constraints' visibility at npu_top level
#       a. For hierarchical synthesis with npu_slice_top being hardend, npu_flatten_sdc=0
#       b. For STA at npu_top level which requires npu_slice_top constraints, npu_flatten_sdc=1
set npu_flatten_sdc 0
if { [info exists ::env(NPU_FLATTEN_SDC)] } {
    set npu_flatten_sdc $::env(NPU_FLATTEN_SDC)
}

set apb_clock_freq [expr $main_clock_freq / 2]; # Frequency in MHz. Default: 50% of Ncore Freq.

# -- Clocks uncertainty (setup and hold)
#
set clk_unc_setup 0.200
set clk_unc_hold  0.050
if { [info exists ::env(NPU_CLK_UNC_SETUP)] } {
  set clk_unc_setup $::env(NPU_CLK_UNC_SETUP)
} else {
  set clk_unc_setup 0.200
}
if { [info exists ::env(NPU_CLK_UNC_HOLD)] } {
  set clk_unc_hold $::env(NPU_CLK_UNC_HOLD)
} else {
  set clk_unc_hold  0.050
}
puts "Info: npu_top `uid clk_unc_setup = $clk_unc_setup clk_unc_hold = $clk_unc_hold"

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

# -- L1 ARC controller
#
set nl1arc_has_mmu 1

#alias
set apb_clock_name   "pclkdbg"
set ncore_clock_name "npu_core_clk"
set ncorehier ""
set l2pfx "nl2_"
set l2hier "${ncorehier}*u_npu_l2_arc"

set ncore_clock_freq $main_clock_freq
set noc_clock_freq   $main_clock_freq
set cfg_clock_freq   $main_clock_freq

# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------

# APB Debug itf Clock
set apb_clock_per  [expr 1000.0 / $apb_clock_freq] ; # Period in ns
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
puts "Info: APB Debug clock $apb_clock_name created @ $apb_clock_freq MHz"

# Clock of slice0 from top sdc
set sl0_clock_name "sl0_clk"
set sl0_clock_per  [expr 1000.0 / $ncore_clock_freq] ; # Period in ns
set sl0_clock_port [get_ports $sl0_clock_name]
create_clock -name $sl0_clock_name -period ${sl0_clock_per} ${sl0_clock_port}
set_drive 0 $sl0_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl0_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl0_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl0_clock_per}] -rise_from $sl0_clock_name -fall_to $sl0_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl0_clock_per}] -fall_from $sl0_clock_name -rise_to $sl0_clock_name
set_clock_transition 0.1 $sl0_clock_name
set_dont_touch_network $sl0_clock_name
set sl0_clock_obj [get_clocks $sl0_clock_name]
puts "Info: npu_core clock $sl0_clock_name created @ $ncore_clock_freq MHz"
set sl0_wdt_clock_name "sl0_wdt_clk"
set sl0_wdt_clock_per  [expr 1000.0 / $ncore_wdt_clock_freq] ; # Period in ns
set sl0_wdt_clock_port [get_ports $sl0_wdt_clock_name]
create_clock -name $sl0_wdt_clock_name -period ${sl0_wdt_clock_per} ${sl0_wdt_clock_port}
set_drive 0 $sl0_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl0_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl0_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl0_wdt_clock_per}] -rise_from $sl0_wdt_clock_name -fall_to $sl0_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl0_wdt_clock_per}] -fall_from $sl0_wdt_clock_name -rise_to $sl0_wdt_clock_name
set_clock_transition 0.1 $sl0_wdt_clock_name
set_dont_touch_network $sl0_wdt_clock_name
set sl0_wdt_clock_obj [get_clocks $sl0_wdt_clock_name]
puts "Info: npu_core clock $sl0_wdt_clock_name created @ $ncore_wdt_clock_freq MHz"
# Clock of slice1 from top sdc
set sl1_clock_name "sl1_clk"
set sl1_clock_per  [expr 1000.0 / $ncore_clock_freq] ; # Period in ns
set sl1_clock_port [get_ports $sl1_clock_name]
create_clock -name $sl1_clock_name -period ${sl1_clock_per} ${sl1_clock_port}
set_drive 0 $sl1_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl1_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl1_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl1_clock_per}] -rise_from $sl1_clock_name -fall_to $sl1_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl1_clock_per}] -fall_from $sl1_clock_name -rise_to $sl1_clock_name
set_clock_transition 0.1 $sl1_clock_name
set_dont_touch_network $sl1_clock_name
set sl1_clock_obj [get_clocks $sl1_clock_name]
puts "Info: npu_core clock $sl1_clock_name created @ $ncore_clock_freq MHz"
set sl1_wdt_clock_name "sl1_wdt_clk"
set sl1_wdt_clock_per  [expr 1000.0 / $ncore_wdt_clock_freq] ; # Period in ns
set sl1_wdt_clock_port [get_ports $sl1_wdt_clock_name]
create_clock -name $sl1_wdt_clock_name -period ${sl1_wdt_clock_per} ${sl1_wdt_clock_port}
set_drive 0 $sl1_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl1_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl1_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl1_wdt_clock_per}] -rise_from $sl1_wdt_clock_name -fall_to $sl1_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl1_wdt_clock_per}] -fall_from $sl1_wdt_clock_name -rise_to $sl1_wdt_clock_name
set_clock_transition 0.1 $sl1_wdt_clock_name
set_dont_touch_network $sl1_wdt_clock_name
set sl1_wdt_clock_obj [get_clocks $sl1_wdt_clock_name]
puts "Info: npu_core clock $sl1_wdt_clock_name created @ $ncore_wdt_clock_freq MHz"
# Clock of slice2 from top sdc
set sl2_clock_name "sl2_clk"
set sl2_clock_per  [expr 1000.0 / $ncore_clock_freq] ; # Period in ns
set sl2_clock_port [get_ports $sl2_clock_name]
create_clock -name $sl2_clock_name -period ${sl2_clock_per} ${sl2_clock_port}
set_drive 0 $sl2_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl2_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl2_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl2_clock_per}] -rise_from $sl2_clock_name -fall_to $sl2_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl2_clock_per}] -fall_from $sl2_clock_name -rise_to $sl2_clock_name
set_clock_transition 0.1 $sl2_clock_name
set_dont_touch_network $sl2_clock_name
set sl2_clock_obj [get_clocks $sl2_clock_name]
puts "Info: npu_core clock $sl2_clock_name created @ $ncore_clock_freq MHz"
set sl2_wdt_clock_name "sl2_wdt_clk"
set sl2_wdt_clock_per  [expr 1000.0 / $ncore_wdt_clock_freq] ; # Period in ns
set sl2_wdt_clock_port [get_ports $sl2_wdt_clock_name]
create_clock -name $sl2_wdt_clock_name -period ${sl2_wdt_clock_per} ${sl2_wdt_clock_port}
set_drive 0 $sl2_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl2_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl2_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl2_wdt_clock_per}] -rise_from $sl2_wdt_clock_name -fall_to $sl2_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl2_wdt_clock_per}] -fall_from $sl2_wdt_clock_name -rise_to $sl2_wdt_clock_name
set_clock_transition 0.1 $sl2_wdt_clock_name
set_dont_touch_network $sl2_wdt_clock_name
set sl2_wdt_clock_obj [get_clocks $sl2_wdt_clock_name]
puts "Info: npu_core clock $sl2_wdt_clock_name created @ $ncore_wdt_clock_freq MHz"
# Clock of slice3 from top sdc
set sl3_clock_name "sl3_clk"
set sl3_clock_per  [expr 1000.0 / $ncore_clock_freq] ; # Period in ns
set sl3_clock_port [get_ports $sl3_clock_name]
create_clock -name $sl3_clock_name -period ${sl3_clock_per} ${sl3_clock_port}
set_drive 0 $sl3_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl3_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl3_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl3_clock_per}] -rise_from $sl3_clock_name -fall_to $sl3_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl3_clock_per}] -fall_from $sl3_clock_name -rise_to $sl3_clock_name
set_clock_transition 0.1 $sl3_clock_name
set_dont_touch_network $sl3_clock_name
set sl3_clock_obj [get_clocks $sl3_clock_name]
puts "Info: npu_core clock $sl3_clock_name created @ $ncore_clock_freq MHz"
set sl3_wdt_clock_name "sl3_wdt_clk"
set sl3_wdt_clock_per  [expr 1000.0 / $ncore_wdt_clock_freq] ; # Period in ns
set sl3_wdt_clock_port [get_ports $sl3_wdt_clock_name]
create_clock -name $sl3_wdt_clock_name -period ${sl3_wdt_clock_per} ${sl3_wdt_clock_port}
set_drive 0 $sl3_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl3_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl3_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl3_wdt_clock_per}] -rise_from $sl3_wdt_clock_name -fall_to $sl3_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl3_wdt_clock_per}] -fall_from $sl3_wdt_clock_name -rise_to $sl3_wdt_clock_name
set_clock_transition 0.1 $sl3_wdt_clock_name
set_dont_touch_network $sl3_wdt_clock_name
set sl3_wdt_clock_obj [get_clocks $sl3_wdt_clock_name]
puts "Info: npu_core clock $sl3_wdt_clock_name created @ $ncore_wdt_clock_freq MHz"
# Clock of slice4 from top sdc
set sl4_clock_name "sl4_clk"
set sl4_clock_per  [expr 1000.0 / $ncore_clock_freq] ; # Period in ns
set sl4_clock_port [get_ports $sl4_clock_name]
create_clock -name $sl4_clock_name -period ${sl4_clock_per} ${sl4_clock_port}
set_drive 0 $sl4_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl4_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl4_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl4_clock_per}] -rise_from $sl4_clock_name -fall_to $sl4_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl4_clock_per}] -fall_from $sl4_clock_name -rise_to $sl4_clock_name
set_clock_transition 0.1 $sl4_clock_name
set_dont_touch_network $sl4_clock_name
set sl4_clock_obj [get_clocks $sl4_clock_name]
puts "Info: npu_core clock $sl4_clock_name created @ $ncore_clock_freq MHz"
set sl4_wdt_clock_name "sl4_wdt_clk"
set sl4_wdt_clock_per  [expr 1000.0 / $ncore_wdt_clock_freq] ; # Period in ns
set sl4_wdt_clock_port [get_ports $sl4_wdt_clock_name]
create_clock -name $sl4_wdt_clock_name -period ${sl4_wdt_clock_per} ${sl4_wdt_clock_port}
set_drive 0 $sl4_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl4_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl4_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl4_wdt_clock_per}] -rise_from $sl4_wdt_clock_name -fall_to $sl4_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl4_wdt_clock_per}] -fall_from $sl4_wdt_clock_name -rise_to $sl4_wdt_clock_name
set_clock_transition 0.1 $sl4_wdt_clock_name
set_dont_touch_network $sl4_wdt_clock_name
set sl4_wdt_clock_obj [get_clocks $sl4_wdt_clock_name]
puts "Info: npu_core clock $sl4_wdt_clock_name created @ $ncore_wdt_clock_freq MHz"
# Clock of slice5 from top sdc
set sl5_clock_name "sl5_clk"
set sl5_clock_per  [expr 1000.0 / $ncore_clock_freq] ; # Period in ns
set sl5_clock_port [get_ports $sl5_clock_name]
create_clock -name $sl5_clock_name -period ${sl5_clock_per} ${sl5_clock_port}
set_drive 0 $sl5_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl5_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl5_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl5_clock_per}] -rise_from $sl5_clock_name -fall_to $sl5_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl5_clock_per}] -fall_from $sl5_clock_name -rise_to $sl5_clock_name
set_clock_transition 0.1 $sl5_clock_name
set_dont_touch_network $sl5_clock_name
set sl5_clock_obj [get_clocks $sl5_clock_name]
puts "Info: npu_core clock $sl5_clock_name created @ $ncore_clock_freq MHz"
set sl5_wdt_clock_name "sl5_wdt_clk"
set sl5_wdt_clock_per  [expr 1000.0 / $ncore_wdt_clock_freq] ; # Period in ns
set sl5_wdt_clock_port [get_ports $sl5_wdt_clock_name]
create_clock -name $sl5_wdt_clock_name -period ${sl5_wdt_clock_per} ${sl5_wdt_clock_port}
set_drive 0 $sl5_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl5_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl5_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl5_wdt_clock_per}] -rise_from $sl5_wdt_clock_name -fall_to $sl5_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl5_wdt_clock_per}] -fall_from $sl5_wdt_clock_name -rise_to $sl5_wdt_clock_name
set_clock_transition 0.1 $sl5_wdt_clock_name
set_dont_touch_network $sl5_wdt_clock_name
set sl5_wdt_clock_obj [get_clocks $sl5_wdt_clock_name]
puts "Info: npu_core clock $sl5_wdt_clock_name created @ $ncore_wdt_clock_freq MHz"
# Clock of slice6 from top sdc
set sl6_clock_name "sl6_clk"
set sl6_clock_per  [expr 1000.0 / $ncore_clock_freq] ; # Period in ns
set sl6_clock_port [get_ports $sl6_clock_name]
create_clock -name $sl6_clock_name -period ${sl6_clock_per} ${sl6_clock_port}
set_drive 0 $sl6_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl6_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl6_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl6_clock_per}] -rise_from $sl6_clock_name -fall_to $sl6_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl6_clock_per}] -fall_from $sl6_clock_name -rise_to $sl6_clock_name
set_clock_transition 0.1 $sl6_clock_name
set_dont_touch_network $sl6_clock_name
set sl6_clock_obj [get_clocks $sl6_clock_name]
puts "Info: npu_core clock $sl6_clock_name created @ $ncore_clock_freq MHz"
set sl6_wdt_clock_name "sl6_wdt_clk"
set sl6_wdt_clock_per  [expr 1000.0 / $ncore_wdt_clock_freq] ; # Period in ns
set sl6_wdt_clock_port [get_ports $sl6_wdt_clock_name]
create_clock -name $sl6_wdt_clock_name -period ${sl6_wdt_clock_per} ${sl6_wdt_clock_port}
set_drive 0 $sl6_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl6_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl6_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl6_wdt_clock_per}] -rise_from $sl6_wdt_clock_name -fall_to $sl6_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl6_wdt_clock_per}] -fall_from $sl6_wdt_clock_name -rise_to $sl6_wdt_clock_name
set_clock_transition 0.1 $sl6_wdt_clock_name
set_dont_touch_network $sl6_wdt_clock_name
set sl6_wdt_clock_obj [get_clocks $sl6_wdt_clock_name]
puts "Info: npu_core clock $sl6_wdt_clock_name created @ $ncore_wdt_clock_freq MHz"
# Clock of slice7 from top sdc
set sl7_clock_name "sl7_clk"
set sl7_clock_per  [expr 1000.0 / $ncore_clock_freq] ; # Period in ns
set sl7_clock_port [get_ports $sl7_clock_name]
create_clock -name $sl7_clock_name -period ${sl7_clock_per} ${sl7_clock_port}
set_drive 0 $sl7_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl7_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl7_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl7_clock_per}] -rise_from $sl7_clock_name -fall_to $sl7_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl7_clock_per}] -fall_from $sl7_clock_name -rise_to $sl7_clock_name
set_clock_transition 0.1 $sl7_clock_name
set_dont_touch_network $sl7_clock_name
set sl7_clock_obj [get_clocks $sl7_clock_name]
puts "Info: npu_core clock $sl7_clock_name created @ $ncore_clock_freq MHz"
set sl7_wdt_clock_name "sl7_wdt_clk"
set sl7_wdt_clock_per  [expr 1000.0 / $ncore_wdt_clock_freq] ; # Period in ns
set sl7_wdt_clock_port [get_ports $sl7_wdt_clock_name]
create_clock -name $sl7_wdt_clock_name -period ${sl7_wdt_clock_per} ${sl7_wdt_clock_port}
set_drive 0 $sl7_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl7_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl7_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl7_wdt_clock_per}] -rise_from $sl7_wdt_clock_name -fall_to $sl7_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl7_wdt_clock_per}] -fall_from $sl7_wdt_clock_name -rise_to $sl7_wdt_clock_name
set_clock_transition 0.1 $sl7_wdt_clock_name
set_dont_touch_network $sl7_wdt_clock_name
set sl7_wdt_clock_obj [get_clocks $sl7_wdt_clock_name]
puts "Info: npu_core clock $sl7_wdt_clock_name created @ $ncore_wdt_clock_freq MHz"
# Clock of slice8 from top sdc
set sl8_clock_name "sl8_clk"
set sl8_clock_per  [expr 1000.0 / $ncore_clock_freq] ; # Period in ns
set sl8_clock_port [get_ports $sl8_clock_name]
create_clock -name $sl8_clock_name -period ${sl8_clock_per} ${sl8_clock_port}
set_drive 0 $sl8_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl8_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl8_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl8_clock_per}] -rise_from $sl8_clock_name -fall_to $sl8_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl8_clock_per}] -fall_from $sl8_clock_name -rise_to $sl8_clock_name
set_clock_transition 0.1 $sl8_clock_name
set_dont_touch_network $sl8_clock_name
set sl8_clock_obj [get_clocks $sl8_clock_name]
puts "Info: npu_core clock $sl8_clock_name created @ $ncore_clock_freq MHz"
set sl8_wdt_clock_name "sl8_wdt_clk"
set sl8_wdt_clock_per  [expr 1000.0 / $ncore_wdt_clock_freq] ; # Period in ns
set sl8_wdt_clock_port [get_ports $sl8_wdt_clock_name]
create_clock -name $sl8_wdt_clock_name -period ${sl8_wdt_clock_per} ${sl8_wdt_clock_port}
set_drive 0 $sl8_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl8_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl8_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl8_wdt_clock_per}] -rise_from $sl8_wdt_clock_name -fall_to $sl8_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl8_wdt_clock_per}] -fall_from $sl8_wdt_clock_name -rise_to $sl8_wdt_clock_name
set_clock_transition 0.1 $sl8_wdt_clock_name
set_dont_touch_network $sl8_wdt_clock_name
set sl8_wdt_clock_obj [get_clocks $sl8_wdt_clock_name]
puts "Info: npu_core clock $sl8_wdt_clock_name created @ $ncore_wdt_clock_freq MHz"
# Clock of slice9 from top sdc
set sl9_clock_name "sl9_clk"
set sl9_clock_per  [expr 1000.0 / $ncore_clock_freq] ; # Period in ns
set sl9_clock_port [get_ports $sl9_clock_name]
create_clock -name $sl9_clock_name -period ${sl9_clock_per} ${sl9_clock_port}
set_drive 0 $sl9_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl9_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl9_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl9_clock_per}] -rise_from $sl9_clock_name -fall_to $sl9_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl9_clock_per}] -fall_from $sl9_clock_name -rise_to $sl9_clock_name
set_clock_transition 0.1 $sl9_clock_name
set_dont_touch_network $sl9_clock_name
set sl9_clock_obj [get_clocks $sl9_clock_name]
puts "Info: npu_core clock $sl9_clock_name created @ $ncore_clock_freq MHz"
set sl9_wdt_clock_name "sl9_wdt_clk"
set sl9_wdt_clock_per  [expr 1000.0 / $ncore_wdt_clock_freq] ; # Period in ns
set sl9_wdt_clock_port [get_ports $sl9_wdt_clock_name]
create_clock -name $sl9_wdt_clock_name -period ${sl9_wdt_clock_per} ${sl9_wdt_clock_port}
set_drive 0 $sl9_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl9_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl9_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl9_wdt_clock_per}] -rise_from $sl9_wdt_clock_name -fall_to $sl9_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl9_wdt_clock_per}] -fall_from $sl9_wdt_clock_name -rise_to $sl9_wdt_clock_name
set_clock_transition 0.1 $sl9_wdt_clock_name
set_dont_touch_network $sl9_wdt_clock_name
set sl9_wdt_clock_obj [get_clocks $sl9_wdt_clock_name]
puts "Info: npu_core clock $sl9_wdt_clock_name created @ $ncore_wdt_clock_freq MHz"
# Clock of slice10 from top sdc
set sl10_clock_name "sl10_clk"
set sl10_clock_per  [expr 1000.0 / $ncore_clock_freq] ; # Period in ns
set sl10_clock_port [get_ports $sl10_clock_name]
create_clock -name $sl10_clock_name -period ${sl10_clock_per} ${sl10_clock_port}
set_drive 0 $sl10_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl10_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl10_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl10_clock_per}] -rise_from $sl10_clock_name -fall_to $sl10_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl10_clock_per}] -fall_from $sl10_clock_name -rise_to $sl10_clock_name
set_clock_transition 0.1 $sl10_clock_name
set_dont_touch_network $sl10_clock_name
set sl10_clock_obj [get_clocks $sl10_clock_name]
puts "Info: npu_core clock $sl10_clock_name created @ $ncore_clock_freq MHz"
set sl10_wdt_clock_name "sl10_wdt_clk"
set sl10_wdt_clock_per  [expr 1000.0 / $ncore_wdt_clock_freq] ; # Period in ns
set sl10_wdt_clock_port [get_ports $sl10_wdt_clock_name]
create_clock -name $sl10_wdt_clock_name -period ${sl10_wdt_clock_per} ${sl10_wdt_clock_port}
set_drive 0 $sl10_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl10_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl10_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl10_wdt_clock_per}] -rise_from $sl10_wdt_clock_name -fall_to $sl10_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl10_wdt_clock_per}] -fall_from $sl10_wdt_clock_name -rise_to $sl10_wdt_clock_name
set_clock_transition 0.1 $sl10_wdt_clock_name
set_dont_touch_network $sl10_wdt_clock_name
set sl10_wdt_clock_obj [get_clocks $sl10_wdt_clock_name]
puts "Info: npu_core clock $sl10_wdt_clock_name created @ $ncore_wdt_clock_freq MHz"
# Clock of slice11 from top sdc
set sl11_clock_name "sl11_clk"
set sl11_clock_per  [expr 1000.0 / $ncore_clock_freq] ; # Period in ns
set sl11_clock_port [get_ports $sl11_clock_name]
create_clock -name $sl11_clock_name -period ${sl11_clock_per} ${sl11_clock_port}
set_drive 0 $sl11_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl11_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl11_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl11_clock_per}] -rise_from $sl11_clock_name -fall_to $sl11_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl11_clock_per}] -fall_from $sl11_clock_name -rise_to $sl11_clock_name
set_clock_transition 0.1 $sl11_clock_name
set_dont_touch_network $sl11_clock_name
set sl11_clock_obj [get_clocks $sl11_clock_name]
puts "Info: npu_core clock $sl11_clock_name created @ $ncore_clock_freq MHz"
set sl11_wdt_clock_name "sl11_wdt_clk"
set sl11_wdt_clock_per  [expr 1000.0 / $ncore_wdt_clock_freq] ; # Period in ns
set sl11_wdt_clock_port [get_ports $sl11_wdt_clock_name]
create_clock -name $sl11_wdt_clock_name -period ${sl11_wdt_clock_per} ${sl11_wdt_clock_port}
set_drive 0 $sl11_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl11_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl11_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl11_wdt_clock_per}] -rise_from $sl11_wdt_clock_name -fall_to $sl11_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl11_wdt_clock_per}] -fall_from $sl11_wdt_clock_name -rise_to $sl11_wdt_clock_name
set_clock_transition 0.1 $sl11_wdt_clock_name
set_dont_touch_network $sl11_wdt_clock_name
set sl11_wdt_clock_obj [get_clocks $sl11_wdt_clock_name]
puts "Info: npu_core clock $sl11_wdt_clock_name created @ $ncore_wdt_clock_freq MHz"
# Clock of slice12 from top sdc
set sl12_clock_name "sl12_clk"
set sl12_clock_per  [expr 1000.0 / $ncore_clock_freq] ; # Period in ns
set sl12_clock_port [get_ports $sl12_clock_name]
create_clock -name $sl12_clock_name -period ${sl12_clock_per} ${sl12_clock_port}
set_drive 0 $sl12_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl12_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl12_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl12_clock_per}] -rise_from $sl12_clock_name -fall_to $sl12_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl12_clock_per}] -fall_from $sl12_clock_name -rise_to $sl12_clock_name
set_clock_transition 0.1 $sl12_clock_name
set_dont_touch_network $sl12_clock_name
set sl12_clock_obj [get_clocks $sl12_clock_name]
puts "Info: npu_core clock $sl12_clock_name created @ $ncore_clock_freq MHz"
set sl12_wdt_clock_name "sl12_wdt_clk"
set sl12_wdt_clock_per  [expr 1000.0 / $ncore_wdt_clock_freq] ; # Period in ns
set sl12_wdt_clock_port [get_ports $sl12_wdt_clock_name]
create_clock -name $sl12_wdt_clock_name -period ${sl12_wdt_clock_per} ${sl12_wdt_clock_port}
set_drive 0 $sl12_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl12_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl12_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl12_wdt_clock_per}] -rise_from $sl12_wdt_clock_name -fall_to $sl12_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl12_wdt_clock_per}] -fall_from $sl12_wdt_clock_name -rise_to $sl12_wdt_clock_name
set_clock_transition 0.1 $sl12_wdt_clock_name
set_dont_touch_network $sl12_wdt_clock_name
set sl12_wdt_clock_obj [get_clocks $sl12_wdt_clock_name]
puts "Info: npu_core clock $sl12_wdt_clock_name created @ $ncore_wdt_clock_freq MHz"
# Clock of slice13 from top sdc
set sl13_clock_name "sl13_clk"
set sl13_clock_per  [expr 1000.0 / $ncore_clock_freq] ; # Period in ns
set sl13_clock_port [get_ports $sl13_clock_name]
create_clock -name $sl13_clock_name -period ${sl13_clock_per} ${sl13_clock_port}
set_drive 0 $sl13_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl13_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl13_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl13_clock_per}] -rise_from $sl13_clock_name -fall_to $sl13_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl13_clock_per}] -fall_from $sl13_clock_name -rise_to $sl13_clock_name
set_clock_transition 0.1 $sl13_clock_name
set_dont_touch_network $sl13_clock_name
set sl13_clock_obj [get_clocks $sl13_clock_name]
puts "Info: npu_core clock $sl13_clock_name created @ $ncore_clock_freq MHz"
set sl13_wdt_clock_name "sl13_wdt_clk"
set sl13_wdt_clock_per  [expr 1000.0 / $ncore_wdt_clock_freq] ; # Period in ns
set sl13_wdt_clock_port [get_ports $sl13_wdt_clock_name]
create_clock -name $sl13_wdt_clock_name -period ${sl13_wdt_clock_per} ${sl13_wdt_clock_port}
set_drive 0 $sl13_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl13_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl13_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl13_wdt_clock_per}] -rise_from $sl13_wdt_clock_name -fall_to $sl13_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl13_wdt_clock_per}] -fall_from $sl13_wdt_clock_name -rise_to $sl13_wdt_clock_name
set_clock_transition 0.1 $sl13_wdt_clock_name
set_dont_touch_network $sl13_wdt_clock_name
set sl13_wdt_clock_obj [get_clocks $sl13_wdt_clock_name]
puts "Info: npu_core clock $sl13_wdt_clock_name created @ $ncore_wdt_clock_freq MHz"
# Clock of slice14 from top sdc
set sl14_clock_name "sl14_clk"
set sl14_clock_per  [expr 1000.0 / $ncore_clock_freq] ; # Period in ns
set sl14_clock_port [get_ports $sl14_clock_name]
create_clock -name $sl14_clock_name -period ${sl14_clock_per} ${sl14_clock_port}
set_drive 0 $sl14_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl14_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl14_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl14_clock_per}] -rise_from $sl14_clock_name -fall_to $sl14_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl14_clock_per}] -fall_from $sl14_clock_name -rise_to $sl14_clock_name
set_clock_transition 0.1 $sl14_clock_name
set_dont_touch_network $sl14_clock_name
set sl14_clock_obj [get_clocks $sl14_clock_name]
puts "Info: npu_core clock $sl14_clock_name created @ $ncore_clock_freq MHz"
set sl14_wdt_clock_name "sl14_wdt_clk"
set sl14_wdt_clock_per  [expr 1000.0 / $ncore_wdt_clock_freq] ; # Period in ns
set sl14_wdt_clock_port [get_ports $sl14_wdt_clock_name]
create_clock -name $sl14_wdt_clock_name -period ${sl14_wdt_clock_per} ${sl14_wdt_clock_port}
set_drive 0 $sl14_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl14_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl14_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl14_wdt_clock_per}] -rise_from $sl14_wdt_clock_name -fall_to $sl14_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl14_wdt_clock_per}] -fall_from $sl14_wdt_clock_name -rise_to $sl14_wdt_clock_name
set_clock_transition 0.1 $sl14_wdt_clock_name
set_dont_touch_network $sl14_wdt_clock_name
set sl14_wdt_clock_obj [get_clocks $sl14_wdt_clock_name]
puts "Info: npu_core clock $sl14_wdt_clock_name created @ $ncore_wdt_clock_freq MHz"
# Clock of slice15 from top sdc
set sl15_clock_name "sl15_clk"
set sl15_clock_per  [expr 1000.0 / $ncore_clock_freq] ; # Period in ns
set sl15_clock_port [get_ports $sl15_clock_name]
create_clock -name $sl15_clock_name -period ${sl15_clock_per} ${sl15_clock_port}
set_drive 0 $sl15_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl15_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl15_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl15_clock_per}] -rise_from $sl15_clock_name -fall_to $sl15_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl15_clock_per}] -fall_from $sl15_clock_name -rise_to $sl15_clock_name
set_clock_transition 0.1 $sl15_clock_name
set_dont_touch_network $sl15_clock_name
set sl15_clock_obj [get_clocks $sl15_clock_name]
puts "Info: npu_core clock $sl15_clock_name created @ $ncore_clock_freq MHz"
set sl15_wdt_clock_name "sl15_wdt_clk"
set sl15_wdt_clock_per  [expr 1000.0 / $ncore_wdt_clock_freq] ; # Period in ns
set sl15_wdt_clock_port [get_ports $sl15_wdt_clock_name]
create_clock -name $sl15_wdt_clock_name -period ${sl15_wdt_clock_per} ${sl15_wdt_clock_port}
set_drive 0 $sl15_wdt_clock_name
set_clock_uncertainty -setup $clk_unc_setup $sl15_wdt_clock_name
set_clock_uncertainty -hold  $clk_unc_hold  $sl15_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl15_wdt_clock_per}] -rise_from $sl15_wdt_clock_name -fall_to $sl15_wdt_clock_name
set_clock_uncertainty -setup [expr 0.05 * ${sl15_wdt_clock_per}] -fall_from $sl15_wdt_clock_name -rise_to $sl15_wdt_clock_name
set_clock_transition 0.1 $sl15_wdt_clock_name
set_dont_touch_network $sl15_wdt_clock_name
set sl15_wdt_clock_obj [get_clocks $sl15_wdt_clock_name]
puts "Info: npu_core clock $sl15_wdt_clock_name created @ $ncore_wdt_clock_freq MHz"

#- npu_core {

# -- Clock pin name
#
set noc_clock_name   "npu_noc_clk"
set cfg_clock_name   "npu_cfg_clk"
set arc0_wdt_clock_name "nl2arc0_wdt_clk"
set arc1_wdt_clock_name "nl2arc1_wdt_clk"
set ncore_virt_clock_name "npu_core_async_vclk"




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
# Input Constraints
#------------------------------------------------------------------------------
set arc0_wdt_clock_obj [get_clocks $arc0_wdt_clock_name]
set arc1_wdt_clock_obj [get_clocks $arc1_wdt_clock_name]

set top_reset     [get_ports nl2_rst_a -filter {@port_direction == in}]
set cfg_reset     [get_ports npu_cfg_rst_a -filter {@port_direction == in}]
set noc_reset     [get_ports npu_noc_rst_a -filter {@port_direction == in}]
set core_reset    [get_ports npu_core_rst_a -filter {@port_direction == in}]

set arc0_reset [get_ports "nl2arc0_rst_a" -filter {@port_direction == in}]
set arc1_reset [get_ports "nl2arc1_rst_a" -filter {@port_direction == in}]

set grp0_reset [get_ports "grp0_rst_a" -filter {@port_direction == in}]
set grp1_reset [get_ports "grp1_rst_a" -filter {@port_direction == in}]
set grp2_reset [get_ports "grp2_rst_a" -filter {@port_direction == in}]
set grp3_reset [get_ports "grp3_rst_a" -filter {@port_direction == in}]

set gclk_col [get_clocks -quiet *_gclk]

# Default value for all inputs
set ALL_INPUTS_EXC_CLK0  [remove_from_collection [all_inputs] [get_ports pclkdbg]]
set ALL_INPUTS_EXC_CLK   [remove_from_collection $ALL_INPUTS_EXC_CLK0 [get_ports *_clk]]
set_input_delay [expr 0.25 * ${ncore_clock_per}] -clock ${ncore_clock_obj} [get_ports $ALL_INPUTS_EXC_CLK -filter {@port_direction == in}]



# async reset
set_input_delay [expr 0.25 * ${ncore_clock_per}] -clock ${ncore_clock_obj} ${top_reset}
set_input_delay [expr 0.25 * ${ncore_clock_per}] -clock ${cfg_clock_obj}   ${cfg_reset}
set_input_delay [expr 0.25 * ${ncore_clock_per}] -clock ${noc_clock_obj}   ${noc_reset}
set_input_delay [expr 0.25 * ${ncore_clock_per}] -clock ${ncore_clock_obj} ${core_reset}

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
    remove_input_delay  -clock $clkname [get_ports presetdbgn  -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports atresetn    -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $ncore_virt_clock_name] period]] -clock [get_clocks $ncore_virt_clock_name] [get_ports nl2*_a -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $ncore_virt_clock_name] period]] -clock [get_clocks $ncore_virt_clock_name] [get_ports grp*_a -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $ncore_virt_clock_name] period]] -clock [get_clocks $ncore_virt_clock_name] [get_ports npu_cfg_rst_a -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $ncore_virt_clock_name] period]] -clock [get_clocks $ncore_virt_clock_name] [get_ports npu_noc_rst_a -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $ncore_virt_clock_name] period]] -clock [get_clocks $ncore_virt_clock_name] [get_ports npu_core_rst_a -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $ncore_virt_clock_name] period]] -clock [get_clocks $ncore_virt_clock_name] [get_ports atresetn   -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $ncore_virt_clock_name] period]] -clock [get_clocks $ncore_virt_clock_name] [get_ports presetdbgn -filter {@port_direction == in}]
}


#------------------------------------------------------------------------------
# Output Constraints
#------------------------------------------------------------------------------
# Default value
set_output_delay [expr 0.25 * ${ncore_clock_per}] -clock ${ncore_clock_obj} [get_ports * -filter {@port_direction == out}]


# NPU Master AXI
set_output_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${noc_clock_obj} [get_ports npu_mst0_axi_*  -filter {@port_direction == out}]

# GRP NoC
set_output_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${noc_clock_obj} [get_ports npu_mst1_axi_*  -filter {@port_direction == out}]
set_output_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${noc_clock_obj} [get_ports npu_mst2_axi_*  -filter {@port_direction == out}]
set_output_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${noc_clock_obj} [get_ports npu_mst3_axi_*  -filter {@port_direction == out}]
set_output_delay [expr 0.25*${axi_clk_ratio} * ${ncore_clock_per}] -clock ${noc_clock_obj} [get_ports npu_mst4_axi_*  -filter {@port_direction == out}]


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


# -----------------------------------------------------------------------------
# Ideal network
# -----------------------------------------------------------------------------

#- npu_core }

# SDC from npu_slice_top
#- npu_slice_top 0 {
# =============================================================================
# Constraints for the npu_slice_top module sl0_
# =============================================================================

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# -- NPU slice search path in the hierarchy
set sl0_nslhier "u_l1core0/"
set sl0_l1hier "${sl0_nslhier}*u_npu_l1_arc"

# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------

set sl0_slice_clock_name sl0_clk
set sl0_slice_virt_clock_name sl0_async_vclk
set sl0_slice_clock_freq 1000
if { [info exists ::env(NPU_FMAX)] } {
    set sl0_slice_clock_freq $::env(NPU_FMAX)
}
set sl0_slice_clock_per  [expr 1000.0 / $sl0_slice_clock_freq] ; # Period in ns
set sl0_slice_clock_port [get_ports $sl0_slice_clock_name]
set sl0_slice_clock_Teff [expr $sl0_slice_clock_per - $clk_unc_setup]
set sl0_slice_clock_obj  [get_clocks $sl0_slice_clock_name]
puts "Info: npu_slice 0 clock $sl0_slice_clock_name created @ $sl0_slice_clock_freq MHz"

set sl0_slice_wdt_clock_freq 50
if { [info exists ::env(WDT_NPU_FMAX)] } {
  set sl0_slice_wdt_clock_freq $::env(WDT_NPU_FMAX)
}
set sl0_slice_wdt_clock_name sl0_wdt_clk
set sl0_slice_wdt_clock_per  [expr 1000.0 / $sl0_slice_wdt_clock_freq] ; # Period in ns
set sl0_slice_wdt_clock_port [get_ports $sl0_slice_wdt_clock_name]
set sl0_slice_wdt_clock_obj [get_clocks $sl0_slice_wdt_clock_name]
puts "Info: npu_slice 0 wdt_clock $sl0_slice_wdt_clock_name created @ $sl0_slice_wdt_clock_freq MHz"

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
set  sl0_l1arc_hs_gclocks ""
proc sl0_l1arc_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable sl0_slice_clock_obj
    variable sl0_slice_clock_port
    variable sl0_l1hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable sl0_l1arc_hs_gclocks
    variable clk_gate0_Q
    # Slow search
    #   get_pins * -hier -filter "@full_name=~*${sl0_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*$clk_gate0_Q"
    # Faster search
    #   get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl0_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*"
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl0_l1hier}*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${sl0_slice_clock_obj} -source ${sl0_slice_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append sl0_l1arc_hs_gclocks " $name"
    puts "Info: npu_slice_top 0 L1 ARC HS generated clock '$name' from ICG $ckg_full_name with edges $ck_edges"
}

set sl0_l1pfx "sl0_nl1_"
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}ic_data_bank0_gclk"        "uic_data_bank0_clkgate"  {1 2 5}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}ic_data_bank1_gclk"        "uic_data_bank1_clkgate"  {1 2 5}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}ic_tag_w0_gclk"            "uic_tag_w0_clkgate"      {1 2 5}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}ic_tag_w1_gclk"            "uic_tag_w1_clkgate"      {1 2 5}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}ic_tag_w2_gclk"            "uic_tag_w2_clkgate"      {1 2 5}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}ic_tag_w3_gclk"            "uic_tag_w3_clkgate"      {1 2 5}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}bc_ram0_gclk"              "u_bc0_clkgate"           {1 2 5}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}bc_ram1_gclk"              "u_bc1_clkgate"           {1 2 5}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}pt_ram0_gclk"              "u_pt0_clkgate"           {1 2 5}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}pt_ram1_gclk"              "u_pt1_clkgate"           {1 2 5}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}dccm_bank0_lo_gclk"        "u_clkgate_dccm_0_lo"     {1 2 5}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}dccm_bank0_hi_gclk"        "u_clkgate_dccm_0_hi"     {1 2 5}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}dccm_bank1_lo_gclk"        "u_clkgate_dccm_1_lo"     {1 2 5}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}dccm_bank1_hi_gclk"        "u_clkgate_dccm_1_hi"     {1 2 5}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}data_even_lo_gclk"         "u_clkgate_data_even_lo"  {1 2 5}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}data_even_hi_gclk"         "u_clkgate_data_even_hi"  {1 2 5}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}data_odd_lo_gclk"          "u_clkgate_data_odd_lo"   {1 2 5}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}data_odd_hi_gclk"          "u_clkgate_data_odd_hi"   {1 2 5}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}ntlb_pd0_gclk"             "u_ntlb_pd0_clkgate"      {1 2 7}
sl0_l1arc_hs_generated_clock "${sl0_l1pfx}ntlb_pd1_gclk"             "u_ntlb_pd1_clkgate"      {1 2 5}

# GTOA core runs at half the frequency
create_generated_clock -name "sl0_gtoa_half_gclk" -edges {1 2 5} -add -master_clock ${sl0_slice_clock_obj} -source ${sl0_slice_clock_port} [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl0_nslhier}*u_npu_gtoa*u_l2_clkgate_half_inst*"]
set_dont_touch_network "sl0_gtoa_half_gclk"
set_clock_uncertainty -setup $clk_unc_setup "sl0_gtoa_half_gclk"
set_clock_uncertainty -hold  $clk_unc_hold  "sl0_gtoa_half_gclk"

group_path -name $sl0_slice_clock_name-to-$sl0_slice_clock_name -from $sl0_slice_clock_name -to $sl0_slice_clock_name
group_path -name sl0_gtoa_half_gclk-to-$sl0_slice_clock_name    -from sl0_gtoa_half_gclk    -to $sl0_slice_clock_name
group_path -name $sl0_slice_clock_name-to-sl0_gtoa_half_gclk    -from $sl0_slice_clock_name -to sl0_gtoa_half_gclk
group_path -name sl0_gtoa_half_gclk-to-sl0_gtoa_half_gclk       -from sl0_gtoa_half_gclk    -to sl0_gtoa_half_gclk

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name $sl0_slice_virt_clock_name -period 1.000
} else {
}

set sl0_slice_all_non_gen_clks      [get_clocks * -filter {@is_generated == false}]
set sl0_slice_all_non_gen_virt_clks $sl0_slice_all_non_gen_clks
if {"$npu_lint_virt_clk" ne "0"} {
  set sl0_slice_all_non_gen_virt_clks [remove_from_collection $sl0_slice_all_non_gen_clks [get_clocks $sl0_slice_virt_clock_name]]
}

set sl0_top_reset_name "sl0_rst_a"
set sl0_top_reset [get_ports ${sl0_top_reset_name} -filter {@port_direction == in}]

set_input_delay [expr 0.25 * ${sl0_slice_clock_per}] -clock ${sl0_slice_clock_obj} ${sl0_top_reset}
set_input_delay [expr 0.25 * ${sl0_slice_clock_per}] -clock ${sl0_slice_clock_obj} ${sl0_top_reset} -add
set_input_delay [expr 0.25 * ${sl0_slice_clock_per}] -clock ${sl0_slice_clock_obj} [get_ports sl0nl1arc_* -filter {@port_direction == in}]
set ALL_INPUTS_EXC_WDT_CLK  [remove_from_collection [get_ports sl0_* -filter {@port_direction == in}] [get_ports sl0_wdt_clk]]
set_input_delay [expr 0.25 * ${sl0_slice_clock_per}] -clock ${sl0_slice_clock_obj} [get_ports $ALL_INPUTS_EXC_WDT_CLK -filter {@port_direction == in}]
if {"$npu_lint_virt_clk" ne "0"} {
  foreach_in_collection clkname $sl0_slice_all_non_gen_virt_clks {
    remove_input_delay  -clock $clkname [get_ports ${sl0_top_reset_name} -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports sl0nl1arc_*_a -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl0_slice_virt_clock_name] period]] -clock [get_clocks $sl0_slice_virt_clock_name] [get_ports ${sl0_top_reset_name} -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl0_slice_virt_clock_name] period]] -clock [get_clocks $sl0_slice_virt_clock_name] [get_ports sl0nl1arc_*_a -filter {@port_direction == in}]
}


set_output_delay [expr 0.25 * ${sl0_slice_clock_per}] -clock ${sl0_slice_clock_obj} [get_ports sl0nl1arc_* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl0_slice_clock_per}] -clock ${sl0_slice_clock_obj} [get_ports sl0_ecc_dbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl0_slice_clock_per}] -clock ${sl0_slice_clock_obj} [get_ports sl0_ecc_sbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl0_slice_wdt_clock_per}] -clock ${sl0_slice_wdt_clock_obj} [get_ports sl0nl1arc_wdt_reset_wdt_clk_error -filter {@port_direction == out}]


#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------


if {"$npu_flatten_sdc" eq 1} {
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${sl0_l1hier}*ialb_cpu_top*"]
set_false_path -through [get_pins {*dbg_prot_sel} -hier -filter "@full_name=~*${sl0_l1hier}*ialb_cpu_top*"]
}



if {"$npu_flatten_sdc" eq 1} {
#------------------------------------------------------------------------------
# False Paths  - multi-through
#------------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Multicycle paths
# -----------------------------------------------------------------------------
# ARC HS PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl0_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl0_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl0_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl0_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1


# Conv 2 cycle checker for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl0_nslhier}*u_npu_conv*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl0_nslhier}*u_npu_conv*"] -hold 1
if {"$npu_lint_virt_clk" eq "0"} {
  # Do not merge redundant registers for timing in synthesis
  set_register_merging [get_cells * -hier -filter "@full_name=~*_nomerge_r*"]  false
}

# GTOA 2 cycle checker, the generated clock inside GTOA is 1/2 the frequency of the main clock
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl0_nslhier}*u_npu_gtoa*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl0_nslhier}*u_npu_gtoa*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl0_nslhier}*u_npu_gtoa*"] -start -setup 2 -comment reg2reg_mc2f2s
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl0_nslhier}*u_npu_gtoa*"] -start -hold 1
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl0_nslhier}*u_npu_gtoa*"] -end -setup 2 -comment reg2reg_mc2s2f
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl0_nslhier}*u_npu_gtoa*"] -end -hold 1
# GTOA 3 cycle path for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl0_nslhier}*u_npu_gtoa*"] -start -setup 3 -comment reg2reg_mc3f2s
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl0_nslhier}*u_npu_gtoa*"] -start -hold 2

}

#- npu_slice_top 0 }
#- npu_slice_top 1 {
# =============================================================================
# Constraints for the npu_slice_top module sl1_
# =============================================================================

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# -- NPU slice search path in the hierarchy
set sl1_nslhier "u_l1core1/"
set sl1_l1hier "${sl1_nslhier}*u_npu_l1_arc"

# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------

set sl1_slice_clock_name sl1_clk
set sl1_slice_virt_clock_name sl1_async_vclk
set sl1_slice_clock_freq 1000
if { [info exists ::env(NPU_FMAX)] } {
    set sl1_slice_clock_freq $::env(NPU_FMAX)
}
set sl1_slice_clock_per  [expr 1000.0 / $sl1_slice_clock_freq] ; # Period in ns
set sl1_slice_clock_port [get_ports $sl1_slice_clock_name]
set sl1_slice_clock_Teff [expr $sl1_slice_clock_per - $clk_unc_setup]
set sl1_slice_clock_obj  [get_clocks $sl1_slice_clock_name]
puts "Info: npu_slice 1 clock $sl1_slice_clock_name created @ $sl1_slice_clock_freq MHz"

set sl1_slice_wdt_clock_freq 50
if { [info exists ::env(WDT_NPU_FMAX)] } {
  set sl1_slice_wdt_clock_freq $::env(WDT_NPU_FMAX)
}
set sl1_slice_wdt_clock_name sl1_wdt_clk
set sl1_slice_wdt_clock_per  [expr 1000.0 / $sl1_slice_wdt_clock_freq] ; # Period in ns
set sl1_slice_wdt_clock_port [get_ports $sl1_slice_wdt_clock_name]
set sl1_slice_wdt_clock_obj [get_clocks $sl1_slice_wdt_clock_name]
puts "Info: npu_slice 1 wdt_clock $sl1_slice_wdt_clock_name created @ $sl1_slice_wdt_clock_freq MHz"

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
set  sl1_l1arc_hs_gclocks ""
proc sl1_l1arc_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable sl1_slice_clock_obj
    variable sl1_slice_clock_port
    variable sl1_l1hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable sl1_l1arc_hs_gclocks
    variable clk_gate0_Q
    # Slow search
    #   get_pins * -hier -filter "@full_name=~*${sl1_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*$clk_gate0_Q"
    # Faster search
    #   get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl1_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*"
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl1_l1hier}*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${sl1_slice_clock_obj} -source ${sl1_slice_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append sl1_l1arc_hs_gclocks " $name"
    puts "Info: npu_slice_top 1 L1 ARC HS generated clock '$name' from ICG $ckg_full_name with edges $ck_edges"
}

set sl1_l1pfx "sl1_nl1_"
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}ic_data_bank0_gclk"        "uic_data_bank0_clkgate"  {1 2 5}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}ic_data_bank1_gclk"        "uic_data_bank1_clkgate"  {1 2 5}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}ic_tag_w0_gclk"            "uic_tag_w0_clkgate"      {1 2 5}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}ic_tag_w1_gclk"            "uic_tag_w1_clkgate"      {1 2 5}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}ic_tag_w2_gclk"            "uic_tag_w2_clkgate"      {1 2 5}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}ic_tag_w3_gclk"            "uic_tag_w3_clkgate"      {1 2 5}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}bc_ram0_gclk"              "u_bc0_clkgate"           {1 2 5}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}bc_ram1_gclk"              "u_bc1_clkgate"           {1 2 5}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}pt_ram0_gclk"              "u_pt0_clkgate"           {1 2 5}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}pt_ram1_gclk"              "u_pt1_clkgate"           {1 2 5}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}dccm_bank0_lo_gclk"        "u_clkgate_dccm_0_lo"     {1 2 5}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}dccm_bank0_hi_gclk"        "u_clkgate_dccm_0_hi"     {1 2 5}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}dccm_bank1_lo_gclk"        "u_clkgate_dccm_1_lo"     {1 2 5}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}dccm_bank1_hi_gclk"        "u_clkgate_dccm_1_hi"     {1 2 5}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}data_even_lo_gclk"         "u_clkgate_data_even_lo"  {1 2 5}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}data_even_hi_gclk"         "u_clkgate_data_even_hi"  {1 2 5}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}data_odd_lo_gclk"          "u_clkgate_data_odd_lo"   {1 2 5}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}data_odd_hi_gclk"          "u_clkgate_data_odd_hi"   {1 2 5}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}ntlb_pd0_gclk"             "u_ntlb_pd0_clkgate"      {1 2 7}
sl1_l1arc_hs_generated_clock "${sl1_l1pfx}ntlb_pd1_gclk"             "u_ntlb_pd1_clkgate"      {1 2 5}

# GTOA core runs at half the frequency
create_generated_clock -name "sl1_gtoa_half_gclk" -edges {1 2 5} -add -master_clock ${sl1_slice_clock_obj} -source ${sl1_slice_clock_port} [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl1_nslhier}*u_npu_gtoa*u_l2_clkgate_half_inst*"]
set_dont_touch_network "sl1_gtoa_half_gclk"
set_clock_uncertainty -setup $clk_unc_setup "sl1_gtoa_half_gclk"
set_clock_uncertainty -hold  $clk_unc_hold  "sl1_gtoa_half_gclk"

group_path -name $sl1_slice_clock_name-to-$sl1_slice_clock_name -from $sl1_slice_clock_name -to $sl1_slice_clock_name
group_path -name sl1_gtoa_half_gclk-to-$sl1_slice_clock_name    -from sl1_gtoa_half_gclk    -to $sl1_slice_clock_name
group_path -name $sl1_slice_clock_name-to-sl1_gtoa_half_gclk    -from $sl1_slice_clock_name -to sl1_gtoa_half_gclk
group_path -name sl1_gtoa_half_gclk-to-sl1_gtoa_half_gclk       -from sl1_gtoa_half_gclk    -to sl1_gtoa_half_gclk

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name $sl1_slice_virt_clock_name -period 1.000
} else {
}

set sl1_slice_all_non_gen_clks      [get_clocks * -filter {@is_generated == false}]
set sl1_slice_all_non_gen_virt_clks $sl1_slice_all_non_gen_clks
if {"$npu_lint_virt_clk" ne "0"} {
  set sl1_slice_all_non_gen_virt_clks [remove_from_collection $sl1_slice_all_non_gen_clks [get_clocks $sl1_slice_virt_clock_name]]
}

set sl1_top_reset_name "sl1_rst_a"
set sl1_top_reset [get_ports ${sl1_top_reset_name} -filter {@port_direction == in}]

set_input_delay [expr 0.25 * ${sl1_slice_clock_per}] -clock ${sl1_slice_clock_obj} ${sl1_top_reset}
set_input_delay [expr 0.25 * ${sl1_slice_clock_per}] -clock ${sl1_slice_clock_obj} ${sl1_top_reset} -add
set_input_delay [expr 0.25 * ${sl1_slice_clock_per}] -clock ${sl1_slice_clock_obj} [get_ports sl1nl1arc_* -filter {@port_direction == in}]
set ALL_INPUTS_EXC_WDT_CLK  [remove_from_collection [get_ports sl1_* -filter {@port_direction == in}] [get_ports sl1_wdt_clk]]
set_input_delay [expr 0.25 * ${sl1_slice_clock_per}] -clock ${sl1_slice_clock_obj} [get_ports $ALL_INPUTS_EXC_WDT_CLK -filter {@port_direction == in}]
if {"$npu_lint_virt_clk" ne "0"} {
  foreach_in_collection clkname $sl1_slice_all_non_gen_virt_clks {
    remove_input_delay  -clock $clkname [get_ports ${sl1_top_reset_name} -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports sl1nl1arc_*_a -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl1_slice_virt_clock_name] period]] -clock [get_clocks $sl1_slice_virt_clock_name] [get_ports ${sl1_top_reset_name} -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl1_slice_virt_clock_name] period]] -clock [get_clocks $sl1_slice_virt_clock_name] [get_ports sl1nl1arc_*_a -filter {@port_direction == in}]
}


set_output_delay [expr 0.25 * ${sl1_slice_clock_per}] -clock ${sl1_slice_clock_obj} [get_ports sl1nl1arc_* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl1_slice_clock_per}] -clock ${sl1_slice_clock_obj} [get_ports sl1_ecc_dbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl1_slice_clock_per}] -clock ${sl1_slice_clock_obj} [get_ports sl1_ecc_sbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl1_slice_wdt_clock_per}] -clock ${sl1_slice_wdt_clock_obj} [get_ports sl1nl1arc_wdt_reset_wdt_clk_error -filter {@port_direction == out}]


#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------


if {"$npu_flatten_sdc" eq 1} {
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${sl1_l1hier}*ialb_cpu_top*"]
set_false_path -through [get_pins {*dbg_prot_sel} -hier -filter "@full_name=~*${sl1_l1hier}*ialb_cpu_top*"]
}



if {"$npu_flatten_sdc" eq 1} {
#------------------------------------------------------------------------------
# False Paths  - multi-through
#------------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Multicycle paths
# -----------------------------------------------------------------------------
# ARC HS PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl1_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl1_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl1_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl1_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1


# Conv 2 cycle checker for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl1_nslhier}*u_npu_conv*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl1_nslhier}*u_npu_conv*"] -hold 1
if {"$npu_lint_virt_clk" eq "0"} {
  # Do not merge redundant registers for timing in synthesis
  set_register_merging [get_cells * -hier -filter "@full_name=~*_nomerge_r*"]  false
}

# GTOA 2 cycle checker, the generated clock inside GTOA is 1/2 the frequency of the main clock
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl1_nslhier}*u_npu_gtoa*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl1_nslhier}*u_npu_gtoa*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl1_nslhier}*u_npu_gtoa*"] -start -setup 2 -comment reg2reg_mc2f2s
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl1_nslhier}*u_npu_gtoa*"] -start -hold 1
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl1_nslhier}*u_npu_gtoa*"] -end -setup 2 -comment reg2reg_mc2s2f
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl1_nslhier}*u_npu_gtoa*"] -end -hold 1
# GTOA 3 cycle path for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl1_nslhier}*u_npu_gtoa*"] -start -setup 3 -comment reg2reg_mc3f2s
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl1_nslhier}*u_npu_gtoa*"] -start -hold 2

}

#- npu_slice_top 1 }
#- npu_slice_top 2 {
# =============================================================================
# Constraints for the npu_slice_top module sl2_
# =============================================================================

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# -- NPU slice search path in the hierarchy
set sl2_nslhier "u_l1core2/"
set sl2_l1hier "${sl2_nslhier}*u_npu_l1_arc"

# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------

set sl2_slice_clock_name sl2_clk
set sl2_slice_virt_clock_name sl2_async_vclk
set sl2_slice_clock_freq 1000
if { [info exists ::env(NPU_FMAX)] } {
    set sl2_slice_clock_freq $::env(NPU_FMAX)
}
set sl2_slice_clock_per  [expr 1000.0 / $sl2_slice_clock_freq] ; # Period in ns
set sl2_slice_clock_port [get_ports $sl2_slice_clock_name]
set sl2_slice_clock_Teff [expr $sl2_slice_clock_per - $clk_unc_setup]
set sl2_slice_clock_obj  [get_clocks $sl2_slice_clock_name]
puts "Info: npu_slice 2 clock $sl2_slice_clock_name created @ $sl2_slice_clock_freq MHz"

set sl2_slice_wdt_clock_freq 50
if { [info exists ::env(WDT_NPU_FMAX)] } {
  set sl2_slice_wdt_clock_freq $::env(WDT_NPU_FMAX)
}
set sl2_slice_wdt_clock_name sl2_wdt_clk
set sl2_slice_wdt_clock_per  [expr 1000.0 / $sl2_slice_wdt_clock_freq] ; # Period in ns
set sl2_slice_wdt_clock_port [get_ports $sl2_slice_wdt_clock_name]
set sl2_slice_wdt_clock_obj [get_clocks $sl2_slice_wdt_clock_name]
puts "Info: npu_slice 2 wdt_clock $sl2_slice_wdt_clock_name created @ $sl2_slice_wdt_clock_freq MHz"

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
set  sl2_l1arc_hs_gclocks ""
proc sl2_l1arc_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable sl2_slice_clock_obj
    variable sl2_slice_clock_port
    variable sl2_l1hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable sl2_l1arc_hs_gclocks
    variable clk_gate0_Q
    # Slow search
    #   get_pins * -hier -filter "@full_name=~*${sl2_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*$clk_gate0_Q"
    # Faster search
    #   get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl2_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*"
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl2_l1hier}*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${sl2_slice_clock_obj} -source ${sl2_slice_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append sl2_l1arc_hs_gclocks " $name"
    puts "Info: npu_slice_top 2 L1 ARC HS generated clock '$name' from ICG $ckg_full_name with edges $ck_edges"
}

set sl2_l1pfx "sl2_nl1_"
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}ic_data_bank0_gclk"        "uic_data_bank0_clkgate"  {1 2 5}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}ic_data_bank1_gclk"        "uic_data_bank1_clkgate"  {1 2 5}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}ic_tag_w0_gclk"            "uic_tag_w0_clkgate"      {1 2 5}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}ic_tag_w1_gclk"            "uic_tag_w1_clkgate"      {1 2 5}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}ic_tag_w2_gclk"            "uic_tag_w2_clkgate"      {1 2 5}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}ic_tag_w3_gclk"            "uic_tag_w3_clkgate"      {1 2 5}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}bc_ram0_gclk"              "u_bc0_clkgate"           {1 2 5}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}bc_ram1_gclk"              "u_bc1_clkgate"           {1 2 5}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}pt_ram0_gclk"              "u_pt0_clkgate"           {1 2 5}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}pt_ram1_gclk"              "u_pt1_clkgate"           {1 2 5}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}dccm_bank0_lo_gclk"        "u_clkgate_dccm_0_lo"     {1 2 5}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}dccm_bank0_hi_gclk"        "u_clkgate_dccm_0_hi"     {1 2 5}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}dccm_bank1_lo_gclk"        "u_clkgate_dccm_1_lo"     {1 2 5}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}dccm_bank1_hi_gclk"        "u_clkgate_dccm_1_hi"     {1 2 5}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}data_even_lo_gclk"         "u_clkgate_data_even_lo"  {1 2 5}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}data_even_hi_gclk"         "u_clkgate_data_even_hi"  {1 2 5}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}data_odd_lo_gclk"          "u_clkgate_data_odd_lo"   {1 2 5}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}data_odd_hi_gclk"          "u_clkgate_data_odd_hi"   {1 2 5}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}ntlb_pd0_gclk"             "u_ntlb_pd0_clkgate"      {1 2 7}
sl2_l1arc_hs_generated_clock "${sl2_l1pfx}ntlb_pd1_gclk"             "u_ntlb_pd1_clkgate"      {1 2 5}

# GTOA core runs at half the frequency
create_generated_clock -name "sl2_gtoa_half_gclk" -edges {1 2 5} -add -master_clock ${sl2_slice_clock_obj} -source ${sl2_slice_clock_port} [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl2_nslhier}*u_npu_gtoa*u_l2_clkgate_half_inst*"]
set_dont_touch_network "sl2_gtoa_half_gclk"
set_clock_uncertainty -setup $clk_unc_setup "sl2_gtoa_half_gclk"
set_clock_uncertainty -hold  $clk_unc_hold  "sl2_gtoa_half_gclk"

group_path -name $sl2_slice_clock_name-to-$sl2_slice_clock_name -from $sl2_slice_clock_name -to $sl2_slice_clock_name
group_path -name sl2_gtoa_half_gclk-to-$sl2_slice_clock_name    -from sl2_gtoa_half_gclk    -to $sl2_slice_clock_name
group_path -name $sl2_slice_clock_name-to-sl2_gtoa_half_gclk    -from $sl2_slice_clock_name -to sl2_gtoa_half_gclk
group_path -name sl2_gtoa_half_gclk-to-sl2_gtoa_half_gclk       -from sl2_gtoa_half_gclk    -to sl2_gtoa_half_gclk

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name $sl2_slice_virt_clock_name -period 1.000
} else {
}

set sl2_slice_all_non_gen_clks      [get_clocks * -filter {@is_generated == false}]
set sl2_slice_all_non_gen_virt_clks $sl2_slice_all_non_gen_clks
if {"$npu_lint_virt_clk" ne "0"} {
  set sl2_slice_all_non_gen_virt_clks [remove_from_collection $sl2_slice_all_non_gen_clks [get_clocks $sl2_slice_virt_clock_name]]
}

set sl2_top_reset_name "sl2_rst_a"
set sl2_top_reset [get_ports ${sl2_top_reset_name} -filter {@port_direction == in}]

set_input_delay [expr 0.25 * ${sl2_slice_clock_per}] -clock ${sl2_slice_clock_obj} ${sl2_top_reset}
set_input_delay [expr 0.25 * ${sl2_slice_clock_per}] -clock ${sl2_slice_clock_obj} ${sl2_top_reset} -add
set_input_delay [expr 0.25 * ${sl2_slice_clock_per}] -clock ${sl2_slice_clock_obj} [get_ports sl2nl1arc_* -filter {@port_direction == in}]
set ALL_INPUTS_EXC_WDT_CLK  [remove_from_collection [get_ports sl2_* -filter {@port_direction == in}] [get_ports sl2_wdt_clk]]
set_input_delay [expr 0.25 * ${sl2_slice_clock_per}] -clock ${sl2_slice_clock_obj} [get_ports $ALL_INPUTS_EXC_WDT_CLK -filter {@port_direction == in}]
if {"$npu_lint_virt_clk" ne "0"} {
  foreach_in_collection clkname $sl2_slice_all_non_gen_virt_clks {
    remove_input_delay  -clock $clkname [get_ports ${sl2_top_reset_name} -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports sl2nl1arc_*_a -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl2_slice_virt_clock_name] period]] -clock [get_clocks $sl2_slice_virt_clock_name] [get_ports ${sl2_top_reset_name} -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl2_slice_virt_clock_name] period]] -clock [get_clocks $sl2_slice_virt_clock_name] [get_ports sl2nl1arc_*_a -filter {@port_direction == in}]
}


set_output_delay [expr 0.25 * ${sl2_slice_clock_per}] -clock ${sl2_slice_clock_obj} [get_ports sl2nl1arc_* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl2_slice_clock_per}] -clock ${sl2_slice_clock_obj} [get_ports sl2_ecc_dbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl2_slice_clock_per}] -clock ${sl2_slice_clock_obj} [get_ports sl2_ecc_sbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl2_slice_wdt_clock_per}] -clock ${sl2_slice_wdt_clock_obj} [get_ports sl2nl1arc_wdt_reset_wdt_clk_error -filter {@port_direction == out}]


#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------


if {"$npu_flatten_sdc" eq 1} {
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${sl2_l1hier}*ialb_cpu_top*"]
set_false_path -through [get_pins {*dbg_prot_sel} -hier -filter "@full_name=~*${sl2_l1hier}*ialb_cpu_top*"]
}



if {"$npu_flatten_sdc" eq 1} {
#------------------------------------------------------------------------------
# False Paths  - multi-through
#------------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Multicycle paths
# -----------------------------------------------------------------------------
# ARC HS PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl2_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl2_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl2_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl2_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1


# Conv 2 cycle checker for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl2_nslhier}*u_npu_conv*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl2_nslhier}*u_npu_conv*"] -hold 1
if {"$npu_lint_virt_clk" eq "0"} {
  # Do not merge redundant registers for timing in synthesis
  set_register_merging [get_cells * -hier -filter "@full_name=~*_nomerge_r*"]  false
}

# GTOA 2 cycle checker, the generated clock inside GTOA is 1/2 the frequency of the main clock
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl2_nslhier}*u_npu_gtoa*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl2_nslhier}*u_npu_gtoa*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl2_nslhier}*u_npu_gtoa*"] -start -setup 2 -comment reg2reg_mc2f2s
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl2_nslhier}*u_npu_gtoa*"] -start -hold 1
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl2_nslhier}*u_npu_gtoa*"] -end -setup 2 -comment reg2reg_mc2s2f
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl2_nslhier}*u_npu_gtoa*"] -end -hold 1
# GTOA 3 cycle path for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl2_nslhier}*u_npu_gtoa*"] -start -setup 3 -comment reg2reg_mc3f2s
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl2_nslhier}*u_npu_gtoa*"] -start -hold 2

}

#- npu_slice_top 2 }
#- npu_slice_top 3 {
# =============================================================================
# Constraints for the npu_slice_top module sl3_
# =============================================================================

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# -- NPU slice search path in the hierarchy
set sl3_nslhier "u_l1core3/"
set sl3_l1hier "${sl3_nslhier}*u_npu_l1_arc"

# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------

set sl3_slice_clock_name sl3_clk
set sl3_slice_virt_clock_name sl3_async_vclk
set sl3_slice_clock_freq 1000
if { [info exists ::env(NPU_FMAX)] } {
    set sl3_slice_clock_freq $::env(NPU_FMAX)
}
set sl3_slice_clock_per  [expr 1000.0 / $sl3_slice_clock_freq] ; # Period in ns
set sl3_slice_clock_port [get_ports $sl3_slice_clock_name]
set sl3_slice_clock_Teff [expr $sl3_slice_clock_per - $clk_unc_setup]
set sl3_slice_clock_obj  [get_clocks $sl3_slice_clock_name]
puts "Info: npu_slice 3 clock $sl3_slice_clock_name created @ $sl3_slice_clock_freq MHz"

set sl3_slice_wdt_clock_freq 50
if { [info exists ::env(WDT_NPU_FMAX)] } {
  set sl3_slice_wdt_clock_freq $::env(WDT_NPU_FMAX)
}
set sl3_slice_wdt_clock_name sl3_wdt_clk
set sl3_slice_wdt_clock_per  [expr 1000.0 / $sl3_slice_wdt_clock_freq] ; # Period in ns
set sl3_slice_wdt_clock_port [get_ports $sl3_slice_wdt_clock_name]
set sl3_slice_wdt_clock_obj [get_clocks $sl3_slice_wdt_clock_name]
puts "Info: npu_slice 3 wdt_clock $sl3_slice_wdt_clock_name created @ $sl3_slice_wdt_clock_freq MHz"

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
set  sl3_l1arc_hs_gclocks ""
proc sl3_l1arc_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable sl3_slice_clock_obj
    variable sl3_slice_clock_port
    variable sl3_l1hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable sl3_l1arc_hs_gclocks
    variable clk_gate0_Q
    # Slow search
    #   get_pins * -hier -filter "@full_name=~*${sl3_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*$clk_gate0_Q"
    # Faster search
    #   get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl3_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*"
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl3_l1hier}*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${sl3_slice_clock_obj} -source ${sl3_slice_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append sl3_l1arc_hs_gclocks " $name"
    puts "Info: npu_slice_top 3 L1 ARC HS generated clock '$name' from ICG $ckg_full_name with edges $ck_edges"
}

set sl3_l1pfx "sl3_nl1_"
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}ic_data_bank0_gclk"        "uic_data_bank0_clkgate"  {1 2 5}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}ic_data_bank1_gclk"        "uic_data_bank1_clkgate"  {1 2 5}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}ic_tag_w0_gclk"            "uic_tag_w0_clkgate"      {1 2 5}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}ic_tag_w1_gclk"            "uic_tag_w1_clkgate"      {1 2 5}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}ic_tag_w2_gclk"            "uic_tag_w2_clkgate"      {1 2 5}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}ic_tag_w3_gclk"            "uic_tag_w3_clkgate"      {1 2 5}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}bc_ram0_gclk"              "u_bc0_clkgate"           {1 2 5}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}bc_ram1_gclk"              "u_bc1_clkgate"           {1 2 5}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}pt_ram0_gclk"              "u_pt0_clkgate"           {1 2 5}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}pt_ram1_gclk"              "u_pt1_clkgate"           {1 2 5}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}dccm_bank0_lo_gclk"        "u_clkgate_dccm_0_lo"     {1 2 5}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}dccm_bank0_hi_gclk"        "u_clkgate_dccm_0_hi"     {1 2 5}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}dccm_bank1_lo_gclk"        "u_clkgate_dccm_1_lo"     {1 2 5}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}dccm_bank1_hi_gclk"        "u_clkgate_dccm_1_hi"     {1 2 5}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}data_even_lo_gclk"         "u_clkgate_data_even_lo"  {1 2 5}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}data_even_hi_gclk"         "u_clkgate_data_even_hi"  {1 2 5}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}data_odd_lo_gclk"          "u_clkgate_data_odd_lo"   {1 2 5}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}data_odd_hi_gclk"          "u_clkgate_data_odd_hi"   {1 2 5}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}ntlb_pd0_gclk"             "u_ntlb_pd0_clkgate"      {1 2 7}
sl3_l1arc_hs_generated_clock "${sl3_l1pfx}ntlb_pd1_gclk"             "u_ntlb_pd1_clkgate"      {1 2 5}

# GTOA core runs at half the frequency
create_generated_clock -name "sl3_gtoa_half_gclk" -edges {1 2 5} -add -master_clock ${sl3_slice_clock_obj} -source ${sl3_slice_clock_port} [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl3_nslhier}*u_npu_gtoa*u_l2_clkgate_half_inst*"]
set_dont_touch_network "sl3_gtoa_half_gclk"
set_clock_uncertainty -setup $clk_unc_setup "sl3_gtoa_half_gclk"
set_clock_uncertainty -hold  $clk_unc_hold  "sl3_gtoa_half_gclk"

group_path -name $sl3_slice_clock_name-to-$sl3_slice_clock_name -from $sl3_slice_clock_name -to $sl3_slice_clock_name
group_path -name sl3_gtoa_half_gclk-to-$sl3_slice_clock_name    -from sl3_gtoa_half_gclk    -to $sl3_slice_clock_name
group_path -name $sl3_slice_clock_name-to-sl3_gtoa_half_gclk    -from $sl3_slice_clock_name -to sl3_gtoa_half_gclk
group_path -name sl3_gtoa_half_gclk-to-sl3_gtoa_half_gclk       -from sl3_gtoa_half_gclk    -to sl3_gtoa_half_gclk

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name $sl3_slice_virt_clock_name -period 1.000
} else {
}

set sl3_slice_all_non_gen_clks      [get_clocks * -filter {@is_generated == false}]
set sl3_slice_all_non_gen_virt_clks $sl3_slice_all_non_gen_clks
if {"$npu_lint_virt_clk" ne "0"} {
  set sl3_slice_all_non_gen_virt_clks [remove_from_collection $sl3_slice_all_non_gen_clks [get_clocks $sl3_slice_virt_clock_name]]
}

set sl3_top_reset_name "sl3_rst_a"
set sl3_top_reset [get_ports ${sl3_top_reset_name} -filter {@port_direction == in}]

set_input_delay [expr 0.25 * ${sl3_slice_clock_per}] -clock ${sl3_slice_clock_obj} ${sl3_top_reset}
set_input_delay [expr 0.25 * ${sl3_slice_clock_per}] -clock ${sl3_slice_clock_obj} ${sl3_top_reset} -add
set_input_delay [expr 0.25 * ${sl3_slice_clock_per}] -clock ${sl3_slice_clock_obj} [get_ports sl3nl1arc_* -filter {@port_direction == in}]
set ALL_INPUTS_EXC_WDT_CLK  [remove_from_collection [get_ports sl3_* -filter {@port_direction == in}] [get_ports sl3_wdt_clk]]
set_input_delay [expr 0.25 * ${sl3_slice_clock_per}] -clock ${sl3_slice_clock_obj} [get_ports $ALL_INPUTS_EXC_WDT_CLK -filter {@port_direction == in}]
if {"$npu_lint_virt_clk" ne "0"} {
  foreach_in_collection clkname $sl3_slice_all_non_gen_virt_clks {
    remove_input_delay  -clock $clkname [get_ports ${sl3_top_reset_name} -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports sl3nl1arc_*_a -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl3_slice_virt_clock_name] period]] -clock [get_clocks $sl3_slice_virt_clock_name] [get_ports ${sl3_top_reset_name} -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl3_slice_virt_clock_name] period]] -clock [get_clocks $sl3_slice_virt_clock_name] [get_ports sl3nl1arc_*_a -filter {@port_direction == in}]
}


set_output_delay [expr 0.25 * ${sl3_slice_clock_per}] -clock ${sl3_slice_clock_obj} [get_ports sl3nl1arc_* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl3_slice_clock_per}] -clock ${sl3_slice_clock_obj} [get_ports sl3_ecc_dbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl3_slice_clock_per}] -clock ${sl3_slice_clock_obj} [get_ports sl3_ecc_sbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl3_slice_wdt_clock_per}] -clock ${sl3_slice_wdt_clock_obj} [get_ports sl3nl1arc_wdt_reset_wdt_clk_error -filter {@port_direction == out}]


#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------


if {"$npu_flatten_sdc" eq 1} {
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${sl3_l1hier}*ialb_cpu_top*"]
set_false_path -through [get_pins {*dbg_prot_sel} -hier -filter "@full_name=~*${sl3_l1hier}*ialb_cpu_top*"]
}



if {"$npu_flatten_sdc" eq 1} {
#------------------------------------------------------------------------------
# False Paths  - multi-through
#------------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Multicycle paths
# -----------------------------------------------------------------------------
# ARC HS PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl3_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl3_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl3_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl3_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1


# Conv 2 cycle checker for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl3_nslhier}*u_npu_conv*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl3_nslhier}*u_npu_conv*"] -hold 1
if {"$npu_lint_virt_clk" eq "0"} {
  # Do not merge redundant registers for timing in synthesis
  set_register_merging [get_cells * -hier -filter "@full_name=~*_nomerge_r*"]  false
}

# GTOA 2 cycle checker, the generated clock inside GTOA is 1/2 the frequency of the main clock
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl3_nslhier}*u_npu_gtoa*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl3_nslhier}*u_npu_gtoa*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl3_nslhier}*u_npu_gtoa*"] -start -setup 2 -comment reg2reg_mc2f2s
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl3_nslhier}*u_npu_gtoa*"] -start -hold 1
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl3_nslhier}*u_npu_gtoa*"] -end -setup 2 -comment reg2reg_mc2s2f
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl3_nslhier}*u_npu_gtoa*"] -end -hold 1
# GTOA 3 cycle path for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl3_nslhier}*u_npu_gtoa*"] -start -setup 3 -comment reg2reg_mc3f2s
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl3_nslhier}*u_npu_gtoa*"] -start -hold 2

}

#- npu_slice_top 3 }
#- npu_slice_top 4 {
# =============================================================================
# Constraints for the npu_slice_top module sl4_
# =============================================================================

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# -- NPU slice search path in the hierarchy
set sl4_nslhier "u_l1core4/"
set sl4_l1hier "${sl4_nslhier}*u_npu_l1_arc"

# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------

set sl4_slice_clock_name sl4_clk
set sl4_slice_virt_clock_name sl4_async_vclk
set sl4_slice_clock_freq 1000
if { [info exists ::env(NPU_FMAX)] } {
    set sl4_slice_clock_freq $::env(NPU_FMAX)
}
set sl4_slice_clock_per  [expr 1000.0 / $sl4_slice_clock_freq] ; # Period in ns
set sl4_slice_clock_port [get_ports $sl4_slice_clock_name]
set sl4_slice_clock_Teff [expr $sl4_slice_clock_per - $clk_unc_setup]
set sl4_slice_clock_obj  [get_clocks $sl4_slice_clock_name]
puts "Info: npu_slice 4 clock $sl4_slice_clock_name created @ $sl4_slice_clock_freq MHz"

set sl4_slice_wdt_clock_freq 50
if { [info exists ::env(WDT_NPU_FMAX)] } {
  set sl4_slice_wdt_clock_freq $::env(WDT_NPU_FMAX)
}
set sl4_slice_wdt_clock_name sl4_wdt_clk
set sl4_slice_wdt_clock_per  [expr 1000.0 / $sl4_slice_wdt_clock_freq] ; # Period in ns
set sl4_slice_wdt_clock_port [get_ports $sl4_slice_wdt_clock_name]
set sl4_slice_wdt_clock_obj [get_clocks $sl4_slice_wdt_clock_name]
puts "Info: npu_slice 4 wdt_clock $sl4_slice_wdt_clock_name created @ $sl4_slice_wdt_clock_freq MHz"

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
set  sl4_l1arc_hs_gclocks ""
proc sl4_l1arc_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable sl4_slice_clock_obj
    variable sl4_slice_clock_port
    variable sl4_l1hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable sl4_l1arc_hs_gclocks
    variable clk_gate0_Q
    # Slow search
    #   get_pins * -hier -filter "@full_name=~*${sl4_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*$clk_gate0_Q"
    # Faster search
    #   get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl4_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*"
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl4_l1hier}*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${sl4_slice_clock_obj} -source ${sl4_slice_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append sl4_l1arc_hs_gclocks " $name"
    puts "Info: npu_slice_top 4 L1 ARC HS generated clock '$name' from ICG $ckg_full_name with edges $ck_edges"
}

set sl4_l1pfx "sl4_nl1_"
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}ic_data_bank0_gclk"        "uic_data_bank0_clkgate"  {1 2 5}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}ic_data_bank1_gclk"        "uic_data_bank1_clkgate"  {1 2 5}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}ic_tag_w0_gclk"            "uic_tag_w0_clkgate"      {1 2 5}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}ic_tag_w1_gclk"            "uic_tag_w1_clkgate"      {1 2 5}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}ic_tag_w2_gclk"            "uic_tag_w2_clkgate"      {1 2 5}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}ic_tag_w3_gclk"            "uic_tag_w3_clkgate"      {1 2 5}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}bc_ram0_gclk"              "u_bc0_clkgate"           {1 2 5}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}bc_ram1_gclk"              "u_bc1_clkgate"           {1 2 5}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}pt_ram0_gclk"              "u_pt0_clkgate"           {1 2 5}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}pt_ram1_gclk"              "u_pt1_clkgate"           {1 2 5}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}dccm_bank0_lo_gclk"        "u_clkgate_dccm_0_lo"     {1 2 5}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}dccm_bank0_hi_gclk"        "u_clkgate_dccm_0_hi"     {1 2 5}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}dccm_bank1_lo_gclk"        "u_clkgate_dccm_1_lo"     {1 2 5}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}dccm_bank1_hi_gclk"        "u_clkgate_dccm_1_hi"     {1 2 5}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}data_even_lo_gclk"         "u_clkgate_data_even_lo"  {1 2 5}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}data_even_hi_gclk"         "u_clkgate_data_even_hi"  {1 2 5}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}data_odd_lo_gclk"          "u_clkgate_data_odd_lo"   {1 2 5}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}data_odd_hi_gclk"          "u_clkgate_data_odd_hi"   {1 2 5}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}ntlb_pd0_gclk"             "u_ntlb_pd0_clkgate"      {1 2 7}
sl4_l1arc_hs_generated_clock "${sl4_l1pfx}ntlb_pd1_gclk"             "u_ntlb_pd1_clkgate"      {1 2 5}

# GTOA core runs at half the frequency
create_generated_clock -name "sl4_gtoa_half_gclk" -edges {1 2 5} -add -master_clock ${sl4_slice_clock_obj} -source ${sl4_slice_clock_port} [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl4_nslhier}*u_npu_gtoa*u_l2_clkgate_half_inst*"]
set_dont_touch_network "sl4_gtoa_half_gclk"
set_clock_uncertainty -setup $clk_unc_setup "sl4_gtoa_half_gclk"
set_clock_uncertainty -hold  $clk_unc_hold  "sl4_gtoa_half_gclk"

group_path -name $sl4_slice_clock_name-to-$sl4_slice_clock_name -from $sl4_slice_clock_name -to $sl4_slice_clock_name
group_path -name sl4_gtoa_half_gclk-to-$sl4_slice_clock_name    -from sl4_gtoa_half_gclk    -to $sl4_slice_clock_name
group_path -name $sl4_slice_clock_name-to-sl4_gtoa_half_gclk    -from $sl4_slice_clock_name -to sl4_gtoa_half_gclk
group_path -name sl4_gtoa_half_gclk-to-sl4_gtoa_half_gclk       -from sl4_gtoa_half_gclk    -to sl4_gtoa_half_gclk

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name $sl4_slice_virt_clock_name -period 1.000
} else {
}

set sl4_slice_all_non_gen_clks      [get_clocks * -filter {@is_generated == false}]
set sl4_slice_all_non_gen_virt_clks $sl4_slice_all_non_gen_clks
if {"$npu_lint_virt_clk" ne "0"} {
  set sl4_slice_all_non_gen_virt_clks [remove_from_collection $sl4_slice_all_non_gen_clks [get_clocks $sl4_slice_virt_clock_name]]
}

set sl4_top_reset_name "sl4_rst_a"
set sl4_top_reset [get_ports ${sl4_top_reset_name} -filter {@port_direction == in}]

set_input_delay [expr 0.25 * ${sl4_slice_clock_per}] -clock ${sl4_slice_clock_obj} ${sl4_top_reset}
set_input_delay [expr 0.25 * ${sl4_slice_clock_per}] -clock ${sl4_slice_clock_obj} ${sl4_top_reset} -add
set_input_delay [expr 0.25 * ${sl4_slice_clock_per}] -clock ${sl4_slice_clock_obj} [get_ports sl4nl1arc_* -filter {@port_direction == in}]
set ALL_INPUTS_EXC_WDT_CLK  [remove_from_collection [get_ports sl4_* -filter {@port_direction == in}] [get_ports sl4_wdt_clk]]
set_input_delay [expr 0.25 * ${sl4_slice_clock_per}] -clock ${sl4_slice_clock_obj} [get_ports $ALL_INPUTS_EXC_WDT_CLK -filter {@port_direction == in}]
if {"$npu_lint_virt_clk" ne "0"} {
  foreach_in_collection clkname $sl4_slice_all_non_gen_virt_clks {
    remove_input_delay  -clock $clkname [get_ports ${sl4_top_reset_name} -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports sl4nl1arc_*_a -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl4_slice_virt_clock_name] period]] -clock [get_clocks $sl4_slice_virt_clock_name] [get_ports ${sl4_top_reset_name} -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl4_slice_virt_clock_name] period]] -clock [get_clocks $sl4_slice_virt_clock_name] [get_ports sl4nl1arc_*_a -filter {@port_direction == in}]
}


set_output_delay [expr 0.25 * ${sl4_slice_clock_per}] -clock ${sl4_slice_clock_obj} [get_ports sl4nl1arc_* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl4_slice_clock_per}] -clock ${sl4_slice_clock_obj} [get_ports sl4_ecc_dbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl4_slice_clock_per}] -clock ${sl4_slice_clock_obj} [get_ports sl4_ecc_sbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl4_slice_wdt_clock_per}] -clock ${sl4_slice_wdt_clock_obj} [get_ports sl4nl1arc_wdt_reset_wdt_clk_error -filter {@port_direction == out}]


#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------


if {"$npu_flatten_sdc" eq 1} {
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${sl4_l1hier}*ialb_cpu_top*"]
set_false_path -through [get_pins {*dbg_prot_sel} -hier -filter "@full_name=~*${sl4_l1hier}*ialb_cpu_top*"]
}



if {"$npu_flatten_sdc" eq 1} {
#------------------------------------------------------------------------------
# False Paths  - multi-through
#------------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Multicycle paths
# -----------------------------------------------------------------------------
# ARC HS PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl4_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl4_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl4_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl4_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1


# Conv 2 cycle checker for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl4_nslhier}*u_npu_conv*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl4_nslhier}*u_npu_conv*"] -hold 1
if {"$npu_lint_virt_clk" eq "0"} {
  # Do not merge redundant registers for timing in synthesis
  set_register_merging [get_cells * -hier -filter "@full_name=~*_nomerge_r*"]  false
}

# GTOA 2 cycle checker, the generated clock inside GTOA is 1/2 the frequency of the main clock
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl4_nslhier}*u_npu_gtoa*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl4_nslhier}*u_npu_gtoa*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl4_nslhier}*u_npu_gtoa*"] -start -setup 2 -comment reg2reg_mc2f2s
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl4_nslhier}*u_npu_gtoa*"] -start -hold 1
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl4_nslhier}*u_npu_gtoa*"] -end -setup 2 -comment reg2reg_mc2s2f
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl4_nslhier}*u_npu_gtoa*"] -end -hold 1
# GTOA 3 cycle path for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl4_nslhier}*u_npu_gtoa*"] -start -setup 3 -comment reg2reg_mc3f2s
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl4_nslhier}*u_npu_gtoa*"] -start -hold 2

}

#- npu_slice_top 4 }
#- npu_slice_top 5 {
# =============================================================================
# Constraints for the npu_slice_top module sl5_
# =============================================================================

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# -- NPU slice search path in the hierarchy
set sl5_nslhier "u_l1core5/"
set sl5_l1hier "${sl5_nslhier}*u_npu_l1_arc"

# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------

set sl5_slice_clock_name sl5_clk
set sl5_slice_virt_clock_name sl5_async_vclk
set sl5_slice_clock_freq 1000
if { [info exists ::env(NPU_FMAX)] } {
    set sl5_slice_clock_freq $::env(NPU_FMAX)
}
set sl5_slice_clock_per  [expr 1000.0 / $sl5_slice_clock_freq] ; # Period in ns
set sl5_slice_clock_port [get_ports $sl5_slice_clock_name]
set sl5_slice_clock_Teff [expr $sl5_slice_clock_per - $clk_unc_setup]
set sl5_slice_clock_obj  [get_clocks $sl5_slice_clock_name]
puts "Info: npu_slice 5 clock $sl5_slice_clock_name created @ $sl5_slice_clock_freq MHz"

set sl5_slice_wdt_clock_freq 50
if { [info exists ::env(WDT_NPU_FMAX)] } {
  set sl5_slice_wdt_clock_freq $::env(WDT_NPU_FMAX)
}
set sl5_slice_wdt_clock_name sl5_wdt_clk
set sl5_slice_wdt_clock_per  [expr 1000.0 / $sl5_slice_wdt_clock_freq] ; # Period in ns
set sl5_slice_wdt_clock_port [get_ports $sl5_slice_wdt_clock_name]
set sl5_slice_wdt_clock_obj [get_clocks $sl5_slice_wdt_clock_name]
puts "Info: npu_slice 5 wdt_clock $sl5_slice_wdt_clock_name created @ $sl5_slice_wdt_clock_freq MHz"

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
set  sl5_l1arc_hs_gclocks ""
proc sl5_l1arc_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable sl5_slice_clock_obj
    variable sl5_slice_clock_port
    variable sl5_l1hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable sl5_l1arc_hs_gclocks
    variable clk_gate0_Q
    # Slow search
    #   get_pins * -hier -filter "@full_name=~*${sl5_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*$clk_gate0_Q"
    # Faster search
    #   get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl5_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*"
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl5_l1hier}*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${sl5_slice_clock_obj} -source ${sl5_slice_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append sl5_l1arc_hs_gclocks " $name"
    puts "Info: npu_slice_top 5 L1 ARC HS generated clock '$name' from ICG $ckg_full_name with edges $ck_edges"
}

set sl5_l1pfx "sl5_nl1_"
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}ic_data_bank0_gclk"        "uic_data_bank0_clkgate"  {1 2 5}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}ic_data_bank1_gclk"        "uic_data_bank1_clkgate"  {1 2 5}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}ic_tag_w0_gclk"            "uic_tag_w0_clkgate"      {1 2 5}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}ic_tag_w1_gclk"            "uic_tag_w1_clkgate"      {1 2 5}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}ic_tag_w2_gclk"            "uic_tag_w2_clkgate"      {1 2 5}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}ic_tag_w3_gclk"            "uic_tag_w3_clkgate"      {1 2 5}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}bc_ram0_gclk"              "u_bc0_clkgate"           {1 2 5}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}bc_ram1_gclk"              "u_bc1_clkgate"           {1 2 5}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}pt_ram0_gclk"              "u_pt0_clkgate"           {1 2 5}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}pt_ram1_gclk"              "u_pt1_clkgate"           {1 2 5}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}dccm_bank0_lo_gclk"        "u_clkgate_dccm_0_lo"     {1 2 5}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}dccm_bank0_hi_gclk"        "u_clkgate_dccm_0_hi"     {1 2 5}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}dccm_bank1_lo_gclk"        "u_clkgate_dccm_1_lo"     {1 2 5}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}dccm_bank1_hi_gclk"        "u_clkgate_dccm_1_hi"     {1 2 5}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}data_even_lo_gclk"         "u_clkgate_data_even_lo"  {1 2 5}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}data_even_hi_gclk"         "u_clkgate_data_even_hi"  {1 2 5}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}data_odd_lo_gclk"          "u_clkgate_data_odd_lo"   {1 2 5}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}data_odd_hi_gclk"          "u_clkgate_data_odd_hi"   {1 2 5}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}ntlb_pd0_gclk"             "u_ntlb_pd0_clkgate"      {1 2 7}
sl5_l1arc_hs_generated_clock "${sl5_l1pfx}ntlb_pd1_gclk"             "u_ntlb_pd1_clkgate"      {1 2 5}

# GTOA core runs at half the frequency
create_generated_clock -name "sl5_gtoa_half_gclk" -edges {1 2 5} -add -master_clock ${sl5_slice_clock_obj} -source ${sl5_slice_clock_port} [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl5_nslhier}*u_npu_gtoa*u_l2_clkgate_half_inst*"]
set_dont_touch_network "sl5_gtoa_half_gclk"
set_clock_uncertainty -setup $clk_unc_setup "sl5_gtoa_half_gclk"
set_clock_uncertainty -hold  $clk_unc_hold  "sl5_gtoa_half_gclk"

group_path -name $sl5_slice_clock_name-to-$sl5_slice_clock_name -from $sl5_slice_clock_name -to $sl5_slice_clock_name
group_path -name sl5_gtoa_half_gclk-to-$sl5_slice_clock_name    -from sl5_gtoa_half_gclk    -to $sl5_slice_clock_name
group_path -name $sl5_slice_clock_name-to-sl5_gtoa_half_gclk    -from $sl5_slice_clock_name -to sl5_gtoa_half_gclk
group_path -name sl5_gtoa_half_gclk-to-sl5_gtoa_half_gclk       -from sl5_gtoa_half_gclk    -to sl5_gtoa_half_gclk

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name $sl5_slice_virt_clock_name -period 1.000
} else {
}

set sl5_slice_all_non_gen_clks      [get_clocks * -filter {@is_generated == false}]
set sl5_slice_all_non_gen_virt_clks $sl5_slice_all_non_gen_clks
if {"$npu_lint_virt_clk" ne "0"} {
  set sl5_slice_all_non_gen_virt_clks [remove_from_collection $sl5_slice_all_non_gen_clks [get_clocks $sl5_slice_virt_clock_name]]
}

set sl5_top_reset_name "sl5_rst_a"
set sl5_top_reset [get_ports ${sl5_top_reset_name} -filter {@port_direction == in}]

set_input_delay [expr 0.25 * ${sl5_slice_clock_per}] -clock ${sl5_slice_clock_obj} ${sl5_top_reset}
set_input_delay [expr 0.25 * ${sl5_slice_clock_per}] -clock ${sl5_slice_clock_obj} ${sl5_top_reset} -add
set_input_delay [expr 0.25 * ${sl5_slice_clock_per}] -clock ${sl5_slice_clock_obj} [get_ports sl5nl1arc_* -filter {@port_direction == in}]
set ALL_INPUTS_EXC_WDT_CLK  [remove_from_collection [get_ports sl5_* -filter {@port_direction == in}] [get_ports sl5_wdt_clk]]
set_input_delay [expr 0.25 * ${sl5_slice_clock_per}] -clock ${sl5_slice_clock_obj} [get_ports $ALL_INPUTS_EXC_WDT_CLK -filter {@port_direction == in}]
if {"$npu_lint_virt_clk" ne "0"} {
  foreach_in_collection clkname $sl5_slice_all_non_gen_virt_clks {
    remove_input_delay  -clock $clkname [get_ports ${sl5_top_reset_name} -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports sl5nl1arc_*_a -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl5_slice_virt_clock_name] period]] -clock [get_clocks $sl5_slice_virt_clock_name] [get_ports ${sl5_top_reset_name} -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl5_slice_virt_clock_name] period]] -clock [get_clocks $sl5_slice_virt_clock_name] [get_ports sl5nl1arc_*_a -filter {@port_direction == in}]
}


set_output_delay [expr 0.25 * ${sl5_slice_clock_per}] -clock ${sl5_slice_clock_obj} [get_ports sl5nl1arc_* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl5_slice_clock_per}] -clock ${sl5_slice_clock_obj} [get_ports sl5_ecc_dbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl5_slice_clock_per}] -clock ${sl5_slice_clock_obj} [get_ports sl5_ecc_sbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl5_slice_wdt_clock_per}] -clock ${sl5_slice_wdt_clock_obj} [get_ports sl5nl1arc_wdt_reset_wdt_clk_error -filter {@port_direction == out}]


#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------


if {"$npu_flatten_sdc" eq 1} {
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${sl5_l1hier}*ialb_cpu_top*"]
set_false_path -through [get_pins {*dbg_prot_sel} -hier -filter "@full_name=~*${sl5_l1hier}*ialb_cpu_top*"]
}



if {"$npu_flatten_sdc" eq 1} {
#------------------------------------------------------------------------------
# False Paths  - multi-through
#------------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Multicycle paths
# -----------------------------------------------------------------------------
# ARC HS PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl5_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl5_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl5_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl5_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1


# Conv 2 cycle checker for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl5_nslhier}*u_npu_conv*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl5_nslhier}*u_npu_conv*"] -hold 1
if {"$npu_lint_virt_clk" eq "0"} {
  # Do not merge redundant registers for timing in synthesis
  set_register_merging [get_cells * -hier -filter "@full_name=~*_nomerge_r*"]  false
}

# GTOA 2 cycle checker, the generated clock inside GTOA is 1/2 the frequency of the main clock
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl5_nslhier}*u_npu_gtoa*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl5_nslhier}*u_npu_gtoa*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl5_nslhier}*u_npu_gtoa*"] -start -setup 2 -comment reg2reg_mc2f2s
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl5_nslhier}*u_npu_gtoa*"] -start -hold 1
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl5_nslhier}*u_npu_gtoa*"] -end -setup 2 -comment reg2reg_mc2s2f
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl5_nslhier}*u_npu_gtoa*"] -end -hold 1
# GTOA 3 cycle path for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl5_nslhier}*u_npu_gtoa*"] -start -setup 3 -comment reg2reg_mc3f2s
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl5_nslhier}*u_npu_gtoa*"] -start -hold 2

}

#- npu_slice_top 5 }
#- npu_slice_top 6 {
# =============================================================================
# Constraints for the npu_slice_top module sl6_
# =============================================================================

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# -- NPU slice search path in the hierarchy
set sl6_nslhier "u_l1core6/"
set sl6_l1hier "${sl6_nslhier}*u_npu_l1_arc"

# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------

set sl6_slice_clock_name sl6_clk
set sl6_slice_virt_clock_name sl6_async_vclk
set sl6_slice_clock_freq 1000
if { [info exists ::env(NPU_FMAX)] } {
    set sl6_slice_clock_freq $::env(NPU_FMAX)
}
set sl6_slice_clock_per  [expr 1000.0 / $sl6_slice_clock_freq] ; # Period in ns
set sl6_slice_clock_port [get_ports $sl6_slice_clock_name]
set sl6_slice_clock_Teff [expr $sl6_slice_clock_per - $clk_unc_setup]
set sl6_slice_clock_obj  [get_clocks $sl6_slice_clock_name]
puts "Info: npu_slice 6 clock $sl6_slice_clock_name created @ $sl6_slice_clock_freq MHz"

set sl6_slice_wdt_clock_freq 50
if { [info exists ::env(WDT_NPU_FMAX)] } {
  set sl6_slice_wdt_clock_freq $::env(WDT_NPU_FMAX)
}
set sl6_slice_wdt_clock_name sl6_wdt_clk
set sl6_slice_wdt_clock_per  [expr 1000.0 / $sl6_slice_wdt_clock_freq] ; # Period in ns
set sl6_slice_wdt_clock_port [get_ports $sl6_slice_wdt_clock_name]
set sl6_slice_wdt_clock_obj [get_clocks $sl6_slice_wdt_clock_name]
puts "Info: npu_slice 6 wdt_clock $sl6_slice_wdt_clock_name created @ $sl6_slice_wdt_clock_freq MHz"

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
set  sl6_l1arc_hs_gclocks ""
proc sl6_l1arc_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable sl6_slice_clock_obj
    variable sl6_slice_clock_port
    variable sl6_l1hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable sl6_l1arc_hs_gclocks
    variable clk_gate0_Q
    # Slow search
    #   get_pins * -hier -filter "@full_name=~*${sl6_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*$clk_gate0_Q"
    # Faster search
    #   get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl6_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*"
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl6_l1hier}*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${sl6_slice_clock_obj} -source ${sl6_slice_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append sl6_l1arc_hs_gclocks " $name"
    puts "Info: npu_slice_top 6 L1 ARC HS generated clock '$name' from ICG $ckg_full_name with edges $ck_edges"
}

set sl6_l1pfx "sl6_nl1_"
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}ic_data_bank0_gclk"        "uic_data_bank0_clkgate"  {1 2 5}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}ic_data_bank1_gclk"        "uic_data_bank1_clkgate"  {1 2 5}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}ic_tag_w0_gclk"            "uic_tag_w0_clkgate"      {1 2 5}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}ic_tag_w1_gclk"            "uic_tag_w1_clkgate"      {1 2 5}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}ic_tag_w2_gclk"            "uic_tag_w2_clkgate"      {1 2 5}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}ic_tag_w3_gclk"            "uic_tag_w3_clkgate"      {1 2 5}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}bc_ram0_gclk"              "u_bc0_clkgate"           {1 2 5}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}bc_ram1_gclk"              "u_bc1_clkgate"           {1 2 5}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}pt_ram0_gclk"              "u_pt0_clkgate"           {1 2 5}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}pt_ram1_gclk"              "u_pt1_clkgate"           {1 2 5}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}dccm_bank0_lo_gclk"        "u_clkgate_dccm_0_lo"     {1 2 5}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}dccm_bank0_hi_gclk"        "u_clkgate_dccm_0_hi"     {1 2 5}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}dccm_bank1_lo_gclk"        "u_clkgate_dccm_1_lo"     {1 2 5}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}dccm_bank1_hi_gclk"        "u_clkgate_dccm_1_hi"     {1 2 5}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}data_even_lo_gclk"         "u_clkgate_data_even_lo"  {1 2 5}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}data_even_hi_gclk"         "u_clkgate_data_even_hi"  {1 2 5}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}data_odd_lo_gclk"          "u_clkgate_data_odd_lo"   {1 2 5}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}data_odd_hi_gclk"          "u_clkgate_data_odd_hi"   {1 2 5}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}ntlb_pd0_gclk"             "u_ntlb_pd0_clkgate"      {1 2 7}
sl6_l1arc_hs_generated_clock "${sl6_l1pfx}ntlb_pd1_gclk"             "u_ntlb_pd1_clkgate"      {1 2 5}

# GTOA core runs at half the frequency
create_generated_clock -name "sl6_gtoa_half_gclk" -edges {1 2 5} -add -master_clock ${sl6_slice_clock_obj} -source ${sl6_slice_clock_port} [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl6_nslhier}*u_npu_gtoa*u_l2_clkgate_half_inst*"]
set_dont_touch_network "sl6_gtoa_half_gclk"
set_clock_uncertainty -setup $clk_unc_setup "sl6_gtoa_half_gclk"
set_clock_uncertainty -hold  $clk_unc_hold  "sl6_gtoa_half_gclk"

group_path -name $sl6_slice_clock_name-to-$sl6_slice_clock_name -from $sl6_slice_clock_name -to $sl6_slice_clock_name
group_path -name sl6_gtoa_half_gclk-to-$sl6_slice_clock_name    -from sl6_gtoa_half_gclk    -to $sl6_slice_clock_name
group_path -name $sl6_slice_clock_name-to-sl6_gtoa_half_gclk    -from $sl6_slice_clock_name -to sl6_gtoa_half_gclk
group_path -name sl6_gtoa_half_gclk-to-sl6_gtoa_half_gclk       -from sl6_gtoa_half_gclk    -to sl6_gtoa_half_gclk

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name $sl6_slice_virt_clock_name -period 1.000
} else {
}

set sl6_slice_all_non_gen_clks      [get_clocks * -filter {@is_generated == false}]
set sl6_slice_all_non_gen_virt_clks $sl6_slice_all_non_gen_clks
if {"$npu_lint_virt_clk" ne "0"} {
  set sl6_slice_all_non_gen_virt_clks [remove_from_collection $sl6_slice_all_non_gen_clks [get_clocks $sl6_slice_virt_clock_name]]
}

set sl6_top_reset_name "sl6_rst_a"
set sl6_top_reset [get_ports ${sl6_top_reset_name} -filter {@port_direction == in}]

set_input_delay [expr 0.25 * ${sl6_slice_clock_per}] -clock ${sl6_slice_clock_obj} ${sl6_top_reset}
set_input_delay [expr 0.25 * ${sl6_slice_clock_per}] -clock ${sl6_slice_clock_obj} ${sl6_top_reset} -add
set_input_delay [expr 0.25 * ${sl6_slice_clock_per}] -clock ${sl6_slice_clock_obj} [get_ports sl6nl1arc_* -filter {@port_direction == in}]
set ALL_INPUTS_EXC_WDT_CLK  [remove_from_collection [get_ports sl6_* -filter {@port_direction == in}] [get_ports sl6_wdt_clk]]
set_input_delay [expr 0.25 * ${sl6_slice_clock_per}] -clock ${sl6_slice_clock_obj} [get_ports $ALL_INPUTS_EXC_WDT_CLK -filter {@port_direction == in}]
if {"$npu_lint_virt_clk" ne "0"} {
  foreach_in_collection clkname $sl6_slice_all_non_gen_virt_clks {
    remove_input_delay  -clock $clkname [get_ports ${sl6_top_reset_name} -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports sl6nl1arc_*_a -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl6_slice_virt_clock_name] period]] -clock [get_clocks $sl6_slice_virt_clock_name] [get_ports ${sl6_top_reset_name} -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl6_slice_virt_clock_name] period]] -clock [get_clocks $sl6_slice_virt_clock_name] [get_ports sl6nl1arc_*_a -filter {@port_direction == in}]
}


set_output_delay [expr 0.25 * ${sl6_slice_clock_per}] -clock ${sl6_slice_clock_obj} [get_ports sl6nl1arc_* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl6_slice_clock_per}] -clock ${sl6_slice_clock_obj} [get_ports sl6_ecc_dbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl6_slice_clock_per}] -clock ${sl6_slice_clock_obj} [get_ports sl6_ecc_sbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl6_slice_wdt_clock_per}] -clock ${sl6_slice_wdt_clock_obj} [get_ports sl6nl1arc_wdt_reset_wdt_clk_error -filter {@port_direction == out}]


#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------


if {"$npu_flatten_sdc" eq 1} {
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${sl6_l1hier}*ialb_cpu_top*"]
set_false_path -through [get_pins {*dbg_prot_sel} -hier -filter "@full_name=~*${sl6_l1hier}*ialb_cpu_top*"]
}



if {"$npu_flatten_sdc" eq 1} {
#------------------------------------------------------------------------------
# False Paths  - multi-through
#------------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Multicycle paths
# -----------------------------------------------------------------------------
# ARC HS PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl6_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl6_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl6_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl6_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1


# Conv 2 cycle checker for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl6_nslhier}*u_npu_conv*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl6_nslhier}*u_npu_conv*"] -hold 1
if {"$npu_lint_virt_clk" eq "0"} {
  # Do not merge redundant registers for timing in synthesis
  set_register_merging [get_cells * -hier -filter "@full_name=~*_nomerge_r*"]  false
}

# GTOA 2 cycle checker, the generated clock inside GTOA is 1/2 the frequency of the main clock
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl6_nslhier}*u_npu_gtoa*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl6_nslhier}*u_npu_gtoa*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl6_nslhier}*u_npu_gtoa*"] -start -setup 2 -comment reg2reg_mc2f2s
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl6_nslhier}*u_npu_gtoa*"] -start -hold 1
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl6_nslhier}*u_npu_gtoa*"] -end -setup 2 -comment reg2reg_mc2s2f
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl6_nslhier}*u_npu_gtoa*"] -end -hold 1
# GTOA 3 cycle path for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl6_nslhier}*u_npu_gtoa*"] -start -setup 3 -comment reg2reg_mc3f2s
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl6_nslhier}*u_npu_gtoa*"] -start -hold 2

}

#- npu_slice_top 6 }
#- npu_slice_top 7 {
# =============================================================================
# Constraints for the npu_slice_top module sl7_
# =============================================================================

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# -- NPU slice search path in the hierarchy
set sl7_nslhier "u_l1core7/"
set sl7_l1hier "${sl7_nslhier}*u_npu_l1_arc"

# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------

set sl7_slice_clock_name sl7_clk
set sl7_slice_virt_clock_name sl7_async_vclk
set sl7_slice_clock_freq 1000
if { [info exists ::env(NPU_FMAX)] } {
    set sl7_slice_clock_freq $::env(NPU_FMAX)
}
set sl7_slice_clock_per  [expr 1000.0 / $sl7_slice_clock_freq] ; # Period in ns
set sl7_slice_clock_port [get_ports $sl7_slice_clock_name]
set sl7_slice_clock_Teff [expr $sl7_slice_clock_per - $clk_unc_setup]
set sl7_slice_clock_obj  [get_clocks $sl7_slice_clock_name]
puts "Info: npu_slice 7 clock $sl7_slice_clock_name created @ $sl7_slice_clock_freq MHz"

set sl7_slice_wdt_clock_freq 50
if { [info exists ::env(WDT_NPU_FMAX)] } {
  set sl7_slice_wdt_clock_freq $::env(WDT_NPU_FMAX)
}
set sl7_slice_wdt_clock_name sl7_wdt_clk
set sl7_slice_wdt_clock_per  [expr 1000.0 / $sl7_slice_wdt_clock_freq] ; # Period in ns
set sl7_slice_wdt_clock_port [get_ports $sl7_slice_wdt_clock_name]
set sl7_slice_wdt_clock_obj [get_clocks $sl7_slice_wdt_clock_name]
puts "Info: npu_slice 7 wdt_clock $sl7_slice_wdt_clock_name created @ $sl7_slice_wdt_clock_freq MHz"

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
set  sl7_l1arc_hs_gclocks ""
proc sl7_l1arc_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable sl7_slice_clock_obj
    variable sl7_slice_clock_port
    variable sl7_l1hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable sl7_l1arc_hs_gclocks
    variable clk_gate0_Q
    # Slow search
    #   get_pins * -hier -filter "@full_name=~*${sl7_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*$clk_gate0_Q"
    # Faster search
    #   get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl7_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*"
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl7_l1hier}*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${sl7_slice_clock_obj} -source ${sl7_slice_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append sl7_l1arc_hs_gclocks " $name"
    puts "Info: npu_slice_top 7 L1 ARC HS generated clock '$name' from ICG $ckg_full_name with edges $ck_edges"
}

set sl7_l1pfx "sl7_nl1_"
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}ic_data_bank0_gclk"        "uic_data_bank0_clkgate"  {1 2 5}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}ic_data_bank1_gclk"        "uic_data_bank1_clkgate"  {1 2 5}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}ic_tag_w0_gclk"            "uic_tag_w0_clkgate"      {1 2 5}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}ic_tag_w1_gclk"            "uic_tag_w1_clkgate"      {1 2 5}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}ic_tag_w2_gclk"            "uic_tag_w2_clkgate"      {1 2 5}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}ic_tag_w3_gclk"            "uic_tag_w3_clkgate"      {1 2 5}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}bc_ram0_gclk"              "u_bc0_clkgate"           {1 2 5}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}bc_ram1_gclk"              "u_bc1_clkgate"           {1 2 5}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}pt_ram0_gclk"              "u_pt0_clkgate"           {1 2 5}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}pt_ram1_gclk"              "u_pt1_clkgate"           {1 2 5}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}dccm_bank0_lo_gclk"        "u_clkgate_dccm_0_lo"     {1 2 5}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}dccm_bank0_hi_gclk"        "u_clkgate_dccm_0_hi"     {1 2 5}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}dccm_bank1_lo_gclk"        "u_clkgate_dccm_1_lo"     {1 2 5}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}dccm_bank1_hi_gclk"        "u_clkgate_dccm_1_hi"     {1 2 5}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}data_even_lo_gclk"         "u_clkgate_data_even_lo"  {1 2 5}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}data_even_hi_gclk"         "u_clkgate_data_even_hi"  {1 2 5}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}data_odd_lo_gclk"          "u_clkgate_data_odd_lo"   {1 2 5}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}data_odd_hi_gclk"          "u_clkgate_data_odd_hi"   {1 2 5}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}ntlb_pd0_gclk"             "u_ntlb_pd0_clkgate"      {1 2 7}
sl7_l1arc_hs_generated_clock "${sl7_l1pfx}ntlb_pd1_gclk"             "u_ntlb_pd1_clkgate"      {1 2 5}

# GTOA core runs at half the frequency
create_generated_clock -name "sl7_gtoa_half_gclk" -edges {1 2 5} -add -master_clock ${sl7_slice_clock_obj} -source ${sl7_slice_clock_port} [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl7_nslhier}*u_npu_gtoa*u_l2_clkgate_half_inst*"]
set_dont_touch_network "sl7_gtoa_half_gclk"
set_clock_uncertainty -setup $clk_unc_setup "sl7_gtoa_half_gclk"
set_clock_uncertainty -hold  $clk_unc_hold  "sl7_gtoa_half_gclk"

group_path -name $sl7_slice_clock_name-to-$sl7_slice_clock_name -from $sl7_slice_clock_name -to $sl7_slice_clock_name
group_path -name sl7_gtoa_half_gclk-to-$sl7_slice_clock_name    -from sl7_gtoa_half_gclk    -to $sl7_slice_clock_name
group_path -name $sl7_slice_clock_name-to-sl7_gtoa_half_gclk    -from $sl7_slice_clock_name -to sl7_gtoa_half_gclk
group_path -name sl7_gtoa_half_gclk-to-sl7_gtoa_half_gclk       -from sl7_gtoa_half_gclk    -to sl7_gtoa_half_gclk

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name $sl7_slice_virt_clock_name -period 1.000
} else {
}

set sl7_slice_all_non_gen_clks      [get_clocks * -filter {@is_generated == false}]
set sl7_slice_all_non_gen_virt_clks $sl7_slice_all_non_gen_clks
if {"$npu_lint_virt_clk" ne "0"} {
  set sl7_slice_all_non_gen_virt_clks [remove_from_collection $sl7_slice_all_non_gen_clks [get_clocks $sl7_slice_virt_clock_name]]
}

set sl7_top_reset_name "sl7_rst_a"
set sl7_top_reset [get_ports ${sl7_top_reset_name} -filter {@port_direction == in}]

set_input_delay [expr 0.25 * ${sl7_slice_clock_per}] -clock ${sl7_slice_clock_obj} ${sl7_top_reset}
set_input_delay [expr 0.25 * ${sl7_slice_clock_per}] -clock ${sl7_slice_clock_obj} ${sl7_top_reset} -add
set_input_delay [expr 0.25 * ${sl7_slice_clock_per}] -clock ${sl7_slice_clock_obj} [get_ports sl7nl1arc_* -filter {@port_direction == in}]
set ALL_INPUTS_EXC_WDT_CLK  [remove_from_collection [get_ports sl7_* -filter {@port_direction == in}] [get_ports sl7_wdt_clk]]
set_input_delay [expr 0.25 * ${sl7_slice_clock_per}] -clock ${sl7_slice_clock_obj} [get_ports $ALL_INPUTS_EXC_WDT_CLK -filter {@port_direction == in}]
if {"$npu_lint_virt_clk" ne "0"} {
  foreach_in_collection clkname $sl7_slice_all_non_gen_virt_clks {
    remove_input_delay  -clock $clkname [get_ports ${sl7_top_reset_name} -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports sl7nl1arc_*_a -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl7_slice_virt_clock_name] period]] -clock [get_clocks $sl7_slice_virt_clock_name] [get_ports ${sl7_top_reset_name} -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl7_slice_virt_clock_name] period]] -clock [get_clocks $sl7_slice_virt_clock_name] [get_ports sl7nl1arc_*_a -filter {@port_direction == in}]
}


set_output_delay [expr 0.25 * ${sl7_slice_clock_per}] -clock ${sl7_slice_clock_obj} [get_ports sl7nl1arc_* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl7_slice_clock_per}] -clock ${sl7_slice_clock_obj} [get_ports sl7_ecc_dbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl7_slice_clock_per}] -clock ${sl7_slice_clock_obj} [get_ports sl7_ecc_sbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl7_slice_wdt_clock_per}] -clock ${sl7_slice_wdt_clock_obj} [get_ports sl7nl1arc_wdt_reset_wdt_clk_error -filter {@port_direction == out}]


#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------


if {"$npu_flatten_sdc" eq 1} {
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${sl7_l1hier}*ialb_cpu_top*"]
set_false_path -through [get_pins {*dbg_prot_sel} -hier -filter "@full_name=~*${sl7_l1hier}*ialb_cpu_top*"]
}



if {"$npu_flatten_sdc" eq 1} {
#------------------------------------------------------------------------------
# False Paths  - multi-through
#------------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Multicycle paths
# -----------------------------------------------------------------------------
# ARC HS PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl7_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl7_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl7_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl7_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1


# Conv 2 cycle checker for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl7_nslhier}*u_npu_conv*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl7_nslhier}*u_npu_conv*"] -hold 1
if {"$npu_lint_virt_clk" eq "0"} {
  # Do not merge redundant registers for timing in synthesis
  set_register_merging [get_cells * -hier -filter "@full_name=~*_nomerge_r*"]  false
}

# GTOA 2 cycle checker, the generated clock inside GTOA is 1/2 the frequency of the main clock
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl7_nslhier}*u_npu_gtoa*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl7_nslhier}*u_npu_gtoa*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl7_nslhier}*u_npu_gtoa*"] -start -setup 2 -comment reg2reg_mc2f2s
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl7_nslhier}*u_npu_gtoa*"] -start -hold 1
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl7_nslhier}*u_npu_gtoa*"] -end -setup 2 -comment reg2reg_mc2s2f
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl7_nslhier}*u_npu_gtoa*"] -end -hold 1
# GTOA 3 cycle path for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl7_nslhier}*u_npu_gtoa*"] -start -setup 3 -comment reg2reg_mc3f2s
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl7_nslhier}*u_npu_gtoa*"] -start -hold 2

}

#- npu_slice_top 7 }
#- npu_slice_top 8 {
# =============================================================================
# Constraints for the npu_slice_top module sl8_
# =============================================================================

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# -- NPU slice search path in the hierarchy
set sl8_nslhier "u_l1core8/"
set sl8_l1hier "${sl8_nslhier}*u_npu_l1_arc"

# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------

set sl8_slice_clock_name sl8_clk
set sl8_slice_virt_clock_name sl8_async_vclk
set sl8_slice_clock_freq 1000
if { [info exists ::env(NPU_FMAX)] } {
    set sl8_slice_clock_freq $::env(NPU_FMAX)
}
set sl8_slice_clock_per  [expr 1000.0 / $sl8_slice_clock_freq] ; # Period in ns
set sl8_slice_clock_port [get_ports $sl8_slice_clock_name]
set sl8_slice_clock_Teff [expr $sl8_slice_clock_per - $clk_unc_setup]
set sl8_slice_clock_obj  [get_clocks $sl8_slice_clock_name]
puts "Info: npu_slice 8 clock $sl8_slice_clock_name created @ $sl8_slice_clock_freq MHz"

set sl8_slice_wdt_clock_freq 50
if { [info exists ::env(WDT_NPU_FMAX)] } {
  set sl8_slice_wdt_clock_freq $::env(WDT_NPU_FMAX)
}
set sl8_slice_wdt_clock_name sl8_wdt_clk
set sl8_slice_wdt_clock_per  [expr 1000.0 / $sl8_slice_wdt_clock_freq] ; # Period in ns
set sl8_slice_wdt_clock_port [get_ports $sl8_slice_wdt_clock_name]
set sl8_slice_wdt_clock_obj [get_clocks $sl8_slice_wdt_clock_name]
puts "Info: npu_slice 8 wdt_clock $sl8_slice_wdt_clock_name created @ $sl8_slice_wdt_clock_freq MHz"

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
set  sl8_l1arc_hs_gclocks ""
proc sl8_l1arc_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable sl8_slice_clock_obj
    variable sl8_slice_clock_port
    variable sl8_l1hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable sl8_l1arc_hs_gclocks
    variable clk_gate0_Q
    # Slow search
    #   get_pins * -hier -filter "@full_name=~*${sl8_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*$clk_gate0_Q"
    # Faster search
    #   get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl8_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*"
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl8_l1hier}*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${sl8_slice_clock_obj} -source ${sl8_slice_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append sl8_l1arc_hs_gclocks " $name"
    puts "Info: npu_slice_top 8 L1 ARC HS generated clock '$name' from ICG $ckg_full_name with edges $ck_edges"
}

set sl8_l1pfx "sl8_nl1_"
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}ic_data_bank0_gclk"        "uic_data_bank0_clkgate"  {1 2 5}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}ic_data_bank1_gclk"        "uic_data_bank1_clkgate"  {1 2 5}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}ic_tag_w0_gclk"            "uic_tag_w0_clkgate"      {1 2 5}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}ic_tag_w1_gclk"            "uic_tag_w1_clkgate"      {1 2 5}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}ic_tag_w2_gclk"            "uic_tag_w2_clkgate"      {1 2 5}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}ic_tag_w3_gclk"            "uic_tag_w3_clkgate"      {1 2 5}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}bc_ram0_gclk"              "u_bc0_clkgate"           {1 2 5}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}bc_ram1_gclk"              "u_bc1_clkgate"           {1 2 5}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}pt_ram0_gclk"              "u_pt0_clkgate"           {1 2 5}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}pt_ram1_gclk"              "u_pt1_clkgate"           {1 2 5}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}dccm_bank0_lo_gclk"        "u_clkgate_dccm_0_lo"     {1 2 5}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}dccm_bank0_hi_gclk"        "u_clkgate_dccm_0_hi"     {1 2 5}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}dccm_bank1_lo_gclk"        "u_clkgate_dccm_1_lo"     {1 2 5}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}dccm_bank1_hi_gclk"        "u_clkgate_dccm_1_hi"     {1 2 5}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}data_even_lo_gclk"         "u_clkgate_data_even_lo"  {1 2 5}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}data_even_hi_gclk"         "u_clkgate_data_even_hi"  {1 2 5}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}data_odd_lo_gclk"          "u_clkgate_data_odd_lo"   {1 2 5}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}data_odd_hi_gclk"          "u_clkgate_data_odd_hi"   {1 2 5}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}ntlb_pd0_gclk"             "u_ntlb_pd0_clkgate"      {1 2 7}
sl8_l1arc_hs_generated_clock "${sl8_l1pfx}ntlb_pd1_gclk"             "u_ntlb_pd1_clkgate"      {1 2 5}

# GTOA core runs at half the frequency
create_generated_clock -name "sl8_gtoa_half_gclk" -edges {1 2 5} -add -master_clock ${sl8_slice_clock_obj} -source ${sl8_slice_clock_port} [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl8_nslhier}*u_npu_gtoa*u_l2_clkgate_half_inst*"]
set_dont_touch_network "sl8_gtoa_half_gclk"
set_clock_uncertainty -setup $clk_unc_setup "sl8_gtoa_half_gclk"
set_clock_uncertainty -hold  $clk_unc_hold  "sl8_gtoa_half_gclk"

group_path -name $sl8_slice_clock_name-to-$sl8_slice_clock_name -from $sl8_slice_clock_name -to $sl8_slice_clock_name
group_path -name sl8_gtoa_half_gclk-to-$sl8_slice_clock_name    -from sl8_gtoa_half_gclk    -to $sl8_slice_clock_name
group_path -name $sl8_slice_clock_name-to-sl8_gtoa_half_gclk    -from $sl8_slice_clock_name -to sl8_gtoa_half_gclk
group_path -name sl8_gtoa_half_gclk-to-sl8_gtoa_half_gclk       -from sl8_gtoa_half_gclk    -to sl8_gtoa_half_gclk

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name $sl8_slice_virt_clock_name -period 1.000
} else {
}

set sl8_slice_all_non_gen_clks      [get_clocks * -filter {@is_generated == false}]
set sl8_slice_all_non_gen_virt_clks $sl8_slice_all_non_gen_clks
if {"$npu_lint_virt_clk" ne "0"} {
  set sl8_slice_all_non_gen_virt_clks [remove_from_collection $sl8_slice_all_non_gen_clks [get_clocks $sl8_slice_virt_clock_name]]
}

set sl8_top_reset_name "sl8_rst_a"
set sl8_top_reset [get_ports ${sl8_top_reset_name} -filter {@port_direction == in}]

set_input_delay [expr 0.25 * ${sl8_slice_clock_per}] -clock ${sl8_slice_clock_obj} ${sl8_top_reset}
set_input_delay [expr 0.25 * ${sl8_slice_clock_per}] -clock ${sl8_slice_clock_obj} ${sl8_top_reset} -add
set_input_delay [expr 0.25 * ${sl8_slice_clock_per}] -clock ${sl8_slice_clock_obj} [get_ports sl8nl1arc_* -filter {@port_direction == in}]
set ALL_INPUTS_EXC_WDT_CLK  [remove_from_collection [get_ports sl8_* -filter {@port_direction == in}] [get_ports sl8_wdt_clk]]
set_input_delay [expr 0.25 * ${sl8_slice_clock_per}] -clock ${sl8_slice_clock_obj} [get_ports $ALL_INPUTS_EXC_WDT_CLK -filter {@port_direction == in}]
if {"$npu_lint_virt_clk" ne "0"} {
  foreach_in_collection clkname $sl8_slice_all_non_gen_virt_clks {
    remove_input_delay  -clock $clkname [get_ports ${sl8_top_reset_name} -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports sl8nl1arc_*_a -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl8_slice_virt_clock_name] period]] -clock [get_clocks $sl8_slice_virt_clock_name] [get_ports ${sl8_top_reset_name} -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl8_slice_virt_clock_name] period]] -clock [get_clocks $sl8_slice_virt_clock_name] [get_ports sl8nl1arc_*_a -filter {@port_direction == in}]
}


set_output_delay [expr 0.25 * ${sl8_slice_clock_per}] -clock ${sl8_slice_clock_obj} [get_ports sl8nl1arc_* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl8_slice_clock_per}] -clock ${sl8_slice_clock_obj} [get_ports sl8_ecc_dbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl8_slice_clock_per}] -clock ${sl8_slice_clock_obj} [get_ports sl8_ecc_sbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl8_slice_wdt_clock_per}] -clock ${sl8_slice_wdt_clock_obj} [get_ports sl8nl1arc_wdt_reset_wdt_clk_error -filter {@port_direction == out}]


#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------


if {"$npu_flatten_sdc" eq 1} {
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${sl8_l1hier}*ialb_cpu_top*"]
set_false_path -through [get_pins {*dbg_prot_sel} -hier -filter "@full_name=~*${sl8_l1hier}*ialb_cpu_top*"]
}



if {"$npu_flatten_sdc" eq 1} {
#------------------------------------------------------------------------------
# False Paths  - multi-through
#------------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Multicycle paths
# -----------------------------------------------------------------------------
# ARC HS PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl8_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl8_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl8_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl8_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1


# Conv 2 cycle checker for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl8_nslhier}*u_npu_conv*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl8_nslhier}*u_npu_conv*"] -hold 1
if {"$npu_lint_virt_clk" eq "0"} {
  # Do not merge redundant registers for timing in synthesis
  set_register_merging [get_cells * -hier -filter "@full_name=~*_nomerge_r*"]  false
}

# GTOA 2 cycle checker, the generated clock inside GTOA is 1/2 the frequency of the main clock
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl8_nslhier}*u_npu_gtoa*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl8_nslhier}*u_npu_gtoa*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl8_nslhier}*u_npu_gtoa*"] -start -setup 2 -comment reg2reg_mc2f2s
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl8_nslhier}*u_npu_gtoa*"] -start -hold 1
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl8_nslhier}*u_npu_gtoa*"] -end -setup 2 -comment reg2reg_mc2s2f
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl8_nslhier}*u_npu_gtoa*"] -end -hold 1
# GTOA 3 cycle path for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl8_nslhier}*u_npu_gtoa*"] -start -setup 3 -comment reg2reg_mc3f2s
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl8_nslhier}*u_npu_gtoa*"] -start -hold 2

}

#- npu_slice_top 8 }
#- npu_slice_top 9 {
# =============================================================================
# Constraints for the npu_slice_top module sl9_
# =============================================================================

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# -- NPU slice search path in the hierarchy
set sl9_nslhier "u_l1core9/"
set sl9_l1hier "${sl9_nslhier}*u_npu_l1_arc"

# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------

set sl9_slice_clock_name sl9_clk
set sl9_slice_virt_clock_name sl9_async_vclk
set sl9_slice_clock_freq 1000
if { [info exists ::env(NPU_FMAX)] } {
    set sl9_slice_clock_freq $::env(NPU_FMAX)
}
set sl9_slice_clock_per  [expr 1000.0 / $sl9_slice_clock_freq] ; # Period in ns
set sl9_slice_clock_port [get_ports $sl9_slice_clock_name]
set sl9_slice_clock_Teff [expr $sl9_slice_clock_per - $clk_unc_setup]
set sl9_slice_clock_obj  [get_clocks $sl9_slice_clock_name]
puts "Info: npu_slice 9 clock $sl9_slice_clock_name created @ $sl9_slice_clock_freq MHz"

set sl9_slice_wdt_clock_freq 50
if { [info exists ::env(WDT_NPU_FMAX)] } {
  set sl9_slice_wdt_clock_freq $::env(WDT_NPU_FMAX)
}
set sl9_slice_wdt_clock_name sl9_wdt_clk
set sl9_slice_wdt_clock_per  [expr 1000.0 / $sl9_slice_wdt_clock_freq] ; # Period in ns
set sl9_slice_wdt_clock_port [get_ports $sl9_slice_wdt_clock_name]
set sl9_slice_wdt_clock_obj [get_clocks $sl9_slice_wdt_clock_name]
puts "Info: npu_slice 9 wdt_clock $sl9_slice_wdt_clock_name created @ $sl9_slice_wdt_clock_freq MHz"

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
set  sl9_l1arc_hs_gclocks ""
proc sl9_l1arc_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable sl9_slice_clock_obj
    variable sl9_slice_clock_port
    variable sl9_l1hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable sl9_l1arc_hs_gclocks
    variable clk_gate0_Q
    # Slow search
    #   get_pins * -hier -filter "@full_name=~*${sl9_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*$clk_gate0_Q"
    # Faster search
    #   get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl9_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*"
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl9_l1hier}*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${sl9_slice_clock_obj} -source ${sl9_slice_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append sl9_l1arc_hs_gclocks " $name"
    puts "Info: npu_slice_top 9 L1 ARC HS generated clock '$name' from ICG $ckg_full_name with edges $ck_edges"
}

set sl9_l1pfx "sl9_nl1_"
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}ic_data_bank0_gclk"        "uic_data_bank0_clkgate"  {1 2 5}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}ic_data_bank1_gclk"        "uic_data_bank1_clkgate"  {1 2 5}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}ic_tag_w0_gclk"            "uic_tag_w0_clkgate"      {1 2 5}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}ic_tag_w1_gclk"            "uic_tag_w1_clkgate"      {1 2 5}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}ic_tag_w2_gclk"            "uic_tag_w2_clkgate"      {1 2 5}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}ic_tag_w3_gclk"            "uic_tag_w3_clkgate"      {1 2 5}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}bc_ram0_gclk"              "u_bc0_clkgate"           {1 2 5}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}bc_ram1_gclk"              "u_bc1_clkgate"           {1 2 5}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}pt_ram0_gclk"              "u_pt0_clkgate"           {1 2 5}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}pt_ram1_gclk"              "u_pt1_clkgate"           {1 2 5}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}dccm_bank0_lo_gclk"        "u_clkgate_dccm_0_lo"     {1 2 5}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}dccm_bank0_hi_gclk"        "u_clkgate_dccm_0_hi"     {1 2 5}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}dccm_bank1_lo_gclk"        "u_clkgate_dccm_1_lo"     {1 2 5}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}dccm_bank1_hi_gclk"        "u_clkgate_dccm_1_hi"     {1 2 5}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}data_even_lo_gclk"         "u_clkgate_data_even_lo"  {1 2 5}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}data_even_hi_gclk"         "u_clkgate_data_even_hi"  {1 2 5}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}data_odd_lo_gclk"          "u_clkgate_data_odd_lo"   {1 2 5}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}data_odd_hi_gclk"          "u_clkgate_data_odd_hi"   {1 2 5}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}ntlb_pd0_gclk"             "u_ntlb_pd0_clkgate"      {1 2 7}
sl9_l1arc_hs_generated_clock "${sl9_l1pfx}ntlb_pd1_gclk"             "u_ntlb_pd1_clkgate"      {1 2 5}

# GTOA core runs at half the frequency
create_generated_clock -name "sl9_gtoa_half_gclk" -edges {1 2 5} -add -master_clock ${sl9_slice_clock_obj} -source ${sl9_slice_clock_port} [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl9_nslhier}*u_npu_gtoa*u_l2_clkgate_half_inst*"]
set_dont_touch_network "sl9_gtoa_half_gclk"
set_clock_uncertainty -setup $clk_unc_setup "sl9_gtoa_half_gclk"
set_clock_uncertainty -hold  $clk_unc_hold  "sl9_gtoa_half_gclk"

group_path -name $sl9_slice_clock_name-to-$sl9_slice_clock_name -from $sl9_slice_clock_name -to $sl9_slice_clock_name
group_path -name sl9_gtoa_half_gclk-to-$sl9_slice_clock_name    -from sl9_gtoa_half_gclk    -to $sl9_slice_clock_name
group_path -name $sl9_slice_clock_name-to-sl9_gtoa_half_gclk    -from $sl9_slice_clock_name -to sl9_gtoa_half_gclk
group_path -name sl9_gtoa_half_gclk-to-sl9_gtoa_half_gclk       -from sl9_gtoa_half_gclk    -to sl9_gtoa_half_gclk

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name $sl9_slice_virt_clock_name -period 1.000
} else {
}

set sl9_slice_all_non_gen_clks      [get_clocks * -filter {@is_generated == false}]
set sl9_slice_all_non_gen_virt_clks $sl9_slice_all_non_gen_clks
if {"$npu_lint_virt_clk" ne "0"} {
  set sl9_slice_all_non_gen_virt_clks [remove_from_collection $sl9_slice_all_non_gen_clks [get_clocks $sl9_slice_virt_clock_name]]
}

set sl9_top_reset_name "sl9_rst_a"
set sl9_top_reset [get_ports ${sl9_top_reset_name} -filter {@port_direction == in}]

set_input_delay [expr 0.25 * ${sl9_slice_clock_per}] -clock ${sl9_slice_clock_obj} ${sl9_top_reset}
set_input_delay [expr 0.25 * ${sl9_slice_clock_per}] -clock ${sl9_slice_clock_obj} ${sl9_top_reset} -add
set_input_delay [expr 0.25 * ${sl9_slice_clock_per}] -clock ${sl9_slice_clock_obj} [get_ports sl9nl1arc_* -filter {@port_direction == in}]
set ALL_INPUTS_EXC_WDT_CLK  [remove_from_collection [get_ports sl9_* -filter {@port_direction == in}] [get_ports sl9_wdt_clk]]
set_input_delay [expr 0.25 * ${sl9_slice_clock_per}] -clock ${sl9_slice_clock_obj} [get_ports $ALL_INPUTS_EXC_WDT_CLK -filter {@port_direction == in}]
if {"$npu_lint_virt_clk" ne "0"} {
  foreach_in_collection clkname $sl9_slice_all_non_gen_virt_clks {
    remove_input_delay  -clock $clkname [get_ports ${sl9_top_reset_name} -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports sl9nl1arc_*_a -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl9_slice_virt_clock_name] period]] -clock [get_clocks $sl9_slice_virt_clock_name] [get_ports ${sl9_top_reset_name} -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl9_slice_virt_clock_name] period]] -clock [get_clocks $sl9_slice_virt_clock_name] [get_ports sl9nl1arc_*_a -filter {@port_direction == in}]
}


set_output_delay [expr 0.25 * ${sl9_slice_clock_per}] -clock ${sl9_slice_clock_obj} [get_ports sl9nl1arc_* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl9_slice_clock_per}] -clock ${sl9_slice_clock_obj} [get_ports sl9_ecc_dbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl9_slice_clock_per}] -clock ${sl9_slice_clock_obj} [get_ports sl9_ecc_sbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl9_slice_wdt_clock_per}] -clock ${sl9_slice_wdt_clock_obj} [get_ports sl9nl1arc_wdt_reset_wdt_clk_error -filter {@port_direction == out}]


#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------


if {"$npu_flatten_sdc" eq 1} {
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${sl9_l1hier}*ialb_cpu_top*"]
set_false_path -through [get_pins {*dbg_prot_sel} -hier -filter "@full_name=~*${sl9_l1hier}*ialb_cpu_top*"]
}



if {"$npu_flatten_sdc" eq 1} {
#------------------------------------------------------------------------------
# False Paths  - multi-through
#------------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Multicycle paths
# -----------------------------------------------------------------------------
# ARC HS PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl9_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl9_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl9_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl9_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1


# Conv 2 cycle checker for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl9_nslhier}*u_npu_conv*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl9_nslhier}*u_npu_conv*"] -hold 1
if {"$npu_lint_virt_clk" eq "0"} {
  # Do not merge redundant registers for timing in synthesis
  set_register_merging [get_cells * -hier -filter "@full_name=~*_nomerge_r*"]  false
}

# GTOA 2 cycle checker, the generated clock inside GTOA is 1/2 the frequency of the main clock
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl9_nslhier}*u_npu_gtoa*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl9_nslhier}*u_npu_gtoa*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl9_nslhier}*u_npu_gtoa*"] -start -setup 2 -comment reg2reg_mc2f2s
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl9_nslhier}*u_npu_gtoa*"] -start -hold 1
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl9_nslhier}*u_npu_gtoa*"] -end -setup 2 -comment reg2reg_mc2s2f
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl9_nslhier}*u_npu_gtoa*"] -end -hold 1
# GTOA 3 cycle path for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl9_nslhier}*u_npu_gtoa*"] -start -setup 3 -comment reg2reg_mc3f2s
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl9_nslhier}*u_npu_gtoa*"] -start -hold 2

}

#- npu_slice_top 9 }
#- npu_slice_top 10 {
# =============================================================================
# Constraints for the npu_slice_top module sl10_
# =============================================================================

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# -- NPU slice search path in the hierarchy
set sl10_nslhier "u_l1core10/"
set sl10_l1hier "${sl10_nslhier}*u_npu_l1_arc"

# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------

set sl10_slice_clock_name sl10_clk
set sl10_slice_virt_clock_name sl10_async_vclk
set sl10_slice_clock_freq 1000
if { [info exists ::env(NPU_FMAX)] } {
    set sl10_slice_clock_freq $::env(NPU_FMAX)
}
set sl10_slice_clock_per  [expr 1000.0 / $sl10_slice_clock_freq] ; # Period in ns
set sl10_slice_clock_port [get_ports $sl10_slice_clock_name]
set sl10_slice_clock_Teff [expr $sl10_slice_clock_per - $clk_unc_setup]
set sl10_slice_clock_obj  [get_clocks $sl10_slice_clock_name]
puts "Info: npu_slice 10 clock $sl10_slice_clock_name created @ $sl10_slice_clock_freq MHz"

set sl10_slice_wdt_clock_freq 50
if { [info exists ::env(WDT_NPU_FMAX)] } {
  set sl10_slice_wdt_clock_freq $::env(WDT_NPU_FMAX)
}
set sl10_slice_wdt_clock_name sl10_wdt_clk
set sl10_slice_wdt_clock_per  [expr 1000.0 / $sl10_slice_wdt_clock_freq] ; # Period in ns
set sl10_slice_wdt_clock_port [get_ports $sl10_slice_wdt_clock_name]
set sl10_slice_wdt_clock_obj [get_clocks $sl10_slice_wdt_clock_name]
puts "Info: npu_slice 10 wdt_clock $sl10_slice_wdt_clock_name created @ $sl10_slice_wdt_clock_freq MHz"

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
set  sl10_l1arc_hs_gclocks ""
proc sl10_l1arc_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable sl10_slice_clock_obj
    variable sl10_slice_clock_port
    variable sl10_l1hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable sl10_l1arc_hs_gclocks
    variable clk_gate0_Q
    # Slow search
    #   get_pins * -hier -filter "@full_name=~*${sl10_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*$clk_gate0_Q"
    # Faster search
    #   get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl10_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*"
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl10_l1hier}*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${sl10_slice_clock_obj} -source ${sl10_slice_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append sl10_l1arc_hs_gclocks " $name"
    puts "Info: npu_slice_top 10 L1 ARC HS generated clock '$name' from ICG $ckg_full_name with edges $ck_edges"
}

set sl10_l1pfx "sl10_nl1_"
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}ic_data_bank0_gclk"        "uic_data_bank0_clkgate"  {1 2 5}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}ic_data_bank1_gclk"        "uic_data_bank1_clkgate"  {1 2 5}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}ic_tag_w0_gclk"            "uic_tag_w0_clkgate"      {1 2 5}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}ic_tag_w1_gclk"            "uic_tag_w1_clkgate"      {1 2 5}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}ic_tag_w2_gclk"            "uic_tag_w2_clkgate"      {1 2 5}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}ic_tag_w3_gclk"            "uic_tag_w3_clkgate"      {1 2 5}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}bc_ram0_gclk"              "u_bc0_clkgate"           {1 2 5}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}bc_ram1_gclk"              "u_bc1_clkgate"           {1 2 5}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}pt_ram0_gclk"              "u_pt0_clkgate"           {1 2 5}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}pt_ram1_gclk"              "u_pt1_clkgate"           {1 2 5}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}dccm_bank0_lo_gclk"        "u_clkgate_dccm_0_lo"     {1 2 5}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}dccm_bank0_hi_gclk"        "u_clkgate_dccm_0_hi"     {1 2 5}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}dccm_bank1_lo_gclk"        "u_clkgate_dccm_1_lo"     {1 2 5}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}dccm_bank1_hi_gclk"        "u_clkgate_dccm_1_hi"     {1 2 5}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}data_even_lo_gclk"         "u_clkgate_data_even_lo"  {1 2 5}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}data_even_hi_gclk"         "u_clkgate_data_even_hi"  {1 2 5}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}data_odd_lo_gclk"          "u_clkgate_data_odd_lo"   {1 2 5}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}data_odd_hi_gclk"          "u_clkgate_data_odd_hi"   {1 2 5}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}ntlb_pd0_gclk"             "u_ntlb_pd0_clkgate"      {1 2 7}
sl10_l1arc_hs_generated_clock "${sl10_l1pfx}ntlb_pd1_gclk"             "u_ntlb_pd1_clkgate"      {1 2 5}

# GTOA core runs at half the frequency
create_generated_clock -name "sl10_gtoa_half_gclk" -edges {1 2 5} -add -master_clock ${sl10_slice_clock_obj} -source ${sl10_slice_clock_port} [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl10_nslhier}*u_npu_gtoa*u_l2_clkgate_half_inst*"]
set_dont_touch_network "sl10_gtoa_half_gclk"
set_clock_uncertainty -setup $clk_unc_setup "sl10_gtoa_half_gclk"
set_clock_uncertainty -hold  $clk_unc_hold  "sl10_gtoa_half_gclk"

group_path -name $sl10_slice_clock_name-to-$sl10_slice_clock_name -from $sl10_slice_clock_name -to $sl10_slice_clock_name
group_path -name sl10_gtoa_half_gclk-to-$sl10_slice_clock_name    -from sl10_gtoa_half_gclk    -to $sl10_slice_clock_name
group_path -name $sl10_slice_clock_name-to-sl10_gtoa_half_gclk    -from $sl10_slice_clock_name -to sl10_gtoa_half_gclk
group_path -name sl10_gtoa_half_gclk-to-sl10_gtoa_half_gclk       -from sl10_gtoa_half_gclk    -to sl10_gtoa_half_gclk

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name $sl10_slice_virt_clock_name -period 1.000
} else {
}

set sl10_slice_all_non_gen_clks      [get_clocks * -filter {@is_generated == false}]
set sl10_slice_all_non_gen_virt_clks $sl10_slice_all_non_gen_clks
if {"$npu_lint_virt_clk" ne "0"} {
  set sl10_slice_all_non_gen_virt_clks [remove_from_collection $sl10_slice_all_non_gen_clks [get_clocks $sl10_slice_virt_clock_name]]
}

set sl10_top_reset_name "sl10_rst_a"
set sl10_top_reset [get_ports ${sl10_top_reset_name} -filter {@port_direction == in}]

set_input_delay [expr 0.25 * ${sl10_slice_clock_per}] -clock ${sl10_slice_clock_obj} ${sl10_top_reset}
set_input_delay [expr 0.25 * ${sl10_slice_clock_per}] -clock ${sl10_slice_clock_obj} ${sl10_top_reset} -add
set_input_delay [expr 0.25 * ${sl10_slice_clock_per}] -clock ${sl10_slice_clock_obj} [get_ports sl10nl1arc_* -filter {@port_direction == in}]
set ALL_INPUTS_EXC_WDT_CLK  [remove_from_collection [get_ports sl10_* -filter {@port_direction == in}] [get_ports sl10_wdt_clk]]
set_input_delay [expr 0.25 * ${sl10_slice_clock_per}] -clock ${sl10_slice_clock_obj} [get_ports $ALL_INPUTS_EXC_WDT_CLK -filter {@port_direction == in}]
if {"$npu_lint_virt_clk" ne "0"} {
  foreach_in_collection clkname $sl10_slice_all_non_gen_virt_clks {
    remove_input_delay  -clock $clkname [get_ports ${sl10_top_reset_name} -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports sl10nl1arc_*_a -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl10_slice_virt_clock_name] period]] -clock [get_clocks $sl10_slice_virt_clock_name] [get_ports ${sl10_top_reset_name} -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl10_slice_virt_clock_name] period]] -clock [get_clocks $sl10_slice_virt_clock_name] [get_ports sl10nl1arc_*_a -filter {@port_direction == in}]
}


set_output_delay [expr 0.25 * ${sl10_slice_clock_per}] -clock ${sl10_slice_clock_obj} [get_ports sl10nl1arc_* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl10_slice_clock_per}] -clock ${sl10_slice_clock_obj} [get_ports sl10_ecc_dbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl10_slice_clock_per}] -clock ${sl10_slice_clock_obj} [get_ports sl10_ecc_sbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl10_slice_wdt_clock_per}] -clock ${sl10_slice_wdt_clock_obj} [get_ports sl10nl1arc_wdt_reset_wdt_clk_error -filter {@port_direction == out}]


#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------


if {"$npu_flatten_sdc" eq 1} {
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${sl10_l1hier}*ialb_cpu_top*"]
set_false_path -through [get_pins {*dbg_prot_sel} -hier -filter "@full_name=~*${sl10_l1hier}*ialb_cpu_top*"]
}



if {"$npu_flatten_sdc" eq 1} {
#------------------------------------------------------------------------------
# False Paths  - multi-through
#------------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Multicycle paths
# -----------------------------------------------------------------------------
# ARC HS PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl10_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl10_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl10_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl10_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1


# Conv 2 cycle checker for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl10_nslhier}*u_npu_conv*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl10_nslhier}*u_npu_conv*"] -hold 1
if {"$npu_lint_virt_clk" eq "0"} {
  # Do not merge redundant registers for timing in synthesis
  set_register_merging [get_cells * -hier -filter "@full_name=~*_nomerge_r*"]  false
}

# GTOA 2 cycle checker, the generated clock inside GTOA is 1/2 the frequency of the main clock
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl10_nslhier}*u_npu_gtoa*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl10_nslhier}*u_npu_gtoa*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl10_nslhier}*u_npu_gtoa*"] -start -setup 2 -comment reg2reg_mc2f2s
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl10_nslhier}*u_npu_gtoa*"] -start -hold 1
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl10_nslhier}*u_npu_gtoa*"] -end -setup 2 -comment reg2reg_mc2s2f
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl10_nslhier}*u_npu_gtoa*"] -end -hold 1
# GTOA 3 cycle path for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl10_nslhier}*u_npu_gtoa*"] -start -setup 3 -comment reg2reg_mc3f2s
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl10_nslhier}*u_npu_gtoa*"] -start -hold 2

}

#- npu_slice_top 10 }
#- npu_slice_top 11 {
# =============================================================================
# Constraints for the npu_slice_top module sl11_
# =============================================================================

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# -- NPU slice search path in the hierarchy
set sl11_nslhier "u_l1core11/"
set sl11_l1hier "${sl11_nslhier}*u_npu_l1_arc"

# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------

set sl11_slice_clock_name sl11_clk
set sl11_slice_virt_clock_name sl11_async_vclk
set sl11_slice_clock_freq 1000
if { [info exists ::env(NPU_FMAX)] } {
    set sl11_slice_clock_freq $::env(NPU_FMAX)
}
set sl11_slice_clock_per  [expr 1000.0 / $sl11_slice_clock_freq] ; # Period in ns
set sl11_slice_clock_port [get_ports $sl11_slice_clock_name]
set sl11_slice_clock_Teff [expr $sl11_slice_clock_per - $clk_unc_setup]
set sl11_slice_clock_obj  [get_clocks $sl11_slice_clock_name]
puts "Info: npu_slice 11 clock $sl11_slice_clock_name created @ $sl11_slice_clock_freq MHz"

set sl11_slice_wdt_clock_freq 50
if { [info exists ::env(WDT_NPU_FMAX)] } {
  set sl11_slice_wdt_clock_freq $::env(WDT_NPU_FMAX)
}
set sl11_slice_wdt_clock_name sl11_wdt_clk
set sl11_slice_wdt_clock_per  [expr 1000.0 / $sl11_slice_wdt_clock_freq] ; # Period in ns
set sl11_slice_wdt_clock_port [get_ports $sl11_slice_wdt_clock_name]
set sl11_slice_wdt_clock_obj [get_clocks $sl11_slice_wdt_clock_name]
puts "Info: npu_slice 11 wdt_clock $sl11_slice_wdt_clock_name created @ $sl11_slice_wdt_clock_freq MHz"

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
set  sl11_l1arc_hs_gclocks ""
proc sl11_l1arc_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable sl11_slice_clock_obj
    variable sl11_slice_clock_port
    variable sl11_l1hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable sl11_l1arc_hs_gclocks
    variable clk_gate0_Q
    # Slow search
    #   get_pins * -hier -filter "@full_name=~*${sl11_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*$clk_gate0_Q"
    # Faster search
    #   get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl11_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*"
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl11_l1hier}*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${sl11_slice_clock_obj} -source ${sl11_slice_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append sl11_l1arc_hs_gclocks " $name"
    puts "Info: npu_slice_top 11 L1 ARC HS generated clock '$name' from ICG $ckg_full_name with edges $ck_edges"
}

set sl11_l1pfx "sl11_nl1_"
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}ic_data_bank0_gclk"        "uic_data_bank0_clkgate"  {1 2 5}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}ic_data_bank1_gclk"        "uic_data_bank1_clkgate"  {1 2 5}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}ic_tag_w0_gclk"            "uic_tag_w0_clkgate"      {1 2 5}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}ic_tag_w1_gclk"            "uic_tag_w1_clkgate"      {1 2 5}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}ic_tag_w2_gclk"            "uic_tag_w2_clkgate"      {1 2 5}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}ic_tag_w3_gclk"            "uic_tag_w3_clkgate"      {1 2 5}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}bc_ram0_gclk"              "u_bc0_clkgate"           {1 2 5}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}bc_ram1_gclk"              "u_bc1_clkgate"           {1 2 5}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}pt_ram0_gclk"              "u_pt0_clkgate"           {1 2 5}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}pt_ram1_gclk"              "u_pt1_clkgate"           {1 2 5}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}dccm_bank0_lo_gclk"        "u_clkgate_dccm_0_lo"     {1 2 5}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}dccm_bank0_hi_gclk"        "u_clkgate_dccm_0_hi"     {1 2 5}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}dccm_bank1_lo_gclk"        "u_clkgate_dccm_1_lo"     {1 2 5}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}dccm_bank1_hi_gclk"        "u_clkgate_dccm_1_hi"     {1 2 5}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}data_even_lo_gclk"         "u_clkgate_data_even_lo"  {1 2 5}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}data_even_hi_gclk"         "u_clkgate_data_even_hi"  {1 2 5}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}data_odd_lo_gclk"          "u_clkgate_data_odd_lo"   {1 2 5}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}data_odd_hi_gclk"          "u_clkgate_data_odd_hi"   {1 2 5}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}ntlb_pd0_gclk"             "u_ntlb_pd0_clkgate"      {1 2 7}
sl11_l1arc_hs_generated_clock "${sl11_l1pfx}ntlb_pd1_gclk"             "u_ntlb_pd1_clkgate"      {1 2 5}

# GTOA core runs at half the frequency
create_generated_clock -name "sl11_gtoa_half_gclk" -edges {1 2 5} -add -master_clock ${sl11_slice_clock_obj} -source ${sl11_slice_clock_port} [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl11_nslhier}*u_npu_gtoa*u_l2_clkgate_half_inst*"]
set_dont_touch_network "sl11_gtoa_half_gclk"
set_clock_uncertainty -setup $clk_unc_setup "sl11_gtoa_half_gclk"
set_clock_uncertainty -hold  $clk_unc_hold  "sl11_gtoa_half_gclk"

group_path -name $sl11_slice_clock_name-to-$sl11_slice_clock_name -from $sl11_slice_clock_name -to $sl11_slice_clock_name
group_path -name sl11_gtoa_half_gclk-to-$sl11_slice_clock_name    -from sl11_gtoa_half_gclk    -to $sl11_slice_clock_name
group_path -name $sl11_slice_clock_name-to-sl11_gtoa_half_gclk    -from $sl11_slice_clock_name -to sl11_gtoa_half_gclk
group_path -name sl11_gtoa_half_gclk-to-sl11_gtoa_half_gclk       -from sl11_gtoa_half_gclk    -to sl11_gtoa_half_gclk

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name $sl11_slice_virt_clock_name -period 1.000
} else {
}

set sl11_slice_all_non_gen_clks      [get_clocks * -filter {@is_generated == false}]
set sl11_slice_all_non_gen_virt_clks $sl11_slice_all_non_gen_clks
if {"$npu_lint_virt_clk" ne "0"} {
  set sl11_slice_all_non_gen_virt_clks [remove_from_collection $sl11_slice_all_non_gen_clks [get_clocks $sl11_slice_virt_clock_name]]
}

set sl11_top_reset_name "sl11_rst_a"
set sl11_top_reset [get_ports ${sl11_top_reset_name} -filter {@port_direction == in}]

set_input_delay [expr 0.25 * ${sl11_slice_clock_per}] -clock ${sl11_slice_clock_obj} ${sl11_top_reset}
set_input_delay [expr 0.25 * ${sl11_slice_clock_per}] -clock ${sl11_slice_clock_obj} ${sl11_top_reset} -add
set_input_delay [expr 0.25 * ${sl11_slice_clock_per}] -clock ${sl11_slice_clock_obj} [get_ports sl11nl1arc_* -filter {@port_direction == in}]
set ALL_INPUTS_EXC_WDT_CLK  [remove_from_collection [get_ports sl11_* -filter {@port_direction == in}] [get_ports sl11_wdt_clk]]
set_input_delay [expr 0.25 * ${sl11_slice_clock_per}] -clock ${sl11_slice_clock_obj} [get_ports $ALL_INPUTS_EXC_WDT_CLK -filter {@port_direction == in}]
if {"$npu_lint_virt_clk" ne "0"} {
  foreach_in_collection clkname $sl11_slice_all_non_gen_virt_clks {
    remove_input_delay  -clock $clkname [get_ports ${sl11_top_reset_name} -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports sl11nl1arc_*_a -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl11_slice_virt_clock_name] period]] -clock [get_clocks $sl11_slice_virt_clock_name] [get_ports ${sl11_top_reset_name} -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl11_slice_virt_clock_name] period]] -clock [get_clocks $sl11_slice_virt_clock_name] [get_ports sl11nl1arc_*_a -filter {@port_direction == in}]
}


set_output_delay [expr 0.25 * ${sl11_slice_clock_per}] -clock ${sl11_slice_clock_obj} [get_ports sl11nl1arc_* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl11_slice_clock_per}] -clock ${sl11_slice_clock_obj} [get_ports sl11_ecc_dbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl11_slice_clock_per}] -clock ${sl11_slice_clock_obj} [get_ports sl11_ecc_sbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl11_slice_wdt_clock_per}] -clock ${sl11_slice_wdt_clock_obj} [get_ports sl11nl1arc_wdt_reset_wdt_clk_error -filter {@port_direction == out}]


#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------


if {"$npu_flatten_sdc" eq 1} {
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${sl11_l1hier}*ialb_cpu_top*"]
set_false_path -through [get_pins {*dbg_prot_sel} -hier -filter "@full_name=~*${sl11_l1hier}*ialb_cpu_top*"]
}



if {"$npu_flatten_sdc" eq 1} {
#------------------------------------------------------------------------------
# False Paths  - multi-through
#------------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Multicycle paths
# -----------------------------------------------------------------------------
# ARC HS PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl11_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl11_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl11_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl11_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1


# Conv 2 cycle checker for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl11_nslhier}*u_npu_conv*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl11_nslhier}*u_npu_conv*"] -hold 1
if {"$npu_lint_virt_clk" eq "0"} {
  # Do not merge redundant registers for timing in synthesis
  set_register_merging [get_cells * -hier -filter "@full_name=~*_nomerge_r*"]  false
}

# GTOA 2 cycle checker, the generated clock inside GTOA is 1/2 the frequency of the main clock
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl11_nslhier}*u_npu_gtoa*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl11_nslhier}*u_npu_gtoa*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl11_nslhier}*u_npu_gtoa*"] -start -setup 2 -comment reg2reg_mc2f2s
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl11_nslhier}*u_npu_gtoa*"] -start -hold 1
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl11_nslhier}*u_npu_gtoa*"] -end -setup 2 -comment reg2reg_mc2s2f
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl11_nslhier}*u_npu_gtoa*"] -end -hold 1
# GTOA 3 cycle path for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl11_nslhier}*u_npu_gtoa*"] -start -setup 3 -comment reg2reg_mc3f2s
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl11_nslhier}*u_npu_gtoa*"] -start -hold 2

}

#- npu_slice_top 11 }
#- npu_slice_top 12 {
# =============================================================================
# Constraints for the npu_slice_top module sl12_
# =============================================================================

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# -- NPU slice search path in the hierarchy
set sl12_nslhier "u_l1core12/"
set sl12_l1hier "${sl12_nslhier}*u_npu_l1_arc"

# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------

set sl12_slice_clock_name sl12_clk
set sl12_slice_virt_clock_name sl12_async_vclk
set sl12_slice_clock_freq 1000
if { [info exists ::env(NPU_FMAX)] } {
    set sl12_slice_clock_freq $::env(NPU_FMAX)
}
set sl12_slice_clock_per  [expr 1000.0 / $sl12_slice_clock_freq] ; # Period in ns
set sl12_slice_clock_port [get_ports $sl12_slice_clock_name]
set sl12_slice_clock_Teff [expr $sl12_slice_clock_per - $clk_unc_setup]
set sl12_slice_clock_obj  [get_clocks $sl12_slice_clock_name]
puts "Info: npu_slice 12 clock $sl12_slice_clock_name created @ $sl12_slice_clock_freq MHz"

set sl12_slice_wdt_clock_freq 50
if { [info exists ::env(WDT_NPU_FMAX)] } {
  set sl12_slice_wdt_clock_freq $::env(WDT_NPU_FMAX)
}
set sl12_slice_wdt_clock_name sl12_wdt_clk
set sl12_slice_wdt_clock_per  [expr 1000.0 / $sl12_slice_wdt_clock_freq] ; # Period in ns
set sl12_slice_wdt_clock_port [get_ports $sl12_slice_wdt_clock_name]
set sl12_slice_wdt_clock_obj [get_clocks $sl12_slice_wdt_clock_name]
puts "Info: npu_slice 12 wdt_clock $sl12_slice_wdt_clock_name created @ $sl12_slice_wdt_clock_freq MHz"

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
set  sl12_l1arc_hs_gclocks ""
proc sl12_l1arc_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable sl12_slice_clock_obj
    variable sl12_slice_clock_port
    variable sl12_l1hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable sl12_l1arc_hs_gclocks
    variable clk_gate0_Q
    # Slow search
    #   get_pins * -hier -filter "@full_name=~*${sl12_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*$clk_gate0_Q"
    # Faster search
    #   get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl12_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*"
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl12_l1hier}*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${sl12_slice_clock_obj} -source ${sl12_slice_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append sl12_l1arc_hs_gclocks " $name"
    puts "Info: npu_slice_top 12 L1 ARC HS generated clock '$name' from ICG $ckg_full_name with edges $ck_edges"
}

set sl12_l1pfx "sl12_nl1_"
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}ic_data_bank0_gclk"        "uic_data_bank0_clkgate"  {1 2 5}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}ic_data_bank1_gclk"        "uic_data_bank1_clkgate"  {1 2 5}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}ic_tag_w0_gclk"            "uic_tag_w0_clkgate"      {1 2 5}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}ic_tag_w1_gclk"            "uic_tag_w1_clkgate"      {1 2 5}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}ic_tag_w2_gclk"            "uic_tag_w2_clkgate"      {1 2 5}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}ic_tag_w3_gclk"            "uic_tag_w3_clkgate"      {1 2 5}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}bc_ram0_gclk"              "u_bc0_clkgate"           {1 2 5}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}bc_ram1_gclk"              "u_bc1_clkgate"           {1 2 5}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}pt_ram0_gclk"              "u_pt0_clkgate"           {1 2 5}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}pt_ram1_gclk"              "u_pt1_clkgate"           {1 2 5}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}dccm_bank0_lo_gclk"        "u_clkgate_dccm_0_lo"     {1 2 5}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}dccm_bank0_hi_gclk"        "u_clkgate_dccm_0_hi"     {1 2 5}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}dccm_bank1_lo_gclk"        "u_clkgate_dccm_1_lo"     {1 2 5}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}dccm_bank1_hi_gclk"        "u_clkgate_dccm_1_hi"     {1 2 5}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}data_even_lo_gclk"         "u_clkgate_data_even_lo"  {1 2 5}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}data_even_hi_gclk"         "u_clkgate_data_even_hi"  {1 2 5}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}data_odd_lo_gclk"          "u_clkgate_data_odd_lo"   {1 2 5}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}data_odd_hi_gclk"          "u_clkgate_data_odd_hi"   {1 2 5}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}ntlb_pd0_gclk"             "u_ntlb_pd0_clkgate"      {1 2 7}
sl12_l1arc_hs_generated_clock "${sl12_l1pfx}ntlb_pd1_gclk"             "u_ntlb_pd1_clkgate"      {1 2 5}

# GTOA core runs at half the frequency
create_generated_clock -name "sl12_gtoa_half_gclk" -edges {1 2 5} -add -master_clock ${sl12_slice_clock_obj} -source ${sl12_slice_clock_port} [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl12_nslhier}*u_npu_gtoa*u_l2_clkgate_half_inst*"]
set_dont_touch_network "sl12_gtoa_half_gclk"
set_clock_uncertainty -setup $clk_unc_setup "sl12_gtoa_half_gclk"
set_clock_uncertainty -hold  $clk_unc_hold  "sl12_gtoa_half_gclk"

group_path -name $sl12_slice_clock_name-to-$sl12_slice_clock_name -from $sl12_slice_clock_name -to $sl12_slice_clock_name
group_path -name sl12_gtoa_half_gclk-to-$sl12_slice_clock_name    -from sl12_gtoa_half_gclk    -to $sl12_slice_clock_name
group_path -name $sl12_slice_clock_name-to-sl12_gtoa_half_gclk    -from $sl12_slice_clock_name -to sl12_gtoa_half_gclk
group_path -name sl12_gtoa_half_gclk-to-sl12_gtoa_half_gclk       -from sl12_gtoa_half_gclk    -to sl12_gtoa_half_gclk

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name $sl12_slice_virt_clock_name -period 1.000
} else {
}

set sl12_slice_all_non_gen_clks      [get_clocks * -filter {@is_generated == false}]
set sl12_slice_all_non_gen_virt_clks $sl12_slice_all_non_gen_clks
if {"$npu_lint_virt_clk" ne "0"} {
  set sl12_slice_all_non_gen_virt_clks [remove_from_collection $sl12_slice_all_non_gen_clks [get_clocks $sl12_slice_virt_clock_name]]
}

set sl12_top_reset_name "sl12_rst_a"
set sl12_top_reset [get_ports ${sl12_top_reset_name} -filter {@port_direction == in}]

set_input_delay [expr 0.25 * ${sl12_slice_clock_per}] -clock ${sl12_slice_clock_obj} ${sl12_top_reset}
set_input_delay [expr 0.25 * ${sl12_slice_clock_per}] -clock ${sl12_slice_clock_obj} ${sl12_top_reset} -add
set_input_delay [expr 0.25 * ${sl12_slice_clock_per}] -clock ${sl12_slice_clock_obj} [get_ports sl12nl1arc_* -filter {@port_direction == in}]
set ALL_INPUTS_EXC_WDT_CLK  [remove_from_collection [get_ports sl12_* -filter {@port_direction == in}] [get_ports sl12_wdt_clk]]
set_input_delay [expr 0.25 * ${sl12_slice_clock_per}] -clock ${sl12_slice_clock_obj} [get_ports $ALL_INPUTS_EXC_WDT_CLK -filter {@port_direction == in}]
if {"$npu_lint_virt_clk" ne "0"} {
  foreach_in_collection clkname $sl12_slice_all_non_gen_virt_clks {
    remove_input_delay  -clock $clkname [get_ports ${sl12_top_reset_name} -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports sl12nl1arc_*_a -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl12_slice_virt_clock_name] period]] -clock [get_clocks $sl12_slice_virt_clock_name] [get_ports ${sl12_top_reset_name} -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl12_slice_virt_clock_name] period]] -clock [get_clocks $sl12_slice_virt_clock_name] [get_ports sl12nl1arc_*_a -filter {@port_direction == in}]
}


set_output_delay [expr 0.25 * ${sl12_slice_clock_per}] -clock ${sl12_slice_clock_obj} [get_ports sl12nl1arc_* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl12_slice_clock_per}] -clock ${sl12_slice_clock_obj} [get_ports sl12_ecc_dbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl12_slice_clock_per}] -clock ${sl12_slice_clock_obj} [get_ports sl12_ecc_sbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl12_slice_wdt_clock_per}] -clock ${sl12_slice_wdt_clock_obj} [get_ports sl12nl1arc_wdt_reset_wdt_clk_error -filter {@port_direction == out}]


#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------


if {"$npu_flatten_sdc" eq 1} {
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${sl12_l1hier}*ialb_cpu_top*"]
set_false_path -through [get_pins {*dbg_prot_sel} -hier -filter "@full_name=~*${sl12_l1hier}*ialb_cpu_top*"]
}



if {"$npu_flatten_sdc" eq 1} {
#------------------------------------------------------------------------------
# False Paths  - multi-through
#------------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Multicycle paths
# -----------------------------------------------------------------------------
# ARC HS PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl12_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl12_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl12_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl12_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1


# Conv 2 cycle checker for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl12_nslhier}*u_npu_conv*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl12_nslhier}*u_npu_conv*"] -hold 1
if {"$npu_lint_virt_clk" eq "0"} {
  # Do not merge redundant registers for timing in synthesis
  set_register_merging [get_cells * -hier -filter "@full_name=~*_nomerge_r*"]  false
}

# GTOA 2 cycle checker, the generated clock inside GTOA is 1/2 the frequency of the main clock
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl12_nslhier}*u_npu_gtoa*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl12_nslhier}*u_npu_gtoa*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl12_nslhier}*u_npu_gtoa*"] -start -setup 2 -comment reg2reg_mc2f2s
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl12_nslhier}*u_npu_gtoa*"] -start -hold 1
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl12_nslhier}*u_npu_gtoa*"] -end -setup 2 -comment reg2reg_mc2s2f
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl12_nslhier}*u_npu_gtoa*"] -end -hold 1
# GTOA 3 cycle path for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl12_nslhier}*u_npu_gtoa*"] -start -setup 3 -comment reg2reg_mc3f2s
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl12_nslhier}*u_npu_gtoa*"] -start -hold 2

}

#- npu_slice_top 12 }
#- npu_slice_top 13 {
# =============================================================================
# Constraints for the npu_slice_top module sl13_
# =============================================================================

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# -- NPU slice search path in the hierarchy
set sl13_nslhier "u_l1core13/"
set sl13_l1hier "${sl13_nslhier}*u_npu_l1_arc"

# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------

set sl13_slice_clock_name sl13_clk
set sl13_slice_virt_clock_name sl13_async_vclk
set sl13_slice_clock_freq 1000
if { [info exists ::env(NPU_FMAX)] } {
    set sl13_slice_clock_freq $::env(NPU_FMAX)
}
set sl13_slice_clock_per  [expr 1000.0 / $sl13_slice_clock_freq] ; # Period in ns
set sl13_slice_clock_port [get_ports $sl13_slice_clock_name]
set sl13_slice_clock_Teff [expr $sl13_slice_clock_per - $clk_unc_setup]
set sl13_slice_clock_obj  [get_clocks $sl13_slice_clock_name]
puts "Info: npu_slice 13 clock $sl13_slice_clock_name created @ $sl13_slice_clock_freq MHz"

set sl13_slice_wdt_clock_freq 50
if { [info exists ::env(WDT_NPU_FMAX)] } {
  set sl13_slice_wdt_clock_freq $::env(WDT_NPU_FMAX)
}
set sl13_slice_wdt_clock_name sl13_wdt_clk
set sl13_slice_wdt_clock_per  [expr 1000.0 / $sl13_slice_wdt_clock_freq] ; # Period in ns
set sl13_slice_wdt_clock_port [get_ports $sl13_slice_wdt_clock_name]
set sl13_slice_wdt_clock_obj [get_clocks $sl13_slice_wdt_clock_name]
puts "Info: npu_slice 13 wdt_clock $sl13_slice_wdt_clock_name created @ $sl13_slice_wdt_clock_freq MHz"

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
set  sl13_l1arc_hs_gclocks ""
proc sl13_l1arc_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable sl13_slice_clock_obj
    variable sl13_slice_clock_port
    variable sl13_l1hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable sl13_l1arc_hs_gclocks
    variable clk_gate0_Q
    # Slow search
    #   get_pins * -hier -filter "@full_name=~*${sl13_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*$clk_gate0_Q"
    # Faster search
    #   get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl13_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*"
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl13_l1hier}*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${sl13_slice_clock_obj} -source ${sl13_slice_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append sl13_l1arc_hs_gclocks " $name"
    puts "Info: npu_slice_top 13 L1 ARC HS generated clock '$name' from ICG $ckg_full_name with edges $ck_edges"
}

set sl13_l1pfx "sl13_nl1_"
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}ic_data_bank0_gclk"        "uic_data_bank0_clkgate"  {1 2 5}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}ic_data_bank1_gclk"        "uic_data_bank1_clkgate"  {1 2 5}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}ic_tag_w0_gclk"            "uic_tag_w0_clkgate"      {1 2 5}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}ic_tag_w1_gclk"            "uic_tag_w1_clkgate"      {1 2 5}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}ic_tag_w2_gclk"            "uic_tag_w2_clkgate"      {1 2 5}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}ic_tag_w3_gclk"            "uic_tag_w3_clkgate"      {1 2 5}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}bc_ram0_gclk"              "u_bc0_clkgate"           {1 2 5}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}bc_ram1_gclk"              "u_bc1_clkgate"           {1 2 5}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}pt_ram0_gclk"              "u_pt0_clkgate"           {1 2 5}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}pt_ram1_gclk"              "u_pt1_clkgate"           {1 2 5}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}dccm_bank0_lo_gclk"        "u_clkgate_dccm_0_lo"     {1 2 5}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}dccm_bank0_hi_gclk"        "u_clkgate_dccm_0_hi"     {1 2 5}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}dccm_bank1_lo_gclk"        "u_clkgate_dccm_1_lo"     {1 2 5}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}dccm_bank1_hi_gclk"        "u_clkgate_dccm_1_hi"     {1 2 5}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}data_even_lo_gclk"         "u_clkgate_data_even_lo"  {1 2 5}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}data_even_hi_gclk"         "u_clkgate_data_even_hi"  {1 2 5}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}data_odd_lo_gclk"          "u_clkgate_data_odd_lo"   {1 2 5}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}data_odd_hi_gclk"          "u_clkgate_data_odd_hi"   {1 2 5}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}ntlb_pd0_gclk"             "u_ntlb_pd0_clkgate"      {1 2 7}
sl13_l1arc_hs_generated_clock "${sl13_l1pfx}ntlb_pd1_gclk"             "u_ntlb_pd1_clkgate"      {1 2 5}

# GTOA core runs at half the frequency
create_generated_clock -name "sl13_gtoa_half_gclk" -edges {1 2 5} -add -master_clock ${sl13_slice_clock_obj} -source ${sl13_slice_clock_port} [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl13_nslhier}*u_npu_gtoa*u_l2_clkgate_half_inst*"]
set_dont_touch_network "sl13_gtoa_half_gclk"
set_clock_uncertainty -setup $clk_unc_setup "sl13_gtoa_half_gclk"
set_clock_uncertainty -hold  $clk_unc_hold  "sl13_gtoa_half_gclk"

group_path -name $sl13_slice_clock_name-to-$sl13_slice_clock_name -from $sl13_slice_clock_name -to $sl13_slice_clock_name
group_path -name sl13_gtoa_half_gclk-to-$sl13_slice_clock_name    -from sl13_gtoa_half_gclk    -to $sl13_slice_clock_name
group_path -name $sl13_slice_clock_name-to-sl13_gtoa_half_gclk    -from $sl13_slice_clock_name -to sl13_gtoa_half_gclk
group_path -name sl13_gtoa_half_gclk-to-sl13_gtoa_half_gclk       -from sl13_gtoa_half_gclk    -to sl13_gtoa_half_gclk

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name $sl13_slice_virt_clock_name -period 1.000
} else {
}

set sl13_slice_all_non_gen_clks      [get_clocks * -filter {@is_generated == false}]
set sl13_slice_all_non_gen_virt_clks $sl13_slice_all_non_gen_clks
if {"$npu_lint_virt_clk" ne "0"} {
  set sl13_slice_all_non_gen_virt_clks [remove_from_collection $sl13_slice_all_non_gen_clks [get_clocks $sl13_slice_virt_clock_name]]
}

set sl13_top_reset_name "sl13_rst_a"
set sl13_top_reset [get_ports ${sl13_top_reset_name} -filter {@port_direction == in}]

set_input_delay [expr 0.25 * ${sl13_slice_clock_per}] -clock ${sl13_slice_clock_obj} ${sl13_top_reset}
set_input_delay [expr 0.25 * ${sl13_slice_clock_per}] -clock ${sl13_slice_clock_obj} ${sl13_top_reset} -add
set_input_delay [expr 0.25 * ${sl13_slice_clock_per}] -clock ${sl13_slice_clock_obj} [get_ports sl13nl1arc_* -filter {@port_direction == in}]
set ALL_INPUTS_EXC_WDT_CLK  [remove_from_collection [get_ports sl13_* -filter {@port_direction == in}] [get_ports sl13_wdt_clk]]
set_input_delay [expr 0.25 * ${sl13_slice_clock_per}] -clock ${sl13_slice_clock_obj} [get_ports $ALL_INPUTS_EXC_WDT_CLK -filter {@port_direction == in}]
if {"$npu_lint_virt_clk" ne "0"} {
  foreach_in_collection clkname $sl13_slice_all_non_gen_virt_clks {
    remove_input_delay  -clock $clkname [get_ports ${sl13_top_reset_name} -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports sl13nl1arc_*_a -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl13_slice_virt_clock_name] period]] -clock [get_clocks $sl13_slice_virt_clock_name] [get_ports ${sl13_top_reset_name} -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl13_slice_virt_clock_name] period]] -clock [get_clocks $sl13_slice_virt_clock_name] [get_ports sl13nl1arc_*_a -filter {@port_direction == in}]
}


set_output_delay [expr 0.25 * ${sl13_slice_clock_per}] -clock ${sl13_slice_clock_obj} [get_ports sl13nl1arc_* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl13_slice_clock_per}] -clock ${sl13_slice_clock_obj} [get_ports sl13_ecc_dbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl13_slice_clock_per}] -clock ${sl13_slice_clock_obj} [get_ports sl13_ecc_sbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl13_slice_wdt_clock_per}] -clock ${sl13_slice_wdt_clock_obj} [get_ports sl13nl1arc_wdt_reset_wdt_clk_error -filter {@port_direction == out}]


#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------


if {"$npu_flatten_sdc" eq 1} {
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${sl13_l1hier}*ialb_cpu_top*"]
set_false_path -through [get_pins {*dbg_prot_sel} -hier -filter "@full_name=~*${sl13_l1hier}*ialb_cpu_top*"]
}



if {"$npu_flatten_sdc" eq 1} {
#------------------------------------------------------------------------------
# False Paths  - multi-through
#------------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Multicycle paths
# -----------------------------------------------------------------------------
# ARC HS PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl13_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl13_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl13_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl13_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1


# Conv 2 cycle checker for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl13_nslhier}*u_npu_conv*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl13_nslhier}*u_npu_conv*"] -hold 1
if {"$npu_lint_virt_clk" eq "0"} {
  # Do not merge redundant registers for timing in synthesis
  set_register_merging [get_cells * -hier -filter "@full_name=~*_nomerge_r*"]  false
}

# GTOA 2 cycle checker, the generated clock inside GTOA is 1/2 the frequency of the main clock
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl13_nslhier}*u_npu_gtoa*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl13_nslhier}*u_npu_gtoa*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl13_nslhier}*u_npu_gtoa*"] -start -setup 2 -comment reg2reg_mc2f2s
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl13_nslhier}*u_npu_gtoa*"] -start -hold 1
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl13_nslhier}*u_npu_gtoa*"] -end -setup 2 -comment reg2reg_mc2s2f
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl13_nslhier}*u_npu_gtoa*"] -end -hold 1
# GTOA 3 cycle path for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl13_nslhier}*u_npu_gtoa*"] -start -setup 3 -comment reg2reg_mc3f2s
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl13_nslhier}*u_npu_gtoa*"] -start -hold 2

}

#- npu_slice_top 13 }
#- npu_slice_top 14 {
# =============================================================================
# Constraints for the npu_slice_top module sl14_
# =============================================================================

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# -- NPU slice search path in the hierarchy
set sl14_nslhier "u_l1core14/"
set sl14_l1hier "${sl14_nslhier}*u_npu_l1_arc"

# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------

set sl14_slice_clock_name sl14_clk
set sl14_slice_virt_clock_name sl14_async_vclk
set sl14_slice_clock_freq 1000
if { [info exists ::env(NPU_FMAX)] } {
    set sl14_slice_clock_freq $::env(NPU_FMAX)
}
set sl14_slice_clock_per  [expr 1000.0 / $sl14_slice_clock_freq] ; # Period in ns
set sl14_slice_clock_port [get_ports $sl14_slice_clock_name]
set sl14_slice_clock_Teff [expr $sl14_slice_clock_per - $clk_unc_setup]
set sl14_slice_clock_obj  [get_clocks $sl14_slice_clock_name]
puts "Info: npu_slice 14 clock $sl14_slice_clock_name created @ $sl14_slice_clock_freq MHz"

set sl14_slice_wdt_clock_freq 50
if { [info exists ::env(WDT_NPU_FMAX)] } {
  set sl14_slice_wdt_clock_freq $::env(WDT_NPU_FMAX)
}
set sl14_slice_wdt_clock_name sl14_wdt_clk
set sl14_slice_wdt_clock_per  [expr 1000.0 / $sl14_slice_wdt_clock_freq] ; # Period in ns
set sl14_slice_wdt_clock_port [get_ports $sl14_slice_wdt_clock_name]
set sl14_slice_wdt_clock_obj [get_clocks $sl14_slice_wdt_clock_name]
puts "Info: npu_slice 14 wdt_clock $sl14_slice_wdt_clock_name created @ $sl14_slice_wdt_clock_freq MHz"

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
set  sl14_l1arc_hs_gclocks ""
proc sl14_l1arc_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable sl14_slice_clock_obj
    variable sl14_slice_clock_port
    variable sl14_l1hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable sl14_l1arc_hs_gclocks
    variable clk_gate0_Q
    # Slow search
    #   get_pins * -hier -filter "@full_name=~*${sl14_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*$clk_gate0_Q"
    # Faster search
    #   get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl14_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*"
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl14_l1hier}*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${sl14_slice_clock_obj} -source ${sl14_slice_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append sl14_l1arc_hs_gclocks " $name"
    puts "Info: npu_slice_top 14 L1 ARC HS generated clock '$name' from ICG $ckg_full_name with edges $ck_edges"
}

set sl14_l1pfx "sl14_nl1_"
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}ic_data_bank0_gclk"        "uic_data_bank0_clkgate"  {1 2 5}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}ic_data_bank1_gclk"        "uic_data_bank1_clkgate"  {1 2 5}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}ic_tag_w0_gclk"            "uic_tag_w0_clkgate"      {1 2 5}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}ic_tag_w1_gclk"            "uic_tag_w1_clkgate"      {1 2 5}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}ic_tag_w2_gclk"            "uic_tag_w2_clkgate"      {1 2 5}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}ic_tag_w3_gclk"            "uic_tag_w3_clkgate"      {1 2 5}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}bc_ram0_gclk"              "u_bc0_clkgate"           {1 2 5}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}bc_ram1_gclk"              "u_bc1_clkgate"           {1 2 5}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}pt_ram0_gclk"              "u_pt0_clkgate"           {1 2 5}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}pt_ram1_gclk"              "u_pt1_clkgate"           {1 2 5}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}dccm_bank0_lo_gclk"        "u_clkgate_dccm_0_lo"     {1 2 5}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}dccm_bank0_hi_gclk"        "u_clkgate_dccm_0_hi"     {1 2 5}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}dccm_bank1_lo_gclk"        "u_clkgate_dccm_1_lo"     {1 2 5}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}dccm_bank1_hi_gclk"        "u_clkgate_dccm_1_hi"     {1 2 5}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}data_even_lo_gclk"         "u_clkgate_data_even_lo"  {1 2 5}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}data_even_hi_gclk"         "u_clkgate_data_even_hi"  {1 2 5}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}data_odd_lo_gclk"          "u_clkgate_data_odd_lo"   {1 2 5}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}data_odd_hi_gclk"          "u_clkgate_data_odd_hi"   {1 2 5}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}ntlb_pd0_gclk"             "u_ntlb_pd0_clkgate"      {1 2 7}
sl14_l1arc_hs_generated_clock "${sl14_l1pfx}ntlb_pd1_gclk"             "u_ntlb_pd1_clkgate"      {1 2 5}

# GTOA core runs at half the frequency
create_generated_clock -name "sl14_gtoa_half_gclk" -edges {1 2 5} -add -master_clock ${sl14_slice_clock_obj} -source ${sl14_slice_clock_port} [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl14_nslhier}*u_npu_gtoa*u_l2_clkgate_half_inst*"]
set_dont_touch_network "sl14_gtoa_half_gclk"
set_clock_uncertainty -setup $clk_unc_setup "sl14_gtoa_half_gclk"
set_clock_uncertainty -hold  $clk_unc_hold  "sl14_gtoa_half_gclk"

group_path -name $sl14_slice_clock_name-to-$sl14_slice_clock_name -from $sl14_slice_clock_name -to $sl14_slice_clock_name
group_path -name sl14_gtoa_half_gclk-to-$sl14_slice_clock_name    -from sl14_gtoa_half_gclk    -to $sl14_slice_clock_name
group_path -name $sl14_slice_clock_name-to-sl14_gtoa_half_gclk    -from $sl14_slice_clock_name -to sl14_gtoa_half_gclk
group_path -name sl14_gtoa_half_gclk-to-sl14_gtoa_half_gclk       -from sl14_gtoa_half_gclk    -to sl14_gtoa_half_gclk

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name $sl14_slice_virt_clock_name -period 1.000
} else {
}

set sl14_slice_all_non_gen_clks      [get_clocks * -filter {@is_generated == false}]
set sl14_slice_all_non_gen_virt_clks $sl14_slice_all_non_gen_clks
if {"$npu_lint_virt_clk" ne "0"} {
  set sl14_slice_all_non_gen_virt_clks [remove_from_collection $sl14_slice_all_non_gen_clks [get_clocks $sl14_slice_virt_clock_name]]
}

set sl14_top_reset_name "sl14_rst_a"
set sl14_top_reset [get_ports ${sl14_top_reset_name} -filter {@port_direction == in}]

set_input_delay [expr 0.25 * ${sl14_slice_clock_per}] -clock ${sl14_slice_clock_obj} ${sl14_top_reset}
set_input_delay [expr 0.25 * ${sl14_slice_clock_per}] -clock ${sl14_slice_clock_obj} ${sl14_top_reset} -add
set_input_delay [expr 0.25 * ${sl14_slice_clock_per}] -clock ${sl14_slice_clock_obj} [get_ports sl14nl1arc_* -filter {@port_direction == in}]
set ALL_INPUTS_EXC_WDT_CLK  [remove_from_collection [get_ports sl14_* -filter {@port_direction == in}] [get_ports sl14_wdt_clk]]
set_input_delay [expr 0.25 * ${sl14_slice_clock_per}] -clock ${sl14_slice_clock_obj} [get_ports $ALL_INPUTS_EXC_WDT_CLK -filter {@port_direction == in}]
if {"$npu_lint_virt_clk" ne "0"} {
  foreach_in_collection clkname $sl14_slice_all_non_gen_virt_clks {
    remove_input_delay  -clock $clkname [get_ports ${sl14_top_reset_name} -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports sl14nl1arc_*_a -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl14_slice_virt_clock_name] period]] -clock [get_clocks $sl14_slice_virt_clock_name] [get_ports ${sl14_top_reset_name} -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl14_slice_virt_clock_name] period]] -clock [get_clocks $sl14_slice_virt_clock_name] [get_ports sl14nl1arc_*_a -filter {@port_direction == in}]
}


set_output_delay [expr 0.25 * ${sl14_slice_clock_per}] -clock ${sl14_slice_clock_obj} [get_ports sl14nl1arc_* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl14_slice_clock_per}] -clock ${sl14_slice_clock_obj} [get_ports sl14_ecc_dbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl14_slice_clock_per}] -clock ${sl14_slice_clock_obj} [get_ports sl14_ecc_sbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl14_slice_wdt_clock_per}] -clock ${sl14_slice_wdt_clock_obj} [get_ports sl14nl1arc_wdt_reset_wdt_clk_error -filter {@port_direction == out}]


#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------


if {"$npu_flatten_sdc" eq 1} {
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${sl14_l1hier}*ialb_cpu_top*"]
set_false_path -through [get_pins {*dbg_prot_sel} -hier -filter "@full_name=~*${sl14_l1hier}*ialb_cpu_top*"]
}



if {"$npu_flatten_sdc" eq 1} {
#------------------------------------------------------------------------------
# False Paths  - multi-through
#------------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Multicycle paths
# -----------------------------------------------------------------------------
# ARC HS PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl14_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl14_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl14_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl14_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1


# Conv 2 cycle checker for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl14_nslhier}*u_npu_conv*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl14_nslhier}*u_npu_conv*"] -hold 1
if {"$npu_lint_virt_clk" eq "0"} {
  # Do not merge redundant registers for timing in synthesis
  set_register_merging [get_cells * -hier -filter "@full_name=~*_nomerge_r*"]  false
}

# GTOA 2 cycle checker, the generated clock inside GTOA is 1/2 the frequency of the main clock
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl14_nslhier}*u_npu_gtoa*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl14_nslhier}*u_npu_gtoa*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl14_nslhier}*u_npu_gtoa*"] -start -setup 2 -comment reg2reg_mc2f2s
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl14_nslhier}*u_npu_gtoa*"] -start -hold 1
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl14_nslhier}*u_npu_gtoa*"] -end -setup 2 -comment reg2reg_mc2s2f
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl14_nslhier}*u_npu_gtoa*"] -end -hold 1
# GTOA 3 cycle path for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl14_nslhier}*u_npu_gtoa*"] -start -setup 3 -comment reg2reg_mc3f2s
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl14_nslhier}*u_npu_gtoa*"] -start -hold 2

}

#- npu_slice_top 14 }
#- npu_slice_top 15 {
# =============================================================================
# Constraints for the npu_slice_top module sl15_
# =============================================================================

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# -- NPU slice search path in the hierarchy
set sl15_nslhier "u_l1core15/"
set sl15_l1hier "${sl15_nslhier}*u_npu_l1_arc"

# -----------------------------------------------------------------------------
# Input Clocks
# -----------------------------------------------------------------------------

set sl15_slice_clock_name sl15_clk
set sl15_slice_virt_clock_name sl15_async_vclk
set sl15_slice_clock_freq 1000
if { [info exists ::env(NPU_FMAX)] } {
    set sl15_slice_clock_freq $::env(NPU_FMAX)
}
set sl15_slice_clock_per  [expr 1000.0 / $sl15_slice_clock_freq] ; # Period in ns
set sl15_slice_clock_port [get_ports $sl15_slice_clock_name]
set sl15_slice_clock_Teff [expr $sl15_slice_clock_per - $clk_unc_setup]
set sl15_slice_clock_obj  [get_clocks $sl15_slice_clock_name]
puts "Info: npu_slice 15 clock $sl15_slice_clock_name created @ $sl15_slice_clock_freq MHz"

set sl15_slice_wdt_clock_freq 50
if { [info exists ::env(WDT_NPU_FMAX)] } {
  set sl15_slice_wdt_clock_freq $::env(WDT_NPU_FMAX)
}
set sl15_slice_wdt_clock_name sl15_wdt_clk
set sl15_slice_wdt_clock_per  [expr 1000.0 / $sl15_slice_wdt_clock_freq] ; # Period in ns
set sl15_slice_wdt_clock_port [get_ports $sl15_slice_wdt_clock_name]
set sl15_slice_wdt_clock_obj [get_clocks $sl15_slice_wdt_clock_name]
puts "Info: npu_slice 15 wdt_clock $sl15_slice_wdt_clock_name created @ $sl15_slice_wdt_clock_freq MHz"

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
set  sl15_l1arc_hs_gclocks ""
proc sl15_l1arc_hs_generated_clock { name ckg_module ck_edges } {
    # Global variables used
    variable sl15_slice_clock_obj
    variable sl15_slice_clock_port
    variable sl15_l1hier
    variable clk_unc_setup
    variable clk_unc_hold
    variable sl15_l1arc_hs_gclocks
    variable clk_gate0_Q
    # Slow search
    #   get_pins * -hier -filter "@full_name=~*${sl15_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*$clk_gate0_Q"
    # Faster search
    #   get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl15_nslhier}**ialb_cpu_top**uic_data_bank0_clkgate*"
    set ckg_pin [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl15_l1hier}*ialb_cpu_top**${ckg_module}*"]
    set ckg_full_name [get_object_name $ckg_pin]
    create_generated_clock -name $name -edges "$ck_edges" -add -master_clock ${sl15_slice_clock_obj} -source ${sl15_slice_clock_port} $ckg_pin
    set_dont_touch_network $name
    set_clock_uncertainty -setup $clk_unc_setup $name
    set_clock_uncertainty -hold  $clk_unc_hold  $name
    append sl15_l1arc_hs_gclocks " $name"
    puts "Info: npu_slice_top 15 L1 ARC HS generated clock '$name' from ICG $ckg_full_name with edges $ck_edges"
}

set sl15_l1pfx "sl15_nl1_"
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}ic_data_bank0_gclk"        "uic_data_bank0_clkgate"  {1 2 5}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}ic_data_bank1_gclk"        "uic_data_bank1_clkgate"  {1 2 5}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}ic_tag_w0_gclk"            "uic_tag_w0_clkgate"      {1 2 5}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}ic_tag_w1_gclk"            "uic_tag_w1_clkgate"      {1 2 5}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}ic_tag_w2_gclk"            "uic_tag_w2_clkgate"      {1 2 5}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}ic_tag_w3_gclk"            "uic_tag_w3_clkgate"      {1 2 5}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}bc_ram0_gclk"              "u_bc0_clkgate"           {1 2 5}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}bc_ram1_gclk"              "u_bc1_clkgate"           {1 2 5}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}pt_ram0_gclk"              "u_pt0_clkgate"           {1 2 5}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}pt_ram1_gclk"              "u_pt1_clkgate"           {1 2 5}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}dccm_bank0_lo_gclk"        "u_clkgate_dccm_0_lo"     {1 2 5}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}dccm_bank0_hi_gclk"        "u_clkgate_dccm_0_hi"     {1 2 5}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}dccm_bank1_lo_gclk"        "u_clkgate_dccm_1_lo"     {1 2 5}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}dccm_bank1_hi_gclk"        "u_clkgate_dccm_1_hi"     {1 2 5}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}data_even_lo_gclk"         "u_clkgate_data_even_lo"  {1 2 5}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}data_even_hi_gclk"         "u_clkgate_data_even_hi"  {1 2 5}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}data_odd_lo_gclk"          "u_clkgate_data_odd_lo"   {1 2 5}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}data_odd_hi_gclk"          "u_clkgate_data_odd_hi"   {1 2 5}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}ntlb_pd0_gclk"             "u_ntlb_pd0_clkgate"      {1 2 7}
sl15_l1arc_hs_generated_clock "${sl15_l1pfx}ntlb_pd1_gclk"             "u_ntlb_pd1_clkgate"      {1 2 5}

# GTOA core runs at half the frequency
create_generated_clock -name "sl15_gtoa_half_gclk" -edges {1 2 5} -add -master_clock ${sl15_slice_clock_obj} -source ${sl15_slice_clock_port} [get_pins "*$clk_gate0_Q" -hier -filter "@full_name=~*${sl15_nslhier}*u_npu_gtoa*u_l2_clkgate_half_inst*"]
set_dont_touch_network "sl15_gtoa_half_gclk"
set_clock_uncertainty -setup $clk_unc_setup "sl15_gtoa_half_gclk"
set_clock_uncertainty -hold  $clk_unc_hold  "sl15_gtoa_half_gclk"

group_path -name $sl15_slice_clock_name-to-$sl15_slice_clock_name -from $sl15_slice_clock_name -to $sl15_slice_clock_name
group_path -name sl15_gtoa_half_gclk-to-$sl15_slice_clock_name    -from sl15_gtoa_half_gclk    -to $sl15_slice_clock_name
group_path -name $sl15_slice_clock_name-to-sl15_gtoa_half_gclk    -from $sl15_slice_clock_name -to sl15_gtoa_half_gclk
group_path -name sl15_gtoa_half_gclk-to-sl15_gtoa_half_gclk       -from sl15_gtoa_half_gclk    -to sl15_gtoa_half_gclk

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name $sl15_slice_virt_clock_name -period 1.000
} else {
}

set sl15_slice_all_non_gen_clks      [get_clocks * -filter {@is_generated == false}]
set sl15_slice_all_non_gen_virt_clks $sl15_slice_all_non_gen_clks
if {"$npu_lint_virt_clk" ne "0"} {
  set sl15_slice_all_non_gen_virt_clks [remove_from_collection $sl15_slice_all_non_gen_clks [get_clocks $sl15_slice_virt_clock_name]]
}

set sl15_top_reset_name "sl15_rst_a"
set sl15_top_reset [get_ports ${sl15_top_reset_name} -filter {@port_direction == in}]

set_input_delay [expr 0.25 * ${sl15_slice_clock_per}] -clock ${sl15_slice_clock_obj} ${sl15_top_reset}
set_input_delay [expr 0.25 * ${sl15_slice_clock_per}] -clock ${sl15_slice_clock_obj} ${sl15_top_reset} -add
set_input_delay [expr 0.25 * ${sl15_slice_clock_per}] -clock ${sl15_slice_clock_obj} [get_ports sl15nl1arc_* -filter {@port_direction == in}]
set ALL_INPUTS_EXC_WDT_CLK  [remove_from_collection [get_ports sl15_* -filter {@port_direction == in}] [get_ports sl15_wdt_clk]]
set_input_delay [expr 0.25 * ${sl15_slice_clock_per}] -clock ${sl15_slice_clock_obj} [get_ports $ALL_INPUTS_EXC_WDT_CLK -filter {@port_direction == in}]
if {"$npu_lint_virt_clk" ne "0"} {
  foreach_in_collection clkname $sl15_slice_all_non_gen_virt_clks {
    remove_input_delay  -clock $clkname [get_ports ${sl15_top_reset_name} -filter {@port_direction == in}]
    remove_input_delay  -clock $clkname [get_ports sl15nl1arc_*_a -filter {@port_direction == in}]
  }
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl15_slice_virt_clock_name] period]] -clock [get_clocks $sl15_slice_virt_clock_name] [get_ports ${sl15_top_reset_name} -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * [get_attr [get_clocks $sl15_slice_virt_clock_name] period]] -clock [get_clocks $sl15_slice_virt_clock_name] [get_ports sl15nl1arc_*_a -filter {@port_direction == in}]
}


set_output_delay [expr 0.25 * ${sl15_slice_clock_per}] -clock ${sl15_slice_clock_obj} [get_ports sl15nl1arc_* -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl15_slice_clock_per}] -clock ${sl15_slice_clock_obj} [get_ports sl15_ecc_dbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl15_slice_clock_per}] -clock ${sl15_slice_clock_obj} [get_ports sl15_ecc_sbe -filter {@port_direction == out}]
set_output_delay [expr 0.25 * ${sl15_slice_wdt_clock_per}] -clock ${sl15_slice_wdt_clock_obj} [get_ports sl15nl1arc_wdt_reset_wdt_clk_error -filter {@port_direction == out}]


#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------

set_false_path -through [get_pins {*arcnum*} -hier -filter "@full_name=~*u_l1core*"]
set_false_path -through [get_pins {*l2_event_a*} -hier -filter "@full_name=~*u_l1core*"]
set_false_path -through [get_pins {*l2_send_event*} -hier -filter "@full_name=~*u_l1core*"]
set_false_path -through [get_pins {*l1_peer_event_a*} -hier -filter "@full_name=~*u_l1core*"]
set_false_path -through [get_pins {*l1_peer_send_event*} -hier -filter "@full_name=~*u_l1core*"]
set_false_path -through [get_pins {*vmid*} -hier -filter "@full_name=~*u_l1core*"]

if {"$npu_flatten_sdc" eq 1} {
set_false_path -through [get_pins {*cpu_clk_enable} -hier -filter "@full_name=~*${sl15_l1hier}*ialb_cpu_top*"]
set_false_path -through [get_pins {*dbg_prot_sel} -hier -filter "@full_name=~*${sl15_l1hier}*ialb_cpu_top*"]
}

set_false_path -through [get_pins -hier * -filter "@full_name=~*icc_top*u_cc_aon_wrap*u_cc_clock_ctrl/l1_clk_enable"]
set_false_path -from sl*_rst_a -through [get_pins -hier * -filter "@full_name=~*icc_top*reset_ctrl*sample_*"]
set_false_path -from sl*_rst_a -through [get_pins -hier * -filter "@full_name=~*icc_top*u_biu_top*reset_ctrl*sample_*"]

# NPU CDC synchronizers
set_false_path -from sl*_rst_a -through [get_pins -hier * -filter "@full_name=~*u_*cdc_sync*sample_*"]

if {"$npu_flatten_sdc" eq 1} {
#------------------------------------------------------------------------------
# False Paths  - multi-through
#------------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Multicycle paths
# -----------------------------------------------------------------------------
# ARC HS PCT interrupts
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl15_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"]  \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl15_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"]  \
    -setup 2 -comment reg2reg_mc2
set_multicycle_path -start \
    -from [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl15_l1hier}*ialb_cpu_top*pct_int_act_2cycle_r*"] \
    -to   [get_cells -hier * -filter "@is_sequential==true && @is_hierarchical==false && @full_name=~*${sl15_l1hier}*ialb_cpu_top*u_alb_irq_unit*irq_num_r*"] \
    -hold 1


# Conv 2 cycle checker for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl15_nslhier}*u_npu_conv*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl15_nslhier}*u_npu_conv*"] -hold 1
if {"$npu_lint_virt_clk" eq "0"} {
  # Do not merge redundant registers for timing in synthesis
  set_register_merging [get_cells * -hier -filter "@full_name=~*_nomerge_r*"]  false
}

# GTOA 2 cycle checker, the generated clock inside GTOA is 1/2 the frequency of the main clock
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl15_nslhier}*u_npu_gtoa*"] -setup 2 -comment reg2reg_mc2
set_multicycle_path -through [get_pins {*u_*mc2_inst/data_in}    -hier -filter "@full_name=~*${sl15_nslhier}*u_npu_gtoa*"] -hold 1
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl15_nslhier}*u_npu_gtoa*"] -start -setup 2 -comment reg2reg_mc2f2s
set_multicycle_path -through [get_pins {*u_*mc2f2s_inst/data_in} -hier -filter "@full_name=~*${sl15_nslhier}*u_npu_gtoa*"] -start -hold 1
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl15_nslhier}*u_npu_gtoa*"] -end -setup 2 -comment reg2reg_mc2s2f
set_multicycle_path -through [get_pins {*u_*mc2s2f_inst/data_in} -hier -filter "@full_name=~*${sl15_nslhier}*u_npu_gtoa*"] -end -hold 1
# GTOA 3 cycle path for hlapi_i
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl15_nslhier}*u_npu_gtoa*"] -start -setup 3 -comment reg2reg_mc3f2s
set_multicycle_path -through [get_pins {*u_*mc3f2s_inst/data_in} -hier -filter "@full_name=~*${sl15_nslhier}*u_npu_gtoa*"] -start -hold 2

}

#- npu_slice_top 15 }

#------------------------------------------------------------------------------
# Async clock groups
#------------------------------------------------------------------------------
if {"$npu_lint_virt_clk" ne "0"} {
set scg_cmd "set_clock_groups -asynchronous -allow_paths -group {$ncore_clock_name $l2arc0_hs_gclocks $l2arc1_hs_gclocks $dbank_gclocks} -group {$apb_clock_name} -group {$ncore_virt_clock_name}  \
    -group {sl0_clk $sl0_l1arc_hs_gclocks sl0_gtoa_half_gclk} -group {sl0_wdt_clk} -group {sl0_async_vclk} \
    -group {sl1_clk $sl1_l1arc_hs_gclocks sl1_gtoa_half_gclk} -group {sl1_wdt_clk} -group {sl1_async_vclk} \
    -group {sl2_clk $sl2_l1arc_hs_gclocks sl2_gtoa_half_gclk} -group {sl2_wdt_clk} -group {sl2_async_vclk} \
    -group {sl3_clk $sl3_l1arc_hs_gclocks sl3_gtoa_half_gclk} -group {sl3_wdt_clk} -group {sl3_async_vclk} \
    -group {sl4_clk $sl4_l1arc_hs_gclocks sl4_gtoa_half_gclk} -group {sl4_wdt_clk} -group {sl4_async_vclk} \
    -group {sl5_clk $sl5_l1arc_hs_gclocks sl5_gtoa_half_gclk} -group {sl5_wdt_clk} -group {sl5_async_vclk} \
    -group {sl6_clk $sl6_l1arc_hs_gclocks sl6_gtoa_half_gclk} -group {sl6_wdt_clk} -group {sl6_async_vclk} \
    -group {sl7_clk $sl7_l1arc_hs_gclocks sl7_gtoa_half_gclk} -group {sl7_wdt_clk} -group {sl7_async_vclk} \
    -group {sl8_clk $sl8_l1arc_hs_gclocks sl8_gtoa_half_gclk} -group {sl8_wdt_clk} -group {sl8_async_vclk} \
    -group {sl9_clk $sl9_l1arc_hs_gclocks sl9_gtoa_half_gclk} -group {sl9_wdt_clk} -group {sl9_async_vclk} \
    -group {sl10_clk $sl10_l1arc_hs_gclocks sl10_gtoa_half_gclk} -group {sl10_wdt_clk} -group {sl10_async_vclk} \
    -group {sl11_clk $sl11_l1arc_hs_gclocks sl11_gtoa_half_gclk} -group {sl11_wdt_clk} -group {sl11_async_vclk} \
    -group {sl12_clk $sl12_l1arc_hs_gclocks sl12_gtoa_half_gclk} -group {sl12_wdt_clk} -group {sl12_async_vclk} \
    -group {sl13_clk $sl13_l1arc_hs_gclocks sl13_gtoa_half_gclk} -group {sl13_wdt_clk} -group {sl13_async_vclk} \
    -group {sl14_clk $sl14_l1arc_hs_gclocks sl14_gtoa_half_gclk} -group {sl14_wdt_clk} -group {sl14_async_vclk} \
    -group {sl15_clk $sl15_l1arc_hs_gclocks sl15_gtoa_half_gclk} -group {sl15_wdt_clk} -group {sl15_async_vclk} \
    -group {nl2arc0_wdt_clk} -group {nl2arc1_wdt_clk} -group {npu_noc_clk} -group {npu_cfg_clk} \
"
} else {
set scg_cmd "set_clock_groups -asynchronous -allow_paths -group {$ncore_clock_name $l2arc0_hs_gclocks $l2arc1_hs_gclocks $dbank_gclocks} -group {$apb_clock_name}  \
    -group {sl0_clk $sl0_l1arc_hs_gclocks sl0_gtoa_half_gclk} -group {sl0_wdt_clk} \
    -group {sl1_clk $sl1_l1arc_hs_gclocks sl1_gtoa_half_gclk} -group {sl1_wdt_clk} \
    -group {sl2_clk $sl2_l1arc_hs_gclocks sl2_gtoa_half_gclk} -group {sl2_wdt_clk} \
    -group {sl3_clk $sl3_l1arc_hs_gclocks sl3_gtoa_half_gclk} -group {sl3_wdt_clk} \
    -group {sl4_clk $sl4_l1arc_hs_gclocks sl4_gtoa_half_gclk} -group {sl4_wdt_clk} \
    -group {sl5_clk $sl5_l1arc_hs_gclocks sl5_gtoa_half_gclk} -group {sl5_wdt_clk} \
    -group {sl6_clk $sl6_l1arc_hs_gclocks sl6_gtoa_half_gclk} -group {sl6_wdt_clk} \
    -group {sl7_clk $sl7_l1arc_hs_gclocks sl7_gtoa_half_gclk} -group {sl7_wdt_clk} \
    -group {sl8_clk $sl8_l1arc_hs_gclocks sl8_gtoa_half_gclk} -group {sl8_wdt_clk} \
    -group {sl9_clk $sl9_l1arc_hs_gclocks sl9_gtoa_half_gclk} -group {sl9_wdt_clk} \
    -group {sl10_clk $sl10_l1arc_hs_gclocks sl10_gtoa_half_gclk} -group {sl10_wdt_clk} \
    -group {sl11_clk $sl11_l1arc_hs_gclocks sl11_gtoa_half_gclk} -group {sl11_wdt_clk} \
    -group {sl12_clk $sl12_l1arc_hs_gclocks sl12_gtoa_half_gclk} -group {sl12_wdt_clk} \
    -group {sl13_clk $sl13_l1arc_hs_gclocks sl13_gtoa_half_gclk} -group {sl13_wdt_clk} \
    -group {sl14_clk $sl14_l1arc_hs_gclocks sl14_gtoa_half_gclk} -group {sl14_wdt_clk} \
    -group {sl15_clk $sl15_l1arc_hs_gclocks sl15_gtoa_half_gclk} -group {sl15_wdt_clk} \
    -group {nl2arc0_wdt_clk} -group {nl2arc1_wdt_clk} -group {npu_noc_clk} -group {npu_cfg_clk} \
"
}

echo $scg_cmd
eval $scg_cmd



if {"$npu_lint_virt_clk" eq "0"} {
  set apb_reset     [get_ports presetdbgn -filter {@port_direction == in}]
  set_input_delay [expr 0.25 * ${apb_clock_per}] -clock ${apb_clock_obj}   ${apb_reset}
}
set_input_delay [expr 0.25 * ${apb_clock_per}] -clock ${apb_clock_obj} [get_ports arct0_p* -filter {@port_direction == in}]

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


set_output_delay [expr 0.25 * ${apb_clock_per}]   -clock ${apb_clock_obj} [get_ports arct0_* -filter {@port_direction == out}]


#------------------------------------------------------------------------------
# Max Delay Paths
#------------------------------------------------------------------------------


## GALS wires paths
## NPU slice 0 max_delay should be constraints to Teff = "MIN(sl0_clk_period, npu_core_clk_period) - clock_uncertainty"
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl0nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl0nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl0nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl0nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl0nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl0nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl0nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl0nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl0nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl0nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl0nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl0nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## APB async wires paths
## NPU slice 0 APB max_delay should be constraints to Teff = "MIN(apb_clk_period, npu_core_clk_period) - clock_uncertainty"
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl0nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl0nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl0nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl0nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl0nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl0nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl0nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl0nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]

## SWE paths (Pulse + data)
## NPU slice 0 max_delay should be constraints to Teff = "MIN(sl0_clk_period, npu_core_clk_period) - clock_uncertainty"
## overwrite swe interface constraint to set_max/min_delay, this is harmless and expected. swe is using the qualifier based cdc scheme.
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*u_npu_core/sl0_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*u_npu_core/sl0_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl0_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl0_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl0_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl0_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]


## GALS wires paths
## NPU slice 1 max_delay should be constraints to Teff = "MIN(sl1_clk_period, npu_core_clk_period) - clock_uncertainty"
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl1nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl1nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl1nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl1nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl1nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl1nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl1nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl1nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl1nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl1nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl1nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl1nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## APB async wires paths
## NPU slice 1 APB max_delay should be constraints to Teff = "MIN(apb_clk_period, npu_core_clk_period) - clock_uncertainty"
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl1nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl1nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl1nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl1nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl1nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl1nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl1nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl1nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]

## SWE paths (Pulse + data)
## NPU slice 1 max_delay should be constraints to Teff = "MIN(sl1_clk_period, npu_core_clk_period) - clock_uncertainty"
## overwrite swe interface constraint to set_max/min_delay, this is harmless and expected. swe is using the qualifier based cdc scheme.
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*u_npu_core/sl1_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*u_npu_core/sl1_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl1_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl1_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl1_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl1_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]


## GALS wires paths
## NPU slice 2 max_delay should be constraints to Teff = "MIN(sl2_clk_period, npu_core_clk_period) - clock_uncertainty"
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl2nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl2nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl2nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl2nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl2nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl2nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl2nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl2nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl2nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl2nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl2nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl2nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## APB async wires paths
## NPU slice 2 APB max_delay should be constraints to Teff = "MIN(apb_clk_period, npu_core_clk_period) - clock_uncertainty"
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl2nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl2nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl2nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl2nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl2nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl2nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl2nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl2nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]

## SWE paths (Pulse + data)
## NPU slice 2 max_delay should be constraints to Teff = "MIN(sl2_clk_period, npu_core_clk_period) - clock_uncertainty"
## overwrite swe interface constraint to set_max/min_delay, this is harmless and expected. swe is using the qualifier based cdc scheme.
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*u_npu_core/sl2_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*u_npu_core/sl2_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl2_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl2_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl2_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl2_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]


## GALS wires paths
## NPU slice 3 max_delay should be constraints to Teff = "MIN(sl3_clk_period, npu_core_clk_period) - clock_uncertainty"
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl3nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl3nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl3nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl3nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl3nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl3nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl3nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl3nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl3nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl3nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl3nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl3nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## APB async wires paths
## NPU slice 3 APB max_delay should be constraints to Teff = "MIN(apb_clk_period, npu_core_clk_period) - clock_uncertainty"
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl3nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl3nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl3nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl3nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl3nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl3nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl3nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl3nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]

## SWE paths (Pulse + data)
## NPU slice 3 max_delay should be constraints to Teff = "MIN(sl3_clk_period, npu_core_clk_period) - clock_uncertainty"
## overwrite swe interface constraint to set_max/min_delay, this is harmless and expected. swe is using the qualifier based cdc scheme.
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*u_npu_core/sl3_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*u_npu_core/sl3_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl3_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl3_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl3_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl3_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]


## GALS wires paths
## NPU slice 4 max_delay should be constraints to Teff = "MIN(sl4_clk_period, npu_core_clk_period) - clock_uncertainty"
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl4nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl4nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl4nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl4nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl4nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl4nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl4nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl4nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl4nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl4nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl4nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl4nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## APB async wires paths
## NPU slice 4 APB max_delay should be constraints to Teff = "MIN(apb_clk_period, npu_core_clk_period) - clock_uncertainty"
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl4nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl4nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl4nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl4nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl4nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl4nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl4nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl4nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]

## SWE paths (Pulse + data)
## NPU slice 4 max_delay should be constraints to Teff = "MIN(sl4_clk_period, npu_core_clk_period) - clock_uncertainty"
## overwrite swe interface constraint to set_max/min_delay, this is harmless and expected. swe is using the qualifier based cdc scheme.
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*u_npu_core/sl4_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*u_npu_core/sl4_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl4_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl4_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl4_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl4_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]


## GALS wires paths
## NPU slice 5 max_delay should be constraints to Teff = "MIN(sl5_clk_period, npu_core_clk_period) - clock_uncertainty"
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl5nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl5nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl5nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl5nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl5nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl5nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl5nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl5nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl5nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl5nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl5nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl5nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## APB async wires paths
## NPU slice 5 APB max_delay should be constraints to Teff = "MIN(apb_clk_period, npu_core_clk_period) - clock_uncertainty"
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl5nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl5nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl5nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl5nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl5nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl5nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl5nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl5nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]

## SWE paths (Pulse + data)
## NPU slice 5 max_delay should be constraints to Teff = "MIN(sl5_clk_period, npu_core_clk_period) - clock_uncertainty"
## overwrite swe interface constraint to set_max/min_delay, this is harmless and expected. swe is using the qualifier based cdc scheme.
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*u_npu_core/sl5_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*u_npu_core/sl5_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl5_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl5_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl5_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl5_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]


## GALS wires paths
## NPU slice 6 max_delay should be constraints to Teff = "MIN(sl6_clk_period, npu_core_clk_period) - clock_uncertainty"
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl6nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl6nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl6nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl6nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl6nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl6nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl6nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl6nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl6nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl6nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl6nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl6nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## APB async wires paths
## NPU slice 6 APB max_delay should be constraints to Teff = "MIN(apb_clk_period, npu_core_clk_period) - clock_uncertainty"
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl6nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl6nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl6nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl6nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl6nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl6nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl6nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl6nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]

## SWE paths (Pulse + data)
## NPU slice 6 max_delay should be constraints to Teff = "MIN(sl6_clk_period, npu_core_clk_period) - clock_uncertainty"
## overwrite swe interface constraint to set_max/min_delay, this is harmless and expected. swe is using the qualifier based cdc scheme.
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*u_npu_core/sl6_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*u_npu_core/sl6_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl6_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl6_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl6_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl6_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]


## GALS wires paths
## NPU slice 7 max_delay should be constraints to Teff = "MIN(sl7_clk_period, npu_core_clk_period) - clock_uncertainty"
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl7nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl7nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl7nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl7nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl7nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl7nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl7nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl7nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl7nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl7nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl7nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl7nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## APB async wires paths
## NPU slice 7 APB max_delay should be constraints to Teff = "MIN(apb_clk_period, npu_core_clk_period) - clock_uncertainty"
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl7nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl7nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl7nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl7nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl7nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl7nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl7nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl7nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]

## SWE paths (Pulse + data)
## NPU slice 7 max_delay should be constraints to Teff = "MIN(sl7_clk_period, npu_core_clk_period) - clock_uncertainty"
## overwrite swe interface constraint to set_max/min_delay, this is harmless and expected. swe is using the qualifier based cdc scheme.
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*u_npu_core/sl7_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*u_npu_core/sl7_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl7_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl7_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl7_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl7_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]


## GALS wires paths
## NPU slice 8 max_delay should be constraints to Teff = "MIN(sl8_clk_period, npu_core_clk_period) - clock_uncertainty"
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl8nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl8nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl8nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl8nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl8nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl8nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl8nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl8nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl8nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl8nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl8nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl8nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## APB async wires paths
## NPU slice 8 APB max_delay should be constraints to Teff = "MIN(apb_clk_period, npu_core_clk_period) - clock_uncertainty"
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl8nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl8nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl8nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl8nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl8nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl8nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl8nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl8nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]

## SWE paths (Pulse + data)
## NPU slice 8 max_delay should be constraints to Teff = "MIN(sl8_clk_period, npu_core_clk_period) - clock_uncertainty"
## overwrite swe interface constraint to set_max/min_delay, this is harmless and expected. swe is using the qualifier based cdc scheme.
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*u_npu_core/sl8_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*u_npu_core/sl8_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl8_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl8_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl8_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl8_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]


## GALS wires paths
## NPU slice 9 max_delay should be constraints to Teff = "MIN(sl9_clk_period, npu_core_clk_period) - clock_uncertainty"
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl9nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl9nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl9nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl9nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl9nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl9nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl9nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl9nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl9nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl9nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl9nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl9nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## APB async wires paths
## NPU slice 9 APB max_delay should be constraints to Teff = "MIN(apb_clk_period, npu_core_clk_period) - clock_uncertainty"
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl9nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl9nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl9nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl9nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl9nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl9nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl9nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl9nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]

## SWE paths (Pulse + data)
## NPU slice 9 max_delay should be constraints to Teff = "MIN(sl9_clk_period, npu_core_clk_period) - clock_uncertainty"
## overwrite swe interface constraint to set_max/min_delay, this is harmless and expected. swe is using the qualifier based cdc scheme.
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*u_npu_core/sl9_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*u_npu_core/sl9_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl9_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl9_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl9_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl9_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]


## GALS wires paths
## NPU slice 10 max_delay should be constraints to Teff = "MIN(sl10_clk_period, npu_core_clk_period) - clock_uncertainty"
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl10nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl10nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl10nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl10nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl10nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl10nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl10nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl10nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl10nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl10nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl10nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl10nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## APB async wires paths
## NPU slice 10 APB max_delay should be constraints to Teff = "MIN(apb_clk_period, npu_core_clk_period) - clock_uncertainty"
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl10nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl10nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl10nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl10nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl10nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl10nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl10nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl10nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]

## SWE paths (Pulse + data)
## NPU slice 10 max_delay should be constraints to Teff = "MIN(sl10_clk_period, npu_core_clk_period) - clock_uncertainty"
## overwrite swe interface constraint to set_max/min_delay, this is harmless and expected. swe is using the qualifier based cdc scheme.
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*u_npu_core/sl10_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*u_npu_core/sl10_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl10_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl10_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl10_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl10_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]


## GALS wires paths
## NPU slice 11 max_delay should be constraints to Teff = "MIN(sl11_clk_period, npu_core_clk_period) - clock_uncertainty"
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl11nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl11nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl11nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl11nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl11nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl11nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl11nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl11nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl11nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl11nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl11nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl11nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## APB async wires paths
## NPU slice 11 APB max_delay should be constraints to Teff = "MIN(apb_clk_period, npu_core_clk_period) - clock_uncertainty"
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl11nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl11nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl11nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl11nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl11nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl11nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl11nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl11nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]

## SWE paths (Pulse + data)
## NPU slice 11 max_delay should be constraints to Teff = "MIN(sl11_clk_period, npu_core_clk_period) - clock_uncertainty"
## overwrite swe interface constraint to set_max/min_delay, this is harmless and expected. swe is using the qualifier based cdc scheme.
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*u_npu_core/sl11_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*u_npu_core/sl11_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl11_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl11_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl11_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl11_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]


## GALS wires paths
## NPU slice 12 max_delay should be constraints to Teff = "MIN(sl12_clk_period, npu_core_clk_period) - clock_uncertainty"
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl12nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl12nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl12nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl12nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl12nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl12nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl12nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl12nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl12nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl12nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl12nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl12nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## APB async wires paths
## NPU slice 12 APB max_delay should be constraints to Teff = "MIN(apb_clk_period, npu_core_clk_period) - clock_uncertainty"
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl12nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl12nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl12nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl12nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl12nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl12nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl12nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl12nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]

## SWE paths (Pulse + data)
## NPU slice 12 max_delay should be constraints to Teff = "MIN(sl12_clk_period, npu_core_clk_period) - clock_uncertainty"
## overwrite swe interface constraint to set_max/min_delay, this is harmless and expected. swe is using the qualifier based cdc scheme.
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*u_npu_core/sl12_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*u_npu_core/sl12_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl12_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl12_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl12_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl12_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]


## GALS wires paths
## NPU slice 13 max_delay should be constraints to Teff = "MIN(sl13_clk_period, npu_core_clk_period) - clock_uncertainty"
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl13nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl13nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl13nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl13nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl13nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl13nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl13nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl13nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl13nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl13nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl13nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl13nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## APB async wires paths
## NPU slice 13 APB max_delay should be constraints to Teff = "MIN(apb_clk_period, npu_core_clk_period) - clock_uncertainty"
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl13nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl13nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl13nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl13nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl13nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl13nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl13nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl13nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]

## SWE paths (Pulse + data)
## NPU slice 13 max_delay should be constraints to Teff = "MIN(sl13_clk_period, npu_core_clk_period) - clock_uncertainty"
## overwrite swe interface constraint to set_max/min_delay, this is harmless and expected. swe is using the qualifier based cdc scheme.
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*u_npu_core/sl13_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*u_npu_core/sl13_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl13_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl13_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl13_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl13_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]


## GALS wires paths
## NPU slice 14 max_delay should be constraints to Teff = "MIN(sl14_clk_period, npu_core_clk_period) - clock_uncertainty"
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl14nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl14nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl14nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl14nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl14nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl14nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl14nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl14nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl14nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl14nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl14nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl14nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## APB async wires paths
## NPU slice 14 APB max_delay should be constraints to Teff = "MIN(apb_clk_period, npu_core_clk_period) - clock_uncertainty"
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl14nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl14nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl14nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl14nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl14nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl14nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl14nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl14nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]

## SWE paths (Pulse + data)
## NPU slice 14 max_delay should be constraints to Teff = "MIN(sl14_clk_period, npu_core_clk_period) - clock_uncertainty"
## overwrite swe interface constraint to set_max/min_delay, this is harmless and expected. swe is using the qualifier based cdc scheme.
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*u_npu_core/sl14_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*u_npu_core/sl14_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl14_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl14_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl14_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl14_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]


## GALS wires paths
## NPU slice 15 max_delay should be constraints to Teff = "MIN(sl15_clk_period, npu_core_clk_period) - clock_uncertainty"
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl15nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl15nl1arc_dev_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl15nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl15nl1arc_dev_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl15nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl15nl1arc_dev_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl15nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl15nl1arc_ccm_axi_gals_*rpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}                              -through [get_pins {*sl15nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl15nl1arc_ccm_axi_gals_*wpnt*} -hier -filter "@full_name=~*u_npu_core*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl15nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_npu_core* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*sl15nl1arc_ccm_axi_gals_*data*} -hier -filter "@full_name=~*u_npu_core*"]

## APB async wires paths
## NPU slice 15 APB max_delay should be constraints to Teff = "MIN(apb_clk_period, npu_core_clk_period) - clock_uncertainty"
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl15nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl15nl1arc_dbg_req*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*sl15nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*sl15nl1arc_dbg_ack*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl15nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl15nl1arc_dbg_presp*} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*sl15nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*sl15nl1arc_dbg_pcmd*} -hier -filter  "@full_name=~*u_npu_core*"]

## SWE paths (Pulse + data)
## NPU slice 15 max_delay should be constraints to Teff = "MIN(sl15_clk_period, npu_core_clk_period) - clock_uncertainty"
## overwrite swe interface constraint to set_max/min_delay, this is harmless and expected. swe is using the qualifier based cdc scheme.
set_max_delay -ignore_clock_latency ${ncore_clock_Teff}  -through [get_pins {*u_npu_core/sl15_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                    -through [get_pins {*u_npu_core/sl15_rtt_swe_val} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl15_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl15_rtt_swe_data} -hier -filter  "@full_name=~*u_npu_core*"]
set_max_delay -ignore_clock_latency [expr 1.5*${ncore_clock_per} - ${clk_unc_setup}] -through [get_pins {*u_npu_core/sl15_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]
set_min_delay -ignore_clock_latency 0                                                -through [get_pins {*u_npu_core/sl15_rtt_swe_ext}  -hier -filter  "@full_name=~*u_npu_core*"]

#------------------------------------------------------------------------------
# False Paths
#------------------------------------------------------------------------------
## The following 3 false_path are duplicated, they have no side-effects
set_false_path -from   [get_ports *isolate*  -filter {@port_direction == in}]
set_false_path -from   [get_ports *pd_mem*   -filter {@port_direction == in}]
set_false_path -from   [get_ports *pd_logic* -filter {@port_direction == in}]
set_false_path -from   [get_ports *presetdbgn*       -filter {@port_direction == in}]
set_false_path -to     [get_ports *sys_sleep_mode_r* -filter {@port_direction == out}]
set_false_path -to     [get_ports *wdt_reset_error   -filter {@port_direction == out}]
set_false_path -to     [get_ports *arc_halt_ack      -filter {@port_direction == out}]
set_false_path -to     [get_ports *sys_halt_r        -filter {@port_direction == out}]
set_false_path -to     [get_ports *evt_vm_irq        -filter {@port_direction == out}]
set_false_path -to     [get_ports *sys_sleep_r       -filter {@port_direction == out}]
set_false_path -to     [get_ports *sys_tf_halt_r     -filter {@port_direction == out}]
set_false_path -to     [get_ports *arc_run_ack       -filter {@port_direction == out}]
set_false_path -through [get_pin {*arct_dbg_prot_sel}  -hier -filter "@full_name=~*u_npu_core*"]

# -----------------------------------------------------------------------------
# Source synchronous data_check
# -----------------------------------------------------------------------------



# -----------------------------------------------------------------------------
# Case analysis
# -----------------------------------------------------------------------------
set_case_analysis 0 [get_ports test_mode]

