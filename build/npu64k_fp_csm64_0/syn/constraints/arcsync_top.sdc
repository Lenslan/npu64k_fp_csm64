
###############################################################################
### DESIGN SPECIFIC PART
###############################################################################
set npu_lint_virt_clk 0
if { [info exists ::env(NPU_LINT_VIRT_CLK)] } {
    set npu_lint_virt_clk $::env(NPU_LINT_VIRT_CLK)
}

set CLOCK_FREQ           1000;  # MHz
if { [info exists env(CLOCK_FREQ)] } {
  set CLOCK_FREQ           $env(CLOCK_FREQ)
}
set CLK_NAME               "arcsync_clk"
set CLK_PORT_NAME          "arcsync_clk"
set CLK_A_NAME             "arcsync_axi_clk"
set CLK_A_PORT_NAME        "arcsync_axi_clk"
set RESET_NAME             "arcsync_rst_a"
set RESET_A_NAME           "arcsync_axi_rst_a"

set ALL_INPUTS_EXC_AXI  [remove_from_collection [all_inputs] [get_ports arcsync_axi_*]]
set ALL_INPUTS_EXC_CLK  [remove_from_collection $ALL_INPUTS_EXC_AXI [get_ports $CLK_PORT_NAME]]
set ALL_INPUTS_EXC_CLK_RES [remove_from_collection $ALL_INPUTS_EXC_CLK [get_ports $RESET_NAME]]

set ALL_INPUTS_AXI      [get_ports arcsync_axi_* -filter {@port_direction == in}]
set ALL_INPUTS_AXI_EXC_ACLK [remove_from_collection $ALL_INPUTS_AXI [get_ports $CLK_A_PORT_NAME]]
set ALL_INPUTS_AXI_EXC_ACLK_ARES [remove_from_collection $ALL_INPUTS_AXI_EXC_ACLK [get_ports $RESET_A_NAME]]

set ALL_OUTPUTS_CLK     [remove_from_collection [all_outputs] [get_ports arcsync_axi_*]]
set ALL_OUTPUTS_ACLK    [get_ports arcsync_axi_* -filter {@port_direction == out}]

###################################
### create clocks
###################################
set clock_cycle [expr 1000.0/${CLOCK_FREQ}]
create_clock -name $CLK_NAME -period ${clock_cycle} [get_ports $CLK_PORT_NAME]
set_drive 0 $CLK_NAME
set_clock_uncertainty -setup 0.200 $CLK_NAME
set_clock_uncertainty -hold  0.050 $CLK_NAME
set_clock_uncertainty -setup [expr 0.05 * ${clock_cycle}] -rise_from $CLK_NAME -fall_to $CLK_NAME
set_clock_uncertainty -setup [expr 0.05 * ${clock_cycle}] -fall_from $CLK_NAME -rise_to $CLK_NAME
set_clock_transition 0.1 $CLK_NAME
set_dont_touch_network $CLK_NAME
set main_clock_obj [get_clocks $CLK_NAME]

create_clock -name $CLK_A_NAME -period ${clock_cycle} [get_ports $CLK_A_PORT_NAME]
set_drive 0 $CLK_A_NAME
set_clock_uncertainty -setup 0.200 $CLK_A_NAME
set_clock_uncertainty -hold  0.050 $CLK_A_NAME
set_clock_uncertainty -setup [expr 0.05 * ${clock_cycle}] -rise_from $CLK_A_NAME -fall_to $CLK_A_NAME
set_clock_uncertainty -setup [expr 0.05 * ${clock_cycle}] -fall_from $CLK_A_NAME -rise_to $CLK_A_NAME
set_clock_transition 0.1 $CLK_A_NAME
set_dont_touch_network $CLK_A_NAME

if {"$npu_lint_virt_clk" ne "0"} {
  create_clock -name arcsync_async_vclk -period 1.000
  create_clock -name arcsync_axi_async_vclk -period 1.000
}

# group clk/inputs/outputs for better optimization:
group_path -name CLK -to $CLK_NAME
group_path -name INPUT -through [all_inputs]
group_path -name OUTPUTS -to [all_outputs]

###################################
#### reset input
###################################
# dont buffer reset net
set_ideal_network [get_ports $RESET_NAME]
set_ideal_network [get_ports $RESET_A_NAME]

###################################
### default delays for inputs/outputs
###################################
# default external delay on inputs/outputs: 33% clock cycle
set std_in_delay  [expr ${clock_cycle}/3]
set std_out_delay [expr ${clock_cycle}/3]

# default external delays on inputs driven by external registers: 20% clock cycle
set std_in_delay_reg [expr ${clock_cycle}*0.2]
# default external delay on registered outputs: 80% of clock cycle
set std_out_delay_reg [expr ${clock_cycle}*0.8]

# set default input/output delays for ALL ports except reset
if {"$npu_lint_virt_clk" eq "0"} {
  set_input_delay  ${std_in_delay}  -clock $CLK_NAME $ALL_INPUTS_EXC_CLK_RES
} else {
  set_input_delay  ${std_in_delay}  -clock arcsync_async_vclk $ALL_INPUTS_EXC_CLK_RES
}
set_input_delay  ${std_in_delay}  -clock $CLK_A_NAME $ALL_INPUTS_AXI_EXC_ACLK_ARES

set_output_delay ${std_out_delay} -clock $CLK_NAME $ALL_OUTPUTS_CLK
set_output_delay ${std_out_delay} -clock $CLK_A_NAME $ALL_OUTPUTS_ACLK

## Set reset input delay
if {"$npu_lint_virt_clk" eq "0"} {
  set_input_delay [expr 0.25 * ${clock_cycle}] -clock $CLK_NAME   $RESET_NAME
  set_input_delay [expr 0.25 * ${clock_cycle}] -clock $CLK_A_NAME $RESET_A_NAME
} else {
  set_input_delay [expr 0.25 * ${clock_cycle}] -clock arcsync_async_vclk     $RESET_NAME
  set_input_delay [expr 0.25 * ${clock_cycle}] -clock arcsync_axi_async_vclk $RESET_A_NAME
}

set ALL_NON_GEN_CLKS          [get_clocks * -filter {@is_generated == false}]
if {"$npu_lint_virt_clk" eq "0"} {
  set ALL_NON_GEN_CLKS_EXC_VIRT $ALL_NON_GEN_CLKS
} else {
  set ALL_NON_GEN_CLKS_EXC_VIRT [remove_from_collection $ALL_NON_GEN_CLKS          arcsync_async_vclk]
  set ALL_NON_GEN_CLKS_EXC_VIRT [remove_from_collection $ALL_NON_GEN_CLKS_EXC_VIRT arcsync_axi_async_vclk]
}
remove_input_delay [get_ports [get_object_name $ALL_NON_GEN_CLKS_EXC_VIRT]]
#remove_input_delay [get_ports [get_object_name [get_clocks * -filter {@is_generated == false}]]]

###################################
### clamp inputs
###################################
set_case_analysis 0 [get_ports test_mode]

###############################################################################
### TECHNOLOGY LIBRARY SPECIFIC PART
###############################################################################
if {![info exists TECHNOLOGY]} {
    set TECHNOLOGY undef
}
if {"$TECHNOLOGY" eq "07"} {
  set_driving_cell -lib_cell HDBSVT08_BUF_8 -pin X [get_ports * -filter {@port_direction == in}]
  remove_driving_cell [get_ports [get_object_name [get_clocks * -filter {@is_generated == false}]]]
} elseif {"$TECHNOLOGY" eq "12"} {
  set_driving_cell -lib_cell EDBSVT16_BUF_8 -pin X [get_ports * -filter {@port_direction == in}]
  remove_driving_cell [get_ports [get_object_name [get_clocks * -filter {@is_generated == false}]]]
} else {
  set_input_transition 0.1 [remove_from_collection [get_ports * -filter {@port_direction == in}] [get_ports [get_object_name $ALL_NON_GEN_CLKS_EXC_VIRT]]]
  #set_input_transition 0.1 [remove_from_collection [get_ports * -filter {@port_direction == in}] [get_ports [get_object_name [get_clocks * -filter {@is_generated == false}]]]]
}

###############################################################################
### set_clock_group -asynchronous
###############################################################################
puts "CLK_NAME=$CLK_NAME, CLK_A_NAME=$CLK_A_NAME"
###set_clock_groups -asynchronous -group {$CLK_NAME} -group {$CLK_A_NAME}
if {"$npu_lint_virt_clk" ne "0"} {
  set_clock_groups -asynchronous -allow_paths -group {arcsync_async_vclk} -group {arcsync_axi_async_vclk} -group { arcsync_clk } -group { arcsync_axi_clk }
} else {
  set_clock_groups -asynchronous -allow_paths -group { arcsync_clk } -group { arcsync_axi_clk }
}

###############################################################################
### set max delay and set min delay
###############################################################################
## Use accurate filters for read and write gray-coded pointers to not include any sync data paths
set_max_delay -ignore_clock_latency ${clock_cycle}            -through [get_pins {*axi_async_mst_*rpnt*} -hier -filter "@full_name=~*u_arcsync_async_bridge*u_arcsync_async_*"]
set_min_delay -ignore_clock_latency 0                         -through [get_pins {*axi_async_mst_*rpnt*} -hier -filter "@full_name=~*u_arcsync_async_bridge*u_arcsync_async_*"]
set_max_delay -ignore_clock_latency ${clock_cycle}            -through [get_pins {*axi_async_mst_*wpnt*} -hier -filter "@full_name=~*u_arcsync_async_bridge*u_arcsync_async_*"]
set_min_delay -ignore_clock_latency 0                         -through [get_pins {*axi_async_mst_*wpnt*} -hier -filter "@full_name=~*u_arcsync_async_bridge*u_arcsync_async_*"]
## Add constraints for async fifo data path for timing closure
# Note: If user observes PT speed issue due to is_integrated_clock_gating_cell attribute, user can replace it with a condition which removes all ICG(Inserted clock Gating) cells from the list
set_max_delay -ignore_clock_latency [expr 1.5*${clock_cycle}] -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_arcsync_async_bridge*u_arcsync_async_* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*axi_async_mst_*data*} -hier -filter "@full_name=~*u_arcsync_async_bridge*u_arcsync_async_*"]
set_min_delay -ignore_clock_latency 0                         -from [get_cells -hier *fifo_data_r* -filter "@full_name=~*u_arcsync_async_bridge*u_arcsync_async_* && @is_integrated_clock_gating_cell==false && @is_sequential==true"] -through [get_pins {*axi_async_mst_*data*} -hier -filter "@full_name=~*u_arcsync_async_bridge*u_arcsync_async_*"]

###############################################################################
### OTHER CONSTRAINTS
###############################################################################
# Use additional algorithms to pursuit better area through increased resource sharing:
#set compile_enhanced_resource_sharing false

set_false_path -from [get_ports $RESET_NAME] -through [get_pins -hier * -filter {@full_name=~*arcsync*reset_ctrl*sample_*}]
set_false_path -from [get_ports $RESET_A_NAME] -through [get_pins -hier * -filter {@full_name=~*arcsync*reset_ctrl*sample_*}]
set_false_path -through $ALL_INPUTS_EXC_AXI -through [get_pins -hier * -filter {@full_name=~*u_*cdc_sync*sample_*}]
