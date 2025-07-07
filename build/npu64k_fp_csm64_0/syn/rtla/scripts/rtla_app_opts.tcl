#############################################################################
#
# To disable latency calculation for clock gaters
#############################################################################
puts "INFO: RTLA_CTS=$RTLA_CTS"
if {${RTLA_CTS}} {
  puts "INFO: Enable RTLA clock synthesize"
  set_app_options -list { compile.clockgate.use_clock_latency true }
  set_app_options -list { compile.clockgate.physically_aware true }
  set_app_options -list { compile.clockgate.physically_aware_estimate_timing true }
  set_app_options -list { opt.common.estimate_clock_gate_latency true }
  set_app_options -list { compile.flow.enable_ccd true }
} else {
  puts "INFO: Disable RTLA clock synthesize"
  set_app_options -list { compile.clockgate.use_clock_latency false }
  set_app_options -list { compile.clockgate.physically_aware false }
  set_app_options -list { compile.clockgate.physically_aware_estimate_timing false }
  set_app_options -list { opt.common.estimate_clock_gate_latency false }
  set_app_options -list { compile.flow.enable_ccd false }
}

#############################################################################
#
# To disable auto ungrouping
#############################################################################
puts "INFO: RTLA_UNGROUP = $RTLA_UNGROUP"
if { ${RTLA_UNGROUP} } {
    set_app_options -name compile.datapath.ungroup -value true
    set_app_options -name compile.flow.autoungroup -value true
} else {
    set_app_options -name compile.datapath.ungroup -value false
    set_app_options -name compile.flow.autoungroup -value false
}

#############################################################################
#
# Stop RTL-A when SDC is not clean with following msgs
#############################################################################
# e.g.
#set_output_delay [expr 0.25 * ${slice_clock_per}] -clock ${slice_clock_obj} [get_ports *hssi_error -filter {@port_direction == out}]
#Error: Nothing matched for port_pin_list (SEL-005)
set_msg SEL-005 -level fatal

