#
# Assume ${TECHNOLOGY}, ${DONT_USE_LIST} are pre-defined
#
if { ${TECHNOLOGY}=="07" } {
  #FIXME: this restricts slow ADDERS used(npu_conv_mpy_sum) according to PD team
  lappend DONT_USE_LIST */HDB*VT11_ADDABCD_V1Y2_1
  lappend DONT_USE_LIST */HDB*VT11_ADDABCD_V1Y2_2
} elseif {  ${TECHNOLOGY}=="12" } {
  puts "DONT_USE_LIST  => ${DONT_USE_LIST}"
} else {
  puts "DONT_USE_LIST  => ${DONT_USE_LIST}"
}
