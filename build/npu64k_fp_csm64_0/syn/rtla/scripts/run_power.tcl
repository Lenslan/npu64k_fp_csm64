puts "Info: Running script [info script]\n"

source -echo ./setup/setup.tcl

set_user_units -type power -value 1W

###############################################################################
# Read project
###############################################################################

open_lib -read ${WORK_DIR}/${DESIGN_NAME}.dlib
open_block -read ${DESIGN_NAME}.design
link

###############################################################################
# Compute power
###############################################################################
set TESTS_PATH "$::env(NPU_HOME_RLS)/verif/tests"
set TEST_NAMES [list "npu_idle_pwr" "npu_conv_1x1_pwr" "npu_conv_1x1_pwr_inn" "npu_conv_1x1_pwr_onn" "npu_fused_pwr"]
#set TEST_NAMES [list "npu_idle_pwr" "npu_conv_1x1_pwr" "npu_conv_1x1_pwr_inn" "npu_conv_1x1_pwr_onn" "npu_conv_3x3_pwr" "npu_fused_pwr"]
if { [info exists ::env(RTLA_PWR_CCT_PATH)] } {
    set TESTS_PATH $::env(RTLA_PWR_CCT_PATH)
}
if { [info exists ::env(RTLA_PWR_CCTS)] } {
    set TEST_LIST [regexp -all -inline {\S+} $::env(RTLA_PWR_CCTS)]
	set TEST_NAMES [split ${TEST_LIST} ","]
}

if { ${DESIGN_NAME} == "npu_slice_top" || ${DESIGN_NAME} == "npu_slice_top_int" } {
    set STRIP_PATH "npu_tb_top/icore_chip/icore_sys/icore_archipelago/inpu_top/u_l1core0"
} elseif { ${DESIGN_NAME} == "npu_core" } {
    set STRIP_PATH "npu_tb_top/icore_chip/icore_sys/icore_archipelago/inpu_top/u_npu_core"
} elseif { ${DESIGN_NAME} == "npu_top" } {
    set STRIP_PATH "npu_tb_top/icore_chip/icore_sys/icore_archipelago/inpu_top"
} else {
    set STRIP_PATH ""
}

puts "Info: TESTS_PATH = $TESTS_PATH"
puts "Info: TEST_NAMES = $TEST_NAMES"
puts "Info: STRIP_PATH = $STRIP_PATH"


current_scenario functional::typ
set run_vectorless 1
foreach test $TEST_NAMES {
    set ACTIVITY_PATH $TESTS_PATH/$test/power.saif.gz
    #set ACTIVITY_PATH $TESTS_PATH/$test/power.fsdb
    puts "Checking file: $ACTIVITY_PATH"
    if {[file exist $ACTIVITY_PATH]} {
        echo "Running power analisys for: $test"
        set_rtl_power_analysis_options -pwr_shell $PWR_SHELL -saif $ACTIVITY_PATH -strip_path $STRIP_PATH
        #set_rtl_power_analysis_options -pwr_shell $PWR_SHELL -fsdb $ACTIVITY_PATH -strip_path $STRIP_PATH
        set_rtl_power_analysis_options -postcmds "redirect -tee -file ${rptpfx}.$test.activity.rpt {report_switching_activity}"
        compute_metrics -power
        redirect -tee -file ${rptpfx}.$test.power.metrics.rpt     {report_metrics -power -scenarios functional::typ}
        redirect      -file ${rptpfx}.$test.power.rpt             {report_power -scenarios functional::typ}
        redirect      -file ${rptpfx}.$test.power.hierarchy.rpt   {report_power -nosplit -hierarchy -scenarios functional::typ}
        redirect      -file ${rptpfx}.$test.gating_efficiency.rpt {report_clock_gating_metrics -sortby rtl_reg_gating_efficiency}
        set run_vectorless 0
    }
}
if {$run_vectorless} {
    set_rtl_power_analysis_options -pwr_shell $PWR_SHELL -postcmds "redirect -tee -file ${rptpfx}.default.activity.rpt {report_switching_activity}"
    compute_metrics -power
    redirect -tee -file ${rptpfx}.default.power.metrics.rpt   {report_metrics -power -scenarios functional::typ}
    redirect      -file ${rptpfx}.default.power.rpt           {report_power -scenarios functional::typ}
    redirect      -file ${rptpfx}.default.power.hierarchy.rpt {report_power -nosplit -hierarchy -scenarios functional::typ}
}

exit

