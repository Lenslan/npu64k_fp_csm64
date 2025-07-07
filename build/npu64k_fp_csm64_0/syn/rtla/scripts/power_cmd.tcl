#set TESTS_PATH "/slowfs/us01dwslow023/zebu/dmontes/rtla/npu_top/npu/verif/tests"
#set TEST_NAMES [list "npu_idle_pwr" "npu_conv_1x1_pwr" "npu_conv_3x3_pwr" "npu_fused_pwr"]
#set STRIP_PATH "npu_tb_top/icore_chip/icore_sys/icore_archipelago/inpu_top"
#set PWR_SHELL  "/u/nwtnmgr/image/S-2021.06-PROD-SP1-SP2/latest/Testing/bin/pt_shell"
#set rptpfx "logs/npu_top"

set run_vectorless 1
foreach test $TEST_NAMES {
    set ACTIVITY_PATH $TESTS_PATH/$test/power.saif.gz
    #set ACTIVITY_PATH $TESTS_PATH/$test/power.fsdb
    puts "Checking for $ACTIVITY_PATH"
    if {[file exist $ACTIVITY_PATH]} {
        echo "Running power analisys for: $test"
        set_rtl_power_analysis_options -pwr_shell $PWR_SHELL -postcmds "report_switching_activity" -saif $ACTIVITY_PATH -strip_path $STRIP_PATH
        #set_rtl_power_analysis_options -pwr_shell $PWR_SHELL -postcmds "report_switching_activity" -fsdb $ACTIVITY_PATH -strip_path $STRIP_PATH
        compute_metrics -power
        redirect -tee -file ${rptpfx}.activity.$test.rpt          {report_activity -driver -verbose}
        redirect -tee -file ${rptpfx}.power.$test.rpt             {report_power -scenarios functional::typ}
        redirect      -file ${rptpfx}.power.$test.hierarchy.rpt   {report_power -nosplit -hierarchy -scenarios functional::typ}
        redirect      -file ${rptpfx}.gating_efficiency.$test.rpt {report_clock_gating_metrics -sortby rtl_reg_gating_efficiency}
        set run_vectorless 0
    }
}
if {$run_vectorless} {
    infer_switching_activity
    set_rtl_power_analysis_options -pwr_shell $PWR_SHELL -postcmds "report_switching_activity"
    compute_metrics -power
    redirect -tee -file ${rptpfx}.power.vectorless.rpt           {report_power -scenarios functional::typ}
    redirect      -file ${rptpfx}.power.vectorless.hierarchy.rpt {report_power -nosplit -hierarchy -scenarios functional::typ}
}
