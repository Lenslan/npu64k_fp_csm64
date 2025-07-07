#!/bin/bash -e
#usgae : check_sim_result.sh <sim_sim_log_file>

mydir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
sim_log=${1:-"simv.log"}

err_cnt=0
uvm_err=0
uvm_ftl=0
ast_err=0
arc_err=0
host_err=0
to_err=0
run_end=0


. $mydir/log_utils.sh

function log_result(){
    echo "****************************"
    if [ $err_cnt -eq 0 ]; then
        echo "| Simulation is passed |"
    else
        [ $uvm_err == 0 ] || echo "*** $uvm_err uvm_error(s) found ***"
        [ $uvm_ftl == 0 ] || echo "*** $uvm_ftl uvm_fatal(s) found ***"
        [ $ast_err == 0 ] || echo "*** $ast_err ast_error(s) found ***"
        echo "*** Simulation is failed ***"
    fi
    echo "****************************"
}
  #   [ $to_err  == 0 ] || echo "*** simulation time out  ***"
     #   [ $host_err == 0 ] || echo "*** $host_err host_error(s) found ***"
     #   [ $arc_err == 0 ] || echo "*** $arc_err arc_error(s) found ***"
  #   [ $run_end == 0 ] && echo "*** not fund host/arc run to end ***"


#check host program run 
#function chk_host_flag {
#    host_err=$(grep -c "Host run with error" $sim_log)
#    err_cnt=$((host_err+err_cnt))
#}


#check ARC core program run 
#function chk_arc_flag {
#    arc_err=$(grep -c "ARC run with error" $sim_log)
#    err_cnt=$((arc_err+err_cnt))
#}

#check time out 
#function chk_timeout {
#    to_err=$(grep -c "Simulation finishes becasue it reachs the max cycle" $sim_log)
#    err_cnt=$((to_err+err_cnt))
#}

#check UVM errors
function chk_uvm_error {
    uvm_err=$(grep "UVM_ERROR" $sim_log | grep -v ":    0" | grep -c "UVM_ERROR")
    err_cnt=$((uvm_err+err_cnt))
}
#check UVM fatals
function chk_uvm_fatal {
    uvm_ftl=$(grep "UVM_FATAL" $sim_log | grep -v ":    0" | grep -c "UVM_FATAL" )
    err_cnt=$((uvm_ftl+err_cnt))
}
#check assertion error
function chk_assert_error {
    ast_err=$(grep -c "started at.*failed at\|assertion error" $sim_log)
    err_cnt=$((ast_err+err_cnt))
}
#check host/arc run flag
function chk_run_end {
   # arc_run_end=$(grep -c "ARC run successfully" $sim_log)
   # hst_run_end=$(grep -c "Host run successfully" $sim_log)
   # dpi_run_end=$(grep -c "Program exits simulator" $sim_log)
   # uvm_run_end=$(grep -c "finish called from file.*uvm_root.svh" $sim_log)
   # tb_finish_call_end=$(grep -c "HAPPY ran successfully" $sim_log)
   # if [[ $arc_run_end -eq 0 && $hst_run_end -eq 0  && $dpi_run_end -eq 0 && $uvm_run_end -eq 0 && $tb_finish_call_end -eq 0 ]]; then
    #    err_cnt=$((err_cnt+1))
    #else
        run_end=1
    #fi
}

chk_file $sim_log

set +e
chk_host_flag
chk_arc_flag
chk_timeout
chk_uvm_error
chk_uvm_fatal
chk_assert_error
chk_run_end
set -e

log_result
exit $err_cnt

