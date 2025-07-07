alias   mkcd            'mkdir -p \!* ; cd \!*'
setenv date_var `date +%m%d_%H%M`

source verif/regrs/cct_regr_lsf/generate_sfty_tb.csh

module unload python
module load python/3.9.0

make -C build compile TB_PDM=0 CCT_INT=1 COV_EN=1 VCS_USER_OPTS+=+define+SFTY_ERR_INJ_ON VCS_USER_OPTS+=+define+SAFETY_AUX_ENABLE 
source $NPU_HOME/verif/regrs/cct_regr_lsf/regression.csh $NPU_HOME/verif/regrs/cct_regr_lsf/regr_setup $NPU_HOME/verif/regrs/cct_regr/setup_testlist/aux_cct/master_list.lst 
#$NPU_HOME/verif/regrs/run_npu_tests.sh -l $NPU_HOME/verif/tests/aux_st.list -c -g 1 -f > & ! txt &
#sleep 20m
#setenv jobnum `bjobs | grep sim|wc -l`
#while ( $jobnum > 0)
#    setenv jobnum `bjobs | grep sim|wc -l`
#    echo "$jobnum Jobs still running"
#    sleep 20m
#end
#
#
#mkcd ../coverage/
#urg -dir $NPU_HOME/build/sim/simv.vdb  -parallel -dbname $date_var
#rm -rf $NPU_HOME/build/sim/simv.vdb
#cd $NPU_HOME
