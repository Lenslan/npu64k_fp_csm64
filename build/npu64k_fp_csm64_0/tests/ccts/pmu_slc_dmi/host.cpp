#include "host_utils.hpp"

#ifdef __cplusplus
extern "C" {
#endif

HOST_EXEC() {
  int err_cnt = 0; 
 // arcsync_core_rst_assert_all();
  set_expect_resp(0);
  //if (ARCSYNC_PMU_RESET_PMODE){
  //    l2grp_power_up_all(0/*cluster_id*/);
  //    l1grp_power_up_all(0/*cluster_id*/);
  //    slc_power_up_all(0/*cluster_id*/);
  //}
  arcsync_core_rst_dessert_all(0/*cluster id*/); 
  set_intvect(0/*cluster_id*/);  
  config_npx_sys_map_all();
  config_pmu_count(0/*cluster id*/);
  //do something and update err_cnt
 // arcsync_get_core_status((int)0); 
  // host exit the simulator
 core_run_all(0/*cluster_id*/);
 host_wait(100);
 for (int i=1; i<NPU_SLICE_NUM+1; i++) {
    core_dm_ldst(0/*cluster_id*/, i/*core_id*/); 
 }
 host_wait(100);  

 for (int i=1; i<NPU_SLICE_NUM+1; i++) {
    disable_core_clk(0/*cluster_id*/, i/*core_id*/);
 }
 slc_power_down_all(0/*cluster_id*/);

  
 set_expect_resp(2);
 // DMI ACCESS HERE
 for (int i=1; i<NPU_SLICE_NUM+1; i++) {  
    core_dm_ldst(0/*cluster_id*/, i/*core_id*/);
 }
 
 
 set_expect_resp(0);
 slc_power_up_all(0/*cluster_id*/);
 for (int i=1; i<NPU_SLICE_NUM+1; i++) {  
    enable_core_clk(0/*cluster_id*/, i/*core_id*/); 
 }

 slc_run_all(0/*cluster_id*/);
 
 for (int i=1; i<NPU_SLICE_NUM+1; i++) {   
    core_dm_ldst(0/*cluster_id*/, i/*core_id*/); 
 }
 
 host_exit(err_cnt);
  

 HOST_EXEC_RET;
}

#ifdef __cplusplus
}
#endif

