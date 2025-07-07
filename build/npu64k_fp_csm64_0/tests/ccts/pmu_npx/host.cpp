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

 slc_power_down_all(0/*cluster_id*/);
 l1grp_power_down_all(0/*cluster_id*/);
 l2grp_power_down_all(0/*cluster_id*/);
 
 
 host_wait(1000);
 
 l2grp_power_up_all(0/*cluster_id*/);
 l1grp_power_up_all(0/*cluster_id*/);
 slc_power_up_all(0/*cluster_id*/);

 config_npx_sys_map_all();

 core_run_all(0/*cluster_id*/);


 host_exit(err_cnt);
  

 HOST_EXEC_RET;
}

#ifdef __cplusplus
}
#endif

