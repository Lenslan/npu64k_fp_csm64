#include "host_utils.hpp"

#ifdef __cplusplus
extern "C" {
#endif

HOST_EXEC() {
  int err_cnt = 0; 
  set_intvect(0/*cluster_id*/);
  arcsync_core_rst_dessert_all(0/*cluster id*/); 
  config_npx_sys_map_all();
  core_run(0/*cluster_id*/, 0/*core_id*/);
  core_run(0/*cluster_id*/, 1/*core_id*/);
  

  host_exit(err_cnt);


  HOST_EXEC_RET;
}

#ifdef __cplusplus
}
#endif

