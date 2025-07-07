#include "npu_config.hpp"
#include "host_utils.hpp"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_LINE_LENGTH 256

#ifdef __cplusplus
extern "C" {
#endif

HOST_EXEC() {

    char filename[] = "vcs_run.opt";
    char line[MAX_LINE_LENGTH];
    FILE *file;
    int found_l2_arc = 0;
    int found_l1_arc_all = 0;

    file = fopen(filename, "r");
    if (file == NULL) {
        printf("Error: Unable to open the file!\n");
        exit(EXIT_FAILURE);
    }

    while (fgets(line, MAX_LINE_LENGTH, file) != NULL) {
		if (strstr(line, "+RUN_L2_ARC=") != NULL) {
			cout << "found +RUN_L2_ARC " << endl;
            found_l2_arc = 1;
        }
		if (strstr(line, "+RUN_L1_ALL") != NULL) {
			cout << "found +RUN_L1_ALL " << endl;
            found_l1_arc_all = 1;
        }

    }

    fclose(file);

//=====================================
//   Boot NPX start here
//=====================================

  //powerup npx if needed
  //if (ARCSYNC_HAS_PMU && ARCSYNC_PMU_RESET_PMODE){
  //    l2grp_power_up_all(0/*cluster_id*/);
  //    l1grp_power_up_all(0/*cluster_id*/);
  //    slc_power_up_all(0/*cluster_id*/);
  //}

  //Init System
  int err_cnt = 0; 
  set_intvect(0/*cluster_id*/);
  arcsync_core_rst_dessert_all(0/*cluster id*/); 
  if (NPU_HAS_L2ARC == 1) {
     config_npx_sys_map_all();
  }
  else {
     //NPU1K w/o CSM don't need to config system
     set_sys_cfg_done();
  }
  //Core Run
  if (found_l2_arc && (NPU_HAS_L2ARC == 1)) {
     core_run(0/*cluster_id*/, 0);
  }
  if (found_l1_arc_all) {
	 for(int i=1; i<NPU_SLICE_NUM+1; i++)  {
        core_run(0/*cluster_id*/, i);		 
	}
  }
  
  //do something and update err_cnt

  // host exit the simulator
  host_exit(err_cnt);

  //host_terminate_sim();

  HOST_EXEC_RET;
}

#ifdef __cplusplus
}
#endif

