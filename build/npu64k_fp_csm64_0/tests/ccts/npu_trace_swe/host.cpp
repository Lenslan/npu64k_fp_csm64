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
    int found_slc0_arc  = 0;
    int found_slc1_arc  = 0;
    int found_slc2_arc  = 0;
    int found_slc3_arc  = 0;
    int found_slc4_arc  = 0;
    int found_slc5_arc  = 0;
    int found_slc6_arc  = 0;
    int found_slc7_arc  = 0;
    int found_slc8_arc  = 0;
    int found_slc9_arc  = 0;
    int found_slc10_arc = 0;
    int found_slc11_arc = 0;
    int found_slc12_arc = 0;
    int found_slc13_arc = 0;
    int found_slc14_arc = 0;
    int found_slc15_arc = 0;
    int found_l2_arc = 0;
    int found_l1_arc_all = 0;
    int rd_data;
    long int tcode_data;

    file = fopen(filename, "r");
    if (file == NULL) {
        printf("Error: Unable to open the file!\n");
        exit(EXIT_FAILURE);
    }

    while (fgets(line, MAX_LINE_LENGTH, file) != NULL) {
        if (strstr(line, "+RUN_SLC0_ARC") != NULL) {
    		cout << "found +RUN_SLC0_ARC " << endl;
            found_slc0_arc = 1;
        }
        if (strstr(line, "+RUN_SLC1_ARC") != NULL) {
			cout << "found +RUN_SLC1_ARC " << endl;
            found_slc1_arc = 1;
        }
        if (strstr(line, "+RUN_SLC2_ARC") != NULL) {
			cout << "found +RUN_SLC2_ARC " << endl;
            found_slc2_arc = 1;
        }
        if (strstr(line, "+RUN_SLC3_ARC") != NULL) {
			cout << "found +RUN_SLC3_ARC " << endl;
            found_slc3_arc = 1;
        }
        if (strstr(line, "+RUN_SLC4_ARC") != NULL) {
			cout << "found +RUN_SLC4_ARC " << endl;
            found_slc4_arc = 1;
        }
        if (strstr(line, "+RUN_SLC5_ARC") != NULL) {
			cout << "found +RUN_SLC5_ARC " << endl;
            found_slc5_arc = 1;
        }
        if (strstr(line, "+RUN_SLC6_ARC") != NULL) {
			cout << "found +RUN_SLC6_ARC " << endl;
            found_slc6_arc = 1;
        }
        if (strstr(line, "+RUN_SLC7_ARC") != NULL) {
			cout << "found +RUN_SLC7_ARC " << endl;
            found_slc7_arc = 1;
        }
        if (strstr(line, "+RUN_SLC8_ARC") != NULL) {
    		cout << "found +RUN_SLC8_ARC " << endl;
            found_slc8_arc = 1;
        }
        if (strstr(line, "+RUN_SLC9_ARC") != NULL) {
			cout << "found +RUN_SLC9_ARC " << endl;
            found_slc9_arc = 1;
        }
        if (strstr(line, "+RUN_SLC10_ARC") != NULL) {
			cout << "found +RUN_SLC10_ARC " << endl;
            found_slc10_arc = 1;
        }
        if (strstr(line, "+RUN_SLC11_ARC") != NULL) {
			cout << "found +RUN_SLC11_ARC " << endl;
            found_slc11_arc = 1;
        }
        if (strstr(line, "+RUN_SLC12_ARC") != NULL) {
			cout << "found +RUN_SLC12_ARC " << endl;
            found_slc12_arc = 1;
        }
        if (strstr(line, "+RUN_SLC13_ARC") != NULL) {
			cout << "found +RUN_SLC13_ARC " << endl;
            found_slc13_arc = 1;
        }
        if (strstr(line, "+RUN_SLC14_ARC") != NULL) {
			cout << "found +RUN_SLC14_ARC " << endl;
            found_slc14_arc = 1;
        }
        if (strstr(line, "+RUN_SLC15_ARC") != NULL) {
			cout << "found +RUN_SLC15_ARC " << endl;
            found_slc15_arc = 1;
        }
		if (strstr(line, "+RUN_L2_ARC") != NULL) {
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


  int err_cnt = 0; 
  //if (ARCSYNC_PMU_RESET_PMODE){
  //    l2grp_power_up_all(0/*cluster_id*/);
  //    l1grp_power_up_all(0/*cluster_id*/);
  //    slc_power_up_all(0/*cluster_id*/);
  //}
  arcsync_core_rst_dessert_all(0/*cluster id*/); 
  set_intvect(0/*cluster_id*/);
  config_npx_sys_map_all();

if (NPU_HAS_L2ARC){ 
  if (found_l2_arc) {
     core_run(0/*cluster_id*/, 0);
  }
} //(NPU_HAS_L2ARC == 1)
  if (found_slc0_arc) {
     core_run(0/*cluster_id*/, 1);
  }
if (NPU_HAS_L2ARC){
  if (found_slc1_arc) {
     core_run(0/*cluster_id*/, 2);
  }
  if (found_slc2_arc) {
     core_run(0/*cluster_id*/, 3);
  }
  if (found_slc3_arc) {
     core_run(0/*cluster_id*/, 4);
  }
  if (found_slc4_arc) {
     core_run(0/*cluster_id*/, 5);
  }
  if (found_slc5_arc) {
     core_run(0/*cluster_id*/, 6);
  }
  if (found_slc6_arc) {
     core_run(0/*cluster_id*/, 7);
  }
  if (found_slc7_arc) {
     core_run(0/*cluster_id*/, 8);
  }
  if (found_slc8_arc) {
     core_run(0/*cluster_id*/, 9);
  }
  if (found_slc9_arc) {
     core_run(0/*cluster_id*/, 10);
  }
  if (found_slc10_arc) {
     core_run(0/*cluster_id*/, 11);
  }
  if (found_slc11_arc) {
     core_run(0/*cluster_id*/, 12);
  }
  if (found_slc12_arc) {
     core_run(0/*cluster_id*/, 13);
  }
  if (found_slc13_arc) {
     core_run(0/*cluster_id*/, 14);
  }
  if (found_slc14_arc) {
     core_run(0/*cluster_id*/, 15);
  }
  if (found_slc15_arc) {
     core_run(0/*cluster_id*/, 16);
  }
} //(NPU_HAS_L2ARC == 1)
  if (found_l1_arc_all) {
	 for(int i=1; i<NPU_SLICE_NUM+1; i++)  {
        core_run(0/*cluster_id*/, i);		 
	}
  }
  
  //do something and update err_cnt
  

  // Enable SWE Producer 
  host_apb_db_write((1 << 10),0x1007b,2,0xFFFFFFFF,0);//enable cstm msg
  host_apb_db_write((1 << 10),0x10077,2,0xFFFFFFFF,0);



   for (int i = 0; i <1;i++) {
    wait_for_trace_swe_atb_op();
  } 

    check_swe_tcode_out();
//  host_apb_db_write((1 << 10),0x1007b,2,0x0,0);//disable cstm msg
//
//
//
//
//  for (int i = 0; i <5;i++) {
//    wait_for_trace_swe_atb_op();
//  }
//  // Disable Producers
//  host_apb_db_write((1 << 10),0x10077,2,0x00000000,0);
//  // Flush Command
//  host_apb_db_write((1 << 10),0x10076,2,0x00000001,0);
//
//  wait_for_trace_flush();
//  // Get the Decoded TCODE data
//  tcode_data = get_tcode_data();
//  rd_data = tcode_data;
//  // Write the TCODE data in to filter registers 
//  // This is read using AUX registers in the test
//  host_apb_db_write((1 << 10),0x00040,2,rd_data,0);
//  rd_data = tcode_data >> 32;
//  host_apb_db_write((1 << 10),0x00041,2,rd_data,0);


  // host exit the simulator
  host_exit(err_cnt);

  //host_terminate_sim();

  HOST_EXEC_RET;
}


#ifdef __cplusplus
}
#endif
