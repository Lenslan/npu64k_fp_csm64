#include "host_utils.hpp"

#ifdef __cplusplus
extern "C" {
#endif


HOST_EXEC() {
  int err_cnt=0;
  set_intvect(0/*cluster_id*/);  
  arcsync_core_rst_dessert_all(0/*cluster id*/);   
  config_npx_sys_map_all();
  if (NPU_HAS_L2ARC){
    core_run(0/*cluster_id*/, 0);
  }
  core_run(0/*cluster_id*/, 1);
  
  long long npx_dmi_base = NPX_DMI_BASE;
  long long baddr;
  
  //CSM access
  long long init_v;
  //Write
  for(int grp=0; grp<NPU_NUM_GRP; grp++) {
    for(int bnk=0; bnk<NPU_CSM_BANKS_PER_GRP; bnk++){
      baddr  = npx_dmi_base + 0x8000000 + (grp*NPU_CSM_SIZE_PER_GRP) + (grp<<15)/*32KB*/ + (bnk<<12)/*4KB*/;
      init_v = baddr;
      do_write((long long*)baddr, 8, init_v);
    }
  }
  //Check the write value
  for(int grp=0; grp<NPU_NUM_GRP; grp++) {
    for(int bnk=0; bnk<NPU_CSM_BANKS_PER_GRP; bnk++){
      baddr  = npx_dmi_base + 0x8000000 + (grp*NPU_CSM_SIZE_PER_GRP) + (grp<<15)/*32KB*/ + (bnk<<12)/*4KB*/;
      init_v = baddr;
      err_cnt += do_check((long long*)baddr, 8, init_v);
    }
  }

  //L2 DCCM
  baddr = npx_dmi_base + 0x6000000;
  mem_raw_test((long long *)baddr, 64);

  for(int grp=0; grp<NPU_NUM_GRP; grp++) {
    for(int slc=0; slc<NPU_NUM_SLC_PER_GRP; slc++) {
      for(int mem=0; mem<3;mem++){
        #ifdef NPU_MEM_ECC
	    vm_am_mem_init((uint32_t *)(npx_dmi_base + grp*0x1000000 + slc * 0x400000 + L1_SFTY_MMIO_OFFSET));   //init both vm and am
        #endif
        switch(mem) {
          case 0 : baddr = npx_dmi_base + grp*0x1000000 + slc * 0x400000 + L1_AM_OFFSET; break;
          case 1 : baddr = npx_dmi_base + grp*0x1000000 + slc * 0x400000 + L1_VM_OFFSET; break;
          case 2 : baddr = npx_dmi_base + grp*0x1000000 + slc * 0x400000 + L1_DM_OFFSET; break;
        }
        #ifndef NPU_MEM_ECC
        switch((grp*NPU_NUM_SLC_PER_GRP + slc)%4) { // granularity size
          case 0 :  mem_raw_test((char     *)baddr, 32); break;
          case 1 :  mem_raw_test((short    *)baddr, 32); break;
          case 2 :  mem_raw_test((uint32_t *)baddr, 32); break;
          case 3 :  mem_raw_test((long long*)baddr, 32); break;
        }
        #else
        if(mem==2){ //DM 
          switch(slc%2) { // granularity size
            case 0 :  mem_raw_test((uint32_t *)baddr, 32); break;
            case 1 :  mem_raw_test((long long*)baddr, 32); break;
          }
        }else{//AM, VM
          mem_raw_test((long long*)baddr, 32);
        }
        #endif
      }
    }
  }


  // host exit the simulator
  host_exit(err_cnt);
  HOST_EXEC_RET;
}


#ifdef __cplusplus
}
#endif

