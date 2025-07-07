#ifndef HOST_LOAPI
#define HOST_LOAPI

#include "npu_defines.hpp"  // NOLINT [build/include_subdir]
#include "npu_config.hpp"   // NOLINT [build/include_subdir]
#include "arcsync_utils.hpp"

void l2grp_power_up_all(int cluster_id);
void l1grp_power_up_all(int cluster_id);
void slc_power_up_all(int cluster_id);

void l2_arc_dm_mark_st(long long* addr, long long value) {
  cfg_dmi_long_write(addr, value);
}

void l2_arc_dm_mark_ld(long long* addr, long long value) {
  long long data;
  data = cfg_dmi_long_read(addr);
  while(data != value){
     data = cfg_dmi_long_read(addr);
  }
}

template<typename T> inline T mmio_read(T* p) {
  //npu::run_cycles(1);
  return *p;
}

void core_dm_ldst(int cluster_id, int core_id) {
  long long* baddr;
  long long npx_dmi_base = NPX_DMI_BASE;
  long long data;
  int slc = core_id-1;
  long long fix_value = 112;
  int grp = slc/NPU_NUM_SLC_PER_GRP;
  int oft = slc%NPU_NUM_SLC_PER_GRP;
  int l2arc1 = NPU_NUM_SLC_PER_GRP*NPU_NUM_GRP + 1;
  if (core_id == 0) {
      baddr = (long long*)(npx_dmi_base + 0x400000 * 24);
  }
  else if (core_id == l2arc1) {
      baddr = (long long*)(npx_dmi_base + 0x400000 * 24 + 0x40000);
  }
  else {
      baddr = (long long*)(npx_dmi_base + grp * 0x1000000 + oft * 0x400000 + L1_DM_OFFSET);
  }
  for (int i=0; i<4; i++) {
      cfg_dmi_long_write(baddr, fix_value);
      data = cfg_dmi_long_read(baddr);
      fix_value++;
      baddr++;
  }
}


void core_vm_ldst(int cluster_id, int core_id) {
  long long* baddr;
  long long npx_dmi_base = NPX_DMI_BASE;
  int data;
  long long slc = core_id-1;
  long long fix_value = 116;
  long long grp = slc/NPU_NUM_SLC_PER_GRP;
  long long oft = slc%NPU_NUM_SLC_PER_GRP;
  baddr = (long long*)(npx_dmi_base + grp * 0x1000000 + oft * 0x400000 + L1_VM_OFFSET);

  for (int i=0; i<4; i++) {
      cfg_dmi_long_write(baddr, fix_value);
      data = cfg_dmi_long_read(baddr);
      fix_value++;
      baddr++;
  }
}


void config_cln_grp_read(int g){
  long long cfg_dmi_base=0xf0000000;
  long long baddr; 
  int apidx;

    /* cln1p0_config */
    apidx=0;
    baddr = cfg_dmi_base + g * 0x20000;

    /* config top matrix */
    apidx=0;
    baddr = cfg_dmi_base + g * 0x20000 + 0x1000;
    if(g==0){
      //slice peripheral
      //config_aperture(apidx, baddr, 0xe0000000, 0x01000000, 0); // aperture e000_0000 - e0ff_ffff (grp 0)
      if (NPU_NUM_GRP > 1) {
        cfg_dmi_read((long long *)(baddr + 0x000 + apidx * 4));

      }
      if (NPU_NUM_GRP > 2) {
        cfg_dmi_read((long long *)(baddr + 0x000 + apidx * 4));

      }
      //STU
      //config_aperture(apidx, baddr, 0xe6080000, 0x00002000, 0); // aperture e608_0000 - e608_1fff (grp 0 - stu0-1)
      if (NPU_NUM_GRP > 1) {
        cfg_dmi_read((long long *)(baddr + 0x000 + apidx * 4));

      }
      if (NPU_NUM_GRP > 2) {
        cfg_dmi_read((long long *)(baddr + 0x000 + apidx * 4));

      }
      //CSM
      //cfg_apert_direct(apidx, baddr, 0xe8000000, 0xfc018000, 0); // aperture e800_0000 - ebff_ffff (grp 0 - [16:15]==0 the first 32KB csm)
    
    }
    
  
}

void cfg_aperture_read(long long int base_addr, int array[], int numap_size) {
  for (int apidx=0; apidx < numap_size; apidx++ ){
      array[apidx] = cfg_dmi_read((long long *)(base_addr + apidx * 4));          // get base data
  }
}

int core_status_read(int cluster_id, int core_id) {
  int data;
  int* ptr;
  ptr =  (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + 20 *NUM_CLUSTER * NUM_CORE_PER_CLUSTER + cluster_id * NUM_CORE_PER_CLUSTER + core_id * 4);
  data = cfg_arcsync_read(ptr);
  return data; 
}

int core_pmode_read(int cluster_id, int core_id) {
  int data;
  int* ptr;
  ptr =  (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + cluster_id * NUM_CORE_PER_CLUSTER + core_id * 4);
  data = cfg_arcsync_read(ptr);
  return data; 
}


void wait_powerdown_core(int cluster_id, int core_id) {
  int data;
  //RSTCNT
  do{
      data = core_pmode_read((int)cluster_id, (int)core_id);
  } while (data == 1);
  cout << "power down/up sequence completed" << endl;

  data = core_status_read((int)cluster_id, (int)core_id);
  cout << "core status: cluster: " << cluster_id << ", core: " << core_id << endl;
}

void power_down_core(int cluster_id, int core_id) {
  int data;
  int* ptr;

  ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + NUM_CORE_PER_CLUSTER * cluster_id + core_id * 4);
  data = 1;
  cfg_arcsync_write(ptr, data);
}

void disable_core_clk(int cluster_id, int core_id) {
  int data;
  int* ptr;

  ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS +  28 *NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + core_id * 4);
  data = 0;
  cfg_arcsync_write(ptr, data);
}

void disable_core_clk_all(int cluster_id) {
  int data;
  int* ptr;

  if (NPU_HAS_L2ARC) {
    int i = 0;
    ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS +  28 *NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + i * 4);
    data = 0;
    cfg_arcsync_write(ptr, data);
  }
  for (int i=1; i<NPU_SLICE_NUM+1; i++) {
	  ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS +  28 *NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + i * 4);
      data = 0;
      cfg_arcsync_write(ptr, data);
  }
  if (DUO_L2ARC) {
    int i = NPU_SLICE_NUM+1;
	ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS +  28 *NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + i * 4);
    data = 0;
    cfg_arcsync_write(ptr, data);
  }

}

void enable_core_clk(int cluster_id, int core_id) {
  int data;
  int* ptr;

  ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS +  28 *NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + core_id * 4);
  data = 1;
  cfg_arcsync_write(ptr, data);
}

void enable_core_clk_all(int cluster_id) {
  int data;
  int* ptr;

  if (NPU_HAS_L2ARC) {
    int i = 0;
    ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS +  28 *NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + i * 4);
    data = 1;
    cfg_arcsync_write(ptr, data);
  }
  for (int i=1; i<NPU_SLICE_NUM+1; i++) {
	  ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS +  28 *NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + i * 4);
      data = 1;
      cfg_arcsync_write(ptr, data);
  }
  if (DUO_L2ARC) {
    int i = NPU_SLICE_NUM+1;
	ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS +  28 *NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + i * 4);
    data = 1;
    cfg_arcsync_write(ptr, data);
  }

}

void disable_group_clk(int cluster_id, int group_id) {
  int data;
  int* ptr;
  int offset;
  switch(group_id) {
    case 0 : offset = 0x8; break;
    case 1 : offset = 0x80; break;
    case 2 : offset = 0x600; break;
    case 3 : offset = 0x4000; break;
  }

  ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS +  4 *NUM_CLUSTER + cluster_id * 4);
  data =(0x5A5A<<16) |  offset;;
  cfg_arcsync_write(ptr, data);
}


void disable_group_clk_all(int cluster_id) {
  int data;
  int* ptr;
  int offset;
  
  for (int i=0; i<NPU_NUM_GRP; i++) {  
    switch(i) {
      case 0 : offset = 0x8; break;
      case 1 : offset = 0x80; break;
      case 2 : offset = 0x600; break;
      case 3 : offset = 0x4000; break;
    }

    ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS +  4 *NUM_CLUSTER + cluster_id * 4);
    data =(0x5A5A<<16) |  offset;;
    cfg_arcsync_write(ptr, data);
  }
}


void enable_group_clk(int cluster_id, int group_id) {
  int data;
  int* ptr;
  int offset;
  switch(group_id) {
    case 0 : offset = 0x8; break;
    case 1 : offset = 0x80; break;
    case 2 : offset = 0x600; break;
    case 3 : offset = 0x4000; break;
  }

  ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS +  4 *NUM_CLUSTER + cluster_id * 4);
  data =(0xA5A5<<16) |  offset;;
  cfg_arcsync_write(ptr, data);
}

void enable_group_clk_all(int cluster_id) {
  int data;
  int* ptr;
  int offset;
  
  for (int i=0; i<NPU_NUM_GRP; i++) {  
    switch(i) {
      case 0 : offset = 0x8; break;
      case 1 : offset = 0x80; break;
      case 2 : offset = 0x600; break;
      case 3 : offset = 0x4000; break;
    }

    ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS +  4 *NUM_CLUSTER + cluster_id * 4);
    data =(0xA5A5<<16) |  offset;;
    cfg_arcsync_write(ptr, data);
  }
}

void power_down_group(int cluster_id, int group_id) {
  int data;
  int* ptr;
  int offset;
//44, 48, 52, 56
  switch(group_id) {
    case 0 : offset = 44; break;
    case 1 : offset = 48; break;
    case 2 : offset = 52; break;
    case 3 : offset = 56; break;
  }
  
  
  ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS + offset * NUM_CLUSTER + cluster_id * 4);
  data = 1;
  cfg_arcsync_write(ptr, data);
}



void power_up_core(int cluster_id, int core_id) {
  int data;
  int* ptr;

  ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + NUM_CORE_PER_CLUSTER * cluster_id + core_id * 4);
  data = 0;
  cfg_arcsync_write(ptr, data);
}


void power_up_group(int cluster_id, int group_id) {
  int data;
  int* ptr;
  int offset;
//44, 48, 52, 56
  switch(group_id) {
    case 0 : offset = 44; break;
    case 1 : offset = 48; break;
    case 2 : offset = 52; break;
    case 3 : offset = 56; break;
  }
  
  
  ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS + offset * NUM_CLUSTER + cluster_id * 4);
  data = 0;
  cfg_arcsync_write(ptr, data);
}

void power_down_group_slc(int cluster_id, int group_id) {
	for (int i=1; i<NPU_NUM_SLC_PER_GRP+1; i++) {
        power_down_core(0, group_id*NPU_NUM_SLC_PER_GRP + i);
        wait_powerdown_core(0, group_id*NPU_NUM_SLC_PER_GRP + i);
	}
        power_down_group(0, group_id);
        host_wait(1000);
}

void power_up_group_slc(int cluster_id, int group_id) {
        power_up_group(0, group_id);
        host_wait(1000);
	for (int i=1; i<NPU_NUM_SLC_PER_GRP+1; i++) {
        power_up_core(0, group_id*NPU_NUM_SLC_PER_GRP + i);
        wait_powerdown_core(0, group_id*NPU_NUM_SLC_PER_GRP + i);		
	}
}

void core_run_all(int cluster_id) {
  int data;
  int* ptr;
  if (NPU_HAS_L2ARC) {
    int i = 0;
    ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + 4*NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + i * 4);
    data = 1;
    cfg_arcsync_write(ptr, data);
  }
  for (int i=1; i<NPU_SLICE_NUM+1; i++) {
      ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + 4*NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + i * 4);
      data = 1;
      cfg_arcsync_write(ptr, data);
  }
  if (DUO_L2ARC) {
    int i = NPU_SLICE_NUM+1;
    ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + 4*NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + i * 4);
    data = 1;
    cfg_arcsync_write(ptr, data);
  }
}

void core_halt_all(int cluster_id) {
  int data;
  int* ptr;
  if (NPU_HAS_L2ARC) {
    int i = 0;
    ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + 8*NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + i * 4);
    data = 1;
    cfg_arcsync_write(ptr, data);
  }
  for (int i=1; i<NPU_SLICE_NUM+1; i++) {
      ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + 8*NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + i * 4);
      data = 1;
      cfg_arcsync_write(ptr, data);
  }
  if (DUO_L2ARC) {
    int i = NPU_SLICE_NUM+1;
    ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + 8*NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + i * 4);
    data = 1;
    cfg_arcsync_write(ptr, data);
  }
}

void slc_run_all(int cluster_id) {
  int data;
  int* ptr;
  
  for (int i=1; i<NPU_SLICE_NUM+1; i++) {
      ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + 4*NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + i * 4);
      data = 1;
      cfg_arcsync_write(ptr, data);
  }
}


void core_run(int cluster_id, int core_id) {
  int data;
  int* ptr;

  ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + 4*NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + core_id * 4);
  data = 1;
  cfg_arcsync_write(ptr, data);
}

void core_halt(int cluster_id, int core_id) {
  int data;
  int* ptr;

  ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + 8*NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + core_id * 4);
  data = 1;
  cfg_arcsync_write(ptr, data);
}

void set_intvect(int cluster_id) {
  long long data;
  int data_low;
  int data_high;
  int* ptr;

  if (NPU_HAS_L2ARC) { //l2_arc
	  data = 0x18000000 >> 10;
      data_low = (int)(data & 0xffffffff);
	  data_high = (int)(data >> 32);
      ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + 12*NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + 0);
      cfg_arcsync_write(ptr, data_low);
      ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + 16*NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + 0);
      cfg_arcsync_write(ptr, data_high);
      cout << hex << "set set_intvect, core_id: 0" << " base:" << data_low << endl;
  }
  
  for (int i=1; i<NPU_SLICE_NUM+1; i++) {
    data = ((i-1) * 0x01000000) >> 10;
	  data_low = (int)(data & 0xffffffff);
	  data_high = (int)(data >> 32);
	  ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + 12*NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + i * 4);
      cfg_arcsync_write(ptr, data_low);
	  ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + 16*NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + i * 4);
      cfg_arcsync_write(ptr, data_high);
      cout << hex << "set set_intvect, core_id:" << i << " base:" << data_low << endl;
  }
  
  if (DUO_L2ARC) {
      int i = NPU_SLICE_NUM+1;
	  data = 0x19000000 >> 10;
	  //data = 0x18000000 >> 10;
	  data_low = (int)(data & 0xffffffff);
	  data_high = (int)(data >> 32);
	  ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + 12*NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + i * 4);
      cfg_arcsync_write(ptr, data_low);
	  ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + 16*NUM_CLUSTER * NUM_CORE_PER_CLUSTER + NUM_CORE_PER_CLUSTER * cluster_id + i * 4);
      cfg_arcsync_write(ptr, data_high);
      cout << hex << "set set_intvect, core_id:" << i << " base:" << data_low << endl;
  }
}

void config_pmu_count(int cluster_id) {
  int data;
  int* ptr;
  //RSTCNT
  ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS + 32*NUM_CLUSTER + cluster_id * 4);
  data =1;
  cfg_arcsync_write(ptr, data);

  //PUCNT
  ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS + 36*NUM_CLUSTER + cluster_id * 4);
  data =1;
  cfg_arcsync_write(ptr, data);

  //PDCNT
  ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS + 40*NUM_CLUSTER + cluster_id * 4);
  data =1;
  cfg_arcsync_write(ptr, data);

  //PMU_CORE_LOGIC1
  ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS + 60*NUM_CLUSTER + cluster_id * 4);
  data =1;
  cfg_arcsync_write(ptr, data);

  //PMU_CORE_LOGIC2
  ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS + 64*NUM_CLUSTER + cluster_id * 4);
  data =2;
  cfg_arcsync_write(ptr, data);

  //PMU_GRP_LOGIC1
  ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS + 68*NUM_CLUSTER + cluster_id * 4);
  data =1;
  cfg_arcsync_write(ptr, data);

  //PMU_GRP_LOGIC2
  ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS + 72*NUM_CLUSTER + cluster_id * 4);
  data =2;
  cfg_arcsync_write(ptr, data);

}


void arcsync_core_rst_assert_all(int cluster_id) {
  int data;
  int* ptr;
  int i;

  if (NPU_HAS_L2ARC) {
    i = 0;
    ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + NUM_CORE_PER_CLUSTER * NUM_CLUSTER * 24 + cluster_id * NUM_CORE_PER_CLUSTER + i * 4); 
    data = (0x5A5A<<16) | i;
  }
  
  for (i=1; i<=NPU_SLICE_NUM; i++) {
    ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + NUM_CORE_PER_CLUSTER * NUM_CLUSTER * 24 + cluster_id * NUM_CORE_PER_CLUSTER + i * 4); 
    data = (0x5A5A<<16) | i;
  }
  
  if (DUO_L2ARC) {
    i = NPU_SLICE_NUM+1;
    ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + NUM_CORE_PER_CLUSTER * NUM_CLUSTER * 24 + cluster_id * NUM_CORE_PER_CLUSTER + i * 4); 
    data = (0x5A5A<<16) | i;
  }
  cfg_arcsync_write(ptr, data);
}

void arcsync_core_rst_dessert_all(int cluster_id) {
  int data;
  int* ptr;
  int i;
  
  // powerup npu if needed
  if (ARCSYNC_HAS_PMU && ARCSYNC_PMU_RESET_PMODE){
    if (NPU_HAS_L2ARC){
      l2grp_power_up_all(0/*cluster_id*/);
    }
      l1grp_power_up_all(0/*cluster_id*/);
      slc_power_up_all(0/*cluster_id*/);
  }

  if (0==NPU_CLK_ENA_RST) {
    //enable clock gate
    //enable all group clock enable
    ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS + NUM_CLUSTER * 4 + cluster_id * 4);
    data =(0xA5A5<<16) |  0X4688;
    cfg_arcsync_write(ptr, data);

    //enable all core clock enable
    enable_core_clk_all(0 /*cluster_id*/);
  }

  //de-assert all group reset
  ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS + NUM_CLUSTER * 8 + cluster_id * 4);
  data =(0xA5A5<<16) |  0X468D;
  cfg_arcsync_write(ptr, data);

  //de-assert all core rest
  if (NPU_HAS_L2ARC) {
    i = 0;
    ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + NUM_CORE_PER_CLUSTER * NUM_CLUSTER * 24 + cluster_id * NUM_CORE_PER_CLUSTER + i * 4); 
    data = (0xA5A5<<16) | i;
    cfg_arcsync_write(ptr, data);
  }
  
  for (i=1; i<=NPU_SLICE_NUM; i++) {
       ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + NUM_CORE_PER_CLUSTER * NUM_CLUSTER * 24 + cluster_id * NUM_CORE_PER_CLUSTER + i * 4); 
	   data = (0xA5A5<<16) | i;
       cfg_arcsync_write(ptr, data);
  }
  
  if (DUO_L2ARC) {
    i = NPU_SLICE_NUM+1;
    ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + NUM_CORE_PER_CLUSTER * NUM_CLUSTER * 24 + cluster_id * NUM_CORE_PER_CLUSTER + i * 4); 
    data = (0xA5A5<<16) | i;
    cfg_arcsync_write(ptr, data);
  }
}


void arcsync_core_rst_assert(int cluster_id, int core_id) {
  int data;
  int* ptr;
  ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + NUM_CORE_PER_CLUSTER * NUM_CLUSTER * 24 + cluster_id * NUM_CORE_PER_CLUSTER  + core_id * 4); 
  data = (0x5A5A<<16) | core_id;
  cfg_arcsync_write(ptr, data);
}

void arcsync_l1_group_rst_assert(int cluster_id, int group_id) {
  int data;
  int* ptr;
  int core_id = group_id * NPU_NUM_SLC_PER_GRP + 1;
  int offset;

  for (int i=0; i<NPU_NUM_SLC_PER_GRP; i++) {
      ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + NUM_CORE_PER_CLUSTER * NUM_CLUSTER * 24 + cluster_id * NUM_CORE_PER_CLUSTER + core_id * 4); 
      data = (0x5A5A<<16) | core_id;
	  cout << "reset core_id" << core_id << endl;
      cfg_arcsync_write(ptr, data);
	  core_id++;
  }
  
    switch(group_id) {
      case 0 : offset = 0x8; break;
      case 1 : offset = 0x80; break;
      case 2 : offset = 0x600; break;
      case 3 : offset = 0x4000; break;
    }

    ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS +  8 *NUM_CLUSTER + cluster_id * 4);
    data =(0x5A5A<<16) |  offset;
    cfg_arcsync_write(ptr, data);

}

void arcsync_l1_group_rst_dessert(int cluster_id, int group_id) {
  int data;
  int* ptr;
  int core_id = group_id * NPU_NUM_SLC_PER_GRP + 1;
  int offset;

  for (int i=0; i<NPU_NUM_SLC_PER_GRP; i++) {
      ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + NUM_CORE_PER_CLUSTER * NUM_CLUSTER * 24 + cluster_id * NUM_CORE_PER_CLUSTER + core_id * 4); 
      data = (0xA5A5<<16) | core_id;
      cfg_arcsync_write(ptr, data);
	  core_id++;
  }
  
    switch(group_id) {
      case 0 : offset = 0x8; break;
      case 1 : offset = 0x80; break;
      case 2 : offset = 0x600; break;
      case 3 : offset = 0x4000; break;
    }

    ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS +  8 *NUM_CLUSTER + cluster_id * 4);
    data =(0xA5A5<<16) |  offset;
    cfg_arcsync_write(ptr, data);

}

void arcsync_l2_group_rst_assert(int cluster_id) {
    int offset = 0x5;
    int* ptr;
    int data;
    int core_id = 0;


    for (int i=0; i<NPU_NUM_GRP; i++) {
	    arcsync_l1_group_rst_assert(cluster_id, i);
	}

    //rst L2ARC	
    ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + NUM_CORE_PER_CLUSTER * NUM_CLUSTER * 24 + cluster_id * NUM_CORE_PER_CLUSTER  + core_id * 4); 
    data = (0x5A5A<<16) | core_id;
    cfg_arcsync_write(ptr, data);
  
    if (DUO_L2ARC) {  
      core_id = NPU_SLICE_NUM + 1;
      ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + NUM_CORE_PER_CLUSTER * NUM_CLUSTER * 24 + cluster_id * NUM_CORE_PER_CLUSTER + core_id * 4); 
      data = (0x5A5A<<16) | core_id;
      cfg_arcsync_write(ptr, data);
    }

	//rst L2GRP
    ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS +  8 *NUM_CLUSTER + cluster_id * 4);
    data =(0x5A5A<<16) |  offset;
    cfg_arcsync_write(ptr, data);
}


void arcsync_l2_group_rst_dessert(int cluster_id) {
    int offset = 0x5;
    int* ptr;
    int data;
    int core_id = 0;

    for (int i=0; i<NPU_NUM_GRP; i++) {
	    arcsync_l1_group_rst_dessert(cluster_id, i);
	}
	//rst L2ARC	
    ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + NUM_CORE_PER_CLUSTER * NUM_CLUSTER * 24 + cluster_id * NUM_CORE_PER_CLUSTER + core_id * 4); 
    data = (0xA5A5<<16) | core_id;
    cfg_arcsync_write(ptr, data);
    if (DUO_L2ARC) {  
      core_id = NPU_SLICE_NUM + 1;
      ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + NUM_CORE_PER_CLUSTER * NUM_CLUSTER * 24 + cluster_id * NUM_CORE_PER_CLUSTER + core_id * 4); 
      data = (0xA5A5<<16) | core_id;
      cfg_arcsync_write(ptr, data);
    }
    
	//rst L2GRP
    ptr = (int*)(ARCSYNC_BASE + CLUSTER_CTRL_STATUS +  8 *NUM_CLUSTER + cluster_id * 4);
    data =(0xA5A5<<16) |  offset;
    cfg_arcsync_write(ptr, data);

}

void arcsync_core_rst_dessert(int cluster_id, int core_id) {
  int data;
  int* ptr;
  ptr = (int*)(ARCSYNC_BASE + CORE_CTRL_STATUS + NUM_CORE_PER_CLUSTER * NUM_CLUSTER * 24 + cluster_id * NUM_CORE_PER_CLUSTER  + core_id * 4);   
  data = (0xA5A5<<16) | core_id;
  cfg_arcsync_write(ptr, data);
}

void slc_power_down_all(int cluster_id) {
    for (int i=1; i<NPU_SLICE_NUM+1; i++) {  
       power_down_core(cluster_id, i/*core_id*/);
       wait_powerdown_core(cluster_id, i/*core_id*/);
    }
}

void slc_power_up_all(int cluster_id) {
    for (int i=1; i<NPU_SLICE_NUM+1; i++) {  
       power_up_core(cluster_id, i/*core_id*/);
       wait_powerdown_core(cluster_id, i/*core_id*/);
    }
}

void l1grp_power_down_all(int cluster_id) {
    for (int i=0; i<NPU_NUM_GRP; i++) {  
       power_down_group(cluster_id, i/*group_id*/);
    }
    host_wait(1000); 
}

void l1grp_power_up_all(int cluster_id) {
    for (int i=0; i<NPU_NUM_GRP; i++) {  
       power_up_group(cluster_id, i/*group_id*/);
    }
    host_wait(1000); 
}

void l2grp_power_down_all(int cluster_id) {
       power_down_core(cluster_id, 0/*core_id*/);
       wait_powerdown_core(cluster_id, 0/*core_id*/);
}

void l2grp_power_up_all(int cluster_id) {
	if (NPU_RDF_HIER_LEVEL == 2) {
        for (int i=0; i<NPU_NUM_GRP; i++) {
	       arcsync_l1_group_rst_assert(0, i);
	    }
	}

       power_up_core(cluster_id, 0/*core_id*/);
       wait_powerdown_core(cluster_id, 0/*core_id*/);
	if (NPU_RDF_HIER_LEVEL == 2) {
        for (int i=0; i<NPU_NUM_GRP; i++) {
	       arcsync_l1_group_rst_dessert(0, i);
	    }
	}

}


#endif
