/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2021-2022 Synopsys, Inc.                              **/
/** All Rights Reserved.                                                **/
/**                                                                     **/
/** This Synopsys software and all associated documentation are         **/
/** proprietary to Synopsys, Inc. and may only be used pursuant to the  **/
/** terms and conditions of a written license agreement with Synopsys,  **/
/** Inc. All other use, reproduction, modification, or distribution of  **/
/** this Synopsys software or the associated documentation is strictly  **/
/** prohibited.                                                         **/
/**                                                                     **/
/*************************************************************************/

#include "tensor.hpp"
using namespace tensor::v200;
using namespace npu;
#include "arcsync_utils.hpp"
#include "utils/cln_map.hpp"
#include "utils/npu_mem_utils.hpp"

class test_program : public arc_program {
public:
  inline test_program() : arc_program() {
    irqflag = false;
  }
  virtual void irq() {
    irqflag = true;
  }

  void exec() {
    arcsync_id_init();
    proc_id = get_proc_id();
    evt_cfg();

    disable_err_prot_on_dmp();

    if(proc_id == 0) { //l2arc
        cfg_system_map();
        
        uint64_t mask=0;
        for(int slc=0; slc<NPU_SLICE_NUM; slc++){
            mask = mask | (1LL << (EVT_CHILD0+slc));
        }
        event_send_children((long long)mask);
        event_wait_all ((long long)mask);
        //l1 DM , granularity is 8b
        #ifndef NPU_MEM_ECC
        mem_raw_test((char*     )(LC_SL0_PERI_DM_BASE | 0x0f0), 32);
        mem_raw_test((short*    )(LC_SL0_PERI_DM_BASE | 0x0f0), 32);
        #endif
        mem_raw_test((int*      )(LC_SL0_PERI_DM_BASE | 0x0f0), 32);
        mem_raw_test((long long*)(LC_SL0_PERI_DM_BASE | 0x0f0), 32);
        //IDMA MMIO, granularity is 32b, test /*HLAPI_I*/
        mem_raw_test((int*      )(LC_SL0_IDMA_MMIO_BASE | 0x070), 32);
        mem_raw_test((long long*)(LC_SL0_IDMA_MMIO_BASE | 0x070), 32);
        //ODMA MMIO, granularity is 32b, test /*HLAPI_I*/
        mem_raw_test((int*      )(LC_SL0_ODMA_MMIO_BASE | 0x070), 32);
        mem_raw_test((long long*)(LC_SL0_ODMA_MMIO_BASE | 0x070), 32);
        //CONV MMIO, granularity is 32b, test /*HLAPI_I*/
        mem_raw_test((int*      )(LC_SL0_CONV_MMIO_BASE | 0x070), 32);
        mem_raw_test((long long*)(LC_SL0_CONV_MMIO_BASE | 0x070), 32);
        //GTOA MMIO, granularity is 32b, test /*HLAPI_I*/
        mem_raw_test((int*      )(LC_SL0_GTOA_MMIO_BASE | 0x070), 32);
        mem_raw_test((long long*)(LC_SL0_GTOA_MMIO_BASE | 0x070), 32); 
        #ifdef NPU_MEM_ECC
	    vm_am_mem_init((uint32_t *)(LC_SL0_SFTY_MMIO_BASE));   //init both vm and am
        #endif
        //AM, granularity is 32b
        #ifndef NPU_MEM_ECC
        mem_raw_test((int*      )(LC_SL0_AM_BASE | 0x070 ), 32);
        #endif
        mem_raw_test((long long*)(LC_SL0_AM_BASE | 0x070 ), 32);
        //VM, granularity is 8b
        #ifndef NPU_MEM_ECC
        mem_raw_test((char*     )(LC_SL0_VM_BASE | 0x070), 32);
        mem_raw_test((short*    )(LC_SL0_VM_BASE | 0x070), 32);
        mem_raw_test((int*      )(LC_SL0_VM_BASE | 0x070), 32);
        #endif
        mem_raw_test((long long*)(LC_SL0_VM_BASE | 0x070), 32);
        //L2 DM, granularity is 32b
        #ifndef NPU_MEM_ECC
        mem_raw_test((char*     )(LC_L2_PERI_DM_BASE | 0x0f0), 32);
        mem_raw_test((short*    )(LC_L2_PERI_DM_BASE | 0x0f0), 32);
        #endif
        mem_raw_test((int*      )(LC_L2_PERI_DM_BASE | 0x0f0), 32);
        mem_raw_test((long long*)(LC_L2_PERI_DM_BASE | 0x0f0), 32);
        //ISTU MMIO, granularity is 32b, test /*HLAPI_I*/
        mem_raw_test((int*      )(LC_L2_ISTU0_MMIO_BASE  | 0x070), 32);
        mem_raw_test((long long*)(LC_L2_ISTU0_MMIO_BASE  | 0x070), 32);
        //OSTU MMIO, granularity is 32b, test /*HLAPI_I*/
        mem_raw_test((int*      )(LC_L2_OSTU0_MMIO_BASE  | 0x070), 32);
        mem_raw_test((long long*)(LC_L2_OSTU0_MMIO_BASE  | 0x070), 32);
    }
    else{ //l1arc
        uint64_t mask = (1LL << EVT_PARENT);
        if (NPU_HAS_L2ARC){
            event_wait_any ((long long)mask);
        }
        
        event_send_parent();
    }
    set_sim_finish_flag(err_cnt);

  }

private:
  bool irqflag;
  uint32_t proc_id;
  int err_cnt = 0;
};

