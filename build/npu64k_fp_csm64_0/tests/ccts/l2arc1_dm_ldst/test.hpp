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
    uint32_t mem_size = get_dm_size();
    uint32_t base_addr = LC_L2_PERI_DM_BASE + 0x40000;
    uint32_t offset = 0x80*proc_id;
    uint32_t L2_ARC1_ID=NPU_SLICE_NUM+1;

    if(proc_id == L2_ARC1_ID) { //L2 ARc
        cfg_system_map();
        uint64_t mask=0;
        for(int slc=0; slc<NPU_SLICE_NUM; slc++){
            mask = mask | (1LL << (EVT_CHILD0+slc));
        }
        event_send_children((long long)mask);
        
        //L2 access DCCM
        mem_boundary_cross_test((int*)base_addr, mem_size, 32);

        event_wait_all ((long long)mask);
    }
    else if(proc_id < L2_ARC1_ID) { //L1 ARC in Slice 0 to slice N
        uint64_t mask = (1LL << EVT_PARENT);
        event_wait_any ((long long)mask);
        
        #ifndef NPU_MEM_ECC
        switch(proc_id%4) { // granularity size
            case 0 :  mem_head_tail_test((char     *)base_addr, offset, mem_size, 32); break;
            case 1 :  mem_head_tail_test((uint16_t *)base_addr, offset, mem_size, 32); break;
            case 2 :  mem_head_tail_test((uint32_t *)base_addr, offset, mem_size, 32); break;
            case 3 :  mem_head_tail_test((long long*)base_addr, offset, mem_size, 32); break;
        }
        #else
        switch(proc_id%2) { // granularity size
            case 0 :  mem_head_tail_test((uint32_t *)base_addr, offset, mem_size, 32); break;
            case 1 :  mem_head_tail_test((long long*)base_addr, offset, mem_size, 32); break;
        }
        #endif

        event_send_parent();
    }

    set_sim_finish_flag(err_cnt);
  }



private:
  bool irqflag;
  uint32_t proc_id;
  int err_cnt = 0;
};

