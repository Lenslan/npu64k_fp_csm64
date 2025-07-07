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
#include "utils/npu_mem_map_define.hpp"

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
    uint32_t mem_size = get_am_size();

    if(proc_id == 0) { //L2 ARc
        cfg_system_map();
        uint64_t mask=0;
        for(int slc=0; slc<NPU_SLICE_NUM; slc++){
            mask = mask | (1LL << (EVT_CHILD0+slc));
        }
        event_send_children((long long)mask);
        event_wait_all((long long)mask);

        //L2 access slice memory 
        //AM 2banks, granularity is acct_t(a.k.a char)
        for(int grp=0; grp<NPU_NUM_GRP; grp++){
          for(int slc=0; slc<NPU_NUM_SLC_PER_GRP; slc++){
            uint32_t base_addr = LOCAL_CLST0_BASE + grp*0x100_0000 + slc * 0x40_0000 + L1_AM_OFFSET;
           #ifndef NPU_MEM_ECC
            switch((grp*NPU_NUM_SLC_PER_GRP + slc)%2) { // granularity size
              case 0 :  mem_boundary_cross_test((uint32_t *)base_addr, mem_size, 32); break;
              case 1 :  mem_boundary_cross_test((long long*)base_addr, mem_size, 32); break;
            }
           #else
            mem_boundary_cross_test((long long*)base_addr, mem_size, 32);
           #endif
          }
        }
    }
    else { //L1 ARC in Slice 0 to slice N
        uint64_t mask = (1LL << EVT_PARENT);
        if (NPU_HAS_L2ARC){
            event_wait_any ((long long)mask);
        }
        
        uint32_t base_addr;
        uint32_t offset = 0x80*proc_id;
        #ifdef NPU_MEM_ECC
        uint32_t sfty_erp_ctrl_addr;
        for(int slc=-1; slc<NPU_SLICE_NUM; slc++){
            if(slc==-1) { //slice access memory via its local perip
              sfty_erp_ctrl_addr = LOCAL_PERI_BASE + L1_SFTY_MMIO_OFFSET + 0x0_0000;
            }else{ //slice access other slice mem via cluster perip
              //sfty_erp_ctrl_addr = LOCAL_PERI_BASE + L1_SFTY_MMIO_OFFSET + 0x0_0000;
            }
        }
        am_mem_init((uint32_t *)sfty_erp_ctrl_addr);
        #endif

        for(int slc=-1; slc<NPU_SLICE_NUM; slc++){
            if(slc==-1) { //slice access memory via its local perip
                base_addr = LOCAL_PERI_BASE +  L1_AM_OFFSET;
            }else{ //slice access other slice mem via cluster perip
            //    base_addr = LOCAL_CLST0_BASE + slc * 0x40_0000 + L1_AM_OFFSET;
            }
            mem_head_tail_test((long long*)base_addr, offset, mem_size, 32);
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

