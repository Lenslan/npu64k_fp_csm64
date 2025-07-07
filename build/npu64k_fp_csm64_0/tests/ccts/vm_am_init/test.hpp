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
    evt_cfg();

    uint32_t mem_size = get_vm_size();

    if(proc_id == 0) { //L2 ARc
        cfg_system_map();
        uint64_t mask=0;
        for(int slc=0; slc<NPU_SLICE_NUM; slc++){
            mask = mask | (1LL << (EVT_CHILD0+slc));
        }
        event_send_children((long long)mask);
        event_wait_all ((long long)mask);

        //L2 access slice memory 
        //VM 32banks(data with is 16-byte per bank), addr[8:4] is the bank num, granularity is pix_t(a.k.a char)

    }
    else { //L1 ARC in Slice 0 to slice N
        uint64_t mask = (1LL << EVT_PARENT);
        event_wait_any ((long long)mask);
        
        uint32_t base_addr;
        uint32_t offset = 0x80*proc_id;
        #ifdef NPU_MEM_ECC
        uint32_t sfty_erp_ctrl_addr;
        //for(int slc=-1; slc<NPU_SLICE_NUM; slc++){
        //    if(slc==-1) { //slice access memory via its local perip
        //      sfty_erp_ctrl_addr = LOCAL_PERI_BASE + L1_SFTY_MMIO_OFFSET + 0x0_0000;
        //    }else{ //slice access other slice mem via cluster perip
        //      //sfty_erp_ctrl_addr = LOCAL_PERI_BASE + L1_SFTY_MMIO_OFFSET + 0x0_0000;
        //    }
        //}  
        //vm_mem_init((uint32_t *)sfty_erp_ctrl_addr);   //only init vm
		//am_mem_init((uint32_t *)sfty_erp_ctrl_addr);   //only init am
        sfty_erp_ctrl_addr = LOCAL_PERI_BASE + L1_SFTY_MMIO_OFFSET + 0x0_0000;
		vm_am_mem_init((uint32_t *)sfty_erp_ctrl_addr);   //init both vm and am
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

