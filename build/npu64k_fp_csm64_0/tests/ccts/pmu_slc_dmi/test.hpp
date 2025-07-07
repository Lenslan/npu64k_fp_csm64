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
#ifndef RTL_ARC
        rptos << "[INFO]: l2arc processor ID is " << proc_id << endl;
      	arc_exit(); //exit the sysc simulation
#else
		uint64_t mask=0;
        for(int slc=0; slc<NPU_SLICE_NUM; slc++){
            mask = mask | (1LL << (EVT_CHILD0+slc));
        }
        //event_send_children((long long)mask);
        event_wait_all ((long long)mask);
        set_sim_finish_flag(err_cnt);
#endif

    }
    else { //L1 ARC in Slice 0 to slice N
#ifndef RTL_ARC
        rptos << "[INFO]: l1arc processor ID is " << proc_id << endl;
#endif
#ifndef RTL_ARC
        rptos << "[INFO]: l1arc(" << proc_id << ") sends event back to parent" << endl;
#else
        uint64_t mask = (1LL << EVT_PARENT);
        //if (NPU_HAS_L2ARC){
        //    event_wait_any ((long long)mask);
        //}
        
        //uint32_t base_addr;
        //uint32_t offset = 0x80*proc_id;
        //#ifdef NPU_MEM_ECC
        //uint32_t sfty_erp_ctrl_addr;
        //for(int slc=-1; slc<NPU_SLICE_NUM; slc++){
        //    if(slc==-1) { //slice access memory via its local perip
        //      sfty_erp_ctrl_addr = LOCAL_PERI_BASE + L1_SFTY_MMIO_OFFSET + 0x0_0000;
        //    }else{ //slice access other slice mem via cluster perip
        //      //sfty_erp_ctrl_addr = LOCAL_PERI_BASE + L1_SFTY_MMIO_OFFSET + 0x0_0000;
        //    }
        //}
        //vm_mem_init((uint32_t *)sfty_erp_ctrl_addr);
        //#endif
        //
        //for(int slc=-1; slc<NPU_SLICE_NUM; slc++){
        //    if(slc==-1) { //slice access memory via its local perip
        //        base_addr = LOCAL_PERI_BASE +  L1_VM_OFFSET;
        //    }else{ //slice access other slice mem via cluster perip
        //        //base_addr = LOCAL_CLST0_BASE + slc * 0x40_0000 + L1_VM_OFFSET;
        //    }
        //    mem_head_tail_test((long long*)base_addr, offset, mem_size, 32);
        //}

        event_send_parent();
        set_sim_finish_flag(err_cnt);
#endif

    }

    

  }


private:
  bool irqflag;
  uint32_t proc_id;
  int err_cnt = 0;
};



