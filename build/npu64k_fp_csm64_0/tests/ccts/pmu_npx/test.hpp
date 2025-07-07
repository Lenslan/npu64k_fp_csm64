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



