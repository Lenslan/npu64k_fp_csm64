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

    if(proc_id == 0) { //L2 ARC
        cfg_system_map();
        uint64_t mask=0;
        for(int slc=0; slc<NPU_SLICE_NUM; slc++){
            mask = mask | (1LL << (EVT_CHILD0+slc));
        }
        event_send_children((long long)mask);
        event_wait_all ((long long)mask);
    }
    else { //L1 ARC in Slice 0 to slice N
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


