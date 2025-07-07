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

#define WAIT_COUNT 10000

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
    
    if(proc_id == 0) { //l2arc
        cfg_system_map();

        //wait for slices to sleep
        uint64_t mask = (1LL << EVT_CHILD0);
        event_wait_all((long long)mask);
    }
    else{ //l1arc
        wait_cycles(WAIT_COUNT);
        event_send_parent();
    }
    set_sim_finish_flag(err_cnt);

  }

private:
  bool irqflag;
  uint32_t proc_id;
  int err_cnt = 0;
};

