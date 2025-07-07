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
#include "utils/clkg_ctrl.hpp"
#include "utils/arc_cc.h"
//#include "utils/arc_irq.hpp"
#include "utils/arc_irq_expcn.hpp"
#include "utils/arc_utils.h"

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
    
    setvect_for_int();
    // enable Level 1 clock gating as well as the CPU Core
    enable_l1_clkg();

    if (NPU_HAS_L2ARC && (proc_id == 0)) { //l2arc
		uint64_t mask=0;
        for(int slc=0; slc<NPU_SLICE_NUM; slc++){
            mask = mask | (1LL << (EVT_CHILD0+slc));
        }
        event_wait_all(mask);
        wait_cycles(200);
        for(int slc=1; slc<NPU_SLICE_NUM+1; slc++){
            arcsync_core_clk_disable(slc);
        }
        wait_cycles(50);
        _sr(5000,REG_LIMIT0);
        _sr(0x1,REG_CONTROL0);
        _sr(0x0,REG_COUNT0);
        start_power(); 
        _sleep(0x10);
        stop_power();
    }
    else { //l1arc
        if (NPU_HAS_L2ARC) {
          event_send_parent();
        }
        else {
          wait_cycles(50);
          _sr(5000,REG_LIMIT0);
          _sr(0x1,REG_CONTROL0);
          _sr(0x0,REG_COUNT0);
          start_power(); 
          _sleep(0x10);
          stop_power();
        }
    }
    set_sim_finish_flag(err_cnt);
  }

private:
  bool irqflag;
  uint32_t proc_id;
  int err_cnt = 0;
};

