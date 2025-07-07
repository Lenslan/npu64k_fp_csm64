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
#include "utils/evm_aux_utils.hpp"

class test_program : public arc_program {
public:
  inline test_program() : arc_program() {
    irqflag = false;
  }
  virtual void irq() {
    irqflag = true;
  }
  
  void gen_vm_irq(){
    _sr(0x1, 0xF03); //raise EVT_IRQ to host/parent
    _nop();_nop();_nop();_nop();_nop(); //keep 5 cycles
    _sr(0x0, 0xF03); //clear EVT_IRQ   
  }

  void exec() {
    arcsync_id_init();
    proc_id = get_proc_id();

    setvect_for_int();
    
    uint64_t mask;
    if(proc_id == 0){ //l2 arc 0
      gen_vm_irq();

      for(int s=0; s< NPU_SLICE_NUM; s++){
        mask =  1LL<< (EVT_CHILD0+s);
        event_send_children(mask);
        wait_irq(); //wait for evm_irq from slice
        event_wait_all(mask);
      }        
    }
    else if(proc_id == NPU_SLICE_NUM+1){ //l2 arc 1
      gen_vm_irq();

      for(int s=0; s< NPU_SLICE_NUM; s++){
        wait_irq(); //wait for evm_irq from slice
      }        
    }
    else{ //slice
      mask = (1LL << EVT_PARENT);
      event_wait_all(mask);
      wait_cycles(100);
      
      gen_vm_irq();
      event_send_parent();
    }

    set_sim_finish_flag(err_cnt);
  }

private:
  bool irqflag;
  uint32_t proc_id;
  int err_cnt = 0;
};

