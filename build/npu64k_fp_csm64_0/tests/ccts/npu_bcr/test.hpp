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

  void aux_reg_test(uint32_t reg, bool canread, bool canwrite, uint32_t r, uint32_t wr_mask){
    uint32_t v;

    if(canread){
      v = _lr(reg);
      do_compare(v, r);
    }else{
      excpn_intention_flag = 2;
      v = _lr(reg);
      excpn_intention_flag = 0;
      check_excpn_taken(ECR_ILLEGAL_INST);    
      clear_ecr();
    }
 
    if(canwrite){
      _sr(r, reg);
      check_excpn_taken(0);    
      v = _lr(reg);
      do_compare(v & wr_mask, r & wr_mask);
    }else{
      excpn_intention_flag = 2;
      _sr(0, reg);
      excpn_intention_flag = 0;
      check_excpn_taken(ECR_ILLEGAL_INST);    
      clear_ecr();
    }
  }


  uint32_t _log2(uint32_t in){
    uint32_t o = 0;
    while (in >>= 1) ++o;
    return o;
  }

  void bcr_check(){
    //BCR NPU_BUILD
    uint32_t bcr, r;
    bcr =    (NPU_VER)                             // [7:0] Verision
           | (NPU_SLICE_NUM << 8)                  // [12:8] slice number
           | (NPU_MEM_ECC << 13)                   // [13]  Mem ECC
           | (NPU_HAS_L2ARC << 14)                 // [14] L2 presents
           | ( 0x1 << 15)                          // [15] L1 presents
           | ((NPU_SLICE_MAC==4096 ? 4 : 3) << 16) // [18:16] Number of MAC per slice
           | ( 0x1 << 19)                          // [19] event manager presents
           | (_log2(NPU_STU_CHAN_NUM) << 20)       // [21:20] number of stu channels
           | ((NPU_SAFETY_LEVEL !=0) << 22)        // [22] SFTY is enable
         //| (NPU_HAS_FLOAT << 23)                 // [23] Float point is included
           | ((NPU_SLICE_MEM==3 ? 1 : (NPU_SLICE_MEM==2 ? 3 : 2)) << 26)    // [28:26] VM size // 512KB or 256KB or 128KB
           | ((NPU_SLICE_MEM==3 ? 1 : (NPU_SLICE_MEM==0 ? 2 : 3)) << 29)    // [31:29] AM size // 32KB or 64KB or 128KB
          ;
    //aux_reg_test(NPU_BUILD, 1, 0, bcr, 0x0);
    r = _lr(NPU_BUILD);
    do_compare(bcr, r);
    //EVENT_BCR    
    bcr =    ( 0x02 )                              // [7:0] Verision
           | ( 0x40 << 8 )                         // [14:8] event number
           | ( 0x1 << 15 )                         // [15] arcsync is connected to this core
           | ( 0x8 << 16)                          // [16] number of supported virtual machines 
          ;
    //FIXME: P10019796-58855
    //aux_reg_test(EVENT_BCR, 1, 0, bcr, 0x0);
    //r = _lr(EVENT_BCR);
    //do_compare(bcr, r);
    
    //STU_BCR   
    //aux_reg_test(STU_BCR, 1, 0, 0x0, 0x0);

  }

  void exec() {
    arcsync_id_init();
    proc_id = get_proc_id();
    
    setvect_for_expcn();

    if(proc_id == 0) { //L2 ARc
        uint64_t mask= (1LL<< EVT_CHILD0);
      if (NPU_HAS_L2ARC){
        cfg_system_map();
        event_send_children(mask);
      }
        
        bcr_check();

      if (NPU_HAS_L2ARC){
        event_wait_all (mask);
      }
    }
    else if(proc_id == 1){ //l1arc
      if (NPU_HAS_L2ARC){
        uint64_t mask = (1LL << EVT_PARENT);
        event_wait_any (mask);
      }
        bcr_check();
      if (NPU_HAS_L2ARC){
        event_send_parent();
      }
    }

    set_sim_finish_flag(err_cnt);
  }



private:
  bool irqflag;
  uint32_t proc_id;
  int err_cnt = 0;
};

