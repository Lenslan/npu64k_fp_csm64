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

  void check_err_flag(uint32_t reg_base, uint32_t sbe_flag, uint32_t dbe_flag){
    do_check((uint32_t*)(reg_base + 0x24), 1, sbe_flag); //NPU_SBE_CNT
    do_check((uint32_t*)(reg_base + 0x0),  1, dbe_flag); //NPU_ERP_CTRL
  }

  void  enable_vm_am_ecc_prot(uint32_t reg_base){
    //Enable MEM ECC and clear error if have
    do_write((uint32_t*)(reg_base + 0x0), 1, (uint32_t)0x3); //NPU_ERP_CTRL
    do_write((uint32_t*)(reg_base + 0x24), 1, (uint32_t)(0x1<<31)); //NPU_SBE_CNT
    _sync(); //flush pipeline to make sure MMIO update take effect
    //check error are cleared
    check_err_flag(reg_base, (uint32_t)0x0, (uint32_t)0x3); //check no error reported
  }
  
  void  disable_vm_am_ecc_prot(uint32_t reg_base){
    //disable MEM ECC
    do_write((uint32_t*)(reg_base + 0x0), 1, (uint32_t)0x0);
    _sync(); //flush pipeline to make sure MMIO update take effect      
  }

  void mem_ecc_check(uint32_t reg_base, uint64_t* mem_ptr, bool is_vm, bool is_sbe){
    uint32_t sb_err_flag = is_vm ? (0x1 << 0) : (0x1 << 4);
    uint32_t db_err_flag = is_vm ? (0x1 << 6) | 0x3 : (0x1 << 7) | 0x3 ; 
    // initialize memory with given value
    uint64_t data = 0xfedcba9876543210;
    uint64_t mdf_data = is_sbe ? data ^ (1LL << 3)  // modify bit 3
                               : data ^ (3LL << 8); // modify bit 8 and bit 9
    uint64_t chk_data = is_sbe ? data : mdf_data; //SB error correction DBE detection
    uint32_t chk_dbe_flag = is_sbe ? 0x3 : db_err_flag;
    uint32_t chk_sbe_flag = is_sbe ? sb_err_flag : 0x0;

    uint32_t bsz = 8 ; //byte size

    //Step 1 : Enable ECC protection and initialize memory with given value
    enable_vm_am_ecc_prot(reg_base);
    mem_raw_test(mem_ptr, bsz, data);
    check_err_flag(reg_base, (uint32_t)0x0, (uint32_t)0x3); //check no error reported
    
    //Step 2 : Disable ECC protection and modify single bit content
    disable_vm_am_ecc_prot(reg_base);
    mem_raw_test(mem_ptr, bsz, mdf_data);
    
    //Step 3 : Read memory after re-enabling ECC protection 
    enable_vm_am_ecc_prot(reg_base);
    //Check data correction
    do_check(mem_ptr, 1, chk_data);
    //Check SB error reported
    check_err_flag(reg_base, chk_sbe_flag, chk_dbe_flag);
  }

  void exec() {
    arcsync_id_init();
    proc_id = get_proc_id();
    uint32_t offset = proc_id * 0x80;
    
    setvect_for_expcn();

    if(proc_id == 0) { //L2 ARc
      uint64_t mask= (1LL<< EVT_CHILD0);
      event_send_children(mask);
      event_wait_all (mask);
    }
    else if(proc_id == 1){ //l1arc
      if (NPU_HAS_L2ARC){
        uint64_t mask = (1LL << EVT_PARENT);
        event_wait_any (mask);
      }
      
      //uint32_t* erp_ctrl_reg = (uint32_t*)(LC_SL0_PERI_BASE + L1_SFTY_MMIO_OFFSET + 0x0 /*SLICE_NPU_ERP_CTRL*/);
      vm_am_mem_init((uint32_t*)L1_PERI_SFTY_MMIO_BASE);

      //VM SBE 
      mem_ecc_check((uint32_t)L1_PERI_SFTY_MMIO_BASE, (uint64_t*)(L1_PERI_VM_BASE+offset),  true, true); 
      //VM DBE 
      mem_ecc_check((uint32_t)L1_PERI_SFTY_MMIO_BASE, (uint64_t*)(L1_PERI_VM_BASE+offset),  true, false); 
      //AM SBE 
      mem_ecc_check((uint32_t)L1_PERI_SFTY_MMIO_BASE, (uint64_t*)(L1_PERI_AM_BASE+offset),  false, true); 
      //AM DBE 
      mem_ecc_check((uint32_t)L1_PERI_SFTY_MMIO_BASE, (uint64_t*)(L1_PERI_AM_BASE+offset),  false, false); 

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

