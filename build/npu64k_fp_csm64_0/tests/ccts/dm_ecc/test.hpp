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

  void check_err_flag(uint32_t sbe_flag, uint32_t dbe_flag){
    do_compare(_lr(0x3C), sbe_flag); //SBE_CNT
    do_compare(_lr(0x3F), dbe_flag); //ERP_CTRL
  }

  void  enable_ecc_prot(){
    //Enable MEM ECC and clear error if have
    _sr(0x0, 0x3F); //ERP_CTRL
    _sr(0X0, 0x3C); //SBE_CNT
    _sync(); //flush pipeline to make sure MMIO update take effect
    //check error are cleared
    check_err_flag((uint32_t)0x0, (uint32_t)0x0); //check no error reported
  }
  
  void  disable_ecc_prot(){
    //disable MEM ECC
    _sr(0x2, 0x3F); //ERP_CTRL
    _sync(); //flush pipeline to make sure MMIO update take effect      
  }

  void mem_ecc_check(uint64_t* mem_ptr, bool is_sbe){
    uint32_t sb_err_flag = (1 << 4); // SBE_CNT[7:4] : dm_sbe_cnt
    uint32_t db_err_flag = (1 << 21); // DM fatal error in ERP_CTRL

    // initialize memory with given value
    uint64_t data = 0xfedcba9876543210;
    uint64_t mdf_data = is_sbe ? data ^ (1LL << 3)  // modify bit 3
                               : data ^ (3LL << 8); // modify bit 8 and bit 9
    uint64_t chk_data = is_sbe ? data : mdf_data; //SB error correction DBE detection
    uint32_t chk_dbe_flag = is_sbe ? 0x0 : db_err_flag;
    uint32_t chk_sbe_flag = is_sbe ? sb_err_flag : 0x0;

    uint32_t bsz = 8 ; //byte size

    //Step 1 : Enable ECC protection and initialize memory with given value
    enable_ecc_prot();
    mem_raw_test(mem_ptr, bsz, data);
    check_err_flag((uint32_t)0x0, (uint32_t)0x0); //check no error reported
    
    //Step 2 : Disable ECC protection and modify single bit content
    disable_ecc_prot();
    mem_raw_test(mem_ptr, bsz, mdf_data);
    
    //Step 3 : Read memory after re-enabling ECC protection 
    enable_ecc_prot();
    //Check data correction
    if(! is_sbe){
      clear_ecr();
      excpn_intention_flag = 1; //mem error exceprtion is expected for DBE(ECR 0x030500)
    }

    do_read(mem_ptr, chk_data);
    _sync();
    
    if(! is_sbe){
      excpn_intention_flag = 0;
      check_excpn_taken(ECR_INT_MEM_ERR);
    }
    //Check SB error reported
    check_err_flag(chk_sbe_flag, chk_dbe_flag);

  }

  void exec() {
    arcsync_id_init();
    proc_id = get_proc_id();
    uint32_t offset = proc_id * 0x80;
    
    setvect_for_expcn();

    //DM SBE 
    mem_ecc_check((uint64_t*)(NPU_ARC_DCCM_BASE+offset), true);
    //DM DBE 
    mem_ecc_check((uint64_t*)(NPU_ARC_DCCM_BASE+offset), false);

    set_sim_finish_flag(err_cnt);
  }



private:
  bool irqflag;
  uint32_t proc_id;
  int err_cnt = 0;
};

