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
#include "utils/arc_mmu.hpp"

#define PAE40_TEST_ADDR 0xFF00000000

class test_program : public arc_program {
public:
  inline test_program() : arc_program() {
    irqflag = false;
  }
  virtual void irq() {
    irqflag = true;
  }
 
  void cfg_system_map_0 () {
    cfg_noc(0x0,                               PAE40_TEST_ADDR);
    cfg_scm(PAE40_TEST_ADDR+LC_CSM_BASE,       0x01000000);//16MB
    cfg_ccm(PAE40_TEST_ADDR+LOCAL_CLST0_BASE,  0x00400000);//4MB
    set_cfg_done_flag();
  }

  void mmu_test_prg(uint32_t va, uint64_t pa, bool chk_org=0, bool chk_excpn=0, uint32_t d = 0xbadc00fe){
    //load the NTLB entry 
    LoadNtlbEntry(va, pa);
    enable_mmu();
    //check original value
    if(chk_org) {
      do_check((uint32_t*)va, 10, d);
    }

    if(chk_excpn){
      //write to unmapped address will return error reposne
      clear_ecr();
      excpn_intention_flag = 1 ;
      do_write((uint32_t*)va, 1, d);
      _sync();
      excpn_intention_flag = 0 ;
      // bus error from data memory 
      check_excpn_taken(ECR_DATA_BUS_ERR);

      //read to unmapped address will return error reposne
      clear_ecr();
      excpn_intention_flag = 1 ;
      do_read((uint32_t*)va, d);
      _sync();
      excpn_intention_flag = 0 ;
      // bus error from data memory 
      check_excpn_taken(ECR_DATA_BUS_ERR);
    }else{
      //then read after write
      mem_raw_test((uint64_t*)va, 0x100);
    }
    _sync();
    disable_mmu();
  }


  void exec() {
    arcsync_id_init();
    proc_id = get_proc_id();
    evt_cfg();

    setvect_for_expcn();
    
    //instruction fetch without translation
    uint32_t intvect = _lr(VECBASE_AC_BUILD);
    for(int i=0; i<48; i++){
      uint32_t a = intvect + (i<<12);
      LoadNtlbEntry(a, a);
    }

    uint32_t l2dm_intv = 0x12345678;
    uint32_t l1dm_intv = 0x55667788;
    uint32_t l2va      = 0x22200000;
    uint32_t l1va      = 0x66600000;

    if(proc_id == 0) { //l2arc
      //L2 write L2 DM via fast DCCM  without going to CLN
      do_write((uint32_t*)NPU_ARC_DCCM_BASE, 10, l2dm_intv);
        
      //map CCM port, allocate DM to PAE40_TEST_ADDR + offset
      //cfg_system_map_0();

      uint64_t mask = (1LL << EVT_CHILD0);
      event_send_children((long long)mask);
      //L2 access L2 DM via virtual address that going to CLN
      mmu_test_prg(l2va, LC_L2_PERI_DM_BASE, 1, 0, l2dm_intv);
      //L2 access CSM via virtual address
      mmu_test_prg(l2va+0x1000, LC_CSM_BASE+0x1000);
      //L2 access NOC via virtual address
      mmu_test_prg(l2va+0x2000, PAE40_TEST_ADDR+0x2000, 0, 1);
       
      event_wait_all ((long long)mask);
            
    }
    else if(proc_id == 1) { //sl0 l1arc
      //L1 write L1 DM via via fast DCCM without going to CLN
      do_write((uint32_t*)NPU_ARC_DCCM_BASE, 10, l1dm_intv);
      if(NPU_HAS_L2ARC){
        uint64_t mask = (1LL << EVT_PARENT);
        event_wait_any ((long long)mask);
      } 
      //L1 access L1 DM via virtual address that going to CLN
      mmu_test_prg(l1va, LC_SL0_PERI_DM_BASE, 1, 0,  l1dm_intv);
      //L1 access CSM via virtual address
      mmu_test_prg(l1va+0x1000, LC_CSM_BASE+0x2000);
      //L1 access NOC via virtual address
      mmu_test_prg(l1va+0x2000, PAE40_TEST_ADDR+0x1000, 0, 1);

      event_send_parent();

    }
    set_sim_finish_flag(err_cnt);

  }

private:
  bool irqflag;
  uint32_t proc_id;
  int err_cnt = 0;

};
