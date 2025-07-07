#include "npu_config.hpp"
#include "host_utils.hpp"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define GRP0_SFTY_MMIO_BASE 0xf0000000
#define CSM_TEST_BASE       0xe8000000

#ifdef __cplusplus
extern "C" {
#endif

  void check_err_flag(uint32_t reg_base, uint32_t sbe_flag, uint32_t dbe_flag){
    do_check((uint32_t*)(reg_base + 0x0), 1, sbe_flag); //GRP_DBNK_ECC_CTRL
    do_check((uint32_t*)(reg_base + 0x0), 1, dbe_flag); //GRP_DBNK_ECC_CTRL
  }

  void  enable_ecc_prot(uint32_t reg_base){
    //Enable MEM ECC and clear error if have
    do_write((uint32_t*)(reg_base + 0x0), 1, (uint32_t)0x3); //GRP_DBNK_ECC_CTRL
    //check error are cleared
    check_err_flag(reg_base, (uint32_t)0xb, (uint32_t)0xb); //check no error reported
  }
  
  void  disable_ecc_prot(uint32_t reg_base){
    //disable MEM ECC
    do_write((uint32_t*)(reg_base + 0x0), 1, (uint32_t)0x0);
  }

  void mem_ecc_check(uint32_t reg_base, uint64_t* mem_ptr, bool is_sbe, int bnk=0){
    uint32_t sb_err_flag = (0x1 << 28) | (0xb);
    uint32_t db_err_flag = (bnk<<17) | (0x1 << 16) | (0xb); 
    // initialize memory with given value
    uint64_t data = 0xfedcba9876543210;
    uint64_t mdf_data = is_sbe ? data ^ (1LL << 3)  // modify bit 3
                               : data ^ (3LL << 8); // modify bit 8 and bit 9
    uint64_t chk_data = is_sbe ? data : mdf_data; //SB error correction DBE detection
    uint32_t chk_dbe_flag = is_sbe ? sb_err_flag : db_err_flag;
    uint32_t chk_sbe_flag = is_sbe ? sb_err_flag : db_err_flag;

    uint32_t bsz = 8 ; //byte size

    //Step 1 : Enable ECC protection and initialize memory with given value
    enable_ecc_prot(reg_base);
    mem_raw_test(mem_ptr, bsz, data);
    check_err_flag(reg_base, (uint32_t)0xb, (uint32_t)0xb); //check no error reported
    
    //Step 2 : Disable ECC protection and modify momory
    disable_ecc_prot(reg_base);
    mem_raw_test(mem_ptr, bsz, mdf_data);
    
    //Step 3 : Read memory after re-enabling ECC protection 
    enable_ecc_prot(reg_base);
    //Check data correction
    if(not is_sbe){
      set_expect_resp(2);
    }
    do_read(mem_ptr, chk_data);
    set_expect_resp(0);
    //Check SB error reported
    check_err_flag(reg_base, chk_sbe_flag, chk_dbe_flag);    
    //
    disable_ecc_prot(reg_base);

  }

  void wait_dbank_initdone(uint32_t reg_base) {
      uint32_t chk_data;
      int initdone=0;
      while (!initdone) {
        do_read((uint32_t*)(reg_base), chk_data);
        initdone = (chk_data & 0x8) == (0x8);
      }
  }

HOST_EXEC() {
  int err_cnt=0;
  int initdone_cnt=0;
  int initdone=0;
  set_intvect(0/*cluster_id*/);  
  arcsync_core_rst_dessert_all(0/*cluster id*/);   
  config_npx_sys_map_all();
  core_run(0/*cluster_id*/, 0);
  core_run(0/*cluster_id*/, 1);
 
  for(int grp=0; grp<NPU_NUM_GRP; grp++) {
    wait_dbank_initdone((uint32_t)(GRP0_SFTY_MMIO_BASE + grp*0x20000 + 0x24));
    for(int bnk=0; bnk<NPU_CSM_BANKS_PER_GRP; bnk++){
      uint64_t baddr  = CSM_TEST_BASE + (grp*NPU_CSM_SIZE_PER_GRP) + (grp<<15)/*32KB*/ + (bnk<<12)/*4KB*/; 

        //SBE 
        mem_ecc_check((uint32_t)(GRP0_SFTY_MMIO_BASE + grp*0x20000 + 0x24), (uint64_t*)(baddr), true, bnk); 
        //DBE 
        mem_ecc_check((uint32_t)(GRP0_SFTY_MMIO_BASE + grp*0x20000 + 0x24), (uint64_t*)(baddr+0x20), false, bnk); 
      }
  }
  
  // host exit the simulator
  host_exit(err_cnt);
  HOST_EXEC_RET;
}

#ifdef __cplusplus
}
#endif
