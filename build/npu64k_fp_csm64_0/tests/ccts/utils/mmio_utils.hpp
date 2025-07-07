#ifndef MMIO_UTILS
#define MMIO_UTILS

#include "utils/npu_mem_utils.hpp"
#include "utils/arc_irq_expcn.hpp"

#define REG_READ_ONLY true
#define REG_READ_WRITE false


void mmio_illegal_access(const uint32_t& reg_addr, const bool& can_read, const bool& can_write) {
  if(!can_read){
    int v;
    clear_ecr();
    excpn_intention_flag = 1 ;
    do_read((int*)reg_addr, v);
    _sync();
    excpn_intention_flag = 0 ;
    // bus error from data memory 
    check_excpn_taken(ECR_DATA_BUS_ERR);
  }else{
    //8b read access
    char v8;
    clear_ecr();
    excpn_intention_flag = 1 ;
    do_read((char*)reg_addr, v8);
    _sync();
    excpn_intention_flag = 0 ;
    // bus error from data memory 
    check_excpn_taken(ECR_DATA_BUS_ERR);
  
    //16b read access
    short v16;
    clear_ecr();
    excpn_intention_flag = 1 ;
    do_read((short*)reg_addr, v16);
    _sync();
    excpn_intention_flag = 0 ;
    // bus error from data memory 
    check_excpn_taken(ECR_DATA_BUS_ERR);
  }

  if(!can_write){
    clear_ecr();
    excpn_intention_flag = 1 ;
    do_write((int*)reg_addr, 1, (int)0x0);
    _sync();
    excpn_intention_flag = 0 ;
    // bus error from data memory 
    check_excpn_taken(ECR_DATA_BUS_ERR);
  }else{
    //8b write access
    clear_ecr();
    excpn_intention_flag = 1 ;
    do_write((char*)reg_addr, 1, (char)0x0);
    _sync();
    excpn_intention_flag = 0 ;
    // bus error from data memory 
    check_excpn_taken(ECR_DATA_BUS_ERR);
  
    //16b write access
    clear_ecr();
    excpn_intention_flag = 1 ;
    do_write((short*)reg_addr, 1, (short)0x0);
    _sync();
    excpn_intention_flag = 0 ;
    // bus error from data memory 
    check_excpn_taken(ECR_DATA_BUS_ERR);
  }

}

template <typename T>
void mmio_access_test(const uint32_t& reg_addr, const bool& can_read, const bool& can_write, const T& rst_v, const T& mask) {
    //illegal access test
    mmio_illegal_access(reg_addr, can_read, can_write);

    //reset value check
    if(can_read) {
      do_check((T*)reg_addr, 1, rst_v);
    }

    // read after write test
    if(can_read && can_write){
      T wv = ~((T)0);
      T ref = mask & wv;
      do_write((T*)reg_addr, 1, wv);
      do_check((T*)reg_addr, 1, ref);

      do_write((T*)reg_addr, 1, (T)0);
      do_check((T*)reg_addr, 1, (T)0);
    }
}


void mmio_regs_test(const uint32_t& mmio_base, const uint32_t& nr, const uint32_t& id) {
  uint32_t status_rst_v = (NPU_SAFETY_LEVEL !=0) ? 0x100 : 0x0;
 //                /* MMIO register addr */    /* can read  write */ /*reset value */  /* write mask */
  mmio_access_test(mmio_base + 0x00 /* ID */,         true , false, id,                 (uint32_t)0);
  mmio_access_test(mmio_base + 0x04 /*CTRL*/,         true , true , (uint32_t)0x0,      (uint32_t)0x7);
  mmio_access_test(mmio_base + 0x08 /*STATUS*/,       true , false,  status_rst_v,      (uint32_t)0x0);
  mmio_access_test(mmio_base + 0x0C /*INT_ENABLE*/,   true , true , (uint32_t)0x0,      (uint32_t)0x0101);
  mmio_access_test(mmio_base + 0x10 /*INT_STATUS*/,   true , false, (uint32_t)0x0,      (uint32_t)0x0);
  mmio_access_test(mmio_base + 0x14 /*INT_SET*/,      true , true , (uint32_t)0x0,      (uint32_t)0x0);
  mmio_access_test(mmio_base + 0x18 /*INT_CLR*/,      true , true , (uint32_t)0x0,      (uint32_t)0x0);
  mmio_access_test(mmio_base + 0x1C /*RESERVED*/,     true , false, (uint32_t)0x0,      (uint32_t)0x0);
  mmio_access_test(mmio_base + 0x20 /*CNT_ISSUE*/,    true , true , (uint32_t)0x0,      (uint32_t)0xffffffff);
  mmio_access_test(mmio_base + 0x24 /*CNT_FINISH*/,   true , true , (uint32_t)0x0,      (uint32_t)0xffffffff);
  mmio_access_test(mmio_base + 0x28 /*RESERVED*/,     true , false, (uint32_t)0x0,      (uint32_t)0x0);
  mmio_access_test(mmio_base + 0x2c /*RESERVED*/,     true , false, (uint32_t)0x0,      (uint32_t)0x0);

  //HLAPI_I
  int off;
  for(int i=0; i < nr; i++){
    off = 0x60 + i*4;
    mmio_access_test(mmio_base + off,   true , true , (uint32_t)0x0,      (uint32_t)0xffffffff);
  }
  //HLAPI_IO_CYCLES
  mmio_access_test(mmio_base+off + 0x04/*IO_CYCLES*/, true , true , (uint32_t)0x0,      (uint32_t)0xffffffff);
  mmio_access_test(mmio_base+off + 0x08/*IO_COUNT*/,  true , true , (uint32_t)0x0,      (uint32_t)0xffffffff);
  //HLAPI_O
  mmio_access_test(mmio_base+off + 0x0C/*O_RES*/,     true , false, (uint32_t)0x0,      (uint32_t)0x0);
  mmio_access_test(mmio_base+off + 0x10/*O_SATUS*/,   true , false, (uint32_t)0x0,      (uint32_t)0x0);

  //mmio_access_test(mmio_base + 0x30 /*ISSUE*/,        true , true , (uint32_t)0x0,      (uint32_t)0x0);
  mmio_access_test(mmio_base + 0x34 /*RESERVED*/,     true , false, (uint32_t)0x0,      (uint32_t)0x0);
  mmio_access_test(mmio_base + 0x38 /*TAIL*/,         true , false, (uint32_t)0x0,      (uint32_t)0x0);
  //mmio_access_test(mmio_base + 0x40 /*SINGLE*/,       true , true , (uint64_t)0x0,      (uint64_t)0x0);
  mmio_access_test(mmio_base + 0x48 /*CONCACT_HEAD*/, true , true , (uint64_t)0x0,      (uint64_t)0xffffffffffffffff);
  mmio_access_test(mmio_base + 0x50 /*CONCACT_TAIL*/, true , true , (uint64_t)0x0,      (uint64_t)0xffffffffffffffff);
  //mmio_access_test(mmio_base + 0x58 /*PREFETCH*/,     true , true , (uint64_t)0x0,      (uint64_t)0x0);
}


#endif
