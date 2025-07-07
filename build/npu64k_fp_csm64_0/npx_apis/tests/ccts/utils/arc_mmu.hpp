#ifndef ARC_MMU
#define ARC_MMU

#include "sim_terminate.hpp"

static int get_ntlb_size(){
  int bcr = _lr(MMU_BUILD);
  int sz = (bcr >> 8) & 0x3;
  return (0x1 << (8+sz));
}

static int get_stlb_size(){
  int bcr = _lr(MMU_BUILD);
  int sz = (bcr >> 6) & 0x3;
  return (sz==1 ? 16 : 0 );
}

static int get_npgsz(){
  int bcr = _lr(MMU_BUILD);
  int sz = (bcr >> 15) & 0xf;
  sz = (sz > 2) ? 1 << (sz + 9) : 0;
  return (sz);
}

static int get_spgsz(){
  int bcr = _lr(MMU_BUILD);
  int sz = (bcr >> 19) & 0xf;
  sz = (sz > 2) ? 1 << (sz + 9) : 0;
  return (sz);
}

static int get_pae(){
  int bcr = _lr(MMU_BUILD);
  int sz = (bcr >> 12) & 0x1;
  return (sz);

}

static void enable_mmu(uint8_t asid=0, bool s=0){
  uint32_t v = (0x1 << 31) + (s << 29) + asid;
  _sr(v, PID);
}

static void disable_mmu(){
  _sr(0, PID);
}

static void LoadNtlbEntry(uint32_t va, uint64_t pa){
  uint32_t vpd = (va & 0xfffff000) | 0x300; // V & G are set
  uint32_t ppd = (pa & 0xfffff000) | 0xfff;

  _sr(vpd,TLBPD0);
  _sr(ppd,TLBPD1);
  if(get_pae()){
    uint32_t pae = (pa >> 32) & 0xff; // pyhsical address extension to 40b
   _sr(pae,TLBPD1_HI);
  }

  _sr(7, TLBCOMMAND); //TLBInsertEntry command 
  
  uint32_t res =_lr(TLBINDEX);
  if( (res>>31) && ((res>>28) & 0x7) ){ //error detected
    set_sim_finish_flag(1);
  }
}

#endif
