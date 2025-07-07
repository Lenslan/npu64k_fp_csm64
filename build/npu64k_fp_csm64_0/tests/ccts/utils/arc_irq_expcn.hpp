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

#ifndef ARC_IRQ_EXCPN
#define ARC_IRQ_EXCPN

static _Uncached volatile uint32_t irq_sync_flag = 0;
static _Uncached volatile uint32_t excpn_intention_flag = 0;
static _Uncached volatile uint32_t excpn_casue = 0;

#define ECR_DATA_BUS_ERR  0x011000
#define ECR_ILLEGAL_INST  0x020000
#define ECR_INT_MEM_ERR   0x030500
#define ECR_INST_TLB_MISS 0x040000
#define ECR_DATA_TLB_MISS 0x050000
#define ECR_PrivilegeV    0x070000
#define ECR_PrivilegeV_XPU 0x07011f


#include "arc_mmu.hpp"
#include "npu_mem_map_define.hpp"

template <typename T>
void write_mmio_reg(T* start_ptr,  T data){
#ifdef RTL_ARC
  _Uncached volatile T *ptr = start_ptr;
  *ptr = data;
#else
  mem_write(start_ptr, data);
#endif
}

static _Interrupt void timer0_handler()
{
    unsigned ctrl = _lr(REG_CONTROL0);
    irq_sync_flag = ctrl;
    ctrl &= 0xFFF7; // clear the IP bit
    _sr(ctrl, REG_CONTROL0);
    _sync();
}

static _Interrupt void ext_irq_handler()
{
  irq_sync_flag = 0x5; // ext_irq_pin
  _sync();
}

static _Interrupt void accl_done_handler()
{
  unsigned an = _lr(ICAUSE); //active number
  uint32_t proc_id = get_proc_id();
  uint32_t base = 0;
  uint32_t data = 0x1;
  if((proc_id == 0) || (proc_id == NPU_SLICE_NUM+1)){ //L2 ARC0/1
    if((an>43) && (an<52)){
      base = USTU0_MMIO_BASE + 0x1000*(an-44) + 0x18;     
    }else{
      set_sim_finish_flag(1);
    }
  }else{
    switch(an){
      case 44: base = L1_PERI_CONV_MMIO_BASE + 0x18; break;
      case 45: base = L1_PERI_GTOA_MMIO_BASE + 0x18; break;
      case 46: base = L1_PERI_IDMA_MMIO_BASE + 0x18; break;
      case 47: base = L1_PERI_ODMA_MMIO_BASE + 0x18; break;
      default: set_sim_finish_flag(1); break;
    }
  }  

  write_mmio_reg((uint32_t*)base, data);

  irq_sync_flag = 0x2;
  _sync();
}

static _Interrupt void accl_err_handler()
{
  unsigned an = _lr(ICAUSE); //active number
  uint32_t proc_id = get_proc_id();
  uint32_t base;
  uint32_t data = 0x100;
  if((proc_id == 0) || (proc_id == NPU_SLICE_NUM+1)){ //L2 ARC0/1
    if((an>39) && (an<44)){
      for(int g=0; g<NPU_NUM_GRP; g++){
        for(int c=0; c<NPU_NUM_STU_PER_GRP; c++){
          base = USTU0_MMIO_BASE + 0x2000*(an-40) + 0x1000*c + 0x18;   
          write_mmio_reg((uint32_t*)base, data);
        }
      }
    }else{
      set_sim_finish_flag(1);
    }
  }else{
    if((an>39) && (an<41)){
      for(int a=0; a<5; a++){
          // for mem_ecc_irq
          if (a == 4) {
            base = L1_PERI_SFTY_MMIO_BASE;     
            write_mmio_reg((uint32_t*)base, 0x80000000);
          } else {
            base = L1_PERI_IDMA_MMIO_BASE + 0x1000*a + 0x18;     
            write_mmio_reg((uint32_t*)base, data);
          }
      }
    }else{
      set_sim_finish_flag(1);
    }
  }  


  irq_sync_flag = 0x3;
  _sync();
}

static _Interrupt void arcsync_eid_int_handler()
{
    arcsync_ack_irq();
    irq_sync_flag = 0x4;
    _sync();
}

static _Interrupt void arcsync_ac_int_handler()
{
    arcsync_ack_ac_irq();
    irq_sync_flag = 0x5;
    _sync();
}

// Sleep while waiting for an interrupt
static void wait_irq()
{
    irq_sync_flag = 0;
    _clri();
    while (irq_sync_flag == 0) {
      // [7:5]=0  sleep mode
      //   [4]=1  enable interrupts
      // [3:0]=15 lowest priority required to wakeup
        _sleep(0x1F);
        _clri();
    }
    _seti(0);
}

static void disable_irq()
{
	_clri();
}

static void _Exception mem_excpn_handler() {
    excpn_casue = _lr(REG_ECR);
    
    if(excpn_intention_flag==0) {
      // exit if exceptions detected
      set_sim_finish_flag(1);
    }
    else {
      uint32_t eret = _lr(REG_ERET);
      _sr(eret+4, REG_ERET);  
    }
}

static void _Exception inst_err_excpn_handler() {
    excpn_casue = _lr(REG_ECR);
    if(excpn_intention_flag==2) {
        uint32_t eret = _lr(REG_ERET);
        _sr(eret+4, REG_ERET);
    }else{
        // exit if exceptions detected
        set_sim_finish_flag(1);
    }
}

static void _Exception tlbmiss_excpn_handler() {
    uint32_t ecr=_lr(REG_ECR);
    uint32_t efa=_lr(REG_EFA);
    excpn_casue = ecr;
    switch ((ecr>>16) & 0xf ) {
        case 0x4:
        case 0x5: LoadNtlbEntry(efa, efa); break;
        default: break;
    }
}

static void _Exception privilege_excpn_handler() {
    excpn_casue = _lr(REG_ECR);
    if(excpn_intention_flag==3) {
        uint32_t eret = _lr(REG_ERET);
        _sr(eret+4, REG_ERET);
    }else{
        // exit if exceptions detected
        set_sim_finish_flag(1);
    }
}

static void trap_switch_model(bool user_mode) {
  uint32_t sta = _lr(ERSTATUS);
  if(user_mode) {
    sta |= (0x1 << 20) | (0x1 <<7); //STATUS32.U & STATUS32.US: enable user sleep
  }
  else{
    sta &= 0xffffff7f;
  }
  _sr(sta , ERSTATUS);
}

static void _Exception trap_excpn_handler() {
    uint32_t ecr=_lr(REG_ECR);
    excpn_casue = ecr;
    switch (ecr & 0xff ) {
        case 0x0: trap_switch_model(0); break; //switch to kernel model
        case 0x1: trap_switch_model(1); break; //switch to user model
        default: break;
    }
}

_Asm void SET_SP(int* ptr) {
  % reg ptr
  mov_s %sp, ptr
}
//reserve 100 words for user stack
static int _SP[100]={0};
static void switch_user_mode(){
  _trap(1); 
  user_mode_flag=1;
  SET_SP(&_SP[50]);
}

static void clear_ecr(){
  excpn_casue = 0;
}

static void check_excpn_taken(uint32_t v) {
    if (excpn_casue != v){
        set_sim_finish_flag(1);
    }
}

static void _set_ptag(uint32_t paddr) {
  uint32_t ic_build = _lr(0x77);
  uint32_t ic_size = 1 << (((ic_build >>12) & 0xf) + 9);
  uint32_t ic_ways = 1 << ((ic_build >>8) & 0xf);
  uint32_t ic_way_size = ic_size / ic_ways;

  uint32_t mmu_build = _lr(0x6F);
  uint32_t psize0 = 1 << (((mmu_build >> 15) & 0xf) + 9);

  if(ic_way_size > psize0){
    _sr(paddr, 0x1E); //IC_PTAG 
  }
}

static void setvect_for_expcn(){
  _set_ptag(_lr(0x25)); // int_vect_base
  _setvectx(1, mem_excpn_handler);
  _setvectx(2, inst_err_excpn_handler);
  _setvectx(3, mem_excpn_handler);
  _setvectx(4, tlbmiss_excpn_handler);
  _setvectx(5, tlbmiss_excpn_handler);
  _setvectx(7, privilege_excpn_handler);
  _setvectx(9, trap_excpn_handler);
}

static void setvect_for_int(){
  uint32_t proc_id = get_proc_id();
  int int_base = _lr(0x25); // int_vect_base
  _set_ptag(int_base);

  if((proc_id == 0) || (proc_id == NPU_SLICE_NUM+1)){ //L2 ARC0/1
    _setvecti(16, timer0_handler);
    _setvecti(22, arcsync_ac_int_handler);  //arcsync pyhsical ac irq
    _setvecti(23, arcsync_eid_int_handler); //arcsync pyhsical eid irq

    for(int v=0; v<ARCSYNC_VIRT_MACHINES; v++){
    _setvecti(24+v+0, arcsync_ac_int_handler); //arcsync_ac_irq
    _setvecti(24+v+1, arcsync_eid_int_handler); 
    }

    for(int g=0; g<NPU_NUM_GRP; g++){
    _setvecti(40+g, accl_err_handler); //grp error 
    }

    for(int c=0; c<NPU_STU_CHAN_NUM;c++){
    _setvecti(44+c, accl_done_handler); //STU done 
    }
    _setvecti(52, ext_irq_handler);  //arcsync pyhsical ac irq
    _setvecti(53, ext_irq_handler); //arcsync pyhsical eid irq
  }else{
    _setvecti(16, timer0_handler);
    _setvecti(24, arcsync_ac_int_handler);  //arcsync pyhsical ac irq
    _setvecti(25, arcsync_eid_int_handler); //arcsync pyhsical eid irq
    _setvecti(40, accl_err_handler); // conv/gtoa/idma/odma/mem_ecc err
    _setvecti(44, accl_done_handler); // slc conv done
    _setvecti(45, accl_done_handler); // slc gtoa done
    _setvecti(46, accl_done_handler); // slc idma done
    _setvecti(47, accl_done_handler); // slc odma done
  }
}
#endif
