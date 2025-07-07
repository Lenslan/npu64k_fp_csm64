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

#ifndef CLN_MAP
#define CLN_MAP

#include "sim_terminate.hpp"
#include "npu_mem_map_define.hpp"

#ifdef RTL_ARC
static _Uncached volatile unsigned int *target_ptr;
#else
unsigned int *target_ptr;
using namespace tensor::v200;
using namespace npu;
#endif

static void cln_aux_write(unsigned int addr,unsigned int data)
{
    target_ptr = (volatile unsigned int*) addr;
#ifdef RTL_ARC
    *target_ptr = data;
#else
    mem_write(target_ptr, data);
#endif
}

static void cln_aux_read(unsigned int addr, unsigned int data)
{
    int err=0;
    target_ptr = ( volatile unsigned int *) addr;
#ifdef RTL_ARC
    unsigned int read_value = *target_ptr;
#else
    unsigned int read_value = mem_read(target_ptr);
#endif
    if(read_value != data) {
        set_sim_finish_flag(++err);
    }
} 

static void cfg_noc_x_y (int x=0, int y=0, uint64_t base=0, uint64_t size=0xE0000000) {
#ifdef RTL_DPI
    cout << hex << "noc : x= " << x << ", y=" << y << ", base=" << base << ", size=" << size << endl;
#endif
    uint64_t aux_addr = LC_CLN_MST_NOC_0_0_ADDR;
    if(x | y){
        aux_addr = LC_CLN_MST_NOC_0_1_ADDR +  x*8*2 + 2*(y-1);
    }
    //aperture addr & size
    base = base >> 20; // 1 MB aligned
    size = size >> 20; // unit size is MB, i.e. 2^20

    //aperture addr
    cln_aux_write(LC_CLNR_ADDR_ADDR, aux_addr);
    cln_aux_write(LC_CLNR_DATA, base);
    cln_aux_write(LC_CLNR_ADDR_ADDR, aux_addr);
    cln_aux_read (LC_CLNR_DATA, base);
    //aperture size
    cln_aux_write(LC_CLNR_ADDR_ADDR, aux_addr+1);
    cln_aux_write(LC_CLNR_DATA, size);
    cln_aux_write(LC_CLNR_ADDR_ADDR, aux_addr+1);
    cln_aux_read (LC_CLNR_DATA, size);
}

static void cfg_noc (uint64_t base=0, uint64_t size=0xE0000000) {
    cfg_noc_x_y(0, 0, base, size);
}
//config local cluster SCM
static void cfg_scm(uint64_t base=LC_CSM_BASE, uint64_t size=0x1000000/*16MB*/) {
#ifdef RTL_DPI
    cout << hex << "scm : x= " << 0 << ", y=" << 0 << ", base=" << base << ", size=" << size << endl;
#endif
    int aux_addr = LC_CLNR_SHMEM_ADDR;
    //aperture addr & size
    //Local SCM BASE 
    base = base>>20;  // 1 MB aligned
    size = size>>6;   // unit is 64 Byte

    //aperture addr
    cln_aux_write(LC_CLNR_ADDR_ADDR, aux_addr);
    cln_aux_write(LC_CLNR_DATA, base);
    cln_aux_write(LC_CLNR_ADDR_ADDR, aux_addr);
    cln_aux_read (LC_CLNR_DATA, base);
    //apertur szie
    cln_aux_write(LC_CLNR_ADDR_ADDR, aux_addr+1);
    cln_aux_write(LC_CLNR_DATA, size);
    cln_aux_write(LC_CLNR_ADDR_ADDR, aux_addr+1);
    cln_aux_read (LC_CLNR_DATA, size);
}

//config local ccm_<X> port, apeature <y>
static void cfg_ccm_x_y (int x=0, int y=0, uint64_t base=LOCAL_CLST0_BASE, uint64_t size=0x400000){
#ifdef RTL_DPI
    cout << hex << "ccm : x= " << x << ", y=" << y << ", base=" << base << ", size=" << size << endl;
#endif
    int aux_addr=LC_CLNR_MST_CCM_0_0_ADDR + x*4*2 + y*2 ;
    base = base>>20;      // 1 MB aligned
    unsigned sz = size>>6; //unit is 64Byte
    unsigned int pos;
    for(pos=1; pos<32; pos++) { //simple log2, assume input must be power of 2
        if((sz >> pos) == 1){
            break;
        }
    }
    size = pos;
    
    //aperture addr
    cln_aux_write(LC_CLNR_ADDR_ADDR, aux_addr);
    cln_aux_write(LC_CLNR_DATA, base);
    cln_aux_write(LC_CLNR_ADDR_ADDR, aux_addr);
    cln_aux_read (LC_CLNR_DATA, base);
    //apertur szie
    cln_aux_write(LC_CLNR_ADDR_ADDR, aux_addr+1);
    cln_aux_write(LC_CLNR_DATA, 0x20/*EN*/ | size /*SZ*/);
    cln_aux_write(LC_CLNR_ADDR_ADDR, aux_addr+1);
    cln_aux_read (LC_CLNR_DATA, 0x20/*EN*/ | size /*SZ*/);

}

//config local cluster ccm
static void cfg_ccm(uint64_t base=LOCAL_CLST0_BASE, uint64_t size=0x400000) { 
    //ccm0 binds to L2 ARC
    //ccm1 binds to SL0
    //ccm2 .. SL1
    int idx=0;
    uint64_t addr;

    for(int slc=-1; slc < NPU_SLICE_NUM; slc++){
        if(slc == -1) { //L2
            addr =  base + size * 24;
        }else{//L1 slices
            addr =  base + size * slc;
        }
        cfg_ccm_x_y(idx++, 0, addr, size);
    }
}

static void set_cfg_done_flag(){
   target_ptr = ( volatile unsigned int *) LC_CLNR_SCM_BCR_1;
#ifdef RTL_ARC
    unsigned int read_value = *target_ptr;
#else
    unsigned int read_value = mem_read(target_ptr);
#endif
}

static void cfg_system_map () {
// FIXME: CLN config interface pending
//    cln_aux_read (LC_CLUSTER_BUILD, 0x20);
//    cfg_noc(0x0,              0xE0000000);
//    cfg_scm(LC_CSM_BASE,      0x01000000);//16MB
//    cfg_ccm(LOCAL_CLST0_BASE, 0x00400000);//4MB
//    set_cfg_done_flag();
}

static void enable_cln_l1_clkg() {
  cln_aux_write(LC_GLOBAL_CLK_GATE_DIS, 0);
  cln_aux_read (LC_GLOBAL_CLK_GATE_DIS, 0);

}

#endif
