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

#ifndef NPU_MEM_UTILS
#define NPU_MEM_UTILS

#include "npu_config.hpp"

#ifdef RTL_ARC
#include "utils/arc_irq_expcn.hpp"
#elif defined HOST_DPI

#else
using namespace tensor::v200;
using namespace npu;
#endif

//#define DCCM_BUILD   0x74
#define NPU_BUILD    0xEC
#define EVENT_BCR    0xFB0
#define STU_BCR      0xE4

template <typename T>
void set_type_init(const uint8_t& i, T& o){
  o=0;
  for(unsigned int b=0; b<sizeof(T);b++){
    o = o | ((T)(i + 0x11*b) << 8*b) ;   
  }
}

template <typename T>
void do_write(T* start_ptr, int tsz, T fix_value) {
#ifdef RTL_ARC
  _Uncached volatile T *ptr = start_ptr;
  for(int i=0; i < tsz; i++){
    *ptr++ = (T)(i + fix_value);
  }
#else
  T *ptr = start_ptr;
  T data;
  for(int i=0; i < tsz; i++){
    data  = (T)(i + fix_value);
    mem_write(ptr++, data);
  }
#endif
}

template <typename T>
void do_read(T* start_ptr, T& r) {
#ifdef RTL_ARC
  _Uncached volatile T *ptr = start_ptr;
  r = *ptr;
#else
  r  = mem_read(start_ptr);
#endif
}

template <typename T>
void do_read_only(T* start_ptr, int tsz) {
  T r;
#ifdef RTL_ARC
  _Uncached volatile T *ptr = start_ptr;
  for(int i=0; i < tsz; i++){
    r = *ptr++;
  }
#else
  T *ptr = start_ptr;
  for(int i=0; i < tsz; i++){
    r  = mem_read(ptr++);
  }
#endif
}

template <typename T>
void mem_rw_wo_chk(T* start_ptr, int size){
  T v;
  set_type_init(uint8_t(0x75), v);

  do_write(start_ptr,  size, v); 
  do_read_only(start_ptr, size); 
}

template <typename T>
int do_check(T* start_ptr, int tsz, T fix_value) {
  int err=0;
#ifdef RTL_ARC
  _Uncached volatile T *ptr = start_ptr;
#else
  T *ptr = start_ptr;
#endif
  for(int i=0; i < tsz; i++){
    T v =  (T)(i + fix_value);
  #ifdef RTL_ARC
    T r = *ptr++;
  #else
    T r = mem_read(ptr++);
  #endif

    if(r != v) {
    #ifndef RTL_ARC
      cout << hex << "Error: data mismatch on address " << start_ptr << ", expect " << v << ", got " << r << endl;
    #endif
      set_sim_finish_flag(++err);
    }
  }
  return err;
}

static void do_compare(uint32_t a, uint32_t b) {
  if(a != b) {
  #ifndef RTL_ARC
    cout << hex << "Error: data mismatch, expect " << a << ", got " << b << endl;
  #endif
    set_sim_finish_flag(1);
  }
}


template <typename T>
void mem_boundary_cross_test(T* base, uint32_t mem_sz/*byte size*/, uint32_t test_sz = 32/*byte size*/ ) {
  //convert byte size to type size
  uint32_t msz = mem_sz/sizeof(T);
  int tsz = test_sz/sizeof(T);
  //set initial value 
  T v0, v1;
  set_type_init(uint8_t(0x11), v0);
  set_type_init(uint8_t(0x58), v1);

  // write from base with tsz bytes
  do_write((T*)(base), tsz, v0);  
  do_check((T*)(base), tsz, v0);

  // write from base + msz - tsz/2 with tsz bytes, 
  // half write at end of memory, half write at start of memory
  do_write((T*)(base + msz - tsz/2), tsz, v1);  

  //check half of tsz, which locates at end of mem
  do_check((T*)(base + msz - tsz/2), tsz/2, v1);
  //check half of tsz, the writes will overwrite to beginning of mem  
  do_check((T*)(base) ,              tsz/2, T(v1 + tsz/2));
  //check next half of tsz are not overwritten
  do_check((T*)(base + tsz/2),       tsz/2, T(v0 + tsz/2));

}

template <typename T>
void mem_head_tail_test(T* base, uint32_t offset/*byte offset*/, uint32_t mem_sz/*byte size*/, uint32_t test_sz = 32/*byte size*/ ) {
  //convert byte size to type size
  uint32_t off = offset/sizeof(T);
  uint32_t msz = mem_sz/sizeof(T);
  int tsz = test_sz/sizeof(T);

  //set initial value 
  T v0, v1;
  set_type_init(uint8_t(0x77), v0);
  set_type_init(uint8_t(0x05), v1);

  // write from base with tsz bytes
  do_write((T*)(base+off),     tsz, v0);
  do_write((T*)(base+msz-off), tsz, v1);

  do_check((T*)(base+off),     tsz, v0);
  do_check((T*)(base+msz-off), tsz, v1);
}

template <typename T>
void mem_raw_test(T* base, uint32_t test_sz = 32/*byte size*/) {
  //convert byte size to type size
  int tsz = test_sz/sizeof(T);

  //set initial value 
  T v0;
  set_type_init(uint8_t(0xa3), v0);

  // write from base with tsz bytes
  do_write(base, tsz, v0);
  do_check(base, tsz, v0);
}

template <typename T>
void mem_raw_test(T* base, uint32_t test_sz, T v0) {
  //convert byte size to type size
  int tsz = test_sz/sizeof(T);

  // write from base with tsz bytes
  do_write(base, tsz, v0);
  do_check(base, tsz, v0);
}


template <typename T>
void mem_writeable_test(T* base, bool canwrite=1, bool canread=1) {
  //set initial value 
  T v0;
  set_type_init(uint8_t(0x68), v0);
#ifdef RTL_ARC
  clear_ecr();
  excpn_intention_flag = !canwrite ;    
  do_write((T*)(base), 1, v0);  
  _sync();
  excpn_intention_flag=0;
  //check exception
  if(!canwrite){
    // bus error from data memory 
    check_excpn_taken(ECR_DATA_BUS_ERR);
  }
  else { check_excpn_taken(0); }
 

  clear_ecr();
  excpn_intention_flag = !canread ;    
  do_read((T*)(base), v0);
  _sync();
  excpn_intention_flag=0;
  //check exception
  if(!canread){
    // bus error from data memory 
    check_excpn_taken(ECR_DATA_BUS_ERR);
  }
  else { check_excpn_taken(0); }
#elif defined HOST_DPI 
  int resp;
  //write test
  resp = canwrite ? 0 : 2;
  set_expect_resp(resp);
  do_write((T*)(base), 1, v0);
  //read
  resp = canread ? 0 : 2;
  set_expect_resp(resp);
  do_read((T*)(base), v0);
  //set ok response
  set_expect_resp(0);
#endif
}

static void mmio_boundary_test(uint32_t base, uint32_t size){
    mem_writeable_test((uint8_t*)(base + 0x18/*reg int_clr*/),  0, 0);
    mem_writeable_test((uint8_t*)(base + size - 0x200),         0, 0);
    mem_writeable_test((uint8_t*)(base + size - 0x10),          0, 0);
    mem_writeable_test((uint16_t*)(base + 0x18/*reg int_clr*/), 0, 0);
    mem_writeable_test((uint16_t*)(base + size - 0x200),        0, 0);
    mem_writeable_test((uint16_t*)(base + size - 0x10),         0, 0);
    mem_writeable_test((uint32_t*)(base + 0x18/*reg int_clr*/), 1, 1);
    mem_writeable_test((uint32_t*)(base + size - 0x200),        0, 1);
    mem_writeable_test((uint32_t*)(base + size - 0x10),         0, 1);
    mem_writeable_test((uint64_t*)(base + 0x18/*reg int_clr*/), 0, 1);
    mem_writeable_test((uint64_t*)(base + size - 0x200),        0, 1);
    mem_writeable_test((uint64_t*)(base + size - 0x10),         0, 1);
}

static void mem_boundary_test(uint32_t base, uint32_t size){
  #ifndef NPU_MEM_ECC
    mem_writeable_test((uint8_t*)(base),                        1, 1 );
    mem_writeable_test((uint8_t*)(base + size - 0x200),         1, 1);
    mem_writeable_test((uint8_t*)(base + size - 0x10),          1, 1);
    mem_writeable_test((uint16_t*)(base),                       1, 1);
    mem_writeable_test((uint16_t*)(base + size - 0x200),        1, 1);
    mem_writeable_test((uint16_t*)(base + size - 0x10),         1, 1);
    mem_writeable_test((uint32_t*)(base),                       1, 1);
    mem_writeable_test((uint32_t*)(base + size - 0x200),        1, 1);
    mem_writeable_test((uint32_t*)(base + size - 0x10),         1, 1);
  #endif
    mem_writeable_test((uint64_t*)(base),                       1, 1);
    mem_writeable_test((uint64_t*)(base + size - 0x200),        1, 1);
    mem_writeable_test((uint64_t*)(base + size - 0x10),         1, 1);
}


static uint32_t get_am_size() {
    uint32_t sz;
    //TODO: read BCR NPU_BUILD(0x0EC) to return actual mem size
    //P10019796-58855
    sz = NPU_AM_SIZE;

    return sz;
}

static uint32_t get_vm_size() {
    uint32_t sz;
    //TODO: read BCR NPU_BUILD(0x0EC) to return actual mem size
    //P10019796-58855
    sz = NPU_VM_SIZE;

    return sz;
}

static uint32_t get_dm_size() {
    uint32_t sz;
#ifdef RTL_ARC
    uint32_t sz0 = _lr(DCCM_BUILD); //bit 11:8
    sz0 = (sz0 >>8) & 0xf;
    sz = 1<<(9+sz0); // 1 for 512b
#else
    sz = 0x8000; //FIXME : got from headfile, i donot know where it is
#endif
    return sz;
}

static uint32_t get_csm_size() {
    uint32_t sz;
    //TODO: read BCR CSM_BUILD(0x0E5) to return actual mem size
    //P10019796-58855
    /*
    uint32_t sz0 = _lr(CSM_BUILD); //bit 11:8

    sz0 = (sz0 >>8) & 0xf;
    if(sz0<9){
        sz = 1<<(15+sz0); // 0 for 32KB
    }else{ //reserved
        sz = 0;    
    }
    */
    sz = NPU_CSM_SIZE;
    return sz;
}
static void disable_err_prot_on_dmp() {
#ifdef RTL_ARC
    uint32_t dm_prot = (_lr(0xC7/*ERP_BUILD*/)  >> 8) & 0x7;
    if(dm_prot) {
        _sr(0x2, 0x3F/*ERP_CTRL*/);
    }
#else
// NULL
#endif
}
template <typename T>
void mem_w_msk(T* addr, uint32_t wdata, uint32_t wstrb) {
#ifdef RTL_ARC
    _Uncached volatile T *target_ptr = addr;
    T read_value;
    read_value = *target_ptr;
    *target_ptr = (read_value & ~wstrb) | (wdata & wstrb);  
#else
    T *ptr = addr;
    T read_value;
    read_value = (mem_read(ptr) & ~wstrb) | (wdata & wstrb);
    mem_write(ptr, read_value);
#endif
}

template <typename T>
void mem_w_flip_single(T* addr, uint32_t bit) {
#ifdef RTL_ARC
    _Uncached volatile T *target_ptr = addr;
    T tmp_data;
    tmp_data  = *target_ptr;
    tmp_data ^= ( 1 << bit);
    *target_ptr = tmp_data;
#else
    T *ptr = addr;
    T read_value;
    read_value = (mem_read(ptr));
    read_value ^= ( 1 << bit);
    mem_write(ptr, read_value);
#endif
}

template <typename T>
void mem_w_flip_double(T* addr, uint32_t bit1, uint32_t bit2) {
#ifdef RTL_ARC
    _Uncached volatile T *target_ptr = addr;
    T tmp_data;
    tmp_data = *target_ptr;
    tmp_data ^= ( 1 << bit1);
    tmp_data ^= ( 1 << bit2);
    *target_ptr = tmp_data;
#else
    T *ptr = addr;
    T read_value;
    read_value = (mem_read(ptr));
    read_value ^= ( 1 << bit1);
    read_value ^= ( 1 << bit2);
    mem_write(ptr, read_value);
#endif
}

// memory read after write test
template <typename T>
void mem_init_done_pulling(T* addr, uint32_t wstrb) {
#ifdef RTL_ARC
    _Uncached volatile T *target_ptr = addr;
    int done=0;
    T pull_read_value;
    while(done==0){
        pull_read_value = *target_ptr;
        if( (pull_read_value & wstrb) == 0x0) {
           done++;
        }
    }
#else
    T *target_ptr = addr;
    int done=0;
    T pull_read_value;
    while(done==0){
        pull_read_value = mem_read(target_ptr);
        if( (pull_read_value & wstrb) == 0x0) {
           done++;
        }
    }
#endif
}

template <typename T>
void vm_mem_init(T* sfty_erp_ctrl_mmio) {
  mem_w_msk((int*)(sfty_erp_ctrl_mmio),0x10,0x10);
  mem_init_done_pulling((int*)(sfty_erp_ctrl_mmio),0x10);
}

template <typename T>
void am_mem_init(T* sfty_erp_ctrl_mmio) {
  mem_w_msk((int*)(sfty_erp_ctrl_mmio),0x20,0x20);
  mem_init_done_pulling((int*)(sfty_erp_ctrl_mmio),0x20);
}

template <typename T>
void vm_am_mem_init(T* sfty_erp_ctrl_mmio) {
  mem_w_msk((int*)(sfty_erp_ctrl_mmio),0x30,0x30);
  mem_init_done_pulling((int*)(sfty_erp_ctrl_mmio),0x30);
}
#endif
