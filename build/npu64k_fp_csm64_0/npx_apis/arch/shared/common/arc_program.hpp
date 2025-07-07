/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2021-2023 Synopsys, Inc.                              **/
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

//
// Processor abstraction interface
//

#ifndef ARC_PROGRAM_INCLUDED
#define ARC_PROGRAM_INCLUDED

#include "npu_defines.hpp"
#include <cstdint>
#include <cstddef>
#include <assert.h>

// forward typedefs
namespace npu {
template<typename T> struct ctrl_dma_regs;
}
namespace npu_conv {
struct conv_hlapi_t;
}
namespace npu_act {
struct act_hlapi_t;
}
namespace npu_dma {
struct dma_hlapi_t;
}
namespace npu_stu {
struct stu_hlapi_t;
}


namespace npu {
typedef uint32_t timestamp_t;
typedef uint32_t vm_context_t;
struct pcontext_t {
  inline pcontext_t() = default;
  inline pcontext_t(const pcontext_t&) = default;
  inline pcontext_t(int p, char* d, int b) {
    dbg_id    = b;
    proc_id   = p;
    dccm_base = d;
  }
  int   dbg_id;    // unique id for debugging
  int   proc_id;   // virtual process ID
  char* dccm_base; // base address of DCCM
};


// forward declaration
class arc_program;


//////////////////////////////////////////////////////////////////////////////
//
// Hypervisor functions
//
//////////////////////////////////////////////////////////////////////////////

// get processor ID
uint32_t hv_get_arcnum();
// for L2ARC set the streamid for the transactions initiated by STUs in group
// for L1ARC set the streamid for the transactions initiated by  iDMA/oDMA in core
void hv_set_streamid(int32_t sid, int32_t grp=0);
// for L2ARC set the substreamid for the transactions initiated by STUs in group
// for L1ARC set the substreamid for the transactions initiated by  iDMA/oDMA in core
void hv_set_substreamid(int32_t ssid, int32_t grp=0);
// return the MMIO base address of a slice/top
void* hv_get_core_mmio_base(int32_t core_id);
// poll if any of the virtual machines has an active event
bool hv_poll_vm(vm_context_t& vmid);
// switch context to a virtual machine
void hv_sel_vm(vm_context_t vmid);
// map physical child events range [cpevt,cpevt+cnum-1] to virtual child events range [0,cnum-1]
// map physical accelerator events range [aevt,aevt+anum-1] to virtual child events range [0,anum-1]
void hv_event_map(uint32_t cpevt, // first physical child event
                  uint32_t cnum,  // number of child events
                  uint32_t apevt, // first physical accelerator event
                  uint32_t anum   // number of accelerator events
                  );
// create user mode process with context
void hv_create_vm(arc_program*, const pcontext_t&);
// switch context to user-mode process
void hv_switch_vm();
// kill user-mode process
void hv_kill_vm();
// check if alive
bool hv_vm_active();
// send interrupt to parent
void hv_interrupt_parent();
// map a memory region into the active virtual machine virtual address space
//void hv_map(char* vptr, uint64_t pptr, size_t sz, uint8_t attr);
// unmap a memory region
void hv_unmap(char* vptr);
// set the ARC internal fast DCCM base address
void hv_set_fast_dccm_base(char* p);
// exit process
void hv_arc_exit();
#define arc_exit hv_arc_exit


//////////////////////////////////////////////////////////////////////////////
//
// Virtualized user mode functions
//
//////////////////////////////////////////////////////////////////////////////

// get virtual processor ID
uint32_t get_proc_id();

// get debugging unique ID
uint32_t get_dbg_id();

// formatted printing
void arc_printf(const char* fmt, ...);

//
// Time control
//
// get the current time
timestamp_t get_timestamp();
// run for a number of cycles
void run_cycles(timestamp_t c);
// wait for a number of cycles
void wait_cycles(timestamp_t c);
// yield to hypervisor
void yield();
// exit to hypervisor
void vmexit();

//
// Events
//
// wait for any event from a mask and decrement most lsb counter
uint64_t event_wait_any(uint64_t ev);
// wait for all events from the mask and decrement counters
uint64_t event_wait_all(uint64_t ev);
// send event to parent
void event_send_parent();
// send event to one or multiple peers
void event_send_peers(uint64_t ev);
// send event to one or multiple children
void event_send_children(uint64_t ev);
// increment and decrement event counters, one per bit
void event_incr(uint64_t ev);
void event_decr(uint64_t ev);
// read/write event counters
uint8_t event_read(uint32_t ev);
void event_write(uint32_t ev, uint8_t val);
    
//
// Ancillary functions
//
// SW trace
void sw_trace(uint32_t ev);


//
// Get access to memory addresses
//
// Addresses have three spaces:
// - fast DCCM space is direct access from ARC to its DCCM
// - slice local memory space is the aperture to access local slice memories and MMIO registers
// - global memory space is accessing CLN

// get the ARC internal fast DCCM base address
char* get_fast_dccm_base();
// get the slice local DMI DCCM base address
char* get_slice_dccm_base();
// get the slice VM base address
char* get_slice_vm_base();
// get the slice AM base address
char* get_slice_am_base();
// get the CSM base address
char* get_csm_base();
// get the MMIO based address of an accelerator
char* get_mmio_base_conv();
char* get_mmio_base_act();
char* get_mmio_base_idma();
char* get_mmio_base_odma();
char* get_mmio_base_stu(int);

unsigned char* mem_read(unsigned char* dst, const unsigned char* src, size_t len);
void mem_write(unsigned char* dst, const unsigned char* src, size_t len);
unsigned char* dget_ptr(unsigned char* ptr);

//
// Inline functions to convert between memory spaces
//
// convert from fast DCCM to slice local DCCM
template<typename T> T* fast2slice_dccm(T*);
// convert from fast DCCM to slice global DCCM
template<typename T> T* fast2global_dccm(T*);
// slice local address space to NPU level address space conversion
template<typename T> T* slice2global(T*);

//
// Functions related to a specific processor instance
// 
class arc_program {
  public:
  arc_program();
  // pure virtual functions that need to be implemented by actual test
  virtual void exec() = 0;
  virtual void exec(int argc, const char** argv) {
    exec();
  }
  virtual void irq() = 0;
  // enable a backdoor way to access memory, only works for RTL DPI  
  void set_mem_backdoor(int, int);
  void enable_dmerr(int, int);
  void set_scm_aperture(int, int);
  
};
}
#include "arc_program_inline.hpp"
#endif
