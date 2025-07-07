//
// ARC HW abstraction for DPI simulation
//

#include <cstdlib>
#include <string>
#ifdef RTL_ARC
  #ifdef __cplusplus
    extern "C" {
  #endif
  #include "apexextensions.h"
  #ifdef __cplusplus
    }
  #endif
#include <math.h>
#include <arc/arc_conditions.h>
#include <arc/arc_intrinsics.h>
#endif
using namespace std;
#include <iostream>

#ifdef RTL_DPI
  #ifndef NPU_RTL_SIMULATOR
    #define NPU_RTL_SIMULATOR 0
  #endif
  #if NPU_RTL_SIMULATOR==1
    #include "xrun_hdrs.h"
  #elif NPU_RTL_SIMULATOR==2
    #include "sv2c.h"
  #else
    #include "vc_hdrs.h"
  #endif
#include "vpi_user.h"
#endif


// interrupt callback function
void irq_callback();

namespace tensor::v200 {
  #if defined(HOST_ARC) || defined(HOST_SYSTEMC)
  template<typename T>
  T mem_read(const T* p) {
    return *p;
  }
  template<typename T>
  void mem_write(T* p, const T& d) {
    *p = d;
  }
  #endif
  #ifdef RTL_DPI
  //
  // Memory read/write
  //
  template<typename T>
  inline T mem_read(const T* p) {
    T      r;
    const char*  pv = reinterpret_cast<const char*>(p);
    char*  pr = reinterpret_cast<char*>(&r);
    size_t s = sizeof(T);
    int    m;

    while (s != 0) {
      // check start alignment
      m = 8-(reinterpret_cast<long long>(pv)&0x7);
      if (m == 8 && s < 8) {
        // cannot to do 64b
        m = 4;
      } // else can do 64b
      if (m < 8 && m >= 4) {
        if (s < 4) {
          // cannot to 32b
          m = 2;
        } else {
          // can do 32b
          m = 4;
        }
      }
      if (m < 4 && m >= 2) {
        if (s < 2) {
          // cannot do 16b
          m = 1;
        } else {
          // can do 16b
          m = 2;
        }
      }
      switch (m) {
      case 1: proc_read_byte((int)reinterpret_cast<long long>(pv), pr); break;
      case 2: proc_read_short((int)reinterpret_cast<long long>(pv), reinterpret_cast<short*>(pr)); break;
      case 4: proc_read_int((int)reinterpret_cast<long long>(pv), reinterpret_cast<int*>(pr)); break;
      case 8: proc_read_long((int)reinterpret_cast<long long>(pv), reinterpret_cast<long long*>(pr)); break;
      default: assert(0);
      }
      pv += m;
      pr += m;
      s  -= m;
    }
    return r;
  }
  template<typename T>
  inline void mem_write(T* p, const T& d) {
    char*  pv = reinterpret_cast<char*>(p);
    const char* pr = reinterpret_cast<const char*>(&d);
    size_t s = sizeof(T);
    int    m;
    while (s != 0) {
      // check start alignment
      m = 8-(reinterpret_cast<long long>(pv)&0x7);
      if (m == 8 && s < 8) {
        // cannot do 64b
        m = 4;
      } // else can do 64b
      if (m < 8 && m >= 4) {
        if (s < 4) {
          // cannot to 32b
          m = 2;
        } else {
          // can do 32b
          m = 4;
        }
      }
      if (m < 4 && m >= 2) {
        if (s < 2) {
          // cannot do 16b
          m = 1;
        } else {
          // can do 16b
          m = 2;
        }
      }
      switch (m) {
      case 1: proc_write_byte((int)reinterpret_cast<long long>(pv), *pr); break;
      case 2: proc_write_short((int)reinterpret_cast<long long>(pv), *reinterpret_cast<const short*>(pr)); break;
      case 4: proc_write_int((int)reinterpret_cast<long long>(pv), *reinterpret_cast<const int*>(pr)); break;
      case 8: proc_write_long((int)reinterpret_cast<long long>(pv), *reinterpret_cast<const long long*>(pr)); break;
      default: assert(0);
      }
      pv += m;
      pr += m;
      s  -= m;
    }
  }
  #endif
}

namespace npu {
  // get processor ID
  inline uint32_t hv_get_arcnum() {
  #ifdef RTL_DPI
    return proc_get_arcnum();
  #elif defined(RTL_ARC)
    int tmp;
    tmp = _lr(0x4); // read IDENTITY BCR

    uint32_t arcnum = (tmp>>8)&0x000000ff; // extract arcnum
    assert(arcnum<ARCSYNC_MAX_CORES_PER_CL);
    return arcnum;
  #elif defined(HOST_ARC) || defined(HOST_SYSTEMC)
    assert(0);
    return 0;
  #endif
  }
  inline uint32_t get_proc_id() {
    return hv_get_arcnum();
  }
  inline uint32_t arcsync_coreid() {
  #ifdef RTL_DPI
    return proc_get_arcnum();
  #elif defined(RTL_ARC)
    //assert(0);
    //return 0;
    uint32_t tmp;
    tmp = _lr(0x4); // read IDENTITY BCR

    uint32_t arcnum = (tmp>>8)&0x000000ff; // extract arcnum
    assert(arcnum<ARCSYNC_MAX_CORES_PER_CL);
    tmp = _lr(0x298);  // read CLUSTER_ID
    uint32_t clusternum = tmp & 0x000000ff; // extract clusternum
    assert (clusternum<ARCSYNC_NUM_CLUSTER);
    
    tmp = (clusternum<< (uint32_t)log2(ARCSYNC_MAX_CORES_PER_CL))|arcnum;
    return tmp;
    
  #elif defined(HOST_ARC) || defined(HOST_SYSTEMC)
    assert(0);
    return 0;
  #endif
  }

  inline void evt_cfg() {
  }

  inline void cfg_grp_sid_ssid(uint32_t grp, uint32_t sid, uint32_t ssid) {
  #ifdef RTL_DPI
    proc_sr_aux(grp,  0xF07);
    proc_sr_aux(sid,  0xF08);
    proc_sr_aux(ssid, 0xF09);
  #elif RTL_ARC
    _sr(grp,  0xF07);
    _sr(sid,  0xF08);
    _sr(ssid, 0xF09);
  #endif
  }

  inline void cfg_vmid(uint32_t vmid) {
  #ifdef RTL_DPI
    proc_sr_aux((vmid & 0xf),  0xF00);
  #elif RTL_ARC
    _sr((vmid & 0xf),  0xF00);
  #endif
  }

  inline uint32_t cur_vmid(int vmid) {
  #ifdef RTL_ARC
    return (_lr(0xF00));
  #endif
  #ifdef RTL_DPI
    int vid;
    proc_lr_aux(0xF00, &vid);
    return vid;
  #endif
    return 0; // No return if not defined RTL_ARC or RTL_DPI
  }

  inline void cfg_vmmap(uint32_t cbase, uint32_t cnum, uint32_t abase, uint32_t anum) {
  #ifdef RTL_ARC
    uint32_t temp = ((cbase & 0xFF) | ((cnum & 0xff) << 8) | ((abase & 0xff) << 16) | ((anum & 0xff) << 24));
    _sr(temp,  0xF01);
  #endif
  #ifdef RTL_DPI
    int temp = ((cbase & 0xFF) | ((cnum & 0xff) << 8) | ((abase & 0xff) << 16) | ((anum & 0xff) << 24));
    proc_sr_aux(temp,  0xF01);
  #endif
  }

  inline uint32_t arcsync_arcnum() {
  #ifdef RTL_ARC
    assert(0);
    return 0;
  #elif defined(HOST_ARC) || defined(HOST_SYSTEMC)
    assert(0);
    return 0;
  #else
    return proc_get_arcnum();
  #endif
  }
  inline uint32_t arcsync_clusternum() {
  #ifdef RTL_ARC
    return (_lr(0x298) & 0x0ff); // CLUSTER_ID
  #elif defined(HOST_ARC) || defined(HOST_SYSTEMC)
    assert(0);
    return 0;
  #else
    return proc_get_clusternum();
  #endif
  }
  inline void arcsync_id_init() {
  #ifdef RTL_ARC
    //FIXME: do nothing due to remove GP0/GP1
    //int tmp;
    //tmp = _lr(0x4); // read IDENTITY BCR

    //int arcnum = (tmp>>8)&0x000000ff; // extract arcnum
    //assert(arcnum<ARCSYNC_MAX_CORES_PER_CL);
    //tmp = _lr(0x298);  // read CLUSTER_ID
    //int clusternum = tmp & 0x000000ff; // extract clusternum
    //assert (clusternum<ARCSYNC_NUM_CLUSTER);
    //// concatenate and store into extension AUX regs
    //_sr(arcnum, AR_EVT_GP0);
    //_sr((clusternum<< (int)log2(ARCSYNC_MAX_CORES_PER_CL))|arcnum, AR_EVT_GP1);
  #endif
  }
  // get the ARC internal fast DCCM base address
  inline char* get_fast_dccm_base() {
    return NPU_FAST_DCCM_BASE;
  }
  // get the slice local DMI DCCM base address
  inline char* get_slice_dccm_base() {
    return NPU_INTRA_SLICE_DCCM_BASE;
  }
  // get the slice VM base address
  inline char* get_slice_vm_base() {
    return NPU_INTRA_SLICE_VM_BASE;
  }
  // get the slice AM base address
  inline char* get_slice_am_base() {
    return NPU_INTRA_SLICE_AM_BASE;
  }
  // get the CSM base address
  inline char* get_csm_base() {
    return NPU_CSM_BASE;
  }
 // get the MMIO based address of an accelerator
  inline char* get_mmio_base_idma() {
    return NPU_INTRA_SLICE_IDMA_BASE;
  }
  inline char* get_mmio_base_odma() {
    return NPU_INTRA_SLICE_ODMA_BASE;
  }
  inline char* get_mmio_base_conv() {
    return NPU_INTRA_SLICE_CONV_BASE;
  }
  inline char* get_mmio_base_act() {
    return NPU_INTRA_SLICE_GTOA_BASE;
  }
  inline char* get_mmio_base_istu() {
    return NPU_INTRA_SLICE_ISTU_BASE;
  }
  inline char* get_mmio_base_ostu() {
    return NPU_INTRA_SLICE_OSTU_BASE;
  }

  inline char* get_mmio_base_stu(int idx) {
    return NPU_INTER_STU_BASE+0x1000*idx;
  }


  // translate an ARC fast DCCM pointer to a slice DCCM pointer
  template<typename T>
  inline T* fast2slice_dccm(T* p) {
    assert ((reinterpret_cast<long long>(p) & 0xf0000000) == NPU_ARC_DCCM_BASE &&  "expected fast dccm address range");
    char* pv = reinterpret_cast<char*>(p);
    pv += reinterpret_cast<long long>(NPU_INTRA_SLICE_DCCM_BASE) - reinterpret_cast<long long>(NPU_FAST_DCCM_BASE);
    return reinterpret_cast<T*>(pv);
  }
  // translate an ARC fast DCCM pointer to a global DCCM pointer
  template<typename T>
  inline T* fast2global_dccm(T* p) {
    assert ((reinterpret_cast<long long>(p) & 0xf0000000) == reinterpret_cast<long long>(NPU_FAST_DCCM_BASE) &&  "expected fast dccm address range");
    char* pv = reinterpret_cast<char*>(p);
    char* b = (char*)hv_get_core_mmio_base(hv_get_arcnum());
    pv += reinterpret_cast<long long>(b) - reinterpret_cast<long long>(NPU_FAST_DCCM_BASE);
    return reinterpret_cast<T*>(pv);
  }
  // translate fast or slice local address to global
  template<typename T>
  inline T* slice2global(T* p) {
    assert ((reinterpret_cast<long long>(p) & 0xf0000000) == reinterpret_cast<long long>(NPU_INTRA_SLICE_DCCM_BASE) &&  "expected intra slice local address range");
    // slice local pointer to NPU, 0x400000 per local bus
    char* pv = reinterpret_cast<char*>(p);
    char* b = (char*)hv_get_core_mmio_base(hv_get_arcnum());
    pv += reinterpret_cast<long long>(b) - reinterpret_cast<long long>(NPU_INTRA_SLICE_DCCM_BASE);
    return reinterpret_cast<T*>(pv);
  }

  inline void mem_barrier() {
#ifdef RTL_ARC
    // enforce strict ordering of memory transactions
    _dmb(7);
#endif
  }

  //
  // Time control
  //
  // get the current time
  inline timestamp_t get_timestamp() {
  #ifdef RTL_DPI
    return proc_get_timestamp();
  #elif defined(RTL_ARC)
    return 0;
  #elif defined(HOST_ARC) || defined(HOST_SYSTEMC)
    assert(0);
    return 0;
  #endif
  }
  // run for a number of cycles
  inline void run_cycles(timestamp_t c) {
  #ifdef RTL_DPI
    proc_run_cycles((int)c);
  #elif defined(RTL_ARC)
    for (int i=0; i<((int)c); i++) {
      _nop();
    }
  #elif defined(HOST_ARC) || defined(HOST_SYSTEMC)
  #endif
  }
  // wait for a number of cycles
  inline void wait_cycles(timestamp_t c) {
  #ifdef RTL_DPI
    proc_run_cycles((int)c);
  #elif defined(RTL_ARC)
    for (int i=0; i<((int)c); i++) {
      _nop();
    }
  #elif defined(HOST_ARC) || defined(HOST_SYSTEMC)
  #endif
  }

  //
  // Events and interrupts
  //
  // Virtual Machine Check
  inline bool vm_check(uint64_t& ev) {
    int found = 0;
  #ifdef RTL_DPI
    assert(0);
  #elif defined(RTL_ARC)
    volatile long long r_ev = 0LL;
    ev = EVTVMCHK_f(r_ev);
    found = _condition(_condition_EQ);
  #elif defined(HOST_ARC) || defined(HOST_SYSTEMC)
    assert(0);
    return 0;
  #endif
    return found;
  }

  // wait for any event from a mask and decrement most lsb counter
  inline uint64_t event_wait_any(uint64_t ev) {
    long long res;
    if (ev != 0) {
  #ifdef RTL_DPI
      proc_event_wait_any((long long)ev, &res);
  #elif defined(RTL_ARC)
      volatile long long r_ev = 0LL;
      r_ev |= ev;
      int found=0;
      res = EVTMASKANY_f(r_ev);
      found = _condition(_condition_EQ);
      while (!found) {
        _wevt(0x00);
        res = EVTMASKCHK_f(r_ev);
        found =_condition(_condition_EQ);
      }
      EVTMASKDECR(res);
  #elif defined(HOST_ARC) || defined(HOST_SYSTEMC)
      assert(0);
      return 0;
  #endif
    }
    else {
      res = 0;
    }
    return res;
  }
  // wait for all events from the mask and decrement counters
  inline uint64_t event_wait_all(uint64_t ev) {
    long long res;
    if (ev != 0) {
  #ifdef RTL_DPI
      proc_event_wait_all((long long)ev, &res);
  #elif defined(RTL_ARC)
      volatile long long r_ev = 0LL;
      r_ev |= ev;
      int found=0;
      res = EVTMASKALL_f(r_ev);
      found= _condition(_condition_EQ);
      while (!found) {
        _wevt(0x00);
        res = EVTMASKCHK_f(r_ev);
        found =_condition(_condition_EQ);
      }
      EVTMASKDECR(res);
  #elif defined(HOST_ARC) || defined(HOST_SYSTEMC)
      assert(0);
      return 0;
  #endif
    }
    else {
      res = 0;
    }
    return res;
  }
  // send events, one per bit
  inline void event_send_parent() {
  #ifdef RTL_DPI
    uint64_t ev = 1LL << EVT_PARENT; // assumes parent is 0, child numbered from 1..SLICES
    proc_event_send(ev);
    proc_run_cycles(4);
  #elif defined(RTL_ARC)
    long long mask = 1LL << EVT_PARENT;
    EVTMASKSEND(mask);
    for (int i=0; i<4; i++) {
      _nop();
    }
  #elif defined(HOST_ARC) || defined(HOST_SYSTEMC)
    assert(0);
  #endif
  }
  // send event to one or multiple peers
  inline void event_send_peers(uint64_t ev) {
  #ifdef RTL_DPI
    // ev <<= EVT_PEER0;
    proc_event_send(ev);
    proc_run_cycles(4);
  #elif defined(RTL_ARC)
    volatile long long r_ev = 0LL;
    r_ev |= ev;
    EVTMASKSEND(r_ev);
    for (int i=0; i<4; i++) {
      _nop();
    }
  #elif defined(HOST_ARC) || defined(HOST_SYSTEMC)
    assert(0);
  #endif
  }
  // send event to one or multiple children
  inline void event_send_children(uint64_t ev) {
  #ifdef RTL_DPI
    // ev <<= EVT_CHILD0;
    proc_event_send((long long)ev);
    proc_run_cycles(4);
  #elif defined(RTL_ARC)
    volatile long long r_ev = 0LL;
    r_ev |= ev;
    EVTMASKSEND(r_ev);
    for (int i=0; i<4; i++) {
      _nop();
    }
  #elif defined(HOST_ARC) || defined(HOST_SYSTEMC)
    assert(0);
  #endif
  }
  // increment and decrement event counters, one per bit
  inline void event_incr(uint64_t ev) {
  #ifdef RTL_DPI
    proc_event_incr((long long)ev);
  #elif defined(RTL_ARC)
    volatile long long r_ev = 0LL;
    r_ev |= ev;
    EVTMASKINCR(r_ev);
  #endif
  }
  inline void event_decr(uint64_t ev) {
  #ifdef RTL_DPI
    proc_event_decr((long long)ev);
  #elif defined(RTL_ARC)
    volatile long long r_ev = 0LL;
    r_ev |= ev;
    EVTMASKDECR(r_ev);
  #endif
  }
  // read/write event counters
  inline uint8_t event_read(uint32_t ev) {
    int val=0;
  #ifdef RTL_DPI
    proc_event_read(ev, (int*)&val);
  #elif defined(RTL_ARC)
    assert((ev>=0) && (ev<64));
    _sr(ev, AR_EVT_CNT_SEL); // select event counter
    val = (uint8_t)(_lr(AR_EVT_CNT_VAL) & 0xff);
  #elif defined(HOST_ARC) || defined(HOST_SYSTEMC)
    assert(0);
    return 0;
  #endif
    return val;
  }
  inline void event_write(uint32_t ev, uint8_t val) {
  #ifdef RTL_DPI
    proc_event_write((int)ev, (int)val);
  #elif defined(RTL_ARC)
    assert((ev>=0) && (ev<64));
    _sr(ev, AR_EVT_CNT_SEL);  // select event counter
    _nop();
    _nop();
    _sr(val, AR_EVT_CNT_VAL);     // write the new value
  #elif defined(RTL_ARC) || defined(HOST_ARC) || defined(HOST_SYSTEMC)
  #endif
  }

  //
  // Ancillary functions
  //
  // force program exit and stop simulator
  inline void arc_exit() {
    // remove this object from the simulation scope
    /*
    svScope sc = svGetScope();
    svPutUserData(sc, (void*) NULL, this);
    */
  #ifdef RTL_DPI
    proc_exit();
  #elif defined(RTL_ARC) || defined(HOST_ARC) || defined(HOST_SYSTEMC)
    exit(0);
  #endif
  }
  // SW trace
  inline void sw_trace(uint32_t ev) {
  #ifdef RTL_DPI
    arc_printf("TRACE::%d::%d\n", hv_get_arcnum(), ev);
  #elif defined(RTL_ARC)
  #endif
  }

  // constructor
  inline arc_program::arc_program() {
  #ifdef RTL_DPI
    // get the simulation scope
    svScope sc = svGetScope();
    // add this object to the simulation scope
    svPutUserData(sc, (void*) &irq_callback, this);
  #elif defined(RTL_ARC) || defined(HOST_ARC) || defined(HOST_SYSTEMC)
  #endif
  }

  inline void arc_program::set_mem_backdoor(int bd, int dbg){
  #ifdef RTL_DPI
    proc_mem_backdoor(bd, dbg);
  #elif defined(RTL_ARC) || defined(HOST_ARC) || defined(HOST_SYSTEMC)
  #endif
  }

  inline void arc_program::enable_dmerr(int rerr_bnum, int werr_bnum){
  #ifdef RTL_DPI
    proc_dmerr_en(rerr_bnum, werr_bnum);
  #elif defined(RTL_ARC) || defined(HOST_ARC) || defined(HOST_SYSTEMC)
  #endif
  }

  inline void arc_program::set_scm_aperture(int base, int size){
  #ifdef RTL_DPI
    proc_scm_aperture(base, size);
  #elif defined(RTL_ARC)
  #endif
  }

  // HWV Interface
  inline void hv_sel_vm(uint32_t vmid) {
    cfg_vmid(vmid);
  }

  inline void hv_event_map(uint32_t cbase, uint32_t cnum, uint32_t abase, uint32_t anum) {
    cfg_vmmap(cbase,cnum,abase,anum);
  }

  //inline uint32_t hv_get_arcnum() {
  //  return arcsync_arcnum();
  //}

  inline void hv_set_streamid(uint32_t sid, uint32_t grp) {
  #ifdef RTL_DPI
    proc_sr_aux(grp,  0xF07);
    proc_sr_aux(sid,  0xF08);
  #elif RTL_ARC
    _sr(grp,  0xF07);
    _sr(sid,  0xF08);
  #endif
  }

  //inline void hv_set_streamid(uint32_t sid) {
  //  hv_set_streamid(sid, 0);
  //}

  inline void hv_set_substreamid(uint32_t ssid, uint32_t grp) {
  #ifdef RTL_DPI
    proc_sr_aux(grp,  0xF07);
    proc_sr_aux(ssid, 0xF09);
  #elif RTL_ARC
    _sr(grp,  0xF07);
    _sr(ssid, 0xF09);
  #endif
  }

  //inline void hv_set_substreamid(uint32_t ssid) {
  //  hv_set_substreamid(ssid, 0);
  //}

  // return the MMIO base address of a slice/top
  inline void* hv_get_core_mmio_base(int32_t core_id) {
    void* p;
    if (core_id == 0 || core_id == (NPU_SLICE_NUM+1)) {
      p = NPU_INTER_SLICE_BASE + 0x06000000;
    } else {
      int i = core_id-1;
      p = NPU_INTER_SLICE_BASE + (((4*(i/NPU_NUM_SLC_PER_GRP))+(i%NPU_NUM_SLC_PER_GRP)) * 0x400000);
    }
    return p;
  }

  // TO BE ADDED
  inline void hv_create_vm() {
    assert(0);
  }

  inline void hv_switch_vm() {
    assert(0);
  }

  inline bool hv_vm_active() {
    assert(0);
    return 0;
  }

  inline void hv_set_proc_id() {
    assert(0);
  }

  inline void hv_set_fast_dccm_base() {
    assert(0);
  }

  inline void hv_map() {
    assert(0);
  }

  inline void hv_unmap() {
    assert(0);
  }

  inline void hv_iomap() {
    assert(0);
  }

  inline void hv_iounmap() {
    assert(0);
  }

  inline void hv_irq_map() {
    assert(0);
  }

  inline void hv_parent_interrupt() {
    assert(0);
  }

  inline void hv_irq_cb() {
    assert(0);
  }

  inline void hv_irq_poll() {
    assert(0);
  }
}

