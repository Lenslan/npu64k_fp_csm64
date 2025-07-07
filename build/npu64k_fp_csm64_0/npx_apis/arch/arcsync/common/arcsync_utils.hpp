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

/*
 * arcsync_utils.hpp
 *
 * File defining ARCsync API
 *
 */
#ifndef ARCSYNC_COMMON_ARCSYNC_UTILS_HPP_
#define ARCSYNC_COMMON_ARCSYNC_UTILS_HPP_

#include <cstdint>
#include <cassert>
#include <cmath>

#include "npu_defines.hpp"  // NOLINT [build/include_subdir]
#include "npu_config.hpp"   // NOLINT [build/include_subdir]
#ifndef HOST_DPI
  #include "tensor.hpp"       // NOLINT [build/include_subdir]
#endif

#ifndef CORE_NUM
#define CORE_NUM                           (ARCSYNC_NUM_CLUSTER * ARCSYNC_MAX_CORES_PER_CL)
#endif

#define ARCSYNC_AS_BLD_CFG                  ((ARCSYNC_BASE_ADDR << 12))
#define ARCSYNC_AS_NUM_CORE_CL0_3           ((ARCSYNC_BASE_ADDR << 12) + 0x4)
#define ARCSYNC_AS_NUM_CORE_CL4_7           ((ARCSYNC_BASE_ADDR << 12) + 0x8)
#define ARCSYNC_FS_PASSWD                   ((ARCSYNC_BASE_ADDR << 12) + 0x34)
#define ARCSYNC_FS_DIAG                     ((ARCSYNC_BASE_ADDR << 12) + 0x38)
#define ARCSYNC_FS_ERR_STATUS               ((ARCSYNC_BASE_ADDR << 12) + 0x3C)
#define ARCSYNC_FS_CTRL                    ((ARCSYNC_BASE_ADDR << 12) + 0x40)
#define ARCSYNC_ADDR_GFRC_ENABLE            ((ARCSYNC_BASE_ADDR << 12) + 0x20)
#define ARCSYNC_ADDR_GFRC_CLEAR             ((ARCSYNC_BASE_ADDR << 12) + 0x24)
#define ARCSYNC_ADDR_GFRC_READ_LO           ((ARCSYNC_BASE_ADDR << 12) + 0x28)
#define ARCSYNC_ADDR_GFRC_READ_HI           ((ARCSYNC_BASE_ADDR << 12) + 0x2C)

#define ARCSYNC_ADDR_CL_ENABLE              (0x1000 + (ARCSYNC_BASE_ADDR << 12))
#define ARCSYNC_ADDR_CL_GRP_CLK_EN          (0x1000 + (ARCSYNC_BASE_ADDR << 12) + 4 * ARCSYNC_NUM_CLUSTER)
#define ARCSYNC_ADDR_CL_GRP_RESET           (0x1000 + (ARCSYNC_BASE_ADDR << 12) + 8 * ARCSYNC_NUM_CLUSTER)


#define ARCSYNC_BASE_ADDR_CSM               (0x1000 + (ARCSYNC_BASE_ADDR << 12) + 16 * ARCSYNC_NUM_CLUSTER)
#define ARCSYNC_BASE_ADDR_CL_PERIPH         (0x1000 + (ARCSYNC_BASE_ADDR << 12) + 20 * ARCSYNC_NUM_CLUSTER)

#define ARCSYNC_ADDR_PMU_SET_RSTCNT         (0x1000 + (ARCSYNC_BASE_ADDR << 12) + 32 * ARCSYNC_NUM_CLUSTER)
#define ARCSYNC_ADDR_PMU_SET_PUCNT          (0x1000 + (ARCSYNC_BASE_ADDR << 12) + 36 * ARCSYNC_NUM_CLUSTER)
#define ARCSYNC_ADDR_PMU_SET_PDCNT          (0x1000 + (ARCSYNC_BASE_ADDR << 12) + 40 * ARCSYNC_NUM_CLUSTER)

#define ARCSYNC_BASE_ADDR_CORE_PMODE        ((ARCSYNC_BASE_ADDR << 12) + 0x2000)
#define ARCSYNC_BASE_ADDR_CORE_RUN          (ARCSYNC_BASE_ADDR_CORE_PMODE + 4 * CORE_NUM)
#define ARCSYNC_BASE_ADDR_CORE_HALT         (ARCSYNC_BASE_ADDR_CORE_PMODE + 8 * CORE_NUM)
#define ARCSYNC_BASE_ADDR_BOOT_IVB_LO       (ARCSYNC_BASE_ADDR_CORE_PMODE + 12 * CORE_NUM)
#define ARCSYNC_BASE_ADDR_BOOT_IVB_HI       (ARCSYNC_BASE_ADDR_CORE_PMODE + 16 * CORE_NUM)
#define ARCSYNC_BASE_ADDR_CORE_STATUS       (ARCSYNC_BASE_ADDR_CORE_PMODE + 20 * CORE_NUM)
#define ARCSYNC_BASE_ADDR_CORE_RESET        (ARCSYNC_BASE_ADDR_CORE_PMODE + 24 * CORE_NUM)
#define ARCSYNC_BASE_ADDR_CORE_CLK_EN       (ARCSYNC_BASE_ADDR_CORE_PMODE + 28 * CORE_NUM)

#define ARCSYNC_BASE_ADDR_EID_SEND_EVENT_0  ((ARCSYNC_BASE_ADDR << 12) + 0x4000)
#define ARCSYNC_BASE_ADDR_EID_SEND_EVENT_1  (ARCSYNC_BASE_ADDR_EID_SEND_EVENT_0 + 4 * CORE_NUM)
#define ARCSYNC_BASE_ADDR_EID_RAISE_IRQ_0   (ARCSYNC_BASE_ADDR_EID_SEND_EVENT_0 + 16 * CORE_NUM)
#define ARCSYNC_BASE_ADDR_EID_ACK_IRQ_0     (ARCSYNC_BASE_ADDR_EID_SEND_EVENT_0 + 20 * CORE_NUM)
#define ARCSYNC_BASE_ADDR_EID_RAISE_IRQ_1   (ARCSYNC_BASE_ADDR_EID_SEND_EVENT_0 + 24 * CORE_NUM)
#define ARCSYNC_BASE_ADDR_EID_ACK_IRQ_1     (ARCSYNC_BASE_ADDR_EID_SEND_EVENT_0 + 28 * CORE_NUM)

#define ARCSYNC_BASE_ADDR_AC_NOTIFY_SRC     (ARCSYNC_BASE_ADDR_EID_SEND_EVENT_0 + 48 * CORE_NUM)
#define ARCSYNC_BASE_ADDR_AC_ACK_IRQ        (ARCSYNC_BASE_ADDR_EID_SEND_EVENT_0 + 52 * CORE_NUM)
#define ARCSYNC_BASE_ADDR_AC_CONFIG         ((ARCSYNC_BASE_ADDR << 12) + 0x8000)
#define ARCSYNC_BASE_ADDR_AC_CONTROL        ((ARCSYNC_BASE_ADDR << 12) + 0x9000)

#define ARCSYNC_AC_CTRL_SIZE_NON_4KB_ALIGN  ((CORE_NUM * ARCSYNC_NUM_ATOMIC_CNT) << 2)
#define ARCSYNC_AC_CTRL_SIZE_4KB_RESIDUE    (ARCSYNC_AC_CTRL_SIZE_NON_4KB_ALIGN & 0xFFF)
#define ARCSYNC_AC_CTRL_SIZE_4KB_QUOTIENT   (ARCSYNC_AC_CTRL_SIZE_NON_4KB_ALIGN >> 12)
#define ARCSYNC_AC_CTRL_SIZE_4KB_ALIGN      (ARCSYNC_AC_CTRL_SIZE_4KB_QUOTIENT << 12) + ((ARCSYNC_AC_CTRL_SIZE_4KB_RESIDUE != 0) ? 4096 : 0 )
#define ARCSYNC_BASE_ADDR_MAP_VM_VPROC      (ARCSYNC_BASE_ADDR_AC_CONTROL + ARCSYNC_AC_CTRL_SIZE_4KB_ALIGN)

#define ARCSYNC_VM_CONFIG_SIZE_NON_4KB_ALIGN   ((ARCSYNC_VIRT_MACHINES * ARCSYNC_VIRT_PROC) << 2)
#define ARCSYNC_VM_CONFIG_SIZE_4KB_RESIDUE     (ARCSYNC_VM_CONFIG_SIZE_NON_4KB_ALIGN & 0xFFF)
#define ARCSYNC_VM_CONFIG_SIZE_4KB_QUOTIENT    (ARCSYNC_VM_CONFIG_SIZE_NON_4KB_ALIGN >> 12)
#define ARCSYNC_VM_CONFIG_SIZE_4KB_ALIGN       (ARCSYNC_VM_CONFIG_SIZE_4KB_QUOTIENT << 12) + ((ARCSYNC_VM_CONFIG_SIZE_4KB_RESIDUE != 0) ? 4096 : 0)
#define ARCSYNC_BASE_ADDR_VM0_EID              (ARCSYNC_BASE_ADDR_MAP_VM_VPROC + ARCSYNC_VM_CONFIG_SIZE_4KB_ALIGN)
#define ARCSYNC_BASE_ADDR_VM0_EID_SEND_EVENT_0  ARCSYNC_BASE_ADDR_VM0_EID
#define ARCSYNC_BASE_ADDR_VM0_EID_RAISE_IRQ_0  (ARCSYNC_BASE_ADDR_VM0_EID_SEND_EVENT_0 + 16 * ARCSYNC_VIRT_PROC)
#define ARCSYNC_BASE_ADDR_VM0_EID_ACK_IRQ_0    (ARCSYNC_BASE_ADDR_VM0_EID_SEND_EVENT_0 + 20 * ARCSYNC_VIRT_PROC)
#define ARCSYNC_BASE_ADDR_VM0_AC_NOTIFY_SRC    (ARCSYNC_BASE_ADDR_VM0_EID_SEND_EVENT_0 + 48 * ARCSYNC_VIRT_PROC)
#define ARCSYNC_BASE_ADDR_VM0_AC_ACK_IRQ       (ARCSYNC_BASE_ADDR_VM0_EID_SEND_EVENT_0 + 52 * ARCSYNC_VIRT_PROC)
#define ARCSYNC_BASE_ADDR_VM0_AC_CONTROL       (ARCSYNC_BASE_ADDR_VM0_EID_SEND_EVENT_0 + 56 * ARCSYNC_VIRT_PROC + 4 * (ARCSYNC_NUM_ATOMIC_CNT/ARCSYNC_VIRT_MACHINES))

#define ARCSYNC_ADDR_VM0_GFRC_LO               (ARCSYNC_BASE_ADDR_VM0_EID_SEND_EVENT_0 + 40 * ARCSYNC_VIRT_PROC)
#define ARCSYNC_ADDR_VM0_GFRC_HI               (ARCSYNC_BASE_ADDR_VM0_EID_SEND_EVENT_0 + 40 * ARCSYNC_VIRT_PROC + 4)

template<typename T> inline T arcsync_mmio_read(T* p) {
#ifdef RTL_ARC
  _Uncached volatile T *p_t = (volatile T *)(p);
  return *p_t;
#elif defined HOST_DPI
  return mem_read(p);
#else
  return tensor::v200::mem_read(p);
#endif
}

template<typename T> inline void arcsync_mmio_write(T* p, const T& d) {
#ifdef RTL_ARC
  _Uncached volatile T *p_t = (volatile T *)(p);
  *p_t = d;
#elif defined HOST_DPI
  mem_write(p, d);
#else
  tensor::v200::mem_write(p, d);
#endif
}

static inline
uint32_t get_myid() {
  uint32_t myid;
#ifdef RTL_ARC
  myid = npu::arcsync_coreid();
#elif defined HOST_DPI
  myid = (ARCSYNC_NUM_CLUSTER-1) * ARCSYNC_MAX_CORES_PER_CL;
#endif
  return myid;
}

static inline
void wait_cycles(int a) {
#ifdef RTL_ARC
  npu::wait_cycles(a);
#elif defined HOST_DPI
  host_wait(a);
#endif
}


// Core Control and Status
struct arc_status_t {
  uint32_t halt : 1;        // sys_halt_r : indicate core is halted
  uint32_t tf_halt : 1;     // sys_tf_halt_r : halted due to triple fault exception
  uint32_t sleeping : 1;    // sys_sleep_r : core is sleeping
  uint32_t sleep_mode : 3;  // sys_sleep_mode_r : sleep mode number
  uint32_t pmode : 3;       // core power mode (always 0 if no power domain)
  uint32_t reserved : 23;   // read as 0
};

static inline
uint32_t arcsync_core_status(unsigned coreid) {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_CORE_STATUS + coreid * 4);
  return arcsync_mmio_read(addr);
}

static inline
void arcsync_core_run(const unsigned coreid) {
  if ((arcsync_core_status(coreid) & 0x7) != 0) {  // check if core is halted or sleep
    uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_CORE_RUN + coreid * 4);
    uint32_t value = 1;
    arcsync_mmio_write(addr, value);
    // Polling to confirm the core is run
    while ((arcsync_core_status(coreid) & 0x1) != 0) {  wait_cycles(4); };
  }
}

static inline
void arcsync_core_halt(const unsigned coreid) {
  if ((arcsync_core_status(coreid) & 0x3) == 0) {  // check if core is running
    uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_CORE_HALT + coreid * 4);
    uint32_t value = 1;
    arcsync_mmio_write(addr, value);
    // Polling to confirm the core is halted
    while ((arcsync_core_status(coreid) & 0x1) != 1) {  wait_cycles(4); }; 
  }
}

static inline
bool arcsync_core_reset(const unsigned coreid) {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_CORE_RESET + coreid * 4);
  if (arcsync_mmio_read(addr) == 0) {
    // Read register to confirm the core is not already under reset
    // trigger a reset : will only happen if the correct 'password' is written, to
    // reduce the probability of trigerrign a reset through a programming error
    uint32_t value = 0x5A5A0000 | (coreid & 0xFFFF);
    arcsync_mmio_write(addr, value);

    // Note that if the core is clock gate
    // The reset will not complete until the clock is re-enabled
    // see the CGATE register description
    wait_cycles(4);
    // de-assert reset
    value = 0xA5A50000 | (coreid & 0xFFFF);
    arcsync_mmio_write(addr, value);
    //if (arcsync_mmio_read(addr) == 0) {
    //  return true;
    //}
  }
  return false;
}

static inline
uint32_t arcsync_core_reset_status(unsigned coreid) {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_CORE_RESET + coreid * 4);
  return arcsync_mmio_read(addr);
}

static inline
void arcsync_core_clk_enable(const unsigned coreid) {
  //uint32_t clusternum = (coreid >> (static_cast<int>(log2(ARCSYNC_MAX_CORES_PER_CL)))) & 0xff;
  //uint32_t arcnum = (coreid & ~(0xFFFFFFFF << (static_cast<int>(log2(ARCSYNC_MAX_CORES_PER_CL)))));
  //uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_CGATE + clusternum * 4);
  uint32_t value = 1; //arcsync_mmio_read(addr);
  //value = value | (1 << arcnum);
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_CORE_CLK_EN + coreid * 4);
  arcsync_mmio_write(addr, value);
}

static inline
void arcsync_core_clk_disable(const unsigned coreid) {
  //uint32_t clusternum = (coreid >> (static_cast<int>(log2(ARCSYNC_MAX_CORES_PER_CL)))) & 0xff;
  //uint32_t arcnum = (coreid & ~(0xFFFFFFFF << (static_cast<int>(log2(ARCSYNC_MAX_CORES_PER_CL)))));
  //uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_CGATE + clusternum * 4);
  uint32_t value = 0; //arcsync_mmio_read(addr);
  //value = value & (~(1 << arcnum));
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_CORE_CLK_EN + coreid * 4);
  arcsync_mmio_write(addr, value);
}

static inline
void arcsync_cluster_set_csm_base(const uint32_t clusternum, const uint32_t base_addr) {
    uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_CSM + clusternum * 4);
    uint32_t value = (base_addr>>16);
    arcsync_mmio_write(addr, value);
}

static inline
uint32_t arcsync_cluster_get_csm_base(const uint32_t clusternum) {
    uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_CSM + clusternum * 4);
    return (arcsync_mmio_read(addr) << 16);
}

static inline
void arcsync_cluster_set_periph_base(const uint32_t clusternum, const uint32_t base_addr) {
    uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_CL_PERIPH + clusternum * 4);
    uint32_t value = (base_addr>>16);
    arcsync_mmio_write(addr, value);
}

static inline
uint32_t arcsync_cluster_get_periph_base(const uint32_t clusternum) {
    uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_CL_PERIPH + clusternum * 4);
    return (arcsync_mmio_read(addr) << 16);
}

static inline
void arcsync_core_intvbase(const unsigned coreid, const uint32_t ivb) {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_BOOT_IVB_LO + coreid * 4);
  uint32_t value = ivb >> 10;
  assert((ivb & 0x3FF) == 0);  // 10 LSB must be 0
  arcsync_mmio_write(addr, value);
}

static inline
void arcsync_core_powerdown(int coreid) {
  uint32_t s = arcsync_core_status(coreid);

  if ((s & 0x1C0) == 0) {  // check is core is in power-up status
    uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_CORE_PMODE + coreid * 4);
    uint32_t value = 1;
    arcsync_mmio_write(addr, value);  // Send power down request
  }
}

static inline
void arcsync_core_powerdup(int coreid) {
  uint32_t s = arcsync_core_status(coreid);

//  if ((s & 0x1C0) != 0) {  // check is core is in power-down status
    uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_CORE_PMODE + coreid * 4);
    uint32_t value = 0;
    arcsync_mmio_write(addr, value);  // Send power up request
//  }
}

// Event and Interrupt Dispatch
static inline
void arcsync_send_virt_event(const unsigned vmid, const unsigned receiver_vpid) {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_VM0_EID_SEND_EVENT_0 + (vmid<<12) + (receiver_vpid<<2));
  uint32_t value = 1;
  // Trigger pulse event. No ack will be received from the recipient
  arcsync_mmio_write(addr, value);
}

static inline
void arcsync_send_event(const unsigned coreid) {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_EID_SEND_EVENT_0 + coreid * 4);
  uint32_t value = 1;
  // Trigger pulse event. No ack will be received from the recipient
  arcsync_mmio_write(addr, value);
}

static inline
bool arcsync_virt_event_waiting(const unsigned vmid, const unsigned receiver_vpid) {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_VM0_EID_SEND_EVENT_0 + (vmid<<12) + (receiver_vpid<<2));
  return arcsync_mmio_read(addr) == 1;
}

static inline
bool arcsync_event_waiting(const unsigned coreid) {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_EID_SEND_EVENT_0 + coreid * 4);
  return arcsync_mmio_read(addr) == 1;
}

static inline
bool arcsync_send_virt_irq(const unsigned vmid, const unsigned receiver_vpid, const unsigned sender_vpid) {
uint32_t* r = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_VM0_EID_RAISE_IRQ_0 + (vmid<<12) + (receiver_vpid<<2));
uint32_t* a = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_VM0_EID_ACK_IRQ_0  + (vmid<<12) + (receiver_vpid<<2));

  if (arcsync_mmio_read(a) == 0) {
    arcsync_mmio_write(r, sender_vpid);  // Write the sender's VProc ID to raise the interrupt
    return true; // IRQ is sent
  }
  return false;  // failed to send an interrupt
}

static inline
bool arcsync_send_irq(const unsigned dest_coreid) {
  // Showing behavior for IRQ#0
  uint32_t* r = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_EID_RAISE_IRQ_0 + dest_coreid * 4);
  uint32_t* a = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_EID_ACK_IRQ_0  + dest_coreid * 4);
  uint32_t myid = get_myid();

  // Check there are no pending IRQ not yet acknowledged by the receiving core
  if (arcsync_mmio_read(a) == 0) {
    arcsync_mmio_write(r, myid);  // Write the sender's core ID to raise the interrupt
    return true;  // IRQ is sent
  }
  return false;  // failed to send an interrupt
}

static inline
void arcsync_set_vm_map(const unsigned vmid, const unsigned receiver_vpid, const unsigned mapped_cluster) {
  // set vm map table
  uint32_t* r = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_MAP_VM_VPROC + (((vmid*ARCSYNC_VIRT_PROC) + receiver_vpid)<<2));
  uint32_t value = (1<<31) | mapped_cluster;
  arcsync_mmio_write(r, value);
}


static inline
uint32_t arcsync_ack_irq() {
  uint32_t myid = get_myid();
  uint32_t* addr_r = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_EID_RAISE_IRQ_0 + myid * 4);
  uint32_t* addr_a = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_EID_ACK_IRQ_0  + myid * 4);

  uint32_t sender = arcsync_mmio_read(addr_r);  // Get the core ID who sent the IRQ
  arcsync_mmio_write(addr_a, myid);  // Write to acknowledge: ARCsync will rescind the IRQ
  return sender;
}

static inline
uint32_t arcsync_ack_virt_irq(const unsigned vmid, const unsigned receiver_vpid) {
  uint32_t* addr_r = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_VM0_EID_RAISE_IRQ_0 + (vmid<<12) + (receiver_vpid<<2));
  uint32_t* addr_a = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_VM0_EID_ACK_IRQ_0  + (vmid<<12) + (receiver_vpid<<2));

  uint32_t sender = arcsync_mmio_read(addr_r);  // Get the VPROC ID who sent the IRQ
  arcsync_mmio_write(addr_a, receiver_vpid);  // Write to acknowledge: ARCsync will rescind the IRQ
  return sender;
}

// Atomic Counters
// Types of notification to send
enum AC_notif_type {
  EVENT = 0,
  IRQ = 1,
};
// Operation on the counter
enum AC_cnt_op {
  DECR = 0,
  INCR = 1
};
// Type of request
enum AC_req_type {
  POLL = 0,
  WAIT = 1
};
// Behavior of the counter
//   Semaphore : core to be notified when the initial counter value is non-zero
//               the counter is decremented to acquire the token.
//               Saturate at min/max values to allow multiple tries to acquire
//   Barrier   : core to be notified when the updated value is 0, wrap back to the
//               max bound when the value reaches zero
enum AC_behav {
  NONE    = 0,
  SEM     = 1,
  BARRIER = 2,
  INDEX   = 3
};

struct ac_control_reg {
  AC_req_type     req_typ     : 1;
  AC_notif_type   notif_typ   : 1;
  AC_cnt_op       cnt_op      : 1;
  unsigned        pending     : 1;
  unsigned        reserved    : 28;
};

struct ac_config_reg {
  unsigned    count    :  8;  // Current count
  unsigned    rev_8_11 :  4;
  unsigned    bound    :  8;  // Maximum value the counter can have before saturate or wrappring
  unsigned    rev_20_23:  4;
  AC_behav    bx       :  2;  // Counter behavior
  unsigned    reserved : 14;
};

// Atomic counters access
class arcsync_atomic_cnt {
  const unsigned  ac_id;

 public:
  explicit arcsync_atomic_cnt(int ac) : ac_id(ac) { }
  arcsync_atomic_cnt(const arcsync_atomic_cnt &) = delete;
  ~arcsync_atomic_cnt() { }

  // Initialize the counter. Can only be done safely when no core is current using the AC and
  // waiting for a notification
  void configure(AC_behav bx, unsigned bound, unsigned initial) {
    uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_AC_CONFIG + ac_id * 4);
    uint32_t value = ((unsigned int)bx << 24) | ((bound & 0xff) << 12) | (initial & 0xff);
    arcsync_mmio_write(addr, value);
  }

  // Return the current running count
  uint32_t get_count() {
    uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_AC_CONFIG + ac_id * 4);
    return (arcsync_mmio_read(addr) & 0x3ff);
  }

  void request_update(AC_req_type req, AC_notif_type notif, AC_cnt_op op) {
    uint32_t* addr = reinterpret_cast<uint32_t *>(ARCSYNC_BASE_ADDR_AC_CONTROL +
                                                  (get_myid() + CORE_NUM * ac_id) * 4);
    uint32_t value = ((unsigned int)op << 2) | ((unsigned int)notif << 1) | (unsigned int)req;
    arcsync_mmio_write(addr, value);
  }

  uint32_t get_status() {
    uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_AC_CONTROL +
                                                 (get_myid() + CORE_NUM * ac_id) * 4);
    return (arcsync_mmio_read(addr));
  }

  bool check_last_request() {
    uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_AC_CONTROL +
                                                 (get_myid()+CORE_NUM * ac_id) * 4);
    uint32_t c = arcsync_mmio_read(addr);
    c = c & 0x9;
    return (c == 1);  // Not pending (bit 3 =0) and comparison matched (bit 0 = 1)
  }

  void decr_request(AC_req_type req, AC_notif_type notif) {
    request_update(req, notif, AC_cnt_op::DECR);
  }

  void incr_request(AC_req_type req, AC_notif_type notif) {
    request_update(req, notif, AC_cnt_op::INCR);
  }

  void wait_event() {
    // Vic 2, event manager is 64-bit
    //long evt_arcsync_ac = 1LL << EVT_ARCSYNC_AC;
    //npu::event_wait_all(evt_arcsync_ac);
  #ifdef RTL_ARC
    npu::event_wait_all(1LL<<EVT_ARCSYNC_AC);
  #elif defined HOST_DPI
    //FIXME:
    wait_cycles(100);
  #else

  #endif
  }

  // Substract 1 and return true if the comparison condition for the counter matches (EQUAL/NEQ)
  bool decrement_check() {
    uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_AC_CONTROL +
                                                 (get_myid() + CORE_NUM * ac_id) * 4);
    // Send decrement request with no event/irq notification
    uint32_t value = ((unsigned int)AC_cnt_op::DECR << 2) | ((unsigned int)AC_req_type::POLL);
    arcsync_mmio_write(addr, value);
    // Check comparison result by reading back AC_CONTROL
    uint32_t res = arcsync_mmio_read(addr);
    return (res & 0x1);
  }

    // Add 1 and return true if the comparison condition for the counter matches (EQUAL/NEQ)
  bool increment_check() {
    uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_AC_CONTROL +
                                                 get_myid() * ac_id * 4);
    // Send increment request with no event/irq notification
    uint32_t value = ((unsigned int)AC_cnt_op::INCR << 2) | ((unsigned int) AC_req_type::POLL);
    arcsync_mmio_write(addr, value);

    // Check compare result by reading back AC_CONTROL
    uint32_t res = arcsync_mmio_read(addr);
    return (res & 0x1);
  }

  //////////////////////////////////
  // virtual machine AC subroutine//
  void virt_request_update(AC_req_type req, AC_notif_type notif, AC_cnt_op op, const unsigned vmid, const unsigned vpid) {
    unsigned ac_idx_in_vm;
    ac_idx_in_vm = ac_id % (ARCSYNC_NUM_ATOMIC_CNT/ARCSYNC_VIRT_MACHINES);
    uint32_t* addr = reinterpret_cast<uint32_t *>(ARCSYNC_BASE_ADDR_VM0_AC_CONTROL + (vmid<<12) +
                                                  (vpid + ARCSYNC_VIRT_PROC * ac_idx_in_vm) * 4);
    uint32_t value = ((unsigned int)op << 2) | ((unsigned int)notif << 1) | (unsigned int)req;
    arcsync_mmio_write(addr, value);
  }

  uint32_t virt_get_status(const unsigned vmid, const unsigned vpid) {
    int ac_idx_in_vm;
    ac_idx_in_vm = ac_id % (ARCSYNC_NUM_ATOMIC_CNT/ARCSYNC_VIRT_MACHINES);
    uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_VM0_AC_CONTROL + (vmid<<12) +
                                                 (vpid + ARCSYNC_VIRT_PROC * ac_idx_in_vm) * 4);
    return (arcsync_mmio_read(addr));
  }

  bool virt_check_last_request(const unsigned vmid, const unsigned vpid) {
    int ac_idx_in_vm;
    ac_idx_in_vm = ac_id % (ARCSYNC_NUM_ATOMIC_CNT/ARCSYNC_VIRT_MACHINES);
    uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_VM0_AC_CONTROL + (vmid<<12) +
                                                 (vpid + ARCSYNC_VIRT_PROC * ac_idx_in_vm) * 4);
    uint32_t c = arcsync_mmio_read(addr);
    c = c & 0x9;
    return (c == 1);  // Not pending (bit 3 =0) and comparison matched (bit 0 = 1)
  }

  void virt_decr_request(AC_req_type req, AC_notif_type notif, const unsigned vmid, const unsigned vpid) {
    virt_request_update(req, notif, AC_cnt_op::DECR, vmid, vpid);
  }

  void virt_incr_request(AC_req_type req, AC_notif_type notif, const unsigned vmid, const unsigned vpid) {
    virt_request_update(req, notif, AC_cnt_op::INCR, vmid, vpid);
  }

  // Substract 1 and return true if the comparison condition for the counter matches (EQUAL/NEQ)
  bool virt_decrement_check(const unsigned vmid, const unsigned vpid) {
    int ac_idx_in_vm;
    ac_idx_in_vm = ac_id % (ARCSYNC_NUM_ATOMIC_CNT/ARCSYNC_VIRT_MACHINES);
    uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_VM0_AC_CONTROL + (vmid<<12) +
                                                 (vpid + ARCSYNC_VIRT_PROC * ac_idx_in_vm) * 4);
    // Send decrement request with no event/irq notification
    uint32_t value = ((unsigned int)AC_cnt_op::DECR << 2) | ((unsigned int)AC_req_type::POLL);
    arcsync_mmio_write(addr, value);
    // Check comparison result by reading back AC_CONTROL
    uint32_t res = arcsync_mmio_read(addr);
    return (res & 0x1);
  }

    // Add 1 and return true if the comparison condition for the counter matches (EQUAL/NEQ)
  bool virt_increment_check(const unsigned vmid, const unsigned vpid) {
    int ac_idx_in_vm;
    ac_idx_in_vm = ac_id % (ARCSYNC_NUM_ATOMIC_CNT/ARCSYNC_VIRT_MACHINES);
    uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_VM0_AC_CONTROL + (vmid<<12) +
                                                 (vpid + ARCSYNC_VIRT_PROC * ac_idx_in_vm) * 4);
    // Send increment request with no event/irq notification
    uint32_t value = ((unsigned int)AC_cnt_op::INCR << 2) | ((unsigned int) AC_req_type::POLL);
    arcsync_mmio_write(addr, value);

    // Check compare result by reading back AC_CONTROL
    uint32_t res = arcsync_mmio_read(addr);
    return (res & 0x1);
  }
  // virtual machine AC subroutine//
  //////////////////////////////////

};

static inline
void arcsync_ack_ac_irq() {
  uint32_t myid = get_myid();
  uint32_t* addr_a = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_AC_ACK_IRQ + myid * 4);
  arcsync_mmio_write(addr_a, myid);  // Write to acknowledge: ARCsync will rescind the IRQ
}

static void arcsync_ack_virt_ac_irq(const unsigned vmid, const unsigned receiver_vpid) {
  uint32_t* addr_a = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_VM0_AC_ACK_IRQ + (vmid<<12) + (receiver_vpid<<2));
  arcsync_mmio_write(addr_a, receiver_vpid);  // Write to acknowledge: ARCsync will rescind the IRQ
}

static inline
uint32_t arcsync_check_ac_irq() {
  uint32_t myid = get_myid();
  uint32_t* addr_a = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_AC_ACK_IRQ + myid * 4);
  return arcsync_mmio_read (addr_a);
}

static inline
uint32_t arcsync_check_virt_ac_irq(const unsigned vmid, const unsigned receiver_vpid) {
  uint32_t myid = get_myid();
  uint32_t* addr_a = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_VM0_AC_ACK_IRQ + (vmid<<12) + (receiver_vpid<<2));
  return arcsync_mmio_read (addr_a);
}

// Mutex Semaphores and Barriers
// Mutex
class arcsync_mutex {
  arcsync_atomic_cnt ac;

 public:
  explicit arcsync_mutex(int ac_id, int do_configure = 0) : ac(ac_id) {
    if (do_configure == 1) {
      // Bound 1, Init 0, notify when the count is 1 (unlocked)
      ac.configure(AC_behav::SEM, 1, 1);
    }
  }
  ~arcsync_mutex() {  }

  void unlock() {
    ac.incr_request(AC_req_type::POLL, AC_notif_type::EVENT);
    // AC new value==1, notifications will trigger for other cores since it is now !=0
  }

  bool try_lock() {
    // return true if the sem is acquired (initial AC value was !=0)
    return ac.decrement_check();
  }

  void lock() {
    ac.decr_request(AC_req_type::WAIT, AC_notif_type::EVENT);
    do {
      ac.wait_event();
    } while (!ac.check_last_request());
  }

  // Partial example with IRQ. Global volatile variable "synchro_flag" is updated by the IRQ handler
  // (not shown here)
  void lock_irq_notify() {
    ac.decr_request(AC_req_type::WAIT, AC_notif_type::IRQ);

#ifdef RTL_ARC
    extern volatile bool synchro_flag;
    synchro_flag = 0;
    unsigned ilvl = _clri();  // clear and disable interrupts while checking flag
    while (synchro_flag == 0) {  // IRQ handler will set flag when it triggers
      // [7:5]=0  sleep mode
      //   [4]=1  enable interrupts
      // [3:0]=15 lowest priority required to wakeup
      _sleep(0x1F);
      _clri();
    }
    _seti(ilvl);  // restore interrupts
#endif
  }

  /////////////////////////////////
  // virtual machine sub-routine //
  void virt_unlock(const unsigned vmid, const unsigned vpid) {
    ac.virt_incr_request(AC_req_type::POLL, AC_notif_type::EVENT, vmid, vpid);
    // AC new value==1, notifications will trigger for other cores since it is now !=0
  }

  void virt_lock(const unsigned vmid, const unsigned vpid) {
    ac.virt_decr_request(AC_req_type::WAIT, AC_notif_type::EVENT, vmid, vpid);
    do {
      ac.wait_event();
    } while (!ac.virt_check_last_request(vmid, vpid));
  }  

  // Partial example with IRQ. Global volatile variable "synchro_flag" is updated by the IRQ handler
  // (not shown here)
  void virt_lock_irq_notify(const unsigned vmid, const unsigned vpid) {
    ac.virt_decr_request(AC_req_type::WAIT, AC_notif_type::IRQ, vmid, vpid);

#ifdef RTL_ARC
    extern volatile bool synchro_flag;
    synchro_flag = 0;
    unsigned ilvl = _clri();  // clear and disable interrupts while checking flag
    while (synchro_flag == 0) {  // IRQ handler will set flag when it triggers
      // [7:5]=0  sleep mode
      //   [4]=1  enable interrupts
      // [3:0]=15 lowest priority required to wakeup
      _sleep(0x1F);
      _clri();
    }
    _seti(ilvl);  // restore interrupts
#endif
  }

  // virtual machine sub-routine //
  /////////////////////////////////
};

// Semaphore
template<unsigned MaxVal> class arcsync_semaphore {
  arcsync_atomic_cnt ac;

 public:
  arcsync_semaphore(int ac_id, int desired, int do_configure = 0) : ac(ac_id) {
    assert((desired >= 0) && (desired <= static_cast<int64_t>(MaxVal)));
    if (do_configure == 1) {
      ac.configure(AC_behav::SEM, MaxVal, desired);
    }
  }

  arcsync_semaphore(const arcsync_semaphore &) = delete;
  ~arcsync_semaphore() { }

  constexpr unsigned max() { return MaxVal; }

  void release() {
    // New AC value will be >0, notifications will trigger for other cores waiting
    ac.incr_request(AC_req_type::POLL, AC_notif_type::EVENT);
  }

  bool try_acquire() {
    // return true if the sem is acquired (initial AC value was !=0)
    return ac.decrement_check();
  }

  void acquire() {
    ac.decr_request(AC_req_type::WAIT, AC_notif_type::EVENT);
    do {
      ac.wait_event();
    } while (!ac.check_last_request());
  }
};

// Barrier
class arcsync_barrier {
  arcsync_atomic_cnt ac;

 public:
  arcsync_barrier(int ac_id, int expected, int do_configure = 0): ac(ac_id)  {
  assert(expected > 0);
    if (do_configure == 1) {
      ac.configure(
        AC_behav::BARRIER,
        expected,       // Expected # cores that will participate to the rendezvous
        expected);      // Initial count
    }
  }

  arcsync_barrier(const arcsync_barrier &) = delete;
  ~arcsync_barrier() { }

  // Indicate the core has arrived at the barrier, without waiting.
  // The core MUST call wait() latter, before arriving at the barrier a second time
  // (i.e.: arrive() is never called twice in a row by the same core).
  void arrive() {
    ac.decr_request(AC_req_type::WAIT, AC_notif_type::EVENT);
  }

  // A core must call wait() once for every arrive() call
  void wait() {
    // Wait for the event and decrement local counter
    ac.wait_event();
  }

  // Main function of the barrier.
  void arrive_and_wait() {
    ac.decr_request(AC_req_type::WAIT, AC_notif_type::EVENT);
    // If we are the last core, the wait will just decrement the
    // local event counter and quickly return.
    ac.wait_event();
  }
};

// Global Free Running Counter
// arcsync_gfrc_enable: Enable or disable the counter
static inline
void arcsync_gfrc_enable(bool enable) {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_ADDR_GFRC_ENABLE);
  uint32_t value = enable;
  arcsync_mmio_write(addr, value);
}

// arcsync_gfrc_status: Return current enable/disable status
static inline
uint32_t arcsync_gfrc_status() {
  uint32_t* addr = reinterpret_cast<uint32_t *>(ARCSYNC_ADDR_GFRC_ENABLE);
  return arcsync_mmio_read(addr);
}

// arcsync_gfrc_clear: Clear count to zero
static inline
void arcsync_gfrc_clear() {
  uint32_t* addr = reinterpret_cast<uint32_t *>(ARCSYNC_ADDR_GFRC_CLEAR);
  uint32_t value = 1;
  arcsync_mmio_write(addr, value);
}

// arcsync_gfrc_read: Read all 64bits of the counter (in one access)
static inline
uint64_t arcsync_gfrc_read() {
  uint64_t* addr = reinterpret_cast<uint64_t*>(ARCSYNC_ADDR_GFRC_READ_LO);
  return arcsync_mmio_read(addr);
}

// arcsync_gfrc_read_low: Read the lower 32bit of the counter,
// for cores that do not have 64b load capabilities
static inline
uint32_t arcsync_gfrc_read_low() {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_ADDR_GFRC_READ_LO);
  return arcsync_mmio_read(addr);
}

// arcsync_gfrc_read_hi: Read the 32 upper bits of the counter,
// for cores that do not have 64b load capabilities
static inline
uint32_t arcsync_gfrc_read_hi() {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_ADDR_GFRC_READ_HI);
  return arcsync_mmio_read(addr);
}


// arcsync_vm_gfrc_read: Read all 64bits of the counter from a VM (in one access)
static inline
uint64_t arcsync_vm_gfrc_read(const unsigned vmid, const unsigned receiver_vpid) {
  uint64_t* addr = reinterpret_cast<uint64_t*>(ARCSYNC_ADDR_VM0_GFRC_LO + (vmid<<12) + (receiver_vpid<<2));
  return arcsync_mmio_read(addr);
}

// arcsync_gfrc_read_low: Read the lower 32bit of the counter from a VM,
// for cores that do not have 64b load capabilities
static inline
uint32_t arcsync_vm_gfrc_read_low(const unsigned vmid, const unsigned receiver_vpid) {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_ADDR_VM0_GFRC_LO + (vmid<<12) + (receiver_vpid<<2));
  return arcsync_mmio_read(addr);
}

// arcsync_gfrc_read_hi: Read the 32 upper bits of the counter from a VM,
// for cores that do not have 64b load capabilities
static inline
uint32_t arcsync_vm_gfrc_read_hi(const unsigned vmid, const unsigned receiver_vpid) {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_ADDR_VM0_GFRC_HI + (vmid<<12) + (receiver_vpid<<2));
  return arcsync_mmio_read(addr);
}





// Power Management Unit
// arcsync_pmu_pu_count: set power up counter value which controls the number of cycles between
// the power down signal de-assertion and the isolate signal de-assertion
static inline
void arcsync_pmu_pu_count_set(uint32_t count) {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_ADDR_PMU_SET_PUCNT);
  arcsync_mmio_write(addr, count);
}

static inline
uint32_t arcsync_pmu_pu_count_get() {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_ADDR_PMU_SET_PUCNT);
  return arcsync_mmio_read(addr);
}

// arcsync_pmu_pd_count: set the power down counter value which controls the number of cycles
// between the isolate signal asserting and the power down signal assertion
static inline
void arcsync_pmu_pd_count_set(uint32_t count) {
  uint32_t* addr   = reinterpret_cast<uint32_t*>(ARCSYNC_ADDR_PMU_SET_PDCNT);
  arcsync_mmio_write(addr, count);
}

static inline
uint32_t arcsync_pmu_pd_count_get() {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_ADDR_PMU_SET_PDCNT);
  return arcsync_mmio_read(addr);
}

// arcsync_pmu_rst_count: set the reset counter value which controls the number of cycles
// between the isolate signal de-assertion and the reset signal de-assertion
static inline
void arcsync_pmu_rst_count_set(uint32_t count) {
  uint32_t* addr = reinterpret_cast<uint32_t *>(ARCSYNC_ADDR_PMU_SET_RSTCNT);
  arcsync_mmio_write(addr, count);
}

static inline
uint32_t arcsync_pmu_rst_count_get() {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_ADDR_PMU_SET_RSTCNT);
  return arcsync_mmio_read(addr);
}

static inline
void arcsync_fs_passwd_set(const uint32_t passwd) {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_FS_PASSWD);
  arcsync_mmio_write(addr, passwd);
}

static inline
uint32_t arcsync_fs_passwd_read() {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_FS_PASSWD);
  return arcsync_mmio_read(addr);
}

static inline
void arcsync_reset_release_and_run() {
uint32_t* addr;
uint32_t value;
uint32_t coreid;
  for (int i = 0; i < 16; i++) {
    coreid = i + 1;
    addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_CORE_RESET + coreid * 4);
    value = 0xA5A50000 | (coreid & 0xFFFF);
    arcsync_mmio_write(addr, value);
    addr = reinterpret_cast<uint32_t*>(ARCSYNC_BASE_ADDR_CORE_RUN + coreid * 4);
    value = 1;
    arcsync_mmio_write(addr, value);
    // Polling to confirm the core is run
    while ((arcsync_core_status(coreid) & 0x1) != 0) {  wait_cycles(4); };
  }
}

static inline
void arcsync_fs_diag_write(const uint32_t fs_diag) {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_FS_DIAG);
  arcsync_mmio_write(addr, fs_diag);
}
static inline
uint32_t arcsync_fs_diag_read() {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_FS_DIAG);
  return arcsync_mmio_read(addr);
}
static inline
void arcsync_fs_sfty_ctrl_write(const uint32_t fs_ctrl) {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_FS_CTRL);
  arcsync_mmio_write(addr, fs_ctrl);
}
static inline
uint32_t arcsync_fs_sfty_ctrl_read() {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_FS_CTRL);
  return arcsync_mmio_read(addr);
}
static inline
uint32_t arcsync_fs_sfty_err_status_read() {
  uint32_t* addr = reinterpret_cast<uint32_t*>(ARCSYNC_FS_ERR_STATUS);
  return arcsync_mmio_read(addr);
}
#endif  // ARCSYNC_COMMON_ARCSYNC_UTILS_HPP_
