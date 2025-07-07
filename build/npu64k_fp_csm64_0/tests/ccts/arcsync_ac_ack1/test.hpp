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

#include "npu_config.hpp"
#include "arc_program.hpp"
#ifdef SYSTEMC
#include "npu_tlm2_bus.hpp"
#endif

#if defined(SYSTEMC) || defined(RTL_DPI)
#include <fstream>
#endif

#include "tensor.hpp"

using namespace tensor::v200;
using namespace npu;

#include "arcsync_utils.hpp"
#include "utils/sim_terminate.hpp"
#include "utils/arc_irq_expcn.hpp"


#ifdef RTL_ARC

volatile bool synchro_flag;

uint32_t sender_id= 0 ;
// Note: In this CCT, only test event0 and IRQ0.
uint32_t vmid = 1;
uint32_t vm_receiver_vpid = 0;
uint32_t vm_sender_vpid = (ARCSYNC_NUM_CLUSTER>1) ? 1 : 0;
uint32_t vm_mapped_cluster = 0;

_Interrupt void arcsync_irq_handler()
{
  arcsync_ack_ac_irq();

  synchro_flag = 1;
  _sync();
}

_Interrupt void arcsync_L2_vm_irq_handler()
{
  arcsync_ack_virt_ac_irq(vmid, vm_receiver_vpid);

  synchro_flag = 1;
  _sync();
}
#endif

class npu_test : public arc_program {
  public:
    inline npu_test() : arc_program() { };
    inline void set_rptname(string file) {
      rptname = file;
    }

    virtual void exec() override {
#ifdef RTL_ARC
      arcsync_id_init();
#endif
      proc_id = get_proc_id();
      evt_cfg();
#ifndef RTL_ARC
      char file[64];
      assert(rptname.size() < sizeof(file)-8);
      std::snprintf(file, sizeof(file), "%s-%02d.rpt", rptname.c_str(), proc_id);
      rptos.open(file);
#endif

      // test body
      int err_cnt = 0;

      #ifndef SEED
      srand(55);
      #else
      srand(SEED);
      #endif
      //int virt_ac_num = rand()%8;
      int virt_ac_num = 1; // virtualization ac_num: 0~((ARCSYNC_NUM_ATOMIC_CNT/ARCSYNC_VIRT_MACHINES)-1)
      int non_virt_ac_num;
      uint32_t irq_bit_position;
      uint32_t j;
      //vmid=2;

      if (0==proc_id) { //l2arc
        uint64_t mask;
        int      idx;
        if (ARCSYNC_VIRT_MACHINES > 1) {
          idx  = 24;
        }
        else {
          idx  = 0;
        }
        // Config User VM (VMb) in Virtual while use Hyper VM (VMa) in non-Virtual
        // VMb map user slice start from peers0
        for (int i=1; i<8; i++) {
          cfg_vmid(i);
          cfg_vmmap(idx, 0x10, 0x30, 0x8);
        }

        int int_base = _lr(0x25); // int_vect_base
        _set_ptag(int_base);

        if (ARCSYNC_VIRT_MACHINES > 0) {
          for (j=0; j<ARCSYNC_VIRT_MACHINES; j++) {
            vmid = j;

            non_virt_ac_num = vmid*(ARCSYNC_NUM_ATOMIC_CNT/ARCSYNC_VIRT_MACHINES) + (virt_ac_num%(ARCSYNC_NUM_ATOMIC_CNT/ARCSYNC_VIRT_MACHINES));

            // Note: In Vic 2, L2 arcsync virtualized irq number mapping:
            //   vm0 {gp_irq, ac_irq}: [25:24],
            //   vm1 {gp_irq, ac_irq}: [27:26],
            //   vm2 {gp_irq, ac_irq}: [29:28],
            //   ...
            //   vm7 {gp_irq, ac_irq}: [39:38]
            // Physical (non-vm) IRQ mapping
            //   AC : irq22
            //   EID : irq23
            irq_bit_position = 24 + (vmid*2);
            _setvecti(irq_bit_position, arcsync_L2_vm_irq_handler);

            // Note: set evt_vm_sel_r=vmid
            _sr(vmid, 0xF00);

            // send event to cluster 0 L2ARC0 through $vmid_$vm_receiver_vpid general purpose event/irq pin
            arcsync_set_vm_map(vmid, vm_receiver_vpid, vm_mapped_cluster);

            arcsync_mutex         mutex{non_virt_ac_num,1};
            wait_cycles(40);

            //mutex.virt_lock();
            mutex.virt_lock_irq_notify(vmid, vm_receiver_vpid); // test virt ac irq
            wait_cycles(20);
            mutex.virt_unlock(vmid, vm_receiver_vpid);

            // new added
            mutex.virt_lock(vmid, vm_receiver_vpid); // test virt ac event

            //mask = (1LL << EVT_CHILD0);
            //event_send_children((long long)mask); // wake up l1arc

            wait_cycles(20);
            mutex.virt_unlock(vmid, vm_receiver_vpid);
          } // for j
        }
        else {
          // Physical (non-vm) IRQ mapping
          //   AC : irq22
          //   EID : irq23
          irq_bit_position = 22;
          _setvecti(irq_bit_position, arcsync_irq_handler);

          // Note: set evt_vm_sel_r=0
          _sr(0x0, 0xF00);

          arcsync_mutex         mutex{1,1};
          wait_cycles(40);

          mutex.lock_irq_notify(); // test virt ac irq
          wait_cycles(20);
          mutex.unlock();

          mutex.lock(); // test virt ac event
          wait_cycles(20);
          mutex.unlock();
        }

        mask = (1LL << EVT_CHILD0);
        event_send_children((long long)mask);
        wait_cycles(10);

        mask = (1LL << EVT_CHILD0);
        event_wait_all ((long long)mask);

#ifndef RTL_ARC
      	arc_exit(); //exit the sysc simulation
#else
        set_sim_finish_flag(err_cnt);
#endif

      } else {          //l1arc
        if (ARCSYNC_VIRT_MACHINES > 1) {
          if (vmid == 0) {
            //Hypervisor
            _sr(0x0, 0xF00);
          }
          else {
            //User
            _sr(0x1, 0xF00);
          }
        }
        else {
          //Hypervisor
          _sr(0x0, 0xF00);
        }

        uint64_t mask;

        // In Vic 2, L1 arcsync irq number mapping:
        // Physical (non-vm) IRQ mapping
        //   AC (ac_irq)  : irq22
        //   EID (eid_irq) : irq23
        _setvecti(22, arcsync_irq_handler);

        mask = (1LL << EVT_PARENT);
        event_wait_all ((long long)mask);

        arcsync_mutex         mutex{1, 1};

        mutex.lock_irq_notify(); // test non-virt ac irq
        wait_cycles(10);
        mutex.unlock();

        // code end and send event to parent
        event_send_parent();

#ifndef RTL_ARC
        rptos << "[INFO]: l1arc(" << proc_id << ") sends event back to parent" << endl;
#else
        set_sim_finish_flag(err_cnt);
#endif
      }

#ifndef RTL_ARC
      rptos.close();
#endif
}
    virtual void irq() override {
    }

  private:
    string   rptname;
    uint32_t proc_id;
#ifndef RTL_ARC
    std::ofstream rptos;
#endif
};
