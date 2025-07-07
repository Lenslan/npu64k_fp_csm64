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
#ifdef SYSTEMC
#include "npu_tlm2_bus.hpp"
#endif

#if defined(SYSTEMC) || defined(RTL_DPI)
#include <fstream>
#endif

#include "tensor.hpp"

using namespace tensor::v200;
using namespace npu;

#include "arc_program.hpp"
#include "arcsync_utils.hpp"
#include "utils/sim_terminate.hpp"

#ifdef RTL_ARC
_Uncached volatile uint32_t arcsync_flag = 0;
_Uncached uint32_t sender_id= 0 ;
// Note: In this CCT, only test event0 and IRQ0.
_Uncached uint32_t vm_receiver_vpid = 0;
_Uncached uint32_t vm_sender_vpid = (ARCSYNC_NUM_CLUSTER>1) ? 1 : 0;
_Uncached uint32_t vm_mapped_cluster = 0;

_Interrupt void arcsync_irq_handler()
{
  sender_id = arcsync_ack_irq();

  arcsync_flag = 1;
  _sync();
}

_Interrupt void arcsync_L2_vm_irq_handler()
{
  uint32_t vmid;
  if (ARCSYNC_VIRT_MACHINES > 1) {
    vmid = 1;
  }
  else {
    vmid = 0;
  }
  sender_id = arcsync_ack_virt_irq(vmid, vm_receiver_vpid);

  arcsync_flag = 1;
  _sync();
}

#endif
class npu_test : public arc_program {
  public:
    inline npu_test() : arc_program() { };
    inline void set_rptname(string file) {
      rptname = file;
    }

#ifdef RTL_ARC
    static void wait_arcsync_irq()
    {
      _clri();
      while (arcsync_flag == 0) {
        _sleep(0x1F);
        _clri();
      }
      _seti(0);
    }
#endif

    virtual void exec() override {
      uint32_t vmid;
      int      idx;
      if (ARCSYNC_VIRT_MACHINES > 1) {
        vmid = 1;
        idx  = 24;
      }
      else {
        vmid = 0;
        idx  = 0;
      }
      proc_id = arcsync_coreid();
      evt_cfg();
#ifndef RTL_ARC
      char file[64];
      assert(rptname.size() < sizeof(file)-8);
      std::snprintf(file, sizeof(file), "%s-%02d.rpt", rptname.c_str(), proc_id);
      rptos.open(file);
#endif

      // test body
      int err_cnt = 0;
      bool core_rst_done_bool = false;
      uint32_t core_rst_status;
      uint32_t addr_a;
      uint32_t irq_bit_position;

      if (0==proc_id) { //l2arc
        // Config User VM (VMb) in Virtualization and hyper VM (VMa) in non-Virtual config
        // VMb map user slice start from peers0
        for (int i=1; i<ARCSYNC_VIRT_MACHINES; i++) {
          cfg_vmid(i);
          cfg_vmmap(idx, 0x10, 0x30, 0x8);
        }
        uint64_t mask;
#ifndef RTL_ARC
        rptos << "[INFO]: l2arc processor ID is " << proc_id << endl;
        mask = (1LL << EVT_CHILD0);
        event_send_children((long long)mask);
        rptos << "[INFO]: l2arc sends event to l1arc with mask =" << mask << " " << endl;
#else
        // Note: In Vic 2, L2 arcsync virtualized irq number mapping:
        //   vm0 {gp_irq, ac_irq}: [25:24],
        //   vm1 {gp_irq, ac_irq}: [27:26],
        //   vm2 {gp_irq, ac_irq}: [29:28],
        //   ...
        //   vm7 {gp_irq, ac_irq}: [39:38]
        // Physical (non-vm) IRQ mapping
        //   AC : irq22
        //   EID : irq23
        if (ARCSYNC_VIRT_MACHINES > 0) {
          irq_bit_position = 24 + (vmid*2) + 1;
        _setvecti(irq_bit_position, arcsync_L2_vm_irq_handler);
        }
        else {
          irq_bit_position = 23;
        _setvecti(irq_bit_position, arcsync_irq_handler);
        }

        // Note: set evt_vm_sel_r=vmid
        _sr(vmid, 0xF00);

        uint32_t csm = arcsync_cluster_get_csm_base(0);
        arcsync_cluster_set_csm_base(0, csm + 0x1000000);
        npu::wait_cycles(4);
        uint32_t csm_mod = arcsync_cluster_get_csm_base(0);
        if (csm_mod != csm + 0x1000000) { err_cnt++; }
        arcsync_cluster_set_csm_base(0, csm);

        uint32_t per = arcsync_cluster_get_periph_base(0);
        arcsync_cluster_set_periph_base(0, per + 0x1000000);
        npu::wait_cycles(4);
        uint32_t per_mod = arcsync_cluster_get_periph_base(0);
        if (per_mod != per + 0x1000000) { err_cnt++; }
        arcsync_cluster_set_periph_base(0, per);

        if (ARCSYNC_VIRT_MACHINES > 0) {
          // send event to cluster 0 L2ARC0 through $vmid_$vm_receiver_vpid general purpose event/irq pin
          arcsync_set_vm_map(vmid, vm_receiver_vpid, vm_mapped_cluster);
        }

        uint32_t coreid = 1; // slice 0 coreid
        arcsync_core_halt(coreid);

        arcsync_core_intvbase(coreid, 0x18000000);

        arcsync_core_run(coreid);

        arcsync_core_halt(coreid); // Put core ID 1 in halt mode

        // trigger cluster 0, slice 0 core run
        arcsync_core_run(coreid);

        npu::wait_cycles(10);
        arcsync_core_run(coreid); // only for test api
#endif // RTL_ARC
        // check event from l1
        // wait for ARCSYNC_EVT and CHILD0 event
        mask = (1LL << EVT_CHILD0);
        mask = mask | (1LL<< EVT_ARCSYNC_EVT0);
        //mask = (1LL<< EVT_ARCSYNC_EVT0);
        event_wait_all ((long long)mask);

#ifndef RTL_ARC
        rptos << "[INFO]: l2arc(" << proc_id << ") get events from all children with mask=" << mask << endl;
#endif

#ifdef RTL_ARC
        wait_arcsync_irq();

        // Note: to check L1 ARC is not sleep
        if ((arcsync_core_status(1) & 0x4) == 0) {
          // core ID #1 is not sleep
          err_cnt++;
        }

        if (ARCSYNC_VIRT_MACHINES > 0) {
          // Note: the sender_id value is get in arcsync_L2_vm_irq_handler()
          if (sender_id != vm_sender_vpid) {
            err_cnt++;
          }
        }
#endif
        //L1 ARC can not accept ARCsync Event, use Parent Event instead
        //arcsync_send_event(1);
        mask = (1LL << EVT_CHILD0);
        event_send_children((long long)mask);

        bool ok = arcsync_send_irq(1);
        if (ok == 0){
            err_cnt++;
        }

        addr_a 	= ARCSYNC_BASE_ADDR_EID_ACK_IRQ_0 + (1 * 4);

        while (mmio_read (&addr_a) == 1){
            _nop(); _nop(); _nop();
        }

        mask = (1LL << EVT_CHILD0);
        event_wait_all ((long long)mask);
#ifndef RTL_ARC
        rptos << "REPORT found all events" << endl;
      	arc_exit(); //exit the sysc simulation
#else
        set_sim_finish_flag(err_cnt);
#endif
    // --------------------------------------------------------------------
      } else if (1==proc_id) {          //l1arc
        if (vmid == 0) {
          //Hypervisor
          _sr(0x0, 0xF00);
        }
        else {
          //User
          _sr(0x1, 0xF00);
        }
        uint64_t mask;
#ifndef RTL_ARC
        rptos << "[INFO]: l1arc processor ID is " << proc_id << endl;
        mask = (1LL << EVT_PARENT);
        event_wait_any ((long long)mask);
        rptos << "l1(" << proc_id << ") get event" << endl;
#endif
        // send event to l2
	    event_send_parent();
        uint32_t evt_core_id = 0;
        bool     ok;

        // In Vic 2, L1 arcsync irq number mapping:
        // Physical (non-vm) IRQ mapping
        //   AC (ac_irq)  : irq22
        //   EID (eid_irq) : irq23
        irq_bit_position = 23;
        npu::wait_cycles(1000);
        if (ARCSYNC_VIRT_MACHINES > 0) {
          while (arcsync_virt_event_waiting(vmid, vm_receiver_vpid) == false) {
            npu::wait_cycles(10);
          }
          arcsync_send_virt_event(vmid, vm_receiver_vpid);

#ifndef RTL_ARC
          rptos << "[INFO]: l1arc(" << proc_id << ") sends event back to parent" << endl;
#else

          // Note: IRQ sender should not send IRQ until IRQ is ackknowledged
          addr_a 	= ARCSYNC_BASE_ADDR_VM0_EID_ACK_IRQ_0 + ((vmid<<12) + vm_receiver_vpid) * 4;
          while (mmio_read (&addr_a) == 1){
              _nop(); _nop(); _nop();
          }
  
          //bool ok = arcsync_send_irq(0);
          ok = arcsync_send_virt_irq(vmid, vm_receiver_vpid, vm_sender_vpid);
          if (ok == 0){
              err_cnt++;
          }
          //ok = arcsync_send_irq(0);
#endif
        }
        else {
          // Use Physical Event
          while (arcsync_event_waiting(evt_core_id) == false) {
            npu::wait_cycles(10);
          }
          arcsync_send_event(evt_core_id);

#ifndef RTL_ARC
          rptos << "[INFO]: l1arc(" << proc_id << ") sends event back to parent" << endl;
#else

          // Note: IRQ sender should not send IRQ until IRQ is ackknowledged
          addr_a 	= ARCSYNC_BASE_ADDR_EID_ACK_IRQ_0 + evt_core_id*4;
          while (mmio_read (&addr_a) == 1){
              _nop(); _nop(); _nop();
          }
  
          ok = arcsync_send_irq(evt_core_id);
          if (ok == 0){
              err_cnt++;
          }
#endif
        }

#ifdef RTL_ARC
        //L1 ARC not support event from ARCsync, use parent event instead
        mask = 1LL<< EVT_PARENT;
        event_wait_all ((long long)mask);


        arcsync_flag = 0;
        _setvecti(irq_bit_position, arcsync_irq_handler);
        wait_arcsync_irq();

        event_send_parent();

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

