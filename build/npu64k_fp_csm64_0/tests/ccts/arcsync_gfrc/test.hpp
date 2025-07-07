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
      if (0==proc_id) { //l2arc
#ifndef RTL_ARC
        rptos << "[INFO]: l2arc processor ID is " << proc_id << endl;
#endif
        uint32_t status;
        status = arcsync_gfrc_status ();
        if (status != 1) {
          // reset value 1
          err_cnt++;
        }
        arcsync_gfrc_enable(0);

        uint64_t value_64;
        value_64 = arcsync_gfrc_read();
        uint32_t value_lo, value_hi;
        uint64_t value_a;
        value_lo = arcsync_gfrc_read_low ();
        value_hi = arcsync_gfrc_read_hi ();
        value_a = ((uint64_t)value_hi <<32)+value_lo;
        if ((value_64!= value_a)| (value_64 ==0)){
          err_cnt++;
        }

        uint64_t value_64v = 0;
        if (ARCSYNC_VIRT_MACHINES > 0) {
          value_64v = arcsync_vm_gfrc_read(0,0);
          uint32_t value_lov, value_hiv;
          uint64_t value_av;
          value_lov = arcsync_vm_gfrc_read_low (0,0);
          value_hiv = arcsync_vm_gfrc_read_hi (0,0);
          value_av = ((uint64_t)value_hiv <<32)+value_lov;
          if ((value_64v!= value_av)| (value_64v ==0)){
            err_cnt++;
          }
          if (value_64v!=value_64){
            err_cnt++;
          }
        }

        arcsync_gfrc_enable(1);
        #ifndef SEED
        srand(55);
        #else
        srand(SEED);
        #endif
        wait_cycles(rand()%200);

        uint64_t value_64_2;
        value_64_2 = arcsync_gfrc_read();
        if (value_64_2 <= value_64){
          err_cnt++;
        }

        if (ARCSYNC_VIRT_MACHINES > 0) {
          uint64_t value_64v_2;
          value_64v_2 = arcsync_vm_gfrc_read(0,0);
          if (value_64v_2 <= value_64v){
            err_cnt++;
          }
          if (value_64v_2 <= value_64_2) {
            err_cnt++;
          }
        }

        arcsync_gfrc_enable(0);
        arcsync_gfrc_clear ();
        value_64 = arcsync_gfrc_read();
        if (value_64!=0){
          err_cnt++;
        }


#ifndef RTL_ARC
      	arc_exit(); //exit the sysc simulation
#else
        set_sim_finish_flag(err_cnt);
#endif
      } else {          //l1arc
#ifndef RTL_ARC
        rptos << "[INFO]: l1arc processor ID is " << proc_id << endl;
#endif
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

