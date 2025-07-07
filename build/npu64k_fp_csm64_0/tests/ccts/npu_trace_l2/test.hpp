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

#include "tensor.hpp"
using namespace tensor::v200;
using namespace npu;
#include "arcsync_utils.hpp"
#include "utils/cln_map.hpp"
#include "utils/npu_mem_utils.hpp"

class test_program : public arc_program {
public:
  inline test_program() : arc_program() {
    irqflag = false;
  }
  virtual void irq() {
    irqflag = true;
  }

  void exec() {
    proc_id = get_proc_id();
    evt_cfg();

    uint32_t mem_size = get_dm_size();
    uint32_t base_addr = LC_L2_PERI_DM_BASE;
    uint32_t offset = 0x80*proc_id;

    if(proc_id == 0) { //L2 ARc
      //
        //Source Producer Enable
	      _sr (0x57,0x380);
	      _sr (0x81,0x381);
	      _sr (0x1,0x382);

        //Enabling the Producer
	      _sr (0x1,0x380);
	      _sr (0x1,0x381);
	      _sr (0x1,0x382);


        _sr(0XABCDE012, 0X387); //SWE event, will also issue pcsync msg
        _sr(0XAA55AA55, 0X388); //SWE event





        //Disabling the Producer
	      _sr (0x1,0x380);
	      _sr (0x0,0x381);
	      _sr (0x1,0x382);
        //flush command, will issue ptc msg
	      _sr (0x16,0x380);
	      _sr (0x1,0x381);
	      _sr (0x1,0x382);

        uint32_t flush_done = 1;

        while (flush_done == 1) { 
	      _sr (0x16,0x380);
	      _sr (0x0,0x382);
        flush_done = _lr(0x381);
        }

        asm("nop");
        asm("nop");
        asm("nop");

        //self checking -- comparing the tcodes of generted meassages 
        //tcodes dumped into 0x40 & 0x41 aux regs
        uint32_t tcode_data = 0;
        while (tcode_data != 0x0707_093d) { // expected tcode -- swe-swe-pcsync-tsmsg
	      _sr (0x40,0x380);
	      _sr (0x0,0x382);
        tcode_data = _lr(0x381);
        }

        uint32_t tcode_data1 = 0;
        while (tcode_data1 != 0x21) { // expected tcode -- ptc
	      _sr (0x41,0x380);
	      _sr (0x0,0x382);
        tcode_data1 = _lr(0x381);
        }

    }
    else { //L1 ARC in Slice 0 to slice N
    }

    set_sim_finish_flag(err_cnt);
  }



private:
  bool irqflag;
  uint32_t proc_id;
  int err_cnt = 0;
};

