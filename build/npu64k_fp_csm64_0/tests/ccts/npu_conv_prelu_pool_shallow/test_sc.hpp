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

#include "npu_slice_hl_top.hpp"

using namespace npu_slice;

class tb : public sc_core::sc_module {
public:
  SC_HAS_PROCESS(tb);
  tb(sc_core::sc_module_name name, hl_xm & xm, test_program * tst)
   : sc_core::sc_module(name),
     arcsync2l1("arcsync2l1"),
     rgs(), 
     am("am"), dm("dm"), vm("vm"),
     slc("slice", 1, 0, rgs, am, dm, vm, tst) {
    slc.axi_port.bind(xm.get_target());
    slc.arcsync2l1(arcsync2l1);
    slc.irq(irq);
  }
  sc_core::sc_fifo<sc_dt::sc_uint<2>> arcsync2l1;
  sc_core::sc_signal<bool> irq;
  slice_regs   rgs;
  hl_am        am;
  hl_dm        dm;
  hl_vm        vm;
  hl_npu_slice slc;
};

int sc_main(int argc, char * argv[]) {
  // external memory at 0
  hl_xm      xm("xm", 0);
  // instantiate a program on a core
  test_program tst;
  tb tbi("tb", xm, &tst);
  tst.pxm = &xm;
  tst.pvm = &tbi.vm;
  tst.pam = &tbi.am;
  tst.pdm = &tbi.dm;

  npu_timed_module::sim();

  npu_module_if::report_all(cout);

  return 0;
}
