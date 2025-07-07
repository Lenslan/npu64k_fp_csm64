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

#include "npu_ctrl_hl.hpp"
#include "npu_shared_hl_mem.hpp"

class tb : public hl_npu_ctrl, public tlm::tlm_bw_transport_if<> {
public:
  SC_HAS_PROCESS(tb);
  inline tb(sc_core::sc_module_name name, hl_xm & xm,test_program* prg) : 
    hl_npu_ctrl(name, 0, 0, prg), 
    port("port") {
    port.bind(*this);
    port.bind(xm.get_target());
  }
  virtual void update(int ev) {
  }

  tlm::tlm_sync_enum nb_transport_bw(tlm::tlm_generic_payload& trans,
                                     tlm::tlm_phase& phase,
                                     sc_core::sc_time& t) override {
    return tlm::TLM_COMPLETED;
  }

  void invalidate_direct_mem_ptr(sc_dt::uint64 start_range,
                                 sc_dt::uint64 end_range) override { }
  tlm::tlm_initiator_socket<AXI_PORT_WIDTH> port;
};


int sc_main(int argc, char * argv[]) {
  //external memory at 0
  hl_xm      xm("xm", 0);
  // instantiate a program on a core
  test_program tst("test.hlrun.rpt");
  tb tbi("tb", xm, &tst);

  npu_timed_module::sim();

  npu_module_if::report_all(cout);

  return 0;
}


