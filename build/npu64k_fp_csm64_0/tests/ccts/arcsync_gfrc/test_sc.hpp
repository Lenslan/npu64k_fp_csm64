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

#include "npu_top_hl_top.hpp"
#include "arcsync.hpp"
#include "npu_tlm2_bus.hpp"
#include "npu_ext_config.hpp"

#ifndef CORE_NUM
#define CORE_NUM (ARCSYNC_NUM_CLUSTER*ARCSYNC_MAX_CORES_PER_CL)
#endif
#define HAS_AS

using namespace npu_top;
using namespace snps::sim;

class testbench : public sc_core::sc_module {
public:
  SC_HAS_PROCESS(testbench);
  static constexpr uint32_t           GB = 1024 * 1024 * 1024;
  static constexpr uint32_t AS_MMIO_SZ   = 4 * 1024 * 1024;
  static constexpr uint32_t AS_MMIO_BASE = (ARCSYNC_BASE_ADDR<<12);
  const sc_core::sc_time PERIOD = sc_core::sc_time(1.0, sc_core::SC_NS);
  testbench(sc_core::sc_module_name n, arc_program ** prg)
    :  sc_core::sc_module(n)
      ,arcsync2npu("arcsync2npu", CORE_NUM)
      ,core_irqs("core_irqs", CORE_NUM)
      ,ddr("ddr", 0)
      ,top("top", 0)
    #ifndef HAS_AS
      ,bus("bus", 1/*ini*/, 1/*tgt*/)
    #else
      ,as("arcsync")
      ,bus("bus", 1/*ini*/, 2/*tgt*/)
      ,run_req("run_req", CORE_NUM)
      ,run_ack("run_ack", CORE_NUM)
      ,halt_req("halt_req", CORE_NUM)
      ,halt_ack("halt_ack", CORE_NUM)
      ,sys_sleep("sys_sleep", CORE_NUM)
      ,sys_sleep_mode("sys_sleep_mode", CORE_NUM)
      ,sys_halt("sys_halt", CORE_NUM)
      ,wdt_reset("wdt_reset", CORE_NUM)
    #endif
      ,clk("clk", PERIOD)
      ,reset("reset")
  {
    bus.addMappingEntry(0,            0,                    GB - 1, 0); //initiator 0 to ddr, can add more entries for a single port
    bus.addMappingEntry(1, AS_MMIO_BASE, AS_MMIO_BASE+AS_MMIO_SZ-1, 0); //initiator 1 to arcsync 0xd400_0000+4MB-1
    bus.initiator_socket[0].bind(ddr.get_target());

    top.axi_port.bind(bus.target_socket[0]);
    top.arcsync2npu(arcsync2npu);
    top.irqs(core_irqs);

    top.set_program(prg[0]);
    for (unsigned i = 0; i < NPU_SLICE_NUM; i++) {
      top.get_slices()[i].set_program(prg[i+1]);
    }

    #ifdef HAS_AS
    bus.initiator_socket[1].bind(as.axi_port);  //DMI
    as.events(arcsync2npu);                     //events
    as.run_req.bind(run_req);                   //FIXME: ignored
    as.run_ack.bind(run_ack);
    as.halt_req.bind(halt_req);
    as.halt_ack.bind(halt_ack);
    as.sys_sleep(sys_sleep);
    as.sys_sleep_mode(sys_sleep_mode);
    as.sys_halt(sys_halt);
    as.wdt_reset(wdt_reset);
    as.core_irqs.bind(core_irqs);              //irqs
    as.clk(clk);
    as.reset(reset);
    #endif
  }

  sc_core::sc_vector<sc_core::sc_fifo<sc_dt::sc_uint<2>>>       arcsync2npu;
  sc_core::sc_vector<sc_core::sc_signal<bool>>                  core_irqs;
  hl_xm                                                         ddr;
  hl_npu_top                                                    top;
  #ifdef HAS_AS
  arcsync<AXI_PORT_WIDTH>                                       as; //FIXME: arcsync dmi is 64-bit wide while the ddr width is 512, tied to 512 for now
  #endif
  npu_tlm2_bus<AXI_PORT_WIDTH, AXI_PORT_WIDTH>                  bus;

  //arcsync signal itf
  #ifdef HAS_AS
  //sc_core::sc_vector<sc_core::sc_fifo_out<sc_dt::sc_uint<2>>> events;
  sc_core::sc_vector<sc_core::sc_signal<bool>> run_req;
  sc_core::sc_vector<sc_core::sc_signal<bool>> run_ack;
  sc_core::sc_vector<sc_core::sc_signal<bool>> halt_req;
  sc_core::sc_vector<sc_core::sc_signal<bool>> halt_ack;
  sc_core::sc_vector<sc_core::sc_signal<bool>> sys_sleep;
  sc_core::sc_vector<sc_core::sc_signal<sc_dt::sc_uint<2>>> sys_sleep_mode;
  sc_core::sc_vector<sc_core::sc_signal<bool>> sys_halt;
  sc_core::sc_vector<sc_core::sc_signal<bool>> wdt_reset;

  //general signal itf
  scml_clock clk;
  //sc_core::sc_signal<bool> clk;
  sc_core::sc_signal<bool> reset;
  #endif
};


int sc_main(int argc, char * argv[]) {
  cout << "Hello sc_main" << endl;
  //return 0;
  string file = "hlrun";
  npu_test     ttst;
  npu_test     stst[NPU_SLICE_NUM];
  arc_program* prg[NPU_SLICE_NUM+1];

  ttst.set_rptname(file);
  prg[0] = &ttst;
  for (int i = 0; i < NPU_SLICE_NUM; i++) {
    stst[i].set_rptname(file);
    prg[i+1] = &stst[i];
  }

  testbench tb("tb", prg);

  //sc_core::sc_start(10000.0, sc_core::SC_NS);
  //cout << "[INFO]: Simulation done @" << sc_time_stamp() << endl;
  npu_timed_module::sim();

  npu_module_if::report_all(cout);

  //std::ofstream rptos;
  //rptos.open(file, std::ofstream::app);
  //rptos << "REPORT done" << endl;
  //rptos.close();

  return 0;
}

