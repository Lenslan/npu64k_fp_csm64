// Library ARCv2CC-3.2.999999999
//---------------------------------------------------------------------
//           Copyright (c) 2007-2010 The University of Edinburgh
//     All Rights reserved under copyright laws of the United Kingdom
//
// This document, material and/or software contains confidential
// and proprietary information of The University of Edinburgh and is
// protected by copyright, trade secret and other national
// and international laws, and may be embodied in patents issued
// or pending.  Its receipt or possession does not convey any
// rights to use, reproduce, disclose its contents, or to manufacture,
// or sell anything it may describe.  Reverse engineering is prohibited,
// and reproduction, disclosure or use without specific written
// authorization of The University of Edinburgh or its licensees is
// strictly forbidden.
// ARC and the ARC logotype are trademarks of Virage Logic.
//
////////////////////////////////////////////////////////////////////////////////
`include "cc_config.in"
`include "npuarc_cc_exported_defines.v"








////////////////////////////////////////////////////////////////////////////////
//
// Common Verilog/VPP header files
//
////////////////////////////////////////////////////////////////////////////////
//#header rtl/cc_exported_defines.vpp       :ARCv2CC
//#header rtl/cc_defines.vpp                :ARCv2CC

////////////////////////////////////////////////////////////////////////////////
// So that we can use hiergen interfaces, publish the interface definition
// command file for hiergen.
////////////////////////////////////////////////////////////////////////////////
//#vpp rtl/hiergen.vpp                  :PARMS: {output}!dat/cluster_interfaces.txt!

////////////////////////////////////////////////////////////////////////////////
//
// Check the configuration matches all defined constraints
//
////////////////////////////////////////////////////////////////////////////////
//#constraint rtl/constraints.vpp           :CONSTRAINT

////////////////////////////////////////////////////////////////////////////////
//
// Verilog/VPP source files and modules for cluster modules
//
////////////////////////////////////////////////////////////////////////////////
//#source component:ARC_COMN.BCM:rtl/DWbb_bcm21_atv.vpp :RTT,SYNTH,SIM,LOGIC
//#source component:ARC_COMN.BCM:rtl/DWbb_bcm21.vpp     :RTT,SYNTH,SIM,LOGIC
//#source component:ARC_COMN.BCM:rtl/DWbb_bcm99.vpp     :RTT,SYNTH,SIM,LOGIC

//#source rtl/cc_top.vpp                    :ARCv2CC,SYNTH,SIM,LOGIC
//#module cc_top                            :ARCv2CC
//#source rtl/cc_reset_ctrl.vpp             :ARCv2CC,SYNTH,SIM,LOGIC
//#module cc_reset_ctrl                     :ARCv2CC
//#source rtl/cc_aon_wrap.vpp               :ARCv2CC,SYNTH,SIM,LOGIC
//#module cc_aon_wrap                       :ARCv2CC
//#source rtl/cc_pd1_domain.vpp             :ARCv2CC,SYNTH,SIM,LOGIC
//#module cc_pd1_domain                     :ARCv2CC


//#source rtl/cc_aux.vpp                    :ARCv2CC,SYNTH,SIM,LOGIC
//#module cc_aux                            :ARCv2CC
//#source rtl/cc_top_aon_regs.vpp               :ARCv2CC,SYNTH,SIM,LOGIC
//#module cc_top_aon_regs                       :ARCv2CC
//#source rtl/cc_gaux_buffer.vpp            :ARCv2CC,SYNTH,SIM,LOGIC
//#module cc_gaux_buffer                    :ARCv2CC

//#source models/cc_cdc_sync.vpp            :ARCv2CC,SYNTH,SIM,LOGIC
//#module cc_cdc_sync                       :ARCv2CC

//#source rtl/cc_clock_ctrl.vpp             :ARCv2CC,SYNTH,SIM,LOGIC
//#module cc_clock_ctrl                     :ARCv2CC
//#source models/cc_clkgate.vpp             :ARCv2CC,SYNTH,SIM,LOGIC
//#module cc_clkgate                        :ARCv2CC
//

//#vpp constraints/cc_top_exported_tim_defines.vpp        :CLEARTEXT,PARMS:{output}!constraints/cc_top_exported_tim_defines.v!
