// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//    #     #     #  #     #          ####  ###### ######   #
//   # #    #     #   #   #          #    #   #    #     #  #
//  #   #   #     #    # #           #        #    #     #  #
// #     #  #     #     #            #        #    ######   #
// #######  #     #    # #           #        #    #   #    #
// #     #  #     #   #   #          #    #   #    #    #   #
// #     #   #####   #     #  #####   ####    #    #     #  ######
//
//============================================================================
//
// Description:
//
//  This module implements the Auxiliary Control of the ARCv2HS CPU.
//  AUX Register Blocks:
// ----------------------------
//  1. AUX :XX: CORE
//  2. APS :05: Action Points
//  3. BCR :08: Build Configuration Regsisters
//  4. DC  :04: DCACHE
//  5. EIA :07: Extension Instruction Architecture
//  6. FPU :01: Floating Point Unit
//  7. IC  :04: ICACHE
//  8. IRQ :12: Interrupt Request Unit
//  9. MMU :05: Memory Management Unit
// 10. MPU :07: Memory Protection Unit
// 11. PCT :06: Performance Counter
// 12. RTC :03: Real-Time Counter
// 13. SMT :01: SmaRT
//     RTT :38: RTT
// 14. TM0 :02: Timers 0
// 15. TM1 :02: Timers 1
// 16. ICCM:00: ICCM
// 17. DCCM:00: DCCM
// 18. BPU :04: BPU
// 19. MCIP:XX: ARConnect
// 20: SNP :XX: IO Coherence control
// 21. DMAC:XX: DMA Controller
// 22. RPU: 03: ROM Patching Unit
//
// Dependency Control Interface
// ----------------------------
//  xx_stall : Generated at  stage XX, by the dependency module, and
//             asserted when stage XX instruction cannot proceed.
//  xx_enable: Asserted when stage XX is permitted to accept a new instruction.
//  xx_pass  : Asserted when stage XX has a valid instruction
//             that is not subject to a local stall.
//  xx_holdup: Asserted when stage XX cannot accept input
//             from its preceding stage.
//  xx_kill  : Asserted when the operation at stage XX will be killed
//             in the current cycle
//             (e.g. by a pipe flush)
//  xx_retain: Asserted when the operation at stage XX must be retained
//             during the current cycle
//
// ==========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Include definitions for the microcode constants, including both ARC
// base-case and any User extension instructions which may be defined.
//
`include "npuarc_ucode_const.v"

// Definitions for all decode-related constants
//
`include "npuarc_decode_const.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_aux_ctrl (
  //////////////////////// AUX Control Interface//////////////////////////////
  //
  // X2 Stage Control
  input                       x2_pass,
  input   [`npuarc_DATA_RANGE]       x2_aux_addr_r,        // from x2_src1_r
  input                       x2_lr_op_r,
  input                       x2_sr_op_r,
  // X3 Stage Control
  input                       x3_pass,
  input                       x3_enable,
  input                       x3_lr_op_r,
  input                       x3_sr_op_r,
  output                      aux_x3_stall,         //  LR RAW hazard detect
  input                       fch_restart,

  // CA Stage Control
  input                       ca_pass,
  input                       ca_enable,
  input                       ca_lr_op_r,
  input                       ca_sr_op_r,
  input                       ca_aux_cond,

  // WA Stage Control
  input                       wa_enable,
  // leda NTL_CON13C off
  // LMD: non driving port
  // LJ:  Not all bits used  
  input                       wa_sr_op_r,
  // leda NTL_CON13C on
  // AUX <-> EXU Aux interface
  output     [`npuarc_DATA_RANGE]    aux_ca_lr_data,       //  (CA) Merge LR data
  output                      aux_ca_serial_sr,     //  (CA) SR group flush pipe
  output                      aux_ca_strict_sr,     //  (CA) SR flush pipe

  // AUX -> DEP Hazard detect
  output reg                  aux_x2_r4_sr,         // core region 4 SR at X2
  output reg                  aux_x3_r4_sr_r,       // core region 4 SR at X3
  output reg                  aux_ca_r4_sr_r,       // core region 4 SR at CA

  ////////// Auxiliary interface for (CORE) SR/LR instructions ///////////////
  //
  output reg                  aux_core_ren_r,       //  (X3) Aux Reg Enable
  output reg                  aux_cr1_ren_r,        //  (X3) Aux Region 1 Enable
  output reg                  aux_cr2_ren_r,        //  (X3) Aux Region 2 Enable
  output reg                  aux_cr3_ren_r,        //  (X3) Aux Region 3 Enable
  output reg                  aux_cr4_ren_r,        //  (X3) Aux Region 4 Enable
  output reg                  aux_cr5_ren_r,        //  (X3) Aux Region 5 Enable

  output      [10:0]          aux_core_raddr_r,     //  (X3) Aux Address
  output reg                  aux_core_wen_r,       //  (WA) Aux Reg Enable
  output      [10:0]          aux_core_waddr_r,     //  (WA) Aux Address

  input       [`npuarc_DATA_RANGE]   core_aux_rdata,       //  (X3) LR read data
  input                       core_aux_illegal,     //  (X3) SR/LR illegal
  input                       core_aux_k_rd,        //  (X3) need Kernel Read
  input                       core_aux_k_wr,        //  (X3) need Kernel Write
  input                       core_aux_unimpl,      //  (X3) Invalid Reg
  input                       core_aux_serial_sr,   //  (X3) SR group flush pipe
  input                       core_aux_strict_sr,   //  (X3) SR flush pipe
  input                       core_aux_stall,       //  Core RAW Hazard detect

  ////////// Auxiliary interface for (BCR) SR/LR instructions ////////////////
  //
  output reg                  aux_bcr_ren_r,        //  (X3) Aux read enable
  output reg [`npuarc_BCR_REG_RANGE] aux_bcr_raddr_r,      //  (X3) Aux Address
  input      [`npuarc_DATA_RANGE]    bcr_aux_rdata,        //  (X3) LR read data
  input                       bcr_aux_illegal,      //  (X3) SR/LR  illegal
  input                       bcr_aux_k_rd,         //  (X3) need Kernel Read

  output                      dmp_aux_sr_op,        // DMP SR op in Pipe


  ////////// Auxiliary interface for (DC) SR/LR instructions /////////////////
  //
  output reg                  aux_dc_ren_r,         //  (X3) Aux read enable
  output reg  [4:0]           aux_dc_raddr_r,       //  (X3) Aux Address
  output reg                  aux_dc_wen_r,         //  (WA) Aux write enable
  output reg  [4:0]           aux_dc_waddr_r,       //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   dc_aux_rdata,         //  (X3) LR read data
  input                       dc_aux_illegal,       //  (X3) SR/LR illegal
  input                       dc_aux_k_rd,          //  (X3) need Kernel Rd
  input                       dc_aux_k_wr,          //  (X3) need Kernel Wr
  input                       dc_aux_unimpl,        //  (X3) Invalid Reg
  input                       dc_aux_serial_sr,     //  (X3) SR group flush
  input                       dc_aux_strict_sr,     //  (X3) SR single flus  h
  input                       dc_aux_busy,          //  Structural hazard

  ////////// Auxiliary interface for (EIA) SR/LR instructions ////////////////
  //
  output reg                  aux_eia_ren_r,        //  (X3) Aux Unit LR Enable
  output      [`npuarc_DATA_RANGE]   aux_eia_raddr_r,      //  (X3) Aux Unit LR Address
  output reg                  aux_eia_wen_r,        //  (WA) Aux Unit SR Enable
  output      [`npuarc_DATA_RANGE]   aux_eia_waddr_r,      //  (WA) Aux Unit SR Address
  input       [`npuarc_DATA_RANGE]   eia_aux_rdata,        //  (X3) LR read data
  input                       eia_aux_illegal,      //  (X3) SR/LR illegal
  input                       eia_aux_k_rd,         //  (X3) need Kernel Read
  input                       eia_aux_k_wr,         //  (X3) need Kernel Write
  input                       eia_aux_unimpl,       //  (X3) Invalid Reg
  input                       eia_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       eia_aux_strict_sr,    //  (X3) SR flush pipe
  input                       eia_aux_stall,        //  EIA RAW Hazard detect

  ////////// Auxiliary interface for common aux register accesses ////////////
  //
  output                      aux_rs_valid,         //  CCAUX valid rd request
  output [`npuarc_CCAUX_RGN_RANGE]   aux_rs_region,        //  CCAUX region identity
  output [`npuarc_CCAUX_ADDR_RANGE]  aux_rs_addr,          //  CCAUX region offset
  output                      aux_rs_read,          //  CCAUX read enable
  output                      aux_rs_write,         //  CCAUX write enable
  input  [`npuarc_DATA_RANGE]        aux_rs_data,          //  CCAUX LR data
  input  [`npuarc_CCAUX_STAT_RANGE]  aux_rs_status,        //  CCAUX credintials
  input                       aux_rs_accept,        //  CCAUX response read

  output                      aux_wr_valid,         //  CCAux wr valid
  output [`npuarc_CCAUX_RGN_RANGE]   aux_wr_region,        //  CCAux wr region
  output [`npuarc_CCAUX_ADDR_RANGE]  aux_wr_addr,          //  CCAux wr Address
  input                       aux_wr_allow,         //  CCAux new write allowed
  output                      aux_cm_phase,         //  CCAux in commit phase
  output                      aux_cm_valid,         //  CCAux commit is valid


  ////////// Auxiliary interface for (ICACHE) SR/LR instructions /////////////
  //
  output reg                  aux_ic_ren_r,         //  (X3) Aux Reg Enable
  output reg  [3:0]           aux_ic_raddr_r,       //  (X3) Aux Address
  output reg                  aux_ic_wen_r,         //  (WA) Aux Reg Enable
  output reg  [3:0]           aux_ic_waddr_r,       //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   ic_aux_rdata,         //  (X3) LR read data
  input                       ic_aux_illegal,       //  (X3) SR/LR illegal
  input                       ic_aux_k_rd,          //  (X3) need Kernel Read
  input                       ic_aux_k_wr,          //  (X3) need Kernel Write
  input                       ic_aux_unimpl,        //  (X3) Invalid Reg
  input                       ic_aux_serial_sr,     //  (X3) SR group flush pipe
  input                       ic_aux_strict_sr,     //  (X3) SR flush pipe

  output reg                  aux_bpu_ren_r,        //  (X3) Aux Reg Enable
  output reg  [3:0]           aux_bpu_raddr_r,      //  (X3) Aux Address
  output reg                  aux_bpu_wen_r,        //  (WA) Aux Reg Enable
  output reg  [3:0]           aux_bpu_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   bpu_aux_rdata,        //  (X3) LR read data
  input                       bpu_aux_illegal,      //  (X3) SR/LR illegal
  input                       bpu_aux_k_rd,         //  (X3) need Kernel Read
  input                       bpu_aux_k_wr,         //  (X3) need Kernel Write
  input                       bpu_aux_unimpl,       //  (X3) Invalid Reg
  input                       bpu_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       bpu_aux_strict_sr,    //  (X3) SR flush pipe

  ////////// Auxiliary interface for (SMT) SR/LR instructions ////////////////
  //
  output                      aux_smt_active,       //  RTT smart is active
  output reg                  aux_smt_ren_r,        //  (X3) Aux Reg Enable
  output reg                  aux_smt_raddr_r,      //  (X3) Aux Address
  output reg                  aux_smt_wen_r,        //  (WA) Aux Reg Enable
  output reg                  aux_smt_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   smt_aux_rdata,        //  (X3) LR read data
  input                       smt_aux_illegal,      //  (X3) SR/LR illegal
  input                       smt_aux_k_rd,         //  (X3) need Kernel Read
  input                       smt_aux_k_wr,         //  (X3) need Kernel Write
  input                       smt_aux_unimpl,       //  (X3) Invalid Reg
  input                       smt_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       smt_aux_strict_sr,    //  (X3) SR flush pipe

  ////////// Auxiliary interface for (RTT) SR/LR instructions ////////////////
  //
  output                      aux_rtt_active,       //  RTT SR is active
  output reg                  aux_rtt_ren_r,        //  (X3) Aux Reg Enable
  output reg  [3:0]           aux_rtt_raddr_r,      //  (X3) Aux Address
  output reg                  aux_rtt_wen_r,        //  (WA) Aux Reg Enable
  output reg  [3:0]           aux_rtt_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   rtt_aux_rdata,        //  (X3) LR read data
  input                       rtt_aux_illegal,      //  (X3) SR/LR illegal
  input                       rtt_aux_k_rd,         //  (X3) need Kernel Read
  input                       rtt_aux_k_wr,         //  (X3) need Kernel Write
  input                       rtt_aux_unimpl,       //  (X3) Invalid Reg
  input                       rtt_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       rtt_aux_strict_sr,    //  (X3) SR flush pipe

  ////////// Auxiliary interface for (Timer) SR/LR instructions //////////////
  //
  output reg                  aux_tm0_ren_r,        //  (X3) Aux Reg Enable
  output reg  [1:0]           aux_tm0_raddr_r,      //  (X3) Aux Address
  output reg                  aux_tm0_wen_r,        //  (WA) Aux Reg Enable
  output reg  [1:0]           aux_tm0_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   tm0_aux_rdata,        //  (X3) LR read data
// leda NTL_CON13C off
// leda NTL_CON37 off 
// LMD: non driving port
// LJ:  standard aux interface 
  input                       tm0_aux_illegal,      //  (X3) SR/LR illegal
// leda NTL_CON13C on 
// leda NTL_CON37 on 
  input                       tm0_aux_k_rd,         //  (X3) needs Kernel Read
  input                       tm0_aux_k_wr,         //  (X3) needs Kernel W perm
  input                       tm0_aux_unimpl,       //  (X3) Invalid Reg
  input                       tm0_aux_serial_sr,    //  (X3) serializing SR
  output                      aux_timer_active,    // timer SR is active 


  output reg                  aux_irq_ren_r,        //  (X3) Aux Reg Enable
  output reg [`npuarc_AUX_REG_RANGE] aux_irq_raddr_r,      //  (X3) Aux Address
  output reg                  aux_irq_wen_r,        //  (WA) Aux Reg Enable
  output reg [`npuarc_AUX_REG_RANGE] aux_irq_waddr_r,      //  (WA) Aux Address
  input      [`npuarc_DATA_RANGE]    irq_aux_rdata,        //  (X3) LR read data
  input                       irq_aux_illegal,      //  (X3) SR/LR illegal
  input                       irq_aux_k_rd,         //  (X3) needs Kernel Read
  input                       irq_aux_k_wr,         //  (X3) needs Kernel W perm
  input                       irq_aux_unimpl,       //  (X3) Invalid Reg
  input                       irq_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       irq_aux_strict_sr,    //  (X3) SR flush pipe

  input                       x2_rtie_op_r,         //  
  input                       x3_rtie_op_r,         //  

  output reg                  aux_wdt_ren_r,        //  (X3) Aux Reg Enable
  output reg  [3:0]           aux_wdt_raddr_r,      //  (X3) Aux Address
  output reg                  aux_wdt_wen_r,        //  (WA) Aux Reg Enable
  output reg  [3:0]           aux_wdt_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   wdt_aux_rdata,        //  (X3) LR read data
  input                       wdt_aux_illegal,      //  (X3) SR/LR illegal
  input                       wdt_aux_k_rd,         //  (X3) needs Kernel Read
  input                       wdt_aux_k_wr,         //  (X3) needs Kernel W perm
  input                       wdt_aux_unimpl,       //  (X3) Invalid Reg
  input                       wdt_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       wdt_aux_strict_sr,    //  (X3) SR flush pipe

  output reg                  aux_rtc_ren_r,        //  (X3) Aux Reg Enable
  output reg  [2:0]           aux_rtc_raddr_r,      //  (X3) Aux Address
  output reg                  aux_rtc_wen_r,        //  (WA) Aux Reg Enable
  output reg  [2:0]           aux_rtc_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   rtc_aux_rdata,        //  (X3) LR read data
  input                       rtc_aux_illegal,      //  (X3) SR/LR illegal
  input                       rtc_aux_k_rd,         //  (X3) needs Kernel Read
  input                       rtc_aux_k_wr,         //  (X3) needs Kernel W perm
  input                       rtc_aux_unimpl,       //  (X3) Invalid Reg
  input                       rtc_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       rtc_aux_strict_sr,    //  (X3) SR flush pipe

  output                      aux_pct_active,       //  PCT SR is active
  output reg                  aux_pct_ren_r,        //  (X3) Aux Reg Enable
  output reg  [5:0]           aux_pct_raddr_r,      //  (X3) Aux Address
  output reg                  aux_pct_wen_r,        //  (WA) Aux Reg Enable
  output reg  [5:0]           aux_pct_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   pct_aux_rdata,        //  (X3) LR read data
  input                       pct_aux_illegal,      //  (X3) SR/LR illegal
  input                       pct_aux_k_rd,         //  (X3) needs Kernel Rd
  input                       pct_aux_k_wr,         //  (X3) needs Kernel Wr
  input                       pct_aux_unimpl,       //  (X3) Invalid Reg
  input                       pct_aux_serial_sr,    //  (X3) SR group flush
  input                       pct_aux_strict_sr,    //  (X3) SR single flush

  output reg                  aux_mpu_ren_r,        //  (X3) Aux Reg Enable
  output reg  [6:0]           aux_mpu_raddr_r,      //  (X3) Aux Address
  output reg                  aux_mpu_wen_r,        //  (WA) Aux Reg Enable
  output reg  [6:0]           aux_mpu_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   mpu_aux_rdata,        //  (X3) LR read data
  input                       mpu_aux_illegal,      //  (X3) SR/LR illegal
  input                       mpu_aux_k_rd,         //  (X3) needs Kernel Read
  input                       mpu_aux_k_wr,         //  (X3) needs Kernel W perm
  input                       mpu_aux_unimpl,       //  (X3) Invalid Reg
  input                       mpu_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       mpu_aux_strict_sr,    //  (X3) SR flush pipe

  output reg                  aux_mmu_ren_r,        //  (X3) Aux Reg Enable
  output reg  [4:0]           aux_mmu_raddr_r,      //  (X3) Aux Address
  output reg                  aux_mmu_wen_r,        //  (WA) Aux Reg Enable
  output reg  [4:0]           aux_mmu_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   mmu_aux_rdata,        //  (X3) LR read data
  input                       mmu_aux_illegal,      //  (X3) SR/LR illegal
  input                       mmu_aux_k_rd,         //  (X3) needs Kernel Read
  input                       mmu_aux_k_wr,         //  (X3) needs Kernel W perm
  input                       mmu_aux_unimpl,       //  (X3) Invalid Reg
  input                       mmu_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       mmu_aux_strict_sr,    //  (X3) SR flush pipe

  output reg                  aux_dccm_ren_r,       //  (X3) Aux Reg Enable
  output reg                  aux_dccm_wen_r,       //  (WA) Aux Reg Enable
  input       [`npuarc_DATA_RANGE]   dccm_aux_rdata,       //  (X3) LR read data
  input                       dccm_aux_illegal,     //  (X3) SR/LR illegal
  input                       dccm_aux_k_rd,        //  (X3) needs Kernel Read
  input                       dccm_aux_k_wr,        //  (X3) needs Kernel Write
  input                       dccm_aux_unimpl,      //  (X3) Invalid Reg
  input                       dccm_aux_serial_sr,   //  (X3) SR group flush pipe
  input                       dccm_aux_strict_sr,   //  (X3) SR flush pipe

  output                      aux_aps_active,       //  AP SR is active
  output reg                  aux_aps_ren_r,        //  (X3) Aux Reg Enable
  output reg  [4:0]           aux_aps_raddr_r,      //  (X3) Aux Address
  output reg                  aux_aps_wen_r,        //  (WA) Aux Write Enable
  output reg  [4:0]           aux_aps_waddr_r,      //  (WA) Aux Write Address
  input       [`npuarc_DATA_RANGE]   aps_aux_rdata,        //  (X3) LR read data
  input                       aps_aux_illegal,      //  (X3) SR/LR illegal
  input                       aps_aux_k_rd,         //  (X3) need Kernel Read
  input                       aps_aux_k_wr,         //  (X3) needs Kernel W perm
  input                       aps_aux_unimpl,       //  (X3) Invalid Reg
  input                       aps_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       aps_aux_strict_sr,    //  (X3) SR flush pipe

  output reg                  aux_dper_ren_r,       //  (X3) Aux Reg Enable
  output reg                  aux_dper_raddr_r,     //  (X3) Aux Reg Address
  output reg                  aux_dper_wen_r,       //  (WA) Aux Reg Enable
  output reg                  aux_dper_waddr_r,     //  (WA) Aux Reg Address
  input       [`npuarc_DATA_RANGE]   dper_aux_rdata,       //  (X3) LR read data
  input                       dper_aux_illegal,     //  (X3) SR/LR illegal
  input                       dper_aux_k_rd,        //  (X3) need Kernel Read
  input                       dper_aux_k_wr,        //  (X3) needs Kernel W perm
  input                       dper_aux_unimpl,      //  (X3) Invalid Reg
  input                       dper_aux_serial_sr,   //  (X3) SR group flush pipe
  input                       dper_aux_strict_sr,   //  (X3) SR flush pipe


  ////////// Outputs to Exception Pipeline ///////////////////////////////////
  //
  output reg                  x3_aux_unimpl_r,      //
  output reg                  x3_aux_illegal_r,     //
  output reg                  x3_aux_k_ro_r,        //
  output reg                  x3_aux_k_wr_r,        //

  ////////// Misc Outputs ////////////////////////////////////////////////////
  //
  output [`npuarc_AUX_REG_RANGE]     wa_aux_rtt_addr_r,   // WA aux address (narrow)

  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,                  // global clock
  input                       rst_a                 // asynchronous reset signal
);

reg  [`npuarc_AUX_REG_RANGE]         x2_arc_addr_r;    // X2 aux address (narrow)
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some addr bits unused
reg  [`npuarc_DATA_RANGE]            x3_aux_addr_r;    // X3 aux address (wide)
reg  [`npuarc_DATA_RANGE]            ca_aux_addr_r;    // CA aux address (wide)
reg  [`npuarc_DATA_RANGE]            wa_aux_addr_r;    // WA aux address (narrow)
// leda NTL_CON32 on
reg                           x2_arc_range;     // aux addr < 4096 at X2

reg                           x3_unimpl_cg0;
reg                           x3_arc_unimpl_nxt; // ARC Unimplemented
reg                           x3_arc_unimpl_r;   // ARC Unimplemented

reg                           x2_aux_op;        // valid LR, SR or AEX at X2
reg                           x3_aux_op;        // valid LR, SR or AEX at X3
reg                           ca_aux_op;        // valid LR, SR or AEX at CA

reg                           x3_addr_cg0;      // enables X3 address
reg                           ca_addr_cg0;      // enables CA address
reg                           wa_addr_cg0;      // enables WA address

reg                           x3_aux_cg1;       // high-level X3 aux enable
reg                           ca_aux_cg1;       // high-level CA aux enable
reg                           wa_aux_cg1;       // high-level WA aux enable

reg                           aux_ap1_wen_r;    //  Extend AP Aux WEN

reg  [`npuarc_DATA_RANGE]        ccaux_rdata_r;        // CCAUX bus read data register
reg                       ccaux_resp_r;         // CCAUX bus response vector
reg  [`npuarc_CCAUX_STAT_RANGE]  ccaux_status_r;       // CCAUX bus status register
reg  [`npuarc_DATA_RANGE]        ccaux_aux_rdata_r;    // (X3) LR read data
wire                      ccaux_serial_sr_r;    // CCAUX strict bit from status
wire                      ccaux_strict_sr_r;    // CCAUX strict bit from status
wire                      ccaux_illegal_r;      // CCAUX illegal bit from status
wire                      ccaux_k_rd_r;         // CCAUX k rd bit from status
wire                      ccaux_k_wr_r;         // CCAUX k wr bit from status
reg [`npuarc_CCAUX_RGN_RANGE]   x2_ccaux_region;      // CCAUX region select at X2

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinatorial process to define the register enables for all pipeline    //
// registers that are defined in this module.                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : aux_cg0_PROC

  x2_aux_op       = x2_lr_op_r | x2_sr_op_r;            // valid aux op at X2
  x3_aux_op       = x3_lr_op_r | x3_sr_op_r;            // valid aux op at X3
  ca_aux_op       = ca_lr_op_r | ca_sr_op_r;            // valid aux op at CA

  x3_addr_cg0     = x2_pass & x3_enable & x2_aux_op;    // Aux Op Start
  ca_addr_cg0     = x3_pass & ca_enable & x3_aux_op;    // Aux Perm Capture
  wa_addr_cg0     = ca_pass & wa_enable & ca_aux_op;    // Aux Sr Start

  //==========================================================================
  // Enable clock tree to lower levels of aux control pipe, on a per-stage
  // basis, when there is an LR or SR operation in the preceding stage
  // or the current stage. This enables the clock to allow any LR or SR
  // operations to propagate into that stage, as well as allowing them
  // to propagate out. At all other times, there is no need for any clock
  // to any of the region-based pipeline registers at the given stage.
  //
  // The top-level *_cg1 signals take no account of pipeline flow control
  // signals (*_pass or *_enable). That is taken care of by the *_cg0 signals.
  //
  x3_aux_cg1     = x2_aux_op | x3_aux_op;
  ca_aux_cg1     = x3_aux_op | ca_aux_op;
  wa_aux_cg1     = ca_aux_op | wa_sr_op_r;

end // aux_cg0_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinatorial process to detect auxiliary address ranges in X2           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : aux_range_PROC

  //==========================================================================
  // x2_arc_range is asserted whenever the X2 auxiliary address has all
  // zeros in bit positions from AUX_REG_BITS upwards. This indicates that
  // one of the ARC proprietary auxiliary addresses may be accessed, but
  // that is not guaranteed until the address itself is further decoded.
  // If this signal is not asserted, then either the auxiliary address
  // is undefined, or else it is implemented by EIA.
  //
  x2_arc_range      = ~(|(x2_aux_addr_r[`npuarc_DATA_MSB:`npuarc_AUX_REG_BITS]));

  x2_arc_addr_r     = x2_aux_addr_r[`npuarc_AUX_REG_RANGE];
    
  x3_arc_unimpl_nxt = (~x2_arc_range) & x2_aux_op
                    & (~x2_ccaux_region[`npuarc_CCAUX_GAUX_IDX])
                    ;

  x3_unimpl_cg0     = (x3_addr_cg0  & x3_arc_unimpl_nxt)
                    | (x3_enable    & x3_arc_unimpl_r);

end // aux_range_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Auxiliary address pipeline, containing the most recently accessed        //
// address offset at each stage from X2 thru CA. These addresses are        //
// updated when a new LR, SR or AEX operation arrives at each stage,        //
// but they retain their values at all other times. This is acceptable      //
// because the address decoders are also gated with *_lr_op or *_sr_op_r    //
// and those ucode bits are asserted only when a valid LR, SR or AEX        //
// operation is present in each stage.                                      //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @ ( posedge clk  or posedge rst_a )
begin : x3_aux_addr_PROC
  if ( rst_a == 1'b1 ) begin
    x3_aux_addr_r   <= `npuarc_DATA_SIZE'd0;
    end
  else if (x3_addr_cg0 == 1'b1) begin
    x3_aux_addr_r   <= x2_aux_addr_r;
    end
end // block: aux_addr_PROC

always @ (posedge clk  or posedge rst_a)
begin : ca_aux_addr_PROC
  if (rst_a == 1'b1) begin
    ca_aux_addr_r   <= `npuarc_DATA_SIZE'd0;
  end
  else if (ca_addr_cg0 == 1'b1) begin
    ca_aux_addr_r   <= x3_aux_addr_r;
  end
end // block: aux_addr_PROC

always @ (posedge clk  or posedge rst_a)
begin : wa_aux_addr_PROC
  if (rst_a == 1'b1) begin
    wa_aux_addr_r   <= `npuarc_DATA_SIZE'd0;
  end
  else if (wa_addr_cg0 == 1'b1) begin
    wa_aux_addr_r   <= ca_aux_addr_r;
  end
end // block: aux_addr_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Auxiliary ARC Range Unimplemented                                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @ ( posedge clk  or posedge rst_a )
begin : aux_unimpl_PROC
  if ( rst_a == 1'b1 ) begin
    x3_arc_unimpl_r <= 1'b0;
  end
  else if (x3_unimpl_cg0 == 1'b1) begin
    x3_arc_unimpl_r <= (x3_arc_unimpl_nxt & x2_pass);
  end
end // block:  aux_unimpl_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// CORE Auxiliary Registers                                                 //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
wire                        aux_ca_illegal_nxt;
wire                        aux_ca_k_rd_nxt;
wire                        aux_ca_k_wr_nxt;
wire                        aux_ca_unimpl_nxt;
wire                        aux_ca_serial_sr_nxt;
wire                        aux_ca_strict_sr_nxt;

reg                         aux_ca_serial_sr_r;   //  (CA) SR group flush pipe
reg                         aux_ca_strict_sr_r;   //  (CA) SR flush pipe

always @ (posedge clk or posedge rst_a)
begin : aux_perm_PROC
  if ( rst_a == 1'b1 ) begin
    aux_ca_serial_sr_r <= 1'b0;
    aux_ca_strict_sr_r <= 1'b0;
  end
  else if (ca_addr_cg0) begin
    aux_ca_serial_sr_r <= (x3_pass & aux_ca_serial_sr_nxt & (~fch_restart));
    aux_ca_strict_sr_r <= (x3_pass & aux_ca_strict_sr_nxt & (~fch_restart));
  end
end // block: aux_perm_PROC

assign  aux_ca_serial_sr  = ca_sr_op_r & aux_ca_serial_sr_r;
assign  aux_ca_strict_sr  = ca_sr_op_r & aux_ca_strict_sr_r;

assign aux_ca_illegal_nxt = core_aux_illegal
                          | bcr_aux_illegal
                          | dc_aux_illegal
                          | eia_aux_illegal
                          | ccaux_illegal_r
                          | dccm_aux_illegal
                          | dper_aux_illegal
                          | ic_aux_illegal
                          | bpu_aux_illegal
                          | rtc_aux_illegal
                          | tm0_aux_illegal
                          | wdt_aux_illegal
                          | irq_aux_illegal
                          | mmu_aux_illegal
                          | mpu_aux_illegal
                          | aps_aux_illegal
                          | pct_aux_illegal
                          | (smt_aux_illegal
                          )
                          | rtt_aux_illegal
                          ;

assign aux_ca_k_rd_nxt    = core_aux_k_rd
                          | bcr_aux_k_rd
                          | dc_aux_k_rd
                          | eia_aux_k_rd
                          | ccaux_k_rd_r
                          | dccm_aux_k_rd
                          | dper_aux_k_rd
                          | ic_aux_k_rd
                          | bpu_aux_k_rd
                          | rtc_aux_k_rd
                          | wdt_aux_k_rd
                          | tm0_aux_k_rd
                          | irq_aux_k_rd
                          | mmu_aux_k_rd
                          | mpu_aux_k_rd
                          | aps_aux_k_rd
                          | pct_aux_k_rd
                          | (smt_aux_k_rd
                          )
                          | rtt_aux_k_rd
                          ;

assign aux_ca_k_wr_nxt    = core_aux_k_wr
                          | dc_aux_k_wr
                          | eia_aux_k_wr
                          | ccaux_k_wr_r
                          | dccm_aux_k_wr
                          | dper_aux_k_wr
                          | ic_aux_k_wr
                          | bpu_aux_k_wr
                          | rtc_aux_k_wr
                          | wdt_aux_k_wr
                          | tm0_aux_k_wr
                          | irq_aux_k_wr
                          | mmu_aux_k_wr
                          | mpu_aux_k_wr
                          | aps_aux_k_wr
                          | pct_aux_k_wr
                          | (smt_aux_k_wr
                          )
                          | rtt_aux_k_wr
                          ;

//==========================================================================
//
// Only on Aux
//
assign aux_ca_unimpl_nxt  = x3_aux_op
                          & core_aux_unimpl
                          & (~aux_bcr_ren_r)
                          & dc_aux_unimpl
                          & eia_aux_unimpl
                          & (!ccaux_resp_r | ccaux_status_r[`npuarc_CCAUX_UNIMPL_BIT])
                          & dccm_aux_unimpl
                          & dper_aux_unimpl
                          & ic_aux_unimpl
                          & bpu_aux_unimpl
                          & rtc_aux_unimpl
                          & wdt_aux_unimpl
                          & tm0_aux_unimpl
                          & irq_aux_unimpl
                          & mmu_aux_unimpl
                          & mpu_aux_unimpl
                          & aps_aux_unimpl
                          & pct_aux_unimpl
                          & (smt_aux_unimpl
                          )
                          & rtt_aux_unimpl
                          ;

assign aux_ca_serial_sr_nxt = core_aux_serial_sr
                          | dc_aux_serial_sr
                          | eia_aux_serial_sr
                          | ccaux_serial_sr_r
                          | dccm_aux_serial_sr
                          | dper_aux_serial_sr
                          | ic_aux_serial_sr
                          | bpu_aux_serial_sr
                          | rtc_aux_serial_sr
                          | wdt_aux_serial_sr
                          | tm0_aux_serial_sr
                          | irq_aux_serial_sr
                          | mmu_aux_serial_sr
                          | mpu_aux_serial_sr
                          | aps_aux_serial_sr
                          | pct_aux_serial_sr
                          | (smt_aux_serial_sr
                          )
                          | rtt_aux_serial_sr
                          ;

assign aux_ca_strict_sr_nxt = core_aux_strict_sr
                          | dc_aux_strict_sr
                          | eia_aux_strict_sr
                          | ccaux_strict_sr_r
                          | dper_aux_strict_sr
                          | dccm_aux_strict_sr
                          | ic_aux_strict_sr
                          | bpu_aux_strict_sr
                          | rtc_aux_strict_sr
                          | wdt_aux_strict_sr
                          | irq_aux_strict_sr
                          | mmu_aux_strict_sr
                          | mpu_aux_strict_sr
                          | aps_aux_strict_sr
                          | pct_aux_strict_sr
                          | (smt_aux_strict_sr
                          )
                          | rtt_aux_strict_sr
                          ;

reg  [`npuarc_DATA_RANGE] core_aux_rdata_r;       //
reg  [`npuarc_DATA_RANGE] bcr_aux_rdata_r;        //
reg  [`npuarc_DATA_RANGE] dc_aux_rdata_r;         //
reg  [`npuarc_DATA_RANGE] eia_aux_rdata_r;        //
reg  [`npuarc_DATA_RANGE] ic_aux_rdata_r;         //
reg  [`npuarc_DATA_RANGE] bpu_aux_rdata_r;        //
reg  [`npuarc_DATA_RANGE] smt_aux_rdata_r;        //
reg  [`npuarc_DATA_RANGE] rtt_aux_rdata_r;        //
reg  [`npuarc_DATA_RANGE] tm0_aux_rdata_r;        //
reg  [`npuarc_DATA_RANGE] irq_aux_rdata_r;        //
reg  [`npuarc_DATA_RANGE] rtc_aux_rdata_r;        //
reg  [`npuarc_DATA_RANGE] wdt_aux_rdata_r;        //
reg  [`npuarc_DATA_RANGE] pct_aux_rdata_r;        //
reg  [`npuarc_DATA_RANGE] mpu_aux_rdata_r;        //
reg  [`npuarc_DATA_RANGE] mmu_aux_rdata_r;        //
reg  [`npuarc_DATA_RANGE] dccm_aux_rdata_r;       //
reg  [`npuarc_DATA_RANGE] dper_aux_rdata_r;       //
reg  [`npuarc_DATA_RANGE] aps_aux_rdata_r;        //

//==========================================================================
// aux_ca_lr_data is the OR-merge of all CA-stage LR data
// registers from each client. The resulting value is
// currently registered at WA, but may possibly be incorporated
// into the CA result directly.
//
assign aux_ca_lr_data     = core_aux_rdata_r
                          | bcr_aux_rdata_r
                          | dc_aux_rdata_r
                          | eia_aux_rdata_r
                          | ccaux_aux_rdata_r
                          | dccm_aux_rdata_r
                          | dper_aux_rdata_r
                          | ic_aux_rdata_r
                          | bpu_aux_rdata_r
                          | tm0_aux_rdata_r
                          | rtc_aux_rdata_r
                          | wdt_aux_rdata_r
                          | irq_aux_rdata_r
                          | mmu_aux_rdata_r
                          | mpu_aux_rdata_r
                          | aps_aux_rdata_r
                          | pct_aux_rdata_r
                          | smt_aux_rdata_r
                          | rtt_aux_rdata_r
                          ;


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @x3_aux_permissions_PROC: Combinatorial process to derive AUX. register  //
// permissions to pass back to the Exception Pipeline.                      //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: x3_aux_permissions_PROC

  // These are used directly by exceptions logic
  //

  x3_aux_unimpl_r        = aux_ca_unimpl_nxt
                         | (  x3_arc_unimpl_r
                            & eia_aux_unimpl
                           )
                         ;

  x3_aux_illegal_r       = aux_ca_illegal_nxt
                         ;

  x3_aux_k_ro_r          = aux_ca_k_rd_nxt
                         ;

  x3_aux_k_wr_r          = aux_ca_k_wr_nxt
                         ;

end // block: x3_aux_permissions_PROC


//////////////////////////////////////////////////////////////////////////////
// Core Auxiliary Register Control Pipeline                                 //
//////////////////////////////////////////////////////////////////////////////
wire                      aux_core_x3_cg0;     // Core X3-stage reg enable
wire                      aux_core_ca_cg0;     // Core CA-stage reg enable
wire                      aux_core_wa_cg0;     // Core WA-stage reg enable

wire                      aux_core_ren_nxt;    // Core region select at X2
wire                      aux_cr1_ren_nxt;     // Core region 1 select at X2
wire                      aux_cr2_ren_nxt;     // Core region 2 select at X2
wire                      aux_cr3_ren_nxt;     // Core region 3 select at X2
wire                      aux_cr4_ren_nxt;     // Core region 4 select at X2
wire                      aux_cr5_ren_nxt;     // Core region 5 select at X2

reg                       core_ca_ren_r;       // Core region active at CA

reg                       core_region_1;       // aux range: 000-00F
reg                       core_region_2;       // aux range: {01F, 025, 03F, 043}
reg                       core_region_3;       // aux range: 260-267
reg                       core_region_4;       // aux range: 290-298
reg                       core_region_5;       // aux range: 400-404, 405, 412

reg                       core_addr_match;     // X2 addr is in core region

always @*
begin : core_match_PROC

  //==========================================================================
  // match with baseline core aux registers in region 000-00F
  //
  core_region_1 = ~(|x2_arc_addr_r[`npuarc_AUX_REG_MSB:4]);

  //==========================================================================
  // Detect a match with core registers in isolated address locations
  //
  core_region_2 = (x2_arc_addr_r == `npuarc_INTVBASE_AUX)
                | (x2_arc_addr_r == `npuarc_ECC_CTRL_AUX)
                | (x2_arc_addr_r == `npuarc_ECC_SBE_COUNT_AUX)
                | (x2_arc_addr_r == `npuarc_IRQ_ACT_AUX)
                ;

  //==========================================================================
  // Detect a match with all Stack-checking auxiliary register addresses
  //
  core_region_3 = ({x2_arc_addr_r[`npuarc_AUX_REG_MSB:3], 3'b000} == `npuarc_USTACK_TOP_AUX);

  //==========================================================================
  // Detect a match with all code-density auxiliary register addresses
  //
  core_region_4 = ({x2_arc_addr_r[`npuarc_AUX_REG_MSB:4],  4'b00} == `npuarc_JLI_BASE_AUX);

  aux_x2_r4_sr  = x2_arc_range & core_region_4 & x2_sr_op_r;

  //==========================================================================
  // Detect a match with exception aux registers
  //  (a). 0x400-0x403
  //  (b). 0x405
  //  (b.1). 0x411
  //  (c). 0x412
  //
  core_region_5 = ({x2_arc_addr_r[`npuarc_AUX_REG_MSB:2],  2'b00} == `npuarc_ERET_AUX) // (a)
                | (x2_arc_addr_r == `npuarc_EFA_AUX)                            // (b)
                | (x2_arc_addr_r == `npuarc_EFAE_AUX)                           // (b.1)
                | (x2_arc_addr_r == `npuarc_BTA_AUX)                            // (c)
                ;

  //==========================================================================
  // Detect an auxiliary address match with any core auxiliary register
  //
  core_addr_match = core_region_1 | core_region_2 | core_region_5
                  | core_region_3
                  | core_region_4
                  ;

end // block: core_match_PROC

assign  aux_core_x3_cg0   = (x3_addr_cg0  & aux_core_ren_nxt)
                          | (x3_enable    & aux_core_ren_r);

assign  aux_core_ca_cg0   = (ca_addr_cg0)
                          | (ca_enable    & core_ca_ren_r);

assign  aux_core_wa_cg0   = (wa_addr_cg0  & core_ca_ren_r)
                          | (wa_enable    & aux_core_wen_r);

assign  aux_core_ren_nxt  = x2_aux_op
                          & x2_arc_range
                          & core_addr_match;

assign  aux_cr1_ren_nxt   = x2_aux_op
                          & x2_arc_range
                          & core_region_1;

assign  aux_cr2_ren_nxt   = x2_aux_op
                          & x2_arc_range
                          & core_region_2;

assign  aux_cr3_ren_nxt   = x2_aux_op
                          & x2_arc_range
                          & core_region_3;

assign  aux_cr4_ren_nxt   = x2_aux_op
                          & x2_arc_range
                          & core_region_4;

assign  aux_cr5_ren_nxt   = x2_aux_op
                          & x2_arc_range
                          & core_region_5;

assign  aux_core_raddr_r  = x3_aux_addr_r[10:0];
assign  aux_core_waddr_r  = wa_aux_addr_r[10:0];

always @ (posedge clk or posedge rst_a)
begin : core_raux_PROC
  if (rst_a == 1'b1) begin
    aux_core_ren_r     <= 1'b0;
    aux_cr1_ren_r      <= 1'b0;
    aux_cr2_ren_r      <= 1'b0;
    aux_cr3_ren_r      <= 1'b0;
    aux_cr4_ren_r      <= 1'b0;
    aux_cr5_ren_r      <= 1'b0;
    aux_x3_r4_sr_r     <= 1'b0;
  end
  else if (x3_aux_cg1 && aux_core_x3_cg0) begin
    aux_core_ren_r     <= (aux_core_ren_nxt & x2_pass);
    aux_cr1_ren_r      <= (aux_cr1_ren_nxt  & x2_pass);
    aux_cr2_ren_r      <= (aux_cr2_ren_nxt  & x2_pass);
    aux_cr3_ren_r      <= (aux_cr3_ren_nxt  & x2_pass);
    aux_cr4_ren_r      <= (aux_cr4_ren_nxt  & x2_pass);
    aux_cr5_ren_r      <= (aux_cr5_ren_nxt  & x2_pass);
    aux_x3_r4_sr_r     <= (aux_x2_r4_sr & x2_pass);
  end
end // block: core_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : core_rdata_reg_PROC
  if ( rst_a == 1'b1 ) begin
    core_aux_rdata_r   <= {`npuarc_DATA_SIZE{1'b0}};
    core_ca_ren_r      <= 1'b0;
    aux_ca_r4_sr_r     <= 1'b0;
  end
  else if (ca_aux_cg1 && aux_core_ca_cg0) begin
    core_aux_rdata_r   <= (aux_core_ren_r & x3_lr_op_r)
                       ? core_aux_rdata
                       : `npuarc_DATA_SIZE'd0;

    core_ca_ren_r      <= (aux_core_ren_r & x3_pass);
    aux_ca_r4_sr_r     <= (aux_x3_r4_sr_r & x3_pass);
  end
end // block: core_rdata_reg_PROC

always @ (posedge clk or posedge rst_a)
begin : core_waux_PROC
  if (rst_a == 1'b1) begin
    aux_core_wen_r     <= 1'b0;
  end
  else if (wa_aux_cg1 && aux_core_wa_cg0) begin
    aux_core_wen_r     <= (core_ca_ren_r & ca_sr_op_r & ca_pass & ca_aux_cond);
  end
end // block: core_waux_PROC


//////////////////////////////////////////////////////////////////////////////
// SmaRT Auxiliary Control Pipeline                                         //
//////////////////////////////////////////////////////////////////////////////
wire                      aux_smt_x3_cg0;     // SmaRT X3-stage reg enable
wire                      aux_smt_ca_cg0;     // SmaRT CA-stage reg enable
wire                      aux_smt_wa_cg0;     // SmaRT WA-stage reg enable

wire                      aux_smt_ren_nxt;    // SmaRT region select at X2
wire                      aux_smt_raddr_nxt;  // SmaRT read addr offset
wire                      aux_smt_waddr_nxt;  // SmaRT write addr offset

reg                       smt_ca_ren_r;       // SmaRT region active at CA

assign  aux_smt_x3_cg0    = (x3_addr_cg0  & aux_smt_ren_nxt)
                          | (x3_enable    & aux_smt_ren_r);

assign  aux_smt_ca_cg0    = (ca_addr_cg0)
                          | (ca_enable    & smt_ca_ren_r);

assign  aux_smt_wa_cg0    = (wa_addr_cg0  & smt_ca_ren_r)
                          | (wa_enable    & aux_smt_wen_r);

assign  aux_smt_ren_nxt   = x2_aux_op
                          & x2_arc_range
                          & (    ( x2_arc_addr_r == `npuarc_SRT_CTRL_AUX )
                              || ( x2_arc_addr_r == `npuarc_SRT_DATA_AUX ));

assign  aux_smt_raddr_nxt =  x2_arc_addr_r[0];
assign  aux_smt_waddr_nxt =  ca_aux_addr_r[0];

always @ (posedge clk or posedge rst_a)
begin : smt_raux_PROC
  if (rst_a == 1'b1) begin
    aux_smt_ren_r     <= 1'b0;
    aux_smt_raddr_r   <= 1'b0;
  end
  else if (x3_aux_cg1 && aux_smt_x3_cg0) begin
    aux_smt_ren_r     <= (aux_smt_ren_nxt & x2_pass);
    aux_smt_raddr_r   <= aux_smt_raddr_nxt;
  end
end // block: smt_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : smt_rdata_PROC
  if ( rst_a == 1'b1 ) begin
    smt_aux_rdata_r   <= {`npuarc_DATA_SIZE{1'b0}};
    smt_ca_ren_r      <= 1'b0;
  end
  else if (ca_aux_cg1 && aux_smt_ca_cg0) begin
    smt_aux_rdata_r   <= (aux_smt_ren_r & x3_lr_op_r
                         )
                       ? smt_aux_rdata
                       : `npuarc_DATA_SIZE'd0;

    smt_ca_ren_r      <= aux_smt_ren_r & x3_pass;
  end
end // block: smt_rdata_PROC

always @ (posedge clk or posedge rst_a)
begin : smt_waux_PROC
  if (rst_a == 1'b1) begin
    aux_smt_wen_r     <= 1'b0;
    aux_smt_waddr_r   <= 1'b0;
  end
  else if (wa_aux_cg1 && aux_smt_wa_cg0) begin
    aux_smt_wen_r     <= (smt_ca_ren_r & ca_sr_op_r & ca_pass & ca_aux_cond);
    aux_smt_waddr_r   <= aux_smt_waddr_nxt;
  end
end // block: smt_waux_PROC

assign  aux_smt_active = aux_smt_ren_r // X3
                       | smt_ca_ren_r  // CA
                       | aux_smt_wen_r // WA
                       ;

//////////////////////////////////////////////////////////////////////////////
// RTT Auxiliary Control Pipeline                                           //
//////////////////////////////////////////////////////////////////////////////
wire                      aux_rtt_x3_cg0;     // RTT X3-stage reg enable
wire                      aux_rtt_ca_cg0;     // RTT CA-stage reg enable
wire                      aux_rtt_wa_cg0;     // RTT WA-stage reg enable

wire                      aux_rtt_ren_nxt;    // RTT region select at X2
wire [3:0]                aux_rtt_raddr_nxt;  // RTT read addr offset
wire [3:0]                aux_rtt_waddr_nxt;  // RTT write addr offset

reg                       rtt_ca_ren_r;       // RTT region active at CA


assign  aux_rtt_x3_cg0    = (x3_addr_cg0  & aux_rtt_ren_nxt)
                          | (x3_enable    & aux_rtt_ren_r);

assign  aux_rtt_ca_cg0    = (ca_addr_cg0)
                          | (ca_enable    & rtt_ca_ren_r);

assign  aux_rtt_wa_cg0    = (wa_addr_cg0  & rtt_ca_ren_r)
                          | (wa_enable    & aux_rtt_wen_r);

assign  aux_rtt_ren_nxt   = x2_aux_op
                          & x2_arc_range
                          & (    ( x2_arc_addr_r == `npuarc_RTT_CTRL_AUX )
                              || ( x2_arc_addr_r == `npuarc_RTT_ADDR_AUX )
                              || ( x2_arc_addr_r == `npuarc_RTT_DATA_AUX )
                              || ( x2_arc_addr_r == `npuarc_RTT_SWE0_AUX  )
                              || ( x2_arc_addr_r == `npuarc_RTT_SWE1_AUX  )
                             );

assign  aux_rtt_raddr_nxt =  x2_arc_addr_r[3:0];
assign  aux_rtt_waddr_nxt =  ca_aux_addr_r[3:0];
assign  wa_aux_rtt_addr_r =  wa_aux_addr_r[`npuarc_AUX_REG_RANGE];

always @ (posedge clk or posedge rst_a)
begin : rtt_raux_PROC
  if (rst_a == 1'b1) begin
    aux_rtt_ren_r     <= 1'b0;
    aux_rtt_raddr_r   <= 4'b0;
  end
  else if (x3_aux_cg1 && aux_rtt_x3_cg0) begin
    aux_rtt_ren_r     <= (aux_rtt_ren_nxt & x2_pass);
    aux_rtt_raddr_r   <= aux_rtt_raddr_nxt;
  end
end // block: rtt_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : rtt_rdata_PROC
  if ( rst_a == 1'b1 ) begin
    rtt_aux_rdata_r   <= {`npuarc_DATA_SIZE{1'b0}};
    rtt_ca_ren_r      <= 1'b0;
  end
  else if (ca_aux_cg1 && aux_rtt_ca_cg0) begin
    rtt_aux_rdata_r   <= (aux_rtt_ren_r & x3_lr_op_r)
                       ? rtt_aux_rdata
                       : `npuarc_DATA_SIZE'd0;

    rtt_ca_ren_r      <= aux_rtt_ren_r & x3_pass;
  end
end // block: rtt_rdata_PROC

always @ (posedge clk or posedge rst_a)
begin : rtt_waux_PROC
  if (rst_a == 1'b1) begin
    aux_rtt_wen_r     <= 1'b0;
    aux_rtt_waddr_r   <= 4'b0;
  end
  else if (wa_aux_cg1 && aux_rtt_wa_cg0) begin
    aux_rtt_wen_r     <= (rtt_ca_ren_r & ca_sr_op_r & ca_pass & ca_aux_cond);
    aux_rtt_waddr_r   <= aux_rtt_waddr_nxt;
  end
end // block: rtt_waux_PROC

assign  aux_rtt_active = aux_rtt_ren_r // X3
                       | rtt_ca_ren_r  // CA
                       | aux_rtt_wen_r // WA
                       ;



//////////////////////////////////////////////////////////////////////////////
// Timer0 Auxiliary Control Pipeline                                        //
//////////////////////////////////////////////////////////////////////////////
wire                      aux_tm0_x3_cg0;     // Timer0 X3-stage reg enable
wire                      aux_tm0_ca_cg0;     // Timer0 CA-stage reg enable
wire                      aux_tm0_wa_cg0;     // Timer0 WA-stage reg enable

wire                      aux_tm0_ren_nxt;    // Timer0 region select at X2
wire [1:0]                aux_tm0_raddr_nxt;  // Timer0 read addr offset
wire [1:0]                aux_tm0_waddr_nxt;  // Timer0 write addr offset

reg                       tm0_ca_ren_r;       // Timer0 region active at CA

assign  aux_tm0_x3_cg0    = (x3_addr_cg0  & aux_tm0_ren_nxt)
                          | (x3_enable    & aux_tm0_ren_r);

assign  aux_tm0_ca_cg0    = (ca_addr_cg0)
                          | (ca_enable    & tm0_ca_ren_r);

assign  aux_tm0_wa_cg0    = (wa_addr_cg0  & tm0_ca_ren_r)
                          | (wa_enable    & aux_tm0_wen_r);

assign  aux_tm0_ren_nxt   = x2_aux_op
                          & x2_arc_range
                          & (    ( x2_arc_addr_r >= `npuarc_COUNT0_AUX )
                              && ( x2_arc_addr_r <= `npuarc_LIMIT0_AUX ));

assign  aux_tm0_raddr_nxt =  x2_arc_addr_r[1:0];
assign  aux_tm0_waddr_nxt =  ca_aux_addr_r[1:0];

always @ (posedge clk or posedge rst_a)
begin : tm0_raux_PROC
  if (rst_a == 1'b1) begin
    aux_tm0_ren_r     <= 1'b0;
    aux_tm0_raddr_r   <= 2'b00;
  end
  else if (x3_aux_cg1 && aux_tm0_x3_cg0) begin
    aux_tm0_ren_r     <= (aux_tm0_ren_nxt & x2_pass);
    aux_tm0_raddr_r   <= aux_tm0_raddr_nxt;
  end
end // block: tm0_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : tm0_rdata_PROC
  if ( rst_a == 1'b1 ) begin
    tm0_aux_rdata_r   <= {`npuarc_DATA_SIZE{1'b0}};
    tm0_ca_ren_r      <= 1'b0;
  end
  else if (ca_aux_cg1 && aux_tm0_ca_cg0) begin
    tm0_aux_rdata_r   <= (aux_tm0_ren_r & x3_lr_op_r)
                       ? tm0_aux_rdata
                       : `npuarc_DATA_SIZE'd0;

    tm0_ca_ren_r      <= aux_tm0_ren_r & x3_pass;
  end
end // block: tm0_rdata_PROC

always @ (posedge clk or posedge rst_a)
begin : tm0_waux_PROC
  if (rst_a == 1'b1) begin
    aux_tm0_wen_r     <= 1'b0;
    aux_tm0_waddr_r   <= 2'b00;
  end
  else if (wa_aux_cg1 && aux_tm0_wa_cg0) begin
    aux_tm0_wen_r     <= (tm0_ca_ren_r & ca_sr_op_r & ca_pass & ca_aux_cond);
    aux_tm0_waddr_r   <= aux_tm0_waddr_nxt;
  end
end // block: tm0_waux_PROC

assign aux_timer_active = 1'b0
                        | aux_tm0_ren_r // X3
                        | tm0_ca_ren_r  // CA
                        | aux_tm0_wen_r // WA
                        ;

//////////////////////////////////////////////////////////////////////////////
// RTC Auxiliary Control Pipeline                                           //
//////////////////////////////////////////////////////////////////////////////
wire                      aux_rtc_x3_cg0;     // RTC X3-stage reg enable
wire                      aux_rtc_ca_cg0;     // RTC CA-stage reg enable
wire                      aux_rtc_wa_cg0;     // RTC WA-stage reg enable

wire                      aux_rtc_ren_nxt;    // RTC region select at X2
wire [2:0]                aux_rtc_raddr_nxt;  // RTC read addr offset
wire [2:0]                aux_rtc_waddr_nxt;  // RTC write addr offset

reg                       rtc_ca_ren_r;       // RTC region active at CA

assign  aux_rtc_x3_cg0    = (x3_addr_cg0  & aux_rtc_ren_nxt)
                          | (x3_enable    & aux_rtc_ren_r);

assign          aux_rtc_ca_cg0    = (ca_addr_cg0)
                          | (ca_enable    & rtc_ca_ren_r);

assign          aux_rtc_wa_cg0    = (wa_addr_cg0  & rtc_ca_ren_r)
                          | (wa_enable    & aux_rtc_wen_r);

assign  aux_rtc_ren_nxt   = x2_aux_op
                          & x2_arc_range
                          & (    ( x2_arc_addr_r >= `npuarc_RTC_CTRL_AUX )
                              && ( x2_arc_addr_r <= `npuarc_RTC_HIGH_AUX ));

assign  aux_rtc_raddr_nxt =  x2_arc_addr_r[2:0];
assign  aux_rtc_waddr_nxt =  ca_aux_addr_r[2:0];

always @ (posedge clk or posedge rst_a)
begin : rtc_raux_PROC
  if (rst_a == 1'b1) begin
    aux_rtc_ren_r     <= 1'b0;
    aux_rtc_raddr_r   <= 3'b000;
  end
  else if (x3_aux_cg1 && aux_rtc_x3_cg0) begin
    aux_rtc_ren_r     <= (aux_rtc_ren_nxt & x2_pass);
    aux_rtc_raddr_r   <= aux_rtc_raddr_nxt;
  end
end // block: rtc_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : rtc_rdata_PROC
  if ( rst_a == 1'b1 ) begin
    rtc_aux_rdata_r   <= {`npuarc_DATA_SIZE{1'b0}};
    rtc_ca_ren_r      <= 1'b0;
  end
  else if (ca_aux_cg1 && aux_rtc_ca_cg0) begin
    rtc_aux_rdata_r   <= (aux_rtc_ren_r & x3_lr_op_r)
                       ? rtc_aux_rdata
                       : `npuarc_DATA_SIZE'd0;

    rtc_ca_ren_r      <= aux_rtc_ren_r & x3_pass;
  end
end // block: rtc_rdata_PROC

always @ (posedge clk or posedge rst_a)
begin : rtc_waux_PROC
  if (rst_a == 1'b1) begin
    aux_rtc_wen_r     <= 1'b0;
    aux_rtc_waddr_r   <= 3'b000;
  end
  else if (wa_aux_cg1 && aux_rtc_wa_cg0) begin
    aux_rtc_wen_r     <= (rtc_ca_ren_r & ca_sr_op_r & ca_pass & ca_aux_cond);
    aux_rtc_waddr_r   <= aux_rtc_waddr_nxt;
  end
end // block: rtc_waux_PROC






//////////////////////////////////////////////////////////////////////////////
// WDT Auxiliary Control Pipeline                                           //
//////////////////////////////////////////////////////////////////////////////
wire                      aux_wdt_x3_cg0;     // wdt X3-stage reg enable
wire                      aux_wdt_ca_cg0;     // wdt CA-stage reg enable
wire                      aux_wdt_wa_cg0;     // wdt WA-stage reg enable

wire                      aux_wdt_ren_nxt;    // wdt region select at X2
wire [3:0]                aux_wdt_raddr_nxt;  // wdt read addr offset
wire [3:0]                aux_wdt_waddr_nxt;  // wdt write addr offset

wire                      aux_wdt_raw;        // RAW hazard on wdt

reg                       wdt_ca_ren_r;       // wdt region active at CA

reg                       wdt_wa_ren_r;       // wdt region active at WA

assign  aux_wdt_x3_cg0    = (x3_addr_cg0  & aux_wdt_ren_nxt)
                          | (x3_enable    & aux_wdt_ren_r);

assign  aux_wdt_ca_cg0    = (ca_addr_cg0)
                          | (ca_enable    & wdt_ca_ren_r);

assign  aux_wdt_wa_cg0    = (wa_addr_cg0  & wdt_ca_ren_r)
                          | (wa_enable    & aux_wdt_wen_r);

assign  aux_wdt_ren_nxt   = x2_aux_op
                          & x2_arc_range
                          & (    ( x2_arc_addr_r >= `npuarc_WDT_PASSWORD_REG)
                              && ( x2_arc_addr_r <= `npuarc_WDT_PASSWD_STS_REG));

assign  aux_wdt_raddr_nxt =  x2_arc_addr_r[3:0];
assign  aux_wdt_waddr_nxt =  ca_aux_addr_r[3:0];

assign  aux_wdt_raw       = (aux_wdt_ren_r & x3_lr_op_r)
                          & (   (wdt_ca_ren_r & ca_sr_op_r)
                              | (wdt_wa_ren_r & wa_sr_op_r)
                            )
                          ;

always @ (posedge clk or posedge rst_a)
begin : wdt_raux_PROC
  if (rst_a == 1'b1) begin
    aux_wdt_ren_r     <= 1'b0;
    aux_wdt_raddr_r   <= 4'b000;
  end
  else if (x3_aux_cg1 && aux_wdt_x3_cg0) begin
    aux_wdt_ren_r     <= (aux_wdt_ren_nxt & x2_pass);
    aux_wdt_raddr_r   <= aux_wdt_raddr_nxt;
  end
end // block: wdt_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : wdt_rdata_PROC
  if ( rst_a == 1'b1 ) begin
    wdt_aux_rdata_r   <= {`npuarc_DATA_SIZE{1'b0}};
    wdt_ca_ren_r      <= 1'b0;
  end
  else if (ca_aux_cg1 && aux_wdt_ca_cg0) begin
    wdt_aux_rdata_r   <= (aux_wdt_ren_r & x3_lr_op_r)
                       ? wdt_aux_rdata
                       : `npuarc_DATA_SIZE'd0;

    wdt_ca_ren_r      <= aux_wdt_ren_r & x3_pass;
  end
end // block: wdt_rdata_PROC

always @ (posedge clk or posedge rst_a)
begin : wdt_waux_PROC
  if (rst_a == 1'b1) begin
    aux_wdt_wen_r     <= 1'b0;
    aux_wdt_waddr_r   <= 4'b000;
    wdt_wa_ren_r      <= 1'b0;
  end
  else if (wa_aux_cg1 && aux_wdt_wa_cg0) begin
    aux_wdt_wen_r     <= (wdt_ca_ren_r & ca_sr_op_r & ca_pass & ca_aux_cond);
    aux_wdt_waddr_r   <= aux_wdt_waddr_nxt;
    wdt_wa_ren_r      <= wdt_ca_ren_r & ca_pass;
  end
end // block: wdt_waux_PROC


//////////////////////////////////////////////////////////////////////////////
// PCT Auxiliary Control Pipeline                                           //
//////////////////////////////////////////////////////////////////////////////
wire                      aux_pct_x3_cg0;     // PCT X3-stage reg enable
wire                      aux_pct_ca_cg0;     // PCT CA-stage reg enable
wire                      aux_pct_wa_cg0;     // PCT WA-stage reg enable

wire                      aux_pct_ren_nxt;    // PCT region select at X2
wire [5:0]                aux_pct_raddr_nxt;  // PCT read addr offset
wire [5:0]                aux_pct_waddr_nxt;  // PCT write addr offset

reg                       pct_ca_ren_r;       // PCT region active at CA

assign  aux_pct_x3_cg0    = (x3_addr_cg0  & aux_pct_ren_nxt)
                          | (x3_enable    & aux_pct_ren_r);

assign  aux_pct_ca_cg0    = (ca_addr_cg0)
                          | (ca_enable    & pct_ca_ren_r);

assign  aux_pct_wa_cg0    = (wa_addr_cg0  & pct_ca_ren_r)
                          | (wa_enable    & aux_pct_wen_r);

assign  aux_pct_ren_nxt   = x2_aux_op
                          & x2_arc_range
                          & (    ( x2_arc_addr_r >= `npuarc_CC_INDEX_AUX )
                              && ( x2_arc_addr_r <= `npuarc_PCT_END_AUX ))
                          ;

assign  aux_pct_raddr_nxt = x2_arc_addr_r[5:0];
assign  aux_pct_waddr_nxt = ca_aux_addr_r[5:0];

always @ (posedge clk or posedge rst_a)
begin : pct_raux_PROC
  if (rst_a == 1'b1) begin
    aux_pct_ren_r     <= 1'b0;
    aux_pct_raddr_r   <= 6'h00;
  end
  else if (x3_aux_cg1 && aux_pct_x3_cg0) begin
    aux_pct_ren_r     <= (aux_pct_ren_nxt & x2_pass);
    aux_pct_raddr_r   <= aux_pct_raddr_nxt;
  end
end // block: pct_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : pct_rdata_PROC
  if ( rst_a == 1'b1 ) begin
    pct_aux_rdata_r   <= {`npuarc_DATA_SIZE{1'b0}};
    pct_ca_ren_r      <= 1'b0;
  end
  else if (ca_aux_cg1 && aux_pct_ca_cg0) begin
    pct_aux_rdata_r   <= (aux_pct_ren_r & x3_lr_op_r)
                       ? pct_aux_rdata
                       : `npuarc_DATA_SIZE'd0;

    pct_ca_ren_r      <= aux_pct_ren_r & x3_pass;
  end
end // block: pct_rdata_PROC

always @ (posedge clk or posedge rst_a)
begin : pct_waux_PROC
  if (rst_a == 1'b1) begin
    aux_pct_wen_r     <= 1'b0;
    aux_pct_waddr_r   <= 6'h00;
  end
  else if (wa_aux_cg1 && aux_pct_wa_cg0) begin
    aux_pct_wen_r     <= (pct_ca_ren_r & ca_sr_op_r & ca_pass & ca_aux_cond);
    aux_pct_waddr_r   <= aux_pct_waddr_nxt;
  end
end // block: pct_waux_PROC

assign aux_pct_active = aux_pct_ren_r
                      | pct_ca_ren_r
                      | aux_pct_wen_r
                      ;

//////////////////////////////////////////////////////////////////////////////
// MPU Auxiliary Control Pipeline                                           //
//////////////////////////////////////////////////////////////////////////////
wire                      aux_mpu_x3_cg0;     // MPU X3-stage reg enable
wire                      aux_mpu_ca_cg0;     // MPU CA-stage reg enable
wire                      aux_mpu_wa_cg0;     // MPU WA-stage reg enable

wire                      aux_mpu_ren_nxt;    // MPU region select at X2
wire [6:0]                aux_mpu_raddr_nxt;  // MPU read addr offset
wire [6:0]                aux_mpu_waddr_nxt;  // MPU write addr offset

reg                       mpu_ca_ren_r;       // MPU region active at CA

assign  aux_mpu_x3_cg0    = (x3_addr_cg0  & aux_mpu_ren_nxt)
                          | (x3_enable    & aux_mpu_ren_r);

assign  aux_mpu_ca_cg0    = (ca_addr_cg0)
                          | (ca_enable    & mpu_ca_ren_r);

assign  aux_mpu_wa_cg0    = (wa_addr_cg0  & mpu_ca_ren_r)
                          | (wa_enable    & aux_mpu_wen_r);

assign  aux_mpu_ren_nxt   = x2_aux_op
                          & x2_arc_range
                          & (    ( x2_arc_addr_r >= `npuarc_MPU_EN_AUX )
                              && ( x2_arc_addr_r <= `npuarc_MPU_RDP15_AUX ));

assign  aux_mpu_raddr_nxt = x2_arc_addr_r[6:0];
assign  aux_mpu_waddr_nxt = ca_aux_addr_r[6:0];

always @ (posedge clk or posedge rst_a)
begin : mpu_raux_PROC
  if (rst_a == 1'b1) begin
    aux_mpu_ren_r     <= 1'b0;
    aux_mpu_raddr_r   <= 7'h00;
  end
  else if (x3_aux_cg1 && aux_mpu_x3_cg0) begin
    aux_mpu_ren_r     <= (aux_mpu_ren_nxt & x2_pass);
    aux_mpu_raddr_r   <= aux_mpu_raddr_nxt;
  end
end // block: mpu_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : mpu_rdata_PROC
  if ( rst_a == 1'b1 ) begin
    mpu_aux_rdata_r   <= {`npuarc_DATA_SIZE{1'b0}};
    mpu_ca_ren_r      <= 1'b0;
  end
  else if (ca_aux_cg1 && aux_mpu_ca_cg0) begin
    mpu_aux_rdata_r   <= (aux_mpu_ren_r & x3_lr_op_r)
                       ? mpu_aux_rdata
                       : `npuarc_DATA_SIZE'd0;

    mpu_ca_ren_r      <= aux_mpu_ren_r & x3_pass;
  end
end // block: mpu_rdata_PROC

always @ (posedge clk or posedge rst_a)
begin : mpu_waux_PROC
  if (rst_a == 1'b1) begin
    aux_mpu_wen_r     <= 1'b0;
    aux_mpu_waddr_r   <= 7'h00;
  end
  else if (wa_aux_cg1 && aux_mpu_wa_cg0) begin
    aux_mpu_wen_r     <= (mpu_ca_ren_r & ca_sr_op_r & ca_pass & ca_aux_cond);
    aux_mpu_waddr_r   <= aux_mpu_waddr_nxt;
  end
end // block: mpu_waux_PROC



//////////////////////////////////////////////////////////////////////////////
// MMU Auxiliary Control Pipeline                                           //
//////////////////////////////////////////////////////////////////////////////
wire                      aux_mmu_x3_cg0;     // MMU X3-stage reg enable
wire                      aux_mmu_ca_cg0;     // MMU CA-stage reg enable
wire                      aux_mmu_wa_cg0;     // MMU WA-stage reg enable

wire                      aux_mmu_ren_nxt;    // MMU region select at X2
wire [4:0]                aux_mmu_raddr_nxt;  // MMU read addr offset
wire [4:0]                aux_mmu_waddr_nxt;  // MMU write addr offset

reg                       mmu_ca_ren_r;       // MMU region active at CA

assign  aux_mmu_x3_cg0    = (x3_addr_cg0  & aux_mmu_ren_nxt)
                          | (x3_enable    & aux_mmu_ren_r);

assign  aux_mmu_ca_cg0    = (ca_addr_cg0)
                          | (ca_enable    & mmu_ca_ren_r);

assign  aux_mmu_wa_cg0    = (wa_addr_cg0  & mmu_ca_ren_r)
                          | (wa_enable    & aux_mmu_wen_r);

assign  aux_mmu_ren_nxt   = x2_aux_op
                          & x2_arc_range
                          & (    ( x2_arc_addr_r >= `npuarc_TLBPD0_AUX )
                              && ( x2_arc_addr_r <= `npuarc_SCRATCH_DATA0_AUX ));

assign  aux_mmu_raddr_nxt = x2_arc_addr_r[4:0];
assign  aux_mmu_waddr_nxt = ca_aux_addr_r[4:0];

always @ (posedge clk or posedge rst_a)
begin : mmu_raux_PROC
  if (rst_a == 1'b1) begin
    aux_mmu_ren_r     <= 1'b0;
    aux_mmu_raddr_r   <= 5'h00;
  end
  else if (x3_aux_cg1 && aux_mmu_x3_cg0) begin
    aux_mmu_ren_r     <= (aux_mmu_ren_nxt & x2_pass);
    aux_mmu_raddr_r   <= aux_mmu_raddr_nxt;
  end
end // block: mmu_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : mmu_rdata_PROC
  if ( rst_a == 1'b1 ) begin
    mmu_aux_rdata_r   <= {`npuarc_DATA_SIZE{1'b0}};
    mmu_ca_ren_r      <= 1'b0;
  end
  else if (ca_aux_cg1 && aux_mmu_ca_cg0) begin
    mmu_aux_rdata_r   <= (aux_mmu_ren_r & x3_lr_op_r)
                       ? mmu_aux_rdata
                       : `npuarc_DATA_SIZE'd0;

    mmu_ca_ren_r      <= aux_mmu_ren_r & x3_pass;
  end
end // block: mmu_rdata_PROC

always @ (posedge clk or posedge rst_a)
begin : mmu_waux_PROC
  if (rst_a == 1'b1) begin
    aux_mmu_wen_r     <= 1'b0;
    aux_mmu_waddr_r   <= 5'h00;
  end
  else if (wa_aux_cg1 && aux_mmu_wa_cg0) begin
    aux_mmu_wen_r     <= (mmu_ca_ren_r & ca_sr_op_r & ca_pass & ca_aux_cond);
    aux_mmu_waddr_r   <= aux_mmu_waddr_nxt;
  end
end // block: mmu_waux_PROC


//////////////////////////////////////////////////////////////////////////////
// Interrupts Auxiliary Control Pipeline                                    //
//////////////////////////////////////////////////////////////////////////////
wire                      aux_irq_x3_cg0;     // Interrupts X3-stage reg enable
wire                      aux_irq_ca_cg0;     // Interrupts CA-stage reg enable
wire                      aux_irq_wa_cg0;     // Interrupts WA-stage reg enable

wire                      aux_irq_ren_nxt;    // Interrupts region select at X2
wire [`npuarc_AUX_REG_RANGE]     aux_irq_raddr_nxt;  // Interrupts read addr offset
wire [`npuarc_AUX_REG_RANGE]     aux_irq_waddr_nxt;  // Interrupts write addr offset

reg                       x3_irq_stall_cg0;    // 
reg                       x3_irq_stall_nxt;   // 
reg                       x3_irq_stall_r;     // 

reg                       irq_ca_ren_r;       // Interrupts region active at CA

assign  aux_irq_x3_cg0    = (x3_addr_cg0  & aux_irq_ren_nxt)
                          | (x3_enable    & aux_irq_ren_r);

assign  aux_irq_ca_cg0    = (ca_addr_cg0)
                          | (ca_enable    & irq_ca_ren_r);

assign  aux_irq_wa_cg0    = (wa_addr_cg0  & irq_ca_ren_r)
                          | (wa_enable    & aux_irq_wen_r);

assign  aux_irq_ren_nxt   = x2_aux_op
                          & x2_arc_range
                          & (   (x2_arc_addr_r[`npuarc_AUX_REG_MSB:3] == 9'h040)
                              ||(x2_arc_addr_r[`npuarc_AUX_REG_MSB:3] == 9'h081)
                              ||(x2_arc_addr_r[`npuarc_AUX_REG_MSB:3] == 9'h082)
                            )
                          ;

assign  aux_irq_raddr_nxt = x2_arc_addr_r;
assign  aux_irq_waddr_nxt = ca_aux_addr_r[`npuarc_AUX_REG_RANGE];

always @ (posedge clk or posedge rst_a)
begin : irq_raux_PROC
  if (rst_a == 1'b1) begin
    aux_irq_ren_r     <= 1'b0;
    aux_irq_raddr_r   <= `npuarc_AUX_REG_BITS'b0;
  end
  else if (x3_aux_cg1 && aux_irq_x3_cg0) begin
    aux_irq_ren_r     <= (aux_irq_ren_nxt & x2_pass);
    aux_irq_raddr_r   <= aux_irq_raddr_nxt;
  end
end // block: irq_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : irq_rdata_PROC
  if ( rst_a == 1'b1 ) begin
    irq_aux_rdata_r   <= {`npuarc_DATA_SIZE{1'b0}};
    irq_ca_ren_r      <= 1'b0;
  end
  else if (ca_aux_cg1 && aux_irq_ca_cg0) begin
    irq_aux_rdata_r   <= (aux_irq_ren_r & x3_lr_op_r)
                       ? irq_aux_rdata
                       : `npuarc_DATA_SIZE'd0;

    irq_ca_ren_r      <= aux_irq_ren_r & x3_pass;
  end
end // block: irq_rdata_PROC

always @ (posedge clk or posedge rst_a)
begin : irq_waux_PROC
  if (rst_a == 1'b1) begin
    aux_irq_wen_r     <= 1'b0;
    aux_irq_waddr_r   <= `npuarc_AUX_REG_BITS'b0;
  end
  else if (wa_aux_cg1 && aux_irq_wa_cg0) begin
    aux_irq_wen_r     <= (irq_ca_ren_r & ca_sr_op_r & ca_pass & ca_aux_cond);
    aux_irq_waddr_r   <= aux_irq_waddr_nxt;
  end
end // block: irq_waux_PROC

always @*
begin: x3_irq_stall_PROC

  x3_irq_stall_cg0  = x3_irq_stall_r
                    | x3_addr_cg0
                    | ca_addr_cg0
                    ;

  x3_irq_stall_nxt  = (   x2_rtie_op_r
                        & x2_pass
                        & ca_sr_op_r
                        & irq_ca_ren_r
                      )
                    | (   x2_rtie_op_r
                        & x2_pass
                        & x3_sr_op_r
                        & aux_irq_ren_r
                      )
                    | (   x3_rtie_op_r
                        & x3_pass
                        & ca_sr_op_r
                        & irq_ca_ren_r
                      )
                    ;

end // block: x3_irq_stall_PROC

always @ (posedge clk or posedge rst_a)
begin : x3_irq_stall_reg_PROC
  if (rst_a == 1'b1) begin
    x3_irq_stall_r     <= 1'b0;
  end
  else if (x3_irq_stall_cg0) begin
    x3_irq_stall_r     <= x3_irq_stall_nxt;
  end
end // block: x3_irq_stall_PROC


//////////////////////////////////////////////////////////////////////////////
// DCCM Auxiliary Control Pipeline                                          //
//////////////////////////////////////////////////////////////////////////////
wire                      aux_dccm_x3_cg0;    // DCCM X3-stage reg enable
wire                      aux_dccm_ca_cg0;    // DCCM CA-stage reg enable
wire                      aux_dccm_wa_cg0;    // DCCM WA-stage reg enable

wire                      aux_dccm_ren_nxt;   // DCCM region select at X2

reg                       dccm_ca_ren_r;      // DCCM region active at CA

assign  aux_dccm_x3_cg0   = (x3_addr_cg0  & aux_dccm_ren_nxt)
                          | (x3_enable    & aux_dccm_ren_r);

assign  aux_dccm_ca_cg0   = (ca_addr_cg0)
                          | (ca_enable    & dccm_ca_ren_r);

assign  aux_dccm_wa_cg0   = (wa_addr_cg0  & dccm_ca_ren_r)
                          | (wa_enable    & aux_dccm_wen_r);

assign  aux_dccm_ren_nxt  = x2_aux_op
                          & x2_arc_range
                          & ( x2_arc_addr_r == `npuarc_DCCM_AUX );

always @ (posedge clk or posedge rst_a)
begin : dccm_raux_PROC
  if (rst_a == 1'b1) begin
    aux_dccm_ren_r     <= 1'b0;
  end
  else if (x3_aux_cg1 && aux_dccm_x3_cg0) begin
    aux_dccm_ren_r     <= (aux_dccm_ren_nxt & x2_pass);
  end
end // block: dccm_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : dccm_rdata_PROC
  if ( rst_a == 1'b1 ) begin
    dccm_aux_rdata_r  <= {`npuarc_DATA_SIZE{1'b0}};
    dccm_ca_ren_r     <= 1'b0;
  end
  else if (ca_aux_cg1 && aux_dccm_ca_cg0) begin
    dccm_aux_rdata_r  <= (aux_dccm_ren_r & x3_lr_op_r)
                       ? dccm_aux_rdata
                       : `npuarc_DATA_SIZE'd0;
    dccm_ca_ren_r     <= aux_dccm_ren_r & x3_pass;
  end
end // block: dccm_rdata_PROC

always @ (posedge clk or posedge rst_a)
begin : dccm_waux_PROC
  if (rst_a == 1'b1) begin
    aux_dccm_wen_r     <= 1'b0;
  end
  else if (wa_aux_cg1 && aux_dccm_wa_cg0) begin
    aux_dccm_wen_r     <= (dccm_ca_ren_r & ca_sr_op_r & ca_pass & ca_aux_cond);
  end
end // block: dccm_waux_PROC
wire   dccm_aux_sr_op;

assign dccm_aux_sr_op = aux_dccm_wen_r
                      | (dccm_ca_ren_r  & ca_sr_op_r)
                      ;
//////////////////////////////////////////////////////////////////////////////
// DPER Auxiliary Control Pipeline                                          //
//////////////////////////////////////////////////////////////////////////////
wire                      aux_dper_x3_cg0;    // DPER X3-stage reg enable
wire                      aux_dper_ca_cg0;    // DPER CA-stage reg enable
wire                      aux_dper_wa_cg0;    // DPER WA-stage reg enable

wire                      aux_dper_ren_nxt;   // DPER region select at X2

reg                       dper_ca_ren_r;      // DPER region active at CA

assign  aux_dper_x3_cg0   = (x3_addr_cg0  & aux_dper_ren_nxt)
                          | (x3_enable    & aux_dper_ren_r);

assign  aux_dper_ca_cg0   = (ca_addr_cg0)
                          | (ca_enable    & dper_ca_ren_r);

assign  aux_dper_wa_cg0   = (wa_addr_cg0  & dper_ca_ren_r)
                          | (wa_enable    & aux_dper_wen_r);

assign  aux_dper_ren_nxt  = x2_aux_op
                          & x2_arc_range
                          & (   (x2_arc_addr_r == `npuarc_DMP_PER_AUX)
                             || (x2_arc_addr_r == `npuarc_DATA_MEM_ATTR_AUX)
                            )
                          ;

always @ (posedge clk or posedge rst_a)
begin : dper_raux_PROC
  if (rst_a == 1'b1) begin
    aux_dper_ren_r     <= 1'b0;
    aux_dper_raddr_r   <= 1'b0;
  end
  else if (x3_aux_cg1 && aux_dper_x3_cg0) begin
    aux_dper_ren_r     <= (aux_dper_ren_nxt & x2_pass);
    aux_dper_raddr_r   <= x2_arc_addr_r[0];
  end
end // block: dper_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : dper_rdata_PROC
  if ( rst_a == 1'b1 ) begin
    dper_aux_rdata_r  <= {`npuarc_DATA_SIZE{1'b0}};
    dper_ca_ren_r     <= 1'b0;
  end
  else if (ca_aux_cg1 && aux_dper_ca_cg0) begin
    dper_aux_rdata_r  <= (aux_dper_ren_r & x3_lr_op_r)
                       ? dper_aux_rdata
                       : `npuarc_DATA_SIZE'd0;
    dper_ca_ren_r     <= aux_dper_ren_r & x3_pass;
  end
end // block: dper_rdata_PROC

always @ (posedge clk or posedge rst_a)
begin : dper_waux_PROC
  if (rst_a == 1'b1) begin
    aux_dper_wen_r     <= 1'b0;
    aux_dper_waddr_r   <= 1'b0;
  end
  else if (wa_aux_cg1 && aux_dper_wa_cg0) begin
    aux_dper_wen_r     <= (dper_ca_ren_r & ca_sr_op_r & ca_pass & ca_aux_cond);
    aux_dper_waddr_r   <= ca_aux_addr_r[0];
  end
end // block: dper_waux_PROC

wire   dper_aux_sr_op;

assign dper_aux_sr_op = aux_dper_wen_r
                      | (dper_ca_ren_r  & ca_sr_op_r)
                      ;


//////////////////////////////////////////////////////////////////////////////
// DCACHE /DMP  Auxiliary Control Pipeline           
//////////////////////////////////////////////////////////////////////////////
wire                      aux_dc_x3_cg0;    // DCACHE X3-stage reg enable
wire                      aux_dc_ca_cg0;    // DCACHE CA-stage reg enable
wire                      aux_dc_wa_cg0;    // DCACHE WA-stage reg enable


wire                      aux_dc_ren_nxt;   // DCACHE region select at X2
wire [4:0]                aux_dc_raddr_nxt; // DCACHE read addr offset
wire [4:0]                aux_dc_waddr_nxt; // DCACHE write addr offset


reg                       dc_ca_ren_r;      // DCACHE region active at CA
reg                       aux_dc_stall_r;

assign  aux_dc_x3_cg0     = (x3_addr_cg0  & aux_dc_ren_nxt)
                          | (x3_enable    & aux_dc_ren_r);

assign  aux_dc_ca_cg0     = (ca_addr_cg0)
                          | (ca_enable    & dc_ca_ren_r);

assign  aux_dc_wa_cg0     = (wa_addr_cg0  & dc_ca_ren_r)
                          | (wa_enable    & aux_dc_wen_r);

assign  aux_dc_ren_nxt    =  x2_aux_op
                          & x2_arc_range
                          & (    (x2_arc_addr_r >= `npuarc_DC_IVDC_AUX)
                              && (x2_arc_addr_r <= `npuarc_DC_PTAG_HI)
                            )
                          ;

assign  aux_dc_raddr_nxt  = x2_arc_addr_r[4:0];
assign  aux_dc_waddr_nxt  = ca_aux_addr_r[4:0];

//////////////////////////////////////////////////////////////////////////////
// DCACHE Aux stall                                     
//////////////////////////////////////////////////////////////////////////////

always @ (posedge clk or posedge rst_a)
begin : dc_raux_PROC
  if (rst_a == 1'b1) begin
    aux_dc_raddr_r   <= 5'h00;
    aux_dc_ren_r     <= 1'b0;
  end
  else if (x3_aux_cg1 && aux_dc_x3_cg0) begin
    aux_dc_raddr_r   <= aux_dc_raddr_nxt;
    aux_dc_ren_r     <= (aux_dc_ren_nxt & x2_pass);
  end
end // block: dc_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : dc_stall_PROC
  if (rst_a == 1'b1) begin
    aux_dc_stall_r   <= 1'b0;
  end
  else begin
    aux_dc_stall_r   <= dc_aux_busy & (aux_dc_ren_r | aux_dc_ren_nxt);
  end
end // block: dc_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : dc_rdata_PROC
  if ( rst_a == 1'b1 ) begin
    dc_aux_rdata_r   <= {`npuarc_DATA_SIZE{1'b0}};
    dc_ca_ren_r      <= 1'b0;
  end
  else if (ca_aux_cg1 && aux_dc_ca_cg0) begin
    dc_aux_rdata_r   <= (aux_dc_ren_r & x3_lr_op_r)
                       ? dc_aux_rdata
                       : `npuarc_DATA_SIZE'd0;
    dc_ca_ren_r      <= aux_dc_ren_r & x3_pass;
  end
end // block: dc_rdata_PROC

always @ (posedge clk or posedge rst_a)
begin : dc_waux_PROC
  if (rst_a == 1'b1) begin
    aux_dc_wen_r     <= 1'b0;
    aux_dc_waddr_r   <= 5'h00;
  end
  else if (wa_aux_cg1 && aux_dc_wa_cg0) begin
    aux_dc_wen_r     <= (dc_ca_ren_r & ca_sr_op_r & ca_pass & ca_aux_cond);
    aux_dc_waddr_r   <= aux_dc_waddr_nxt;
  end
end // block: dc_waux_PROC

wire   dc_aux_sr_op;

assign dc_aux_sr_op  = 1'b0
                     | aux_dc_wen_r
                     | (dc_ca_ren_r  & ca_sr_op_r)
                     ;


//////////////////////////////////////////////////////////////////////////////
// ICACHE Auxiliary Control Pipeline                                        //
//////////////////////////////////////////////////////////////////////////////
wire                      aux_ic_x3_cg0;    // ICACHE X3-stage reg enable
wire                      aux_ic_ca_cg0;    // ICACHE CA-stage reg enable
wire                      aux_ic_wa_cg0;    // ICACHE WA-stage reg enable

wire                      aux_ic_ren_nxt;   // ICACHE region select at X2
wire [3:0]                aux_ic_raddr_nxt; // ICACHE read addr offset
wire [3:0]                aux_ic_waddr_nxt; // ICACHE write addr offset

reg                       ic_ca_ren_r;      // ICACHE region active at CA

assign  aux_ic_x3_cg0     = (x3_addr_cg0  & aux_ic_ren_nxt)
                          | (x3_enable  & aux_ic_ren_r);

assign  aux_ic_ca_cg0     = (ca_addr_cg0)
                          | (ca_enable  & ic_ca_ren_r);

assign  aux_ic_wa_cg0     = (wa_addr_cg0  & ic_ca_ren_r)
                          | (wa_enable  & aux_ic_wen_r);

assign  aux_ic_ren_nxt    = x2_aux_op
                          & x2_arc_range
                          & (    ( x2_arc_addr_r >= `npuarc_IC_IVIC_AUX ) // 0x010
                              && ( x2_arc_addr_r <= `npuarc_IC_AUX_LIMIT) // 0x01F
                              && ( x2_arc_addr_r != `npuarc_DCCM_AUX    ) // != 0x018
                            )
                          ;

assign  aux_ic_raddr_nxt  = x2_arc_addr_r[3:0];
assign  aux_ic_waddr_nxt  = ca_aux_addr_r[3:0];

always @ (posedge clk or posedge rst_a)
begin : ic_raux_PROC
  if (rst_a == 1'b1) begin
    aux_ic_ren_r     <= 1'b0;
    aux_ic_raddr_r   <= 4'h0;
  end
  else if (x3_aux_cg1 && aux_ic_x3_cg0) begin
    aux_ic_ren_r     <= (aux_ic_ren_nxt & x2_pass);
    aux_ic_raddr_r   <= aux_ic_raddr_nxt;
  end
end // block: ic_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : ic_rdata_PROC
  if ( rst_a == 1'b1 ) begin
    ic_aux_rdata_r   <= {`npuarc_DATA_SIZE{1'b0}};
    ic_ca_ren_r      <= 1'b0;
  end
  else if (ca_aux_cg1 && aux_ic_ca_cg0) begin
    ic_aux_rdata_r   <= (aux_ic_ren_r & x3_lr_op_r)
                       ? ic_aux_rdata
                       : `npuarc_DATA_SIZE'd0;
    ic_ca_ren_r      <= aux_ic_ren_r & x3_pass;
  end
end // block: ic_rdata_PROC

always @ (posedge clk or posedge rst_a)
begin : ic_waux_PROC
  if (rst_a == 1'b1) begin
    aux_ic_wen_r     <= 1'b0;
    aux_ic_waddr_r   <= 4'h0;
  end
  else if (wa_aux_cg1 && aux_ic_wa_cg0) begin
    aux_ic_wen_r     <= (ic_ca_ren_r & ca_sr_op_r & ca_pass & ca_aux_cond);
    aux_ic_waddr_r   <= aux_ic_waddr_nxt;
  end
end // block: ic_waux_PROC


//////////////////////////////////////////////////////////////////////////////
// BPU Auxiliary Control Pipeline                                           //
//////////////////////////////////////////////////////////////////////////////
wire                      aux_bpu_x3_cg0;    // BPU X3-stage reg enable
wire                      aux_bpu_ca_cg0;    // BPU CA-stage reg enable
wire                      aux_bpu_wa_cg0;    // BPU WA-stage reg enable

wire                      aux_bpu_ren_nxt;   // BPU region select at X2
wire [3:0]                aux_bpu_raddr_nxt; // BPU read addr offset
wire [3:0]                aux_bpu_waddr_nxt; // BPU write addr offset

reg                       bpu_ca_ren_r;      // BPU region active at CA

assign  aux_bpu_x3_cg0    = (x3_addr_cg0  & aux_bpu_ren_nxt)
                          | (x3_enable  & aux_bpu_ren_r);

assign  aux_bpu_ca_cg0    = (ca_addr_cg0)
                          | (ca_enable  & bpu_ca_ren_r);

assign  aux_bpu_wa_cg0    = (wa_addr_cg0  & bpu_ca_ren_r)
                          | (wa_enable  & aux_bpu_wen_r);

assign  aux_bpu_ren_nxt   = x2_aux_op
                          & x2_arc_range
                          & ( x2_arc_addr_r [11:4] == 8'h48 )
                          ;

assign  aux_bpu_raddr_nxt = x2_arc_addr_r[3:0];
assign  aux_bpu_waddr_nxt = ca_aux_addr_r[3:0];

always @ (posedge clk or posedge rst_a)
begin : bpu_raux_PROC
  if (rst_a == 1'b1) begin
    aux_bpu_ren_r     <= 1'b0;
    aux_bpu_raddr_r   <= 4'h0;
  end
  else if (x3_aux_cg1 && aux_bpu_x3_cg0) begin
    aux_bpu_ren_r     <= (aux_bpu_ren_nxt & x2_pass);
    aux_bpu_raddr_r   <= aux_bpu_raddr_nxt;
  end
end // block: bpu_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : bpu_rdata_PROC
  if ( rst_a == 1'b1 ) begin
    bpu_aux_rdata_r   <= {`npuarc_DATA_SIZE{1'b0}};
    bpu_ca_ren_r      <= 1'b0;
  end
  else if (ca_aux_cg1 && aux_bpu_ca_cg0) begin
    bpu_aux_rdata_r   <= (aux_bpu_ren_r & x3_lr_op_r)
                       ? bpu_aux_rdata
                       : `npuarc_DATA_SIZE'd0;
    bpu_ca_ren_r      <= aux_bpu_ren_r & x3_pass;
  end
end // block: bpu_rdata_PROC

always @ (posedge clk or posedge rst_a)
begin : bpu_waux_PROC
  if (rst_a == 1'b1) begin
    aux_bpu_wen_r     <= 1'b0;
    aux_bpu_waddr_r   <= 4'h0;
  end
  else if (wa_aux_cg1 && aux_bpu_wa_cg0) begin
    aux_bpu_wen_r     <= (bpu_ca_ren_r & ca_sr_op_r & ca_pass & ca_aux_cond);
    aux_bpu_waddr_r   <= aux_bpu_waddr_nxt;
  end
end // block: bpu_waux_PROC

//////////////////////////////////////////////////////////////////////////////
// EIA Auxiliary Control Pipeline                                           //
//////////////////////////////////////////////////////////////////////////////
wire                      aux_eia_x3_cg0;   // EIA X3-stage reg enable
wire                      aux_eia_ca_cg0;    // EIA CA-stage reg enable
wire                      aux_eia_wa_cg0;    // EIA WA-stage reg enable

wire                      aux_eia_ren_nxt;   // EIA region select at X2

wire                      aux_eia_raw;       // RAW hazard on EIA

reg                       eia_ca_ren_r;      // EIA region active at CA

reg                       eia_wa_ren_r;      // EIA region active at WA

assign  aux_eia_x3_cg0    = (x3_addr_cg0  & aux_eia_ren_nxt)
                          | (x3_enable  & aux_eia_ren_r);

assign  aux_eia_ca_cg0    = (ca_addr_cg0)
                          | (ca_enable  & eia_ca_ren_r);

assign  aux_eia_wa_cg0    = (wa_addr_cg0  & eia_ca_ren_r)
                          | (wa_enable  & aux_eia_wen_r);

assign  aux_eia_ren_nxt   = x2_aux_op;

assign  aux_eia_raddr_r   =  x3_aux_addr_r;
assign  aux_eia_waddr_r   =  wa_aux_addr_r;

assign  aux_eia_raw       = (aux_eia_ren_r & x3_lr_op_r)
                          & (   (eia_ca_ren_r & ca_sr_op_r)
                              | (eia_wa_ren_r & wa_sr_op_r)
                            )
                          ;

always @ (posedge clk or posedge rst_a)
begin : eia_raux_PROC
  if (rst_a == 1'b1) begin
    aux_eia_ren_r     <= 1'b0;
  end
  else if (x3_aux_cg1 && aux_eia_x3_cg0) begin
    aux_eia_ren_r     <= (aux_eia_ren_nxt & x2_pass);
  end
end // block: eia_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : eia_rdata_PROC
  if ( rst_a == 1'b1 ) begin
    eia_aux_rdata_r   <= {`npuarc_DATA_SIZE{1'b0}};
    eia_ca_ren_r      <= 1'b0;
  end
  else if (ca_aux_cg1 && aux_eia_ca_cg0) begin
    eia_aux_rdata_r   <= ((~eia_aux_unimpl) & x3_lr_op_r)
                       ? eia_aux_rdata
                       : `npuarc_DATA_SIZE'd0;
    eia_ca_ren_r      <= (~eia_aux_unimpl) & x3_pass;
  end
end // block: eia_rdata_PROC

always @ (posedge clk or posedge rst_a)
begin : eia_waux_PROC
  if (rst_a == 1'b1) begin
    aux_eia_wen_r     <= 1'b0;
    eia_wa_ren_r      <= 1'b0;
  end
  else if (wa_aux_cg1 && aux_eia_wa_cg0) begin
    aux_eia_wen_r     <= (eia_ca_ren_r & ca_sr_op_r & ca_pass & ca_aux_cond);
    eia_wa_ren_r      <= eia_ca_ren_r & ca_pass;
  end
end // block: eia_waux_PROC

//////////////////////////////////////////////////////////////////////////////
// CCAUX Auxiliary Control Pipeline                                         //
//////////////////////////////////////////////////////////////////////////////
//
wire                      ccaux_x3_ren_cg0;    // CCAUX X3-stage ren enable
wire                      ccaux_x3_rgn_cg0;    // CCAUX X3-stage region enable
wire                      ccaux_resp_x3_cg0;   // CCAUX X3-stage reg enable
wire                      ccaux_ca_cg0;        // CCAUX CA-stage reg enable
wire                      ccaux_wa_cg0;        // CCAUX WA-stage reg enable

wire                      ccaux_x3_ren_nxt;    // CCAUX region select at X2
wire [`npuarc_CCAUX_RGN_RANGE]   ccaux_x3_rgn_nxt;    // CCAUX region select at X2

wire                      ccaux_unimpl_r;      // CCAUX unimpl bit from status

reg                       ccaux_x3_ren_r;      // CCAUX region active at X3
reg  [`npuarc_CCAUX_RGN_RANGE]   ccaux_x3_region_r;   // CCAUX region active at X3
reg                       ccaux_ca_ren_r;      // CCAUX region active at CA
reg  [`npuarc_CCAUX_RGN_RANGE]   ccaux_ca_region_r;   // CCAUX region active at CA
reg                       ccaux_cmt_phase_r;   // CCAUX commit phase at CA
  // leda NTL_CON32 off
  // LMD: Change on net has no effect on any of the outputs
  // LJ:  connect to ccaux interface
reg                       ccaux_cmt_valid_r;   // CCAUX commit valid at CA
  // leda NTL_CON32 on
reg  [`npuarc_CCAUX_RGN_RANGE]   ccaux_wa_region_r;   // CCAUX region active at WA
reg                       ccaux_wa_wen_r;      // CCAUX WA-stage write enable
reg                       ccaux_stall_r;       // stalls X3 stage
reg                       ccaux_stall_one_r;   // forced stall at start of ccaux

always @*
begin : x2_ccaux_region_PROC

  x2_ccaux_region = {`npuarc_CCAUX_RGN_BITS{1'b0}};

  x2_ccaux_region[`npuarc_CCAUX_GAUX_IDX] = x2_aux_op 
                                        & ( 1'b0
                                        | (x2_arc_range & 
                                                        (   ( x2_arc_addr_r >= 12'h9A9)
                                                         && ( x2_arc_addr_r <= 12'h9A9)))
                                          );
end // block : x2_ccaux_region_PROC


assign ccaux_x3_rgn_nxt  = x2_pass ? x2_ccaux_region : {`npuarc_CCAUX_RGN_BITS{1'b0}};
// spyglass disable_block Ac_conv01
// SMD:  synchronizers converge
assign ccaux_x3_ren_cg0  = (x3_addr_cg0    & ccaux_x3_ren_nxt)
                         | (ccaux_x3_ren_r & (!ccaux_stall_one_r) & aux_rs_accept)
                         | fch_restart
                         ;

assign ccaux_x3_rgn_cg0  = (x3_addr_cg0    & ccaux_x3_ren_nxt)
                         | fch_restart
                         ;

assign ccaux_resp_x3_cg0 = (ccaux_x3_ren_r & (!ccaux_stall_one_r) & aux_rs_accept)
                         | (ca_addr_cg0    & ccaux_resp_r)
                         | fch_restart
                         ;
// spyglass enable_block Ac_conv01
assign ccaux_ca_cg0      = (ca_addr_cg0)
                         | (ca_enable  & ccaux_ca_ren_r)
                         | fch_restart
                         ;

assign ccaux_wa_cg0      = (wa_addr_cg0 & ccaux_ca_ren_r)
                         | (wa_enable   & ccaux_wa_wen_r)
                         ;

assign ccaux_ca_wa_cg0   = (ca_enable & ccaux_ca_ren_r)
                         | (wa_enable & ccaux_cmt_phase_r)
                         | fch_restart
                         ;
// leda W563 off
// LMD: Reduction of single bit expression is redundant
// LJ: configurable x2_ccaux_region may be a single bit
// spyglass disable_block Ac_conv01
// SMD:  synchronizers converge
assign ccaux_x3_ren_nxt  = x2_pass
                         & (  (|x2_ccaux_region)
                             | ccaux_stall_one_r
                             | (ccaux_x3_ren_r & (!aux_rs_accept))
                           )
                         ;
// leda W563 on
// spyglass enable_block Ac_conv01
assign ccaux_unimpl_r    = ccaux_status_r[`npuarc_CCAUX_UNIMPL_BIT];
assign ccaux_serial_sr_r = ccaux_status_r[`npuarc_CCAUX_SERIAL_BIT]
                         & (!ccaux_unimpl_r & x3_sr_op_r & ccaux_resp_r)
                         ;
assign ccaux_strict_sr_r = ccaux_status_r[`npuarc_CCAUX_STRICT_BIT]
                         & (!ccaux_unimpl_r & x3_sr_op_r & ccaux_resp_r)
                         ;
assign ccaux_illegal_r   = ccaux_status_r[`npuarc_CCAUX_ILLEGAL_BIT]
                         & (!ccaux_unimpl_r & (x3_lr_op_r | x3_sr_op_r) & ccaux_resp_r)
                         ;
assign ccaux_k_rd_r      = ccaux_status_r[`npuarc_CCAUX_K_RD_BIT]
                         & (!ccaux_unimpl_r & x3_lr_op_r & ccaux_resp_r)
                         ;
assign ccaux_k_wr_r      = ccaux_status_r[`npuarc_CCAUX_K_WR_BIT]
                         & (!ccaux_unimpl_r & x3_sr_op_r & ccaux_resp_r)
                         ;


always @ (posedge clk or posedge rst_a)
begin : ccaux_x3_ren_reg_PROC
  if (rst_a == 1'b1)
    ccaux_x3_ren_r    <= 1'b0;
  else if (ccaux_x3_ren_cg0 == 1'b1)
    ccaux_x3_ren_r    <= ccaux_x3_ren_nxt;
end // block: ccaux_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : ccaux_x3_rgn_reg_PROC
  if (rst_a == 1'b1)
    ccaux_x3_region_r <= {`npuarc_CCAUX_RGN_BITS{1'b0}};
  else if (ccaux_x3_rgn_cg0 == 1'b1)      
    ccaux_x3_region_r <= ccaux_x3_rgn_nxt;
end // block: ccaux_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : ccaux_resp_PROC
  if (rst_a == 1'b1) begin
    ccaux_rdata_r       <= {`npuarc_DATA_SIZE{1'b0}};
    ccaux_resp_r        <= 1'b0;
    ccaux_status_r      <= 6'd0;
  end
  else if (ccaux_resp_x3_cg0 == 1'b1) begin
    ccaux_rdata_r       <= aux_rs_data;
    
    ccaux_resp_r        <= ccaux_x3_ren_r 
                        & (!ccaux_stall_one_r)
                        & aux_rs_accept
                        & (!fch_restart)
                        ;
                         
    ccaux_status_r      <= (aux_rs_accept & (!fch_restart)) // acquire status
                        ? aux_rs_status                   // actual credentials
                        : 6'b001000                       // default 'unimpl'
                        ;
  end
end // block: ccaux_resp_PROC

always @ (posedge clk or posedge rst_a)
begin : ccaux_rdata_PROC
  if (rst_a == 1'b1) begin
    ccaux_aux_rdata_r   <= {`npuarc_DATA_SIZE{1'b0}};
    ccaux_ca_ren_r      <= 1'b0;
    ccaux_ca_region_r   <= {`npuarc_CCAUX_RGN_BITS{1'b0}};
  end
  else if (ccaux_ca_cg0 == 1'b1) begin
    ccaux_aux_rdata_r   <= (!ccaux_unimpl_r & x3_lr_op_r & ccaux_resp_r)
                        ? ccaux_rdata_r
                        : `npuarc_DATA_SIZE'd0
                        ;

    ccaux_ca_ren_r      <= x3_pass & ccaux_resp_r;
    ccaux_ca_region_r   <= ccaux_x3_region_r;
  end
end // block: ccaux_rdata_PROC

always @ (posedge clk or posedge rst_a)
begin : ccaux_waux_PROC
  if (rst_a == 1'b1) begin
    ccaux_wa_wen_r      <= 1'b0;
    ccaux_wa_region_r   <= {`npuarc_CCAUX_RGN_BITS{1'b0}};
  end
  else if (ccaux_wa_cg0 == 1'b1) begin
    ccaux_wa_wen_r      <= ccaux_ca_ren_r & ca_sr_op_r & ca_pass & ca_aux_cond;
    ccaux_wa_region_r   <= ccaux_ca_region_r;
  end
end // block: ccaux_waux_PROC

always @ (posedge clk or posedge rst_a)
begin : ccaux_cmt_PROC
  if (rst_a == 1'b1) begin
    ccaux_cmt_valid_r   <= 1'b0;
    ccaux_cmt_phase_r   <= 1'b0;
  end
  else if (ccaux_ca_wa_cg0 == 1'b1) begin
    ccaux_cmt_valid_r   <= ccaux_ca_ren_r & ca_pass & ca_aux_cond;
    
    ccaux_cmt_phase_r   <= ccaux_ca_ren_r 
                        | (fch_restart & (ccaux_x3_ren_r | ccaux_resp_r))
                        ;
  end
end // block: ccaux_cmt_PROC

always @ (posedge clk or posedge rst_a)
begin : ccaux_stall_PROC
  if (rst_a == 1'b1)
  begin
    ccaux_stall_r       <= 1'b0;
    ccaux_stall_one_r   <= 1'b0;
  end
  else begin
    ccaux_stall_one_r   <= ccaux_x3_ren_nxt;
    
    ccaux_stall_r       <= ccaux_x3_ren_nxt
                        | ccaux_stall_one_r
                        | (ccaux_x3_ren_r & (!aux_rs_accept))
                        | (ccaux_x3_ren_r & x3_sr_op_r & ccaux_ca_ren_r & ca_sr_op_r)
                        | (ccaux_x3_ren_r & x3_sr_op_r & (!aux_wr_allow))
                        ;
  end
end // block: ccaux_stall_PROC

assign aux_rs_valid  = ccaux_x3_ren_r;
assign aux_rs_region = ccaux_x3_region_r;
assign aux_rs_addr   = x3_aux_addr_r[`npuarc_CCAUX_ADDR_RANGE];
assign aux_rs_read   = x3_lr_op_r;
assign aux_rs_write  = x3_sr_op_r;

assign aux_wr_valid  = ccaux_wa_wen_r;
assign aux_wr_region = ccaux_wa_region_r;
assign aux_wr_addr   = wa_aux_addr_r[`npuarc_CCAUX_ADDR_RANGE];
assign aux_cm_phase  = ccaux_cmt_phase_r;
assign aux_cm_valid  = ccaux_cmt_valid_r;




//////////////////////////////////////////////////////////////////////////////
// BCR Auxiliary Control Pipeline                                           //
//////////////////////////////////////////////////////////////////////////////
wire                      aux_bcr_x3_cg0;     // BCR X3-stage reg enable
wire                      aux_bcr_ca_cg0;     // BCR CA-stage reg enable

wire                      aux_bcr_ren_nxt;    // BCR region select at X2
wire [`npuarc_BCR_REG_RANGE]     aux_bcr_raddr_nxt;  // BCR read addr offset

reg                       bcr_ca_ren_r;       // BCR region active at CA

assign  aux_bcr_x3_cg0    = (x3_addr_cg0  & aux_bcr_ren_nxt)
                          | (x3_enable    & aux_bcr_ren_r);

assign  aux_bcr_ca_cg0    = (ca_addr_cg0)
                          | (ca_enable    & bcr_ca_ren_r);

assign  aux_bcr_ren_nxt   = x2_aux_op
                          & x2_arc_range
                          & (((x2_arc_addr_r[11:8] == 4'h0)
                             & ((x2_arc_addr_r[5] & x2_arc_addr_r[6])
                               | (x2_arc_addr_r[6] & x2_arc_addr_r[7])))
                            |((x2_arc_addr_r[11:8] == 4'hF)
                             & ((x2_arc_addr_r[5] & x2_arc_addr_r[6])
                               | (x2_arc_addr_r[7]))));

assign  aux_bcr_raddr_nxt =  x2_arc_addr_r[`npuarc_BCR_REG_RANGE];

always @ (posedge clk or posedge rst_a)
begin : bcr_raux_PROC
  if (rst_a == 1'b1) begin
    aux_bcr_ren_r     <= 1'b0;
    aux_bcr_raddr_r   <= `npuarc_BCR_REG_BITS'd0;
  end
  else if (x3_aux_cg1 && aux_bcr_x3_cg0) begin
    aux_bcr_ren_r     <= (aux_bcr_ren_nxt & x2_pass);
    aux_bcr_raddr_r   <= aux_bcr_raddr_nxt;
  end
end // block: bcr_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : bcr_rdata_PROC
  if ( rst_a == 1'b1 ) begin
    bcr_aux_rdata_r   <= {`npuarc_DATA_SIZE{1'b0}};
    bcr_ca_ren_r      <= 1'b0;
  end
  else if (ca_aux_cg1 && aux_bcr_ca_cg0) begin
    bcr_aux_rdata_r   <= (aux_bcr_ren_r & x3_lr_op_r)
                       ? bcr_aux_rdata
                       : `npuarc_DATA_SIZE'd0;

    bcr_ca_ren_r      <= aux_bcr_ren_r & x3_pass;
  end
end // block: bcr_rdata_PROC


////////////////////////////////////////////////////////////////////////////
// Actionpoints Auxiliary Control Pipeline                                //
////////////////////////////////////////////////////////////////////////////
wire                      aux_aps_x3_cg0;     // APS X3-stage reg enable
wire                      aux_aps_ca_cg0;     // APS CA-stage reg enable
wire                      aux_aps_wa_cg0;     // APS WA-stage reg enable

wire                      aux_aps_ren_nxt;    // APS region select at X2
wire [4:0]                aux_aps_raddr_nxt;  // APS read addr offset
wire [4:0]                aux_aps_waddr_nxt;  // APS write addr offset

reg                       aps_ca_ren_r;       // APS region active at CA

assign  aux_aps_x3_cg0    = (x3_addr_cg0  & aux_aps_ren_nxt)
                          | (x3_enable    & aux_aps_ren_r);

assign  aux_aps_ca_cg0    = (ca_addr_cg0)
                          | (ca_enable    & aps_ca_ren_r);

assign  aux_aps_wa_cg0    = (wa_addr_cg0  & aps_ca_ren_r)
                          | (wa_enable    & aux_aps_wen_r);

assign  aux_aps_ren_nxt   = x2_aux_op
                          & x2_arc_range
                          & (x2_arc_addr_r[`npuarc_AUX_REG_MSB:5] == 7'h11);

assign  aux_aps_raddr_nxt = x2_arc_addr_r[4:0];
assign  aux_aps_waddr_nxt = ca_aux_addr_r[4:0];

always @ (posedge clk or posedge rst_a)
begin : aps_raux_PROC
  if (rst_a == 1'b1) begin
    aux_aps_ren_r     <= 1'b0;
    aux_aps_raddr_r   <= 5'h00;
  end
  else if (x3_aux_cg1 && aux_aps_x3_cg0) begin
    aux_aps_ren_r     <= (aux_aps_ren_nxt & x2_pass);
    aux_aps_raddr_r   <= aux_aps_raddr_nxt;
  end
end // block: aps_raux_PROC

always @ (posedge clk or posedge rst_a)
begin : aps_rdata_PROC
  if ( rst_a == 1'b1 ) begin
    aps_aux_rdata_r   <= {`npuarc_DATA_SIZE{1'b0}};
    aps_ca_ren_r      <= 1'b0;
  end
  else if (ca_aux_cg1 && aux_aps_ca_cg0) begin
    aps_aux_rdata_r   <= (aux_aps_ren_r & x3_lr_op_r)
                       ? aps_aux_rdata
                       : `npuarc_DATA_SIZE'd0;

    aps_ca_ren_r      <= aux_aps_ren_r & x3_pass;
  end
end // block: aps_rdata_PROC

always @ (posedge clk or posedge rst_a)
begin : aps_waux_PROC
  if (rst_a == 1'b1) begin
    aux_aps_wen_r     <= 1'b0;
    aux_aps_waddr_r   <= 5'h00;
  end
  else if (wa_aux_cg1 && aux_aps_wa_cg0) begin
    aux_aps_wen_r     <= (aps_ca_ren_r & ca_sr_op_r & ca_pass & ca_aux_cond);
    aux_aps_waddr_r   <= aux_aps_waddr_nxt;
  end
end // block: aps_waux_PROC

// Action Point Clock GATEing block
// Extend Action Point Aux Clock for one additional cycle
// 
always @ (posedge clk or posedge rst_a)
begin : aps_cgate_PROC
  if (rst_a == 1'b1) begin
    aux_ap1_wen_r     <= 1'b0;
  end
  else if (aux_aps_wen_r | aux_ap1_wen_r) begin
    aux_ap1_wen_r     <= aux_aps_wen_r;
  end
end // block: aps_cgate_PROC

// Action Point Aux Clock Gate Enable
assign aux_aps_active = aux_aps_ren_r
                      | aps_ca_ren_r
                      | aux_aps_wen_r
                      | aux_ap1_wen_r
                      ;

    



//                                                                          //
//  Auxiliary Stall Conditions                                              //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                 x2_sees_ca_aux;
reg                 x3_sees_ca_aux;

reg                 x2_sees_x3_aux;

reg                 x3_aux_raw_r;
reg                 x3_aux_raw_nxt;
reg                 x3_aux_raw_cg0;

always @*
begin: x3_aux_raw_PROC
  x2_sees_ca_aux    = (   x2_lr_op_r 
                        & aux_core_ren_nxt
                        & ca_sr_op_r
                        & core_ca_ren_r
                      )
                    | (   x2_lr_op_r 
                        & aux_bpu_ren_nxt
                        & ca_sr_op_r
                        & bpu_ca_ren_r
                      )
                    | (   x2_lr_op_r 
                        & aux_dc_ren_nxt
                        & ca_sr_op_r
                        & dc_ca_ren_r
                      )
                    | (   x2_lr_op_r 
                        & aux_eia_ren_nxt
                        & ca_sr_op_r
                        & eia_ca_ren_r
                      )
                    | (   x2_lr_op_r 
                        & aux_dccm_ren_nxt
                        & ca_sr_op_r
                        & dccm_ca_ren_r
                      )
                    | (   x2_lr_op_r 
                        & aux_dper_ren_nxt
                        & ca_sr_op_r
                        & dper_ca_ren_r
                      )
                    | (   x2_lr_op_r 
                        & aux_ic_ren_nxt
                        & ca_sr_op_r
                        & ic_ca_ren_r
                      )
                    | (   x2_lr_op_r 
                        & aux_tm0_ren_nxt
                        & ca_sr_op_r
                        & tm0_ca_ren_r
                      )
                    | (   x2_lr_op_r 
                        & aux_rtc_ren_nxt
                        & ca_sr_op_r
                        & rtc_ca_ren_r
                      )
                    | (   x2_lr_op_r 
                        & aux_wdt_ren_nxt
                        & ca_sr_op_r
                        & wdt_ca_ren_r
                      )
                    | (   x2_lr_op_r 
                        & aux_irq_ren_nxt
                        & ca_sr_op_r
                        & irq_ca_ren_r
                      )
                    | (   x2_lr_op_r 
                        & aux_mmu_ren_nxt
                        & ca_sr_op_r
                        & mmu_ca_ren_r
                      )
                    | (   x2_lr_op_r 
                        & aux_mpu_ren_nxt
                        & ca_sr_op_r
                        & mpu_ca_ren_r
                      )
                    | (   x2_lr_op_r 
                        & aux_pct_ren_nxt
                        & ca_sr_op_r
                        & pct_ca_ren_r
                      )
                    | (   x2_lr_op_r 
                        & aux_smt_ren_nxt
                        & ca_sr_op_r
                        & smt_ca_ren_r
                      )
                    | (x2_lr_op_r 
                     & aux_rtt_ren_nxt
                     & ca_sr_op_r
                     & rtt_ca_ren_r)
                    ;

  x3_sees_ca_aux    = (   x3_lr_op_r 
                        & aux_core_ren_r
                        & ca_sr_op_r
                        & core_ca_ren_r
                      )
                    | (   x3_lr_op_r 
                        & aux_bpu_ren_r
                        & ca_sr_op_r
                        & bpu_ca_ren_r
                      )
                    | (   x3_lr_op_r 
                        & aux_dc_ren_r
                        & ca_sr_op_r
                        & dc_ca_ren_r
                      )
                    | (   x3_lr_op_r 
                        & aux_eia_ren_r
                        & ca_sr_op_r
                        & eia_ca_ren_r
                      )
                    | (   x3_lr_op_r 
                        & aux_dccm_ren_r
                        & ca_sr_op_r
                        & dccm_ca_ren_r
                      )
                    | (   x3_lr_op_r 
                        & aux_dper_ren_r
                        & ca_sr_op_r
                        & dper_ca_ren_r
                      )
                    | (   x3_lr_op_r 
                        & aux_ic_ren_r
                        & ca_sr_op_r
                        & ic_ca_ren_r
                      )
                    | (   x3_lr_op_r 
                        & aux_tm0_ren_r
                        & ca_sr_op_r
                        & tm0_ca_ren_r
                      )
                    | (   x3_lr_op_r 
                        & aux_rtc_ren_r
                        & ca_sr_op_r
                        & rtc_ca_ren_r
                      )
                    | (   x3_lr_op_r 
                        & aux_wdt_ren_r
                        & ca_sr_op_r
                        & wdt_ca_ren_r
                      )
                    | (   x3_lr_op_r 
                        & aux_irq_ren_r
                        & ca_sr_op_r
                        & irq_ca_ren_r
                      )
                    | (   x3_lr_op_r 
                        & aux_mmu_ren_r
                        & ca_sr_op_r
                        & mmu_ca_ren_r
                      )
                    | (   x3_lr_op_r 
                        & aux_mpu_ren_r
                        & ca_sr_op_r
                        & mpu_ca_ren_r
                      )
                    | (   x3_lr_op_r 
                        & aux_pct_ren_r
                        & ca_sr_op_r
                        & pct_ca_ren_r
                      )
                    | (   x3_lr_op_r 
                        & aux_smt_ren_r
                        & ca_sr_op_r
                        & smt_ca_ren_r
                      )
                    | (   x3_lr_op_r 
                        & aux_rtt_ren_r
                        & ca_sr_op_r
                        & rtt_ca_ren_r
                      )
                    ;

  x2_sees_x3_aux    = (x2_lr_op_r & x3_sr_op_r)
                    & (   (aux_core_ren_nxt & aux_core_ren_r)
                        | (aux_bpu_ren_nxt  & aux_bpu_ren_r)
                        | (aux_dc_ren_nxt   & aux_dc_ren_r)
                        | (aux_eia_ren_nxt  & aux_eia_ren_r)
                      )
                    | (x2_lr_op_r 
                     & aux_dccm_ren_nxt
                     & x3_sr_op_r
                     & aux_dccm_ren_r)
                    | (x2_lr_op_r 
                     & aux_dper_ren_nxt
                     & x3_sr_op_r
                     & aux_dper_ren_r)
                    | (x2_lr_op_r 
                     & aux_ic_ren_nxt
                     & x3_sr_op_r
                     & aux_ic_ren_r)
                    | (x2_lr_op_r 
                     & aux_tm0_ren_nxt
                     & x3_sr_op_r
                     & aux_tm0_ren_r)
                    | (x2_lr_op_r 
                     & aux_rtc_ren_nxt
                     & x3_sr_op_r
                     & aux_rtc_ren_r)
                    | (x2_lr_op_r 
                     & aux_wdt_ren_nxt
                     & x3_sr_op_r
                     & aux_wdt_ren_r)
                    | (x2_lr_op_r 
                     & aux_irq_ren_nxt
                     & x3_sr_op_r
                     & aux_irq_ren_r)
                    | (x2_lr_op_r 
                     & aux_mmu_ren_nxt
                     & x3_sr_op_r
                     & aux_mmu_ren_r)
                    | (x2_lr_op_r 
                     & aux_mpu_ren_nxt
                     & x3_sr_op_r
                     & aux_mpu_ren_r)
                    | (x2_lr_op_r 
                     & aux_pct_ren_nxt
                     & x3_sr_op_r
                     & aux_pct_ren_r)
                    | (x2_lr_op_r 
                     & aux_smt_ren_nxt
                     & x3_sr_op_r
                     & aux_smt_ren_r)
                    | (x2_lr_op_r 
                     & aux_rtt_ren_nxt
                     & x3_sr_op_r
                     & aux_rtt_ren_r)
                    ;

  x3_aux_raw_cg0    = x3_aux_raw_r
                    | x3_addr_cg0
                    | ca_addr_cg0
                    ;

  x3_aux_raw_nxt    = 1'b0
                    | x2_sees_ca_aux
                    | x3_sees_ca_aux
                    | (x2_sees_x3_aux & (~x3_aux_raw_r))
                    ;


end // block: x3_aux_raw_PROC

always @ (posedge clk or posedge rst_a)
begin : x3_raw_reg_PROC
  if (rst_a == 1'b1) begin
    x3_aux_raw_r     <= 1'b0;
  end
  else if (x3_aux_raw_cg0) begin
    x3_aux_raw_r     <= x3_aux_raw_nxt;
  end
end // block: x3_raw_reg_PROC

assign aux_x3_stall       = core_aux_stall
                          | x3_aux_raw_r
                          | (aux_dc_stall_r & aux_dc_ren_r)
                          | eia_aux_stall
                          | aux_eia_raw
                          | ccaux_stall_r
                          | x3_irq_stall_r
                          ;

assign dmp_aux_sr_op      = 1'b0
                          | dc_aux_sr_op
                          | dccm_aux_sr_op
                          | dper_aux_sr_op
                          ;

endmodule // alb_aux_ctrl
