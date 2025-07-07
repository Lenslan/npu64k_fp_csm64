// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2015 Synopsys, Inc. All rights reserved.
//
// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
// work of Synopsys, Inc., and is fully protected under copyright and 
// trade secret laws. You may not view, use, disclose, copy, or distribute 
// this file or any information contained herein except pursuant to a 
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2011, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//  
//  
//  #######  ###     #            ######   ###  ######   #######  
//  #         #     # #           #     #   #   #     #  #        
//  #         #    #   #          #     #   #   #     #  #        
//  #####     #   #     #         ######    #   ######   #####    
//  #         #   #######         #         #   #        #        
//  #         #   #     #         #         #   #        #        
//  #######  ###  #     #  #####  #        ###  #        #######  
//  
//  
// ===========================================================================
//
// Description:
//
//  This module implements the Extension Interface Automation (EIA) pipeline. 
// 
//  This module is instantiated when the HAS_EIA option is enabled.
//
//  This .vpp source file must be pre-processed with the JavaScript-capable
//  version of the Verilog Pre-Processor (VPP) to produce the equivalent .v 
//  file using a command such as:
//
//   vpp +q +o alb_eia_pipe.vpp
//
// ===========================================================================
// Configuration-dependent macro definitions
//

// Set simulation timescale
//
// `include "const.def"


//////////////////////////////////////////////////////////////////////////////
// Signal declarations for all EIA extensions                               //
//////////////////////////////////////////////////////////////////////////////


//--+----1----+----2----+----3----+----4----+----5----+----6----+----7----+----8






//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 }, edc: { suffix: "auto", clk: {clk : "edc_clk" , clk_ungated: "edc_clk_ungated"}, rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_eia_pipe (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                        clk,             // Clock input - gated
  input                        clk_ungated,     // Clock input - free running
  input                        rst_a,           // Asynchronous reset input

// Library ARCv2HS-3.5.999999999



  ////////// EIA user extension external input signals ///////////////////////
  //
  input   [95:0]  EventManager_evm_event_a,
  input           EventManager_evm_sleep,

  ////////// EIA user extension external output signals //////////////////////
  //
  output          EventManager_evm_wakeup,
  output  [63:0]  EventManager_evm_send,
  output  [31:0]  EventManager_vm_grp0_sid,
  output  [31:0]  EventManager_vm_grp0_ssid,
  output  [31:0]  EventManager_vm_grp1_sid,
  output  [31:0]  EventManager_vm_grp1_ssid,
  output  [31:0]  EventManager_vm_grp2_sid,
  output  [31:0]  EventManager_vm_grp3_sid,
  output  [31:0]  EventManager_vm_grp2_ssid,
  output  [31:0]  EventManager_vm_grp3_ssid,
  output          EventManager_evt_vm_irq,
  output  [3:0]  EventManager_evt_vm_sel,

// leda NTL_CON13C off
// LMD: non driving port
// LJ:  eia interface to exu contains all standard handshake signals regardless
//      of user-defined configurability options
// spyglass disable_block W528
// SMD: Variable set but not read
// SJ:  it is not affect function
// spyglass disable_block W240
// SMD: Input '*' declared but not read
// SJ:  Standard Interface. Some inputs may be unused depending on implementation.
  ////////// Pipeline flow-control signals ///////////////////////////////////
  //
  input                        da_holdup,       // not-valid DA stage instruction
  input                        x1_retain,       // 
  input                        x2_retain,       // 
  input                        x3_retain,       // 

  input                        da_valid_r,      // Valid decode-stage instr
  input                        sa_valid_r,      //
  input                        x1_valid_r,      //
  input                        x2_valid_r,      // 
  input                        x3_valid_r,      // 
  input                        ca_valid_r,      // 

  input                        al_pass,         // transfer instr to next stage
  input                        da_pass,         //
  input                        sa_pass,         // 
  input                        x1_pass,         // 
  input                        x2_pass,         // 
  input                        x3_pass,         // 
  input                        ca_pass,         // 

  input                        da_enable,       // 
  input                        sa_enable,       // 
  input                        x1_enable,       // 
  input                        x2_enable,       // 
  input                        x3_enable,       // 
  input                        ca_enable,       // 

  input                        da_kill,         // flush
  input                        sa_kill,         // 
  input                        x1_kill,         // 
  input                        x2_kill,         // 
  input                        x3_kill,         // 
  input                        ca_kill,         //

  input                        x1_no_eval,      // insn at X1 does not evaluate
  input                        x2_predicate_nxt,// X1 Evaluated predicate

  input                        ca_commit,       // IO <= wa_cmt_norm_evt_nxt
  input                        ca_q_cond,       // status of condition code for
                                                //                  <eia_instr>.cc
  input                        ca_predicate_r,  // Conditional instruction state
                                                // predicate at X1

  output                       eia_exu_grad_req,   // Graduation request in ca  
  input                        exu_eia_grad_ack,   // Graduation Acknowledge in ca  
  input      [2:0] exu_eia_grad_tag,   // Graduation buffer tag from exu

  output                       eia_exu_retire_req, // from eia grad buffer arbiter  
  input                        exu_eia_retire_ack, //                               
  output     [2:0] eia_exu_retire_tag, // Graduation buffer tag to exu  

  ////////// Instruction fields from DA-stage instruction to EIA ////////
  //

  input                        al_is_cond_inst, // conditional instruction

  input     [31:27] da_group_code,   // Major group opcode

  input     [21:16] da_dop_code_32,  // Dual-opd opcode   (32-bit)
  input     [5:0] da_sop_code_32,  // Single-opd opcode (32-bit)
  input     [5:0] da_zop_code_32,  // zero-opd opcode   (32-bit)

  input     [20:16] da_dop_code_16,  // Dual-opd opcode   (16-bit)
  input     [23:21] da_sop_code_16,  // Single-opd opcode (16-bit)
  input     [26:24] da_zop_code_16,  // zero-opd opcode   (16-bit)

  input     [4:0]   da_q_field,      // Instruction predicate - validate
  input     [4:0]   sa_q_field,      // Instruction predicate - xflags dep
  input     [4:0]   x1_q_field,      // Instruction predicate - evaluate
  input                        da_f_bit,        // Flag update enable (F bit)
 
  ////////// Register port addresses in DA stage /////////////////////////////
  //
  input                        da_rf_renb0_r,   // Register read enable  0
  input     [5:0]  da_rf_ra0_r,     // Register read address 0
  input                        da_rf_renb0_64_r,

  input                        da_rf_renb1_r,   // Register read enable  1
  input     [5:0]  da_rf_ra1_r,     // Register read address 1
  input                        da_rf_renb1_64_r,


  input                        da_rf_wenb0,     // Register write enable  0  
  input     [5:0]  da_rf_wa0,       // Register write address 0 
  input                        da_rf_wenb0_64,

  input                        da_rf_wenb1,     // Register write enable  1  
  input     [5:0]  da_rf_wa1,       // Register write address 1 
  input                        da_rf_wenb1_64,



  ////////// Operand inputs at SA stage //////////////////////////////////////
  //
  input                        sa_sr_op_r,      // SR instr in SA
  input                        sa_lr_op_r,      // LR instr in SA
  
  input     [31:0]      sa_src_operand_0,// 32-bit source operand 0 
  input     [31:0]      sa_src_operand_1,// 32-bit source operand 1 
  input     [31:0]      x1_src_operand_0_lo,// 32-bit operand 0 low
  input     [31:0]      x1_src_operand_0_hi,// 32-bit operand 0 high
  input     [31:0]      x1_src_operand_1_lo,// 32-bit operand 1 low
  input     [31:0]      x1_src_operand_1_hi,// 32-bit operand 1 high

  ////////// Flag inputs at SA stage /////////////////////////////////////////
  //
  input     [11:8]      x1_src_zncv,     // Bypassed ZNCV flags input
  
  ////////// Result register write interface from Commit stage ///////////////
  //
  input                        wa_rf_wenb0_r,     // validated write enb 0
  input     [5:0]  wa_rf_wa0_r,       // actual write port 0 address
  input     [31:0]      wa_rf_wdata0_lo_r, // actual write data for port 0
  input                        wa_rf_wenb0_64_r,
  input     [31:0]      wa_rf_wdata0_hi_r,

  input                        wa_rf_wenb1_r,     // validated write enb 1
  input     [5:0]  wa_rf_wa1_r,       // actual write port 1 address
  input     [31:0]      wa_rf_wdata1_lo_r, // Second write port data
  input                        wa_rf_wenb1_64_r,
  input     [31:0]      wa_rf_wdata1_hi_r,


  ////////// Pipeline flow-control signals ///////////////////////////////////
  //
  input                        exu_sa_bflags_ready,  // from dep_pipe
  output reg                   eia_sa_hazard,   // Stall at sa stage (mid cycle)

  ////////////////// Credential outputs late in DA stage /////////////////////
  //
  output reg                   eia_da_valid,        // valid eia inst was decoded
  output reg                   eia_da_src64,        // eia inst has 64-bit source opds
  output reg                   eia_da_flag_wen,     // Execute inst defines flags
  output reg                   eia_da_dst_wen,      // Execute inst writes to explicit reg
  output reg                   eia_da_multi_cycle,  // Eia inst is multi-cycle or untimed

  ///////////////// Read data outputs at SA stage ////////////////////////////
  //
  output     [31:0]     eia_sa_rf_rdata0,// Ext. core register on port 0
  output     [31:0]     eia_sa_rf_rdata0_hi,
  output     [31:0]     eia_sa_rf_rdata1,// Ext. core register on port 1
  output     [31:0]     eia_sa_rf_rdata1_hi,

  ////////// No Core Register Credentials in SA stage ///////////
  //
  output                       eia_da_ra0_ext,  // == 1'b0     
  output                       eia_da_ra1_ext,  // == 1'b0     
  output                       eia_da_wa0_ext,  // == 1'b0     
  output                       eia_da_wa1_ext,  // == 1'b0   

  input                        has_dest_cr_is_ext,  // explicit cr dest pending
  input                        sa_dest_cr_is_ext,
  input                        x1_dest_cr_is_ext,
  input                        x2_dest_cr_is_ext,
  input                        x3_dest_cr_is_ext, 
  input                        ca_dest_cr_is_ext,

  input                        ar0_rf_valid_r,
  input                        ar0_rf_wenb1_r,
  input [6:0]     ar0_rf_wa1_r,
  input                        ar0_rf_wenb1_64_r,
  input                        ar0_dest_cr_is_ext,  
  input                        ar1_rf_valid_r,
  input                        ar1_rf_wenb1_r,
  input [6:0]     ar1_rf_wa1_r,
  input                        ar1_rf_wenb1_64_r,
  input                        ar1_dest_cr_is_ext,  
  input                        ar2_rf_valid_r,
  input                        ar2_rf_wenb1_r,
  input [6:0]     ar2_rf_wa1_r,
  input                        ar2_rf_wenb1_64_r,
  input                        ar2_dest_cr_is_ext,  
  input                        ar3_rf_valid_r,
  input                        ar3_rf_wenb1_r,
  input [6:0]     ar3_rf_wa1_r,
  input                        ar3_rf_wenb1_64_r,
  input                        ar3_dest_cr_is_ext,  
  input                        ar4_rf_valid_r,
  input                        ar4_rf_wenb1_r,
  input [6:0]     ar4_rf_wa1_r,
  input                        ar4_rf_wenb1_64_r,
  input                        ar4_dest_cr_is_ext,  
  input                        ar5_rf_valid_r,
  input                        ar5_rf_wenb1_r,
  input [6:0]     ar5_rf_wa1_r,
  input                        ar5_rf_wenb1_64_r,
  input                        ar5_dest_cr_is_ext,  
  input                        ar6_rf_valid_r,
  input                        ar6_rf_wenb1_r,
  input [6:0]     ar6_rf_wa1_r,
  input                        ar6_rf_wenb1_64_r,
  input                        ar6_dest_cr_is_ext,  
  input                        ar7_rf_valid_r,
  input                        ar7_rf_wenb1_r,
  input [6:0]     ar7_rf_wa1_r,
  input                        ar7_rf_wenb1_64_r,
  input                        ar7_dest_cr_is_ext,  

  input                        sa_rf_wenb0_r,     
  input     [5:0]  sa_rf_wa0_r,       
  input                        sa_rf_wenb0_64_r,

  input                        sa_rf_wenb1_r,     
  input     [5:0]  sa_rf_wa1_r,       
  input                        sa_rf_wenb1_64_r,


  input                        x1_rf_wenb0_r,     
  input     [5:0]  x1_rf_wa0_r,       
  input                        x1_rf_wenb0_64_r,

  input                        x1_rf_wenb1_r,     
  input     [5:0]  x1_rf_wa1_r,       
  input                        x1_rf_wenb1_64_r,


  input                        x2_rf_wenb0_r,     
  input     [5:0]  x2_rf_wa0_r,       
  input                        x2_rf_wenb0_64_r,

  input                        x2_rf_wenb1_r,     
  input     [5:0]  x2_rf_wa1_r,       
  input                        x2_rf_wenb1_64_r,


  input                        x3_rf_wenb0_r,     
  input     [5:0]  x3_rf_wa0_r,       
  input                        x3_rf_wenb0_64_r,

  input                        x3_rf_wenb1_r,     
  input     [5:0]  x3_rf_wa1_r,       
  input                        x3_rf_wenb1_64_r,


  input                        ca_rf_wenb0_r,     
  input     [5:0]  ca_rf_wa0_r,       
  input                        ca_rf_wenb0_64_r,

  input                        ca_rf_wenb1_r,     
  input     [5:0]  ca_rf_wa1_r,       
  input                        ca_rf_wenb1_64_r,


  output reg                   eia_da_kernel_instr, // instr needs kernel mode 
  output reg                   eia_da_illegal,      // reports illegal operation    
  output                       eia_x2_is_eia_instr, // x2 stage is eia opcode 
  output                       eia_x2_kernel_cc,    // == 0, no eia cc 
  output                       eia_x2_kernel_cr,    // == 0, no eia cr 
  output     [5:0]             eia_x3_kernel_param, // ECR param for kernel viol

  output reg                   eia_x1_ext_cond,      // EIA extension condition     
  output reg                   eia_ca_ext_cond,      // EIA extension condition     
  output reg                   eia_da_illegal_cond,  // Illegal extension condition

  ////////// x1-stage explicit result from eia pipe //////////////////////////
  //
  output                       eia_exu_x1_eia_op,    // for dep_pipe
  output                       eia_exu_ca_eia_op,    // for dep_pipe
  output reg                   eia_exu_x1_hold,      // for multi-cycle non-blocking
  output reg                   eia_exu_x1_res_valid, // explicit result valid  in x1
  output reg                   eia_exu_x1_fast_op_r, // same as "eia_exu_x1_res_valid"
  output reg [31:0]            eia_exu_x1_res_data,  // explicit result data   in x1
  output reg [31:0]            eia_exu_x1_res_data_hi, // explicit result data in x1
  output reg [3:0]             eia_exu_x1_res_flags, // explicit result bflags in x1

  ////////// sa- and x2-stage stall for blocking instr w/64-bit source ///////
  //
  output reg                   eia_exu_sa_hold,
  output reg                   eia_exu_x2_hold,      // 64-bit blocking instr active

  ////////// ca-stage explicit result from eia pipe //////////////////////////
  //
  output reg                   eia_exu_ca_res_valid, // explicit result valid  in ca
  output reg [31:0]            eia_exu_ca_res_data,  // explicit result data   in ca
  output reg [31:0]            eia_exu_ca_res_data_hi, // explicit result data in ca
  output reg [3:0]             eia_exu_ca_res_flags, // explicit result bflags in ca

  ////////// Post-Commit explicit result from eia pipe /////////
  //


  output     [31:0]            eia_exu_retire_res_data,  // explicit result data   from gb
  output     [3:0]             eia_exu_retire_res_flags, // explicit result bflags from gb


  ////////// Auxiliary interface for extension SR/LR instructions ////////////
  // Stage X3: LR and Credential Check
  //
  input                        aux_eia_ren_r,        // Aux LR/SR request
  input                        aux_read,             // Aux read register (LR)
  input                        aux_write,            // Aux write register (SR)
  input       [31:0] aux_eia_raddr_r,      // Aux address for read/write
  
  output reg  [31:0]    eia_aux_rdata,        // LR data from EIA extension
  output reg                   eia_aux_k_rd,         // Needs kernel read priviege
  output reg                   eia_aux_k_wr,         // Needs kernel write privilege
  output reg                   eia_aux_serial_sr,    // serialize last
  output reg                   eia_aux_strict_sr,    // serialize immediately
  output reg                   eia_aux_illegal,      // Aux operation is illegal
  output reg                   eia_aux_unimpl,       // Aux address not present
  output reg                   eia_aux_stall,        // Stall eia LR/SR at X3

  // Stage WB: SR address and data
  //
  input                        aux_eia_wen_r,        // Aux SR command
  input       [31:0] aux_eia_waddr_r,      // Aux SR address
  input       [31:0]    aux_eia_wdata_r,      // Aux SR data, IO <= wa_sr_data_r
  
// spyglass enable_block W240
  ////////// Aborted EIA instruction not done ////////////////////
  //
  output reg                   eia_exu_idle          // No pending EIA activity including
                                                     // _kill (not tracked by exu_pipe)

);
// leda NTL_CON13C on

wire     [31:0]            eia_exu_retire_res_data_hi; // explicit result data from gb



////////////////////////////////////////////////////////////////
//                                                            //
//   Declarations for instructions and extension registers    //
//                                                            //
////////////////////////////////////////////////////////////////


// Interface signals required by the 'evmww' extension instruction
//
reg                           i_evmww_decode;
wire                          i_evmww_busy;
reg                           i_evmww_commit;
reg                           i_evmww_kill;
reg                           evmww_start_r_64;
reg                           evmww_start_nxt;
reg                           evmww_end;
wire      [63:0]              evmww_res;




wire      [3:0]               evmww_bflags;
wire      [3:0]               evmww_xflags;


// Interface signals required by the 'evmw' extension instruction
//
reg                           i_evmw_decode;
wire                          i_evmw_busy;
reg                           i_evmw_commit;
reg                           i_evmw_kill;
reg                           evmw_start_r_64;
reg                           evmw_start_nxt;
reg                           evmw_end;
wire      [63:0]              evmw_res;




wire      [3:0]               evmw_bflags;
wire      [3:0]               evmw_xflags;


// Interface signals required by the 'evm' extension instruction
//
reg                           i_evm_decode;
wire                          i_evm_busy;
reg                           i_evm_commit;
reg                           i_evm_kill;
reg                           evm_start_r_64;
reg                           evm_start_nxt;
reg                           evm_end;
wire      [63:0]              evm_res;




wire      [3:0]               evm_bflags;
wire      [3:0]               evm_xflags;



// xpu register

reg       [31:0]       xpu_r;
reg       [31:0]       i_xpu_nxt;
// Interface signals required by the XPU aux register
//

// Interface signals required by the 'EVT_CTRL' extension aux register
//
// leda G_521_2_B off
// LMD: Use lowercase letters 
// LJ:  it is generated by APEX
reg                           EVT_CTRL_ar_ren;
reg                           EVT_CTRL_ca_ar_ren_r;
reg                           EVT_CTRL_ca_ar_ren_nxt;
reg                           EVT_CTRL_ar_rd_cmt;
reg                           EVT_CTRL_ar_rd_abort;          
wire     [31:0]         EVT_CTRL_ar_r; 
reg                           EVT_CTRL_ar_wen;
reg      [31:0]         EVT_CTRL_ar_wdata;
// leda G_521_2_B on    
// Interface signals required by the 'EVT_FILTER_LO' extension aux register
//
// leda G_521_2_B off
// LMD: Use lowercase letters 
// LJ:  it is generated by APEX
reg                           EVT_FILTER_LO_ar_ren;
reg                           EVT_FILTER_LO_ca_ar_ren_r;
reg                           EVT_FILTER_LO_ca_ar_ren_nxt;
reg                           EVT_FILTER_LO_ar_rd_cmt;
reg                           EVT_FILTER_LO_ar_rd_abort;          
wire     [31:0]         EVT_FILTER_LO_ar_r; 
reg                           EVT_FILTER_LO_ar_wen;
reg      [31:0]         EVT_FILTER_LO_ar_wdata;
// leda G_521_2_B on    
// Interface signals required by the 'EVT_FILTER_HI' extension aux register
//
// leda G_521_2_B off
// LMD: Use lowercase letters 
// LJ:  it is generated by APEX
reg                           EVT_FILTER_HI_ar_ren;
reg                           EVT_FILTER_HI_ca_ar_ren_r;
reg                           EVT_FILTER_HI_ca_ar_ren_nxt;
reg                           EVT_FILTER_HI_ar_rd_cmt;
reg                           EVT_FILTER_HI_ar_rd_abort;          
wire     [31:0]         EVT_FILTER_HI_ar_r; 
reg                           EVT_FILTER_HI_ar_wen;
reg      [31:0]         EVT_FILTER_HI_ar_wdata;
// leda G_521_2_B on    
// Interface signals required by the 'EVT_CNT_SEL' extension aux register
//
// leda G_521_2_B off
// LMD: Use lowercase letters 
// LJ:  it is generated by APEX
reg                           EVT_CNT_SEL_ar_ren;
reg                           EVT_CNT_SEL_ca_ar_ren_r;
reg                           EVT_CNT_SEL_ca_ar_ren_nxt;
reg                           EVT_CNT_SEL_ar_rd_cmt;
reg                           EVT_CNT_SEL_ar_rd_abort;          
wire     [31:0]         EVT_CNT_SEL_ar_r; 
reg                           EVT_CNT_SEL_ar_wen;
reg      [31:0]         EVT_CNT_SEL_ar_wdata;
// leda G_521_2_B on    
// Interface signals required by the 'EVT_CNT_VAL' extension aux register
//
// leda G_521_2_B off
// LMD: Use lowercase letters 
// LJ:  it is generated by APEX
reg                           EVT_CNT_VAL_ar_ren;
reg                           EVT_CNT_VAL_ca_ar_ren_r;
reg                           EVT_CNT_VAL_ca_ar_ren_nxt;
reg                           EVT_CNT_VAL_ar_rd_cmt;
reg                           EVT_CNT_VAL_ar_rd_abort;          
wire     [31:0]         EVT_CNT_VAL_ar_r; 
reg                           EVT_CNT_VAL_ar_wen;
reg      [31:0]         EVT_CNT_VAL_ar_wdata;
// leda G_521_2_B on    
// Interface signals required by the 'EVT_VM_SEL' extension aux register
//
// leda G_521_2_B off
// LMD: Use lowercase letters 
// LJ:  it is generated by APEX
reg                           EVT_VM_SEL_ar_ren;
reg                           EVT_VM_SEL_ca_ar_ren_r;
reg                           EVT_VM_SEL_ca_ar_ren_nxt;
reg                           EVT_VM_SEL_ar_rd_cmt;
reg                           EVT_VM_SEL_ar_rd_abort;          
wire     [31:0]         EVT_VM_SEL_ar_r; 
reg                           EVT_VM_SEL_ar_wen;
reg      [31:0]         EVT_VM_SEL_ar_wdata;
// leda G_521_2_B on    
// Interface signals required by the 'EVT_VM_MAP' extension aux register
//
// leda G_521_2_B off
// LMD: Use lowercase letters 
// LJ:  it is generated by APEX
reg                           EVT_VM_MAP_ar_ren;
reg                           EVT_VM_MAP_ca_ar_ren_r;
reg                           EVT_VM_MAP_ca_ar_ren_nxt;
reg                           EVT_VM_MAP_ar_rd_cmt;
reg                           EVT_VM_MAP_ar_rd_abort;          
wire     [31:0]         EVT_VM_MAP_ar_r; 
reg                           EVT_VM_MAP_ar_wen;
reg      [31:0]         EVT_VM_MAP_ar_wdata;
// leda G_521_2_B on    
// Interface signals required by the 'EVT_GRP_SEL' extension aux register
//
// leda G_521_2_B off
// LMD: Use lowercase letters 
// LJ:  it is generated by APEX
reg                           EVT_GRP_SEL_ar_ren;
reg                           EVT_GRP_SEL_ca_ar_ren_r;
reg                           EVT_GRP_SEL_ca_ar_ren_nxt;
reg                           EVT_GRP_SEL_ar_rd_cmt;
reg                           EVT_GRP_SEL_ar_rd_abort;          
wire     [31:0]         EVT_GRP_SEL_ar_r; 
reg                           EVT_GRP_SEL_ar_wen;
reg      [31:0]         EVT_GRP_SEL_ar_wdata;
// leda G_521_2_B on    
// Interface signals required by the 'EVT_SID' extension aux register
//
// leda G_521_2_B off
// LMD: Use lowercase letters 
// LJ:  it is generated by APEX
reg                           EVT_SID_ar_ren;
reg                           EVT_SID_ca_ar_ren_r;
reg                           EVT_SID_ca_ar_ren_nxt;
reg                           EVT_SID_ar_rd_cmt;
reg                           EVT_SID_ar_rd_abort;          
wire     [31:0]         EVT_SID_ar_r; 
reg                           EVT_SID_ar_wen;
reg      [31:0]         EVT_SID_ar_wdata;
// leda G_521_2_B on    
// Interface signals required by the 'EVT_SSID' extension aux register
//
// leda G_521_2_B off
// LMD: Use lowercase letters 
// LJ:  it is generated by APEX
reg                           EVT_SSID_ar_ren;
reg                           EVT_SSID_ca_ar_ren_r;
reg                           EVT_SSID_ca_ar_ren_nxt;
reg                           EVT_SSID_ar_rd_cmt;
reg                           EVT_SSID_ar_rd_abort;          
wire     [31:0]         EVT_SSID_ar_r; 
reg                           EVT_SSID_ar_wen;
reg      [31:0]         EVT_SSID_ar_wdata;
// leda G_521_2_B on    
// Interface signals required by the 'EVT_IRQ' extension aux register
//
// leda G_521_2_B off
// LMD: Use lowercase letters 
// LJ:  it is generated by APEX
reg                           EVT_IRQ_ar_ren;
reg                           EVT_IRQ_ca_ar_ren_r;
reg                           EVT_IRQ_ca_ar_ren_nxt;
reg                           EVT_IRQ_ar_rd_cmt;
reg                           EVT_IRQ_ar_rd_abort;          
wire     [31:0]         EVT_IRQ_ar_r; 
reg                           EVT_IRQ_ar_wen;
reg      [31:0]         EVT_IRQ_ar_wdata;
// leda G_521_2_B on    

// Declare modify (dirty) registers to track implicit writes to shadow cr
// per each extension. The corresponding dirty bit is set on an implicit
// write and used to update main cr reg on commit.
// The complete modify register of the extension is zeroed out upon retirement
// or uncommit events for appropriate instructions from the same extension.


// XFLAGS and XPU registers
reg       [3:0]               ar_xflags_r;     // the XFLAGS aux register
reg       [3:0]               i_xflags_nxt;    // next xflags value
reg                           xpu_sr;          // SR to XPU
reg                           i_xflags_sr;     // SR to XFLAGS
reg                           i_xflags_en;     // XFLAGS write enable

reg       [3:0]               wb_res_xflags;   // xflags result of eia instr at wb
////////////////////////////////////////////////////////////////
//                                                            //
//   Declarations for instructions and extension registers    //
//                                                            //
////////////////////////////////////////////////////////////////

reg                           i_valid;        // decoded instruction is valid
reg       [4:0]      i_cycles;       // Number of execution cycles
reg                           i_untimed;      // 0=>fixed-timing, 1=>untimed
reg                           i_blocks;       // 0=>non-blocking, 1=>blocking
reg                           i_src64;        // source operands are: 1=> 64-bit, 0=> are 32-bit
reg                           i_has_dst;      // 1=>writes results, 0=>no data result
reg                           i_fwrite;       // 1=>writes flags, 0=>no write
reg                           i_kernel;       // 1=>inst needs Kernel mode
reg       [7:0]       i_xnum;         // decoded extension number
reg       [1:0]       i_gnum;         // assigned instruction group number
reg       [1:0]               i_xtype;        // three type mode
reg       [1:0]       eia_sa_gnum;    // Registered
reg       [3:0]               i_att;          // instruction implicit rd/wr attributes
reg                           i_att_cr_nocheck;  // Ignore implicit-implicit hazards
reg                           i_has_reg_sets;//define core/aux reg sets
reg       [5:0]               i_sub_opcode;   // sub_opcode field of instr - for group decode
wire                          eia_inst_valid; // deocded instruction is eia
wire                          eia_inst_has_reg_sets;//0:old apex ext, 1: new apex ext
wire                          eia_src64_inst;//0: 32 bit inst, 1: 64 bit inst
// spyglass disable_block W528
// SMD: Variable set but not read
// SJ:  it will be removed by synthesis  
wire                          eia_att_cr_nocheck;
// spyglass enable_block W528





  

  

  


wire     [31:27] da_swap_group_code;   
wire     [21:16] da_swap_dop_code_32;  
wire     [5:0] da_swap_sop_code_32;  
wire     [5:0] da_swap_zop_code_32;  
wire     [20:16] da_swap_dop_code_16;  
wire     [23:21] da_swap_sop_code_16;  
wire     [26:24] da_swap_zop_code_16;  
wire     [4:0]   da_swap_q_field;      
wire                        da_swap_f_bit; 
wire                        da_swap_valid_r;
wire                        da_swap_kill;
// spyglass disable_block W528
// SMD: Variable set but not read
// SJ:  it will be removed by synthesis
assign da_swap_group_code     = da_group_code;   
assign da_swap_dop_code_32    = da_dop_code_32;  
assign da_swap_sop_code_32    = da_sop_code_32;  
assign da_swap_zop_code_32    = da_zop_code_32;  
assign da_swap_dop_code_16    = da_dop_code_16;  
assign da_swap_sop_code_16    = da_sop_code_16;  
assign da_swap_zop_code_16    = da_zop_code_16;  
assign da_swap_q_field        = da_q_field;      
assign da_swap_f_bit          = da_f_bit;
assign da_swap_valid_r        = da_valid_r;
assign da_swap_kill           = da_kill;
// spyglass enable_block W528




//////////////////////////////////////////////////////////////////////////////
// Decode all EIA extension instructions                                    //
//////////////////////////////////////////////////////////////////////////////

// extension and group defines

// leda B_3440 off
// LMD: synthetic defines from user code
// LJ:  unused but useful for enhancements
localparam  EXT_EventManager                      = 1'd0;


localparam  GRP_evmww                             = 2'd0;
localparam  GRP_evmw                              = 2'd1;
localparam  GRP_evm                               = 2'd2;
// leda B_3440 on

// instruction decoder

always @*
begin : eia_decode_PROC

  // Clear all decoder output signals to ensure no latch inference.
  //
  i_valid        = 1'b1;
  i_blocks       = 1'b0;
  i_src64        = 1'b0;
  i_has_dst      = 1'b0;
  i_fwrite       = 1'b0;
  i_kernel       = 1'b0;
  i_cycles       = 5'd1;
  i_untimed      = 1'b0;
  i_xnum         = 8'd0;
  i_gnum         = 2'd0;
  i_xtype        = 2'b0;
  i_sub_opcode   = 6'h0;
  i_att          = 4'h0;
  i_att_cr_nocheck = 1'b0;
  i_has_reg_sets = 1'b0;
  




  
  ////////////////////////////////////////////////////////////////////////////
  // Decode the hierachical operator fields to see if this is
  // a valid EIA instruction, and assert the appropriate set of
  // control signals for the instruction that is decoded.
  //
  case ( da_swap_group_code )

    5'd7:  // decode extensions in 32-bit format group 7
      begin
        i_sub_opcode = da_swap_dop_code_32;
        case ( da_swap_dop_code_32 )

          6'h2f: // all single or zero operand extensions in group 7
            begin
              i_sub_opcode = da_swap_sop_code_32;
            case ( da_swap_sop_code_32 )
              6'h00: // decode instruction 'EVTMASKCHK'
                begin  
                  i_cycles  = 5'd3;
                  i_blocks  = 1'b1;
                  i_untimed = 1'b0;
                  i_src64   = 1'b1;
                  i_has_dst = 1'b1;
                  i_fwrite  = 1'b1;
                  i_xnum    = 8'd0;
                  i_gnum    = GRP_evmww;
                  i_xtype   = 2'd2;
                  i_att     = 4'b0000;
                  i_att_cr_nocheck = 1'b0;
                  i_has_reg_sets = 1'b1;

                end

              6'h01: // decode instruction 'EVTMASKALL'
                begin  
                  i_cycles  = 5'd3;
                  i_blocks  = 1'b1;
                  i_untimed = 1'b0;
                  i_src64   = 1'b1;
                  i_has_dst = 1'b1;
                  i_fwrite  = 1'b1;
                  i_xnum    = 8'd0;
                  i_gnum    = GRP_evmww;
                  i_xtype   = 2'd2;
                  i_att     = 4'b0000;
                  i_att_cr_nocheck = 1'b0;
                  i_has_reg_sets = 1'b1;

                end

              6'h02: // decode instruction 'EVTMASKANY'
                begin  
                  i_cycles  = 5'd3;
                  i_blocks  = 1'b1;
                  i_untimed = 1'b0;
                  i_src64   = 1'b1;
                  i_has_dst = 1'b1;
                  i_fwrite  = 1'b1;
                  i_xnum    = 8'd0;
                  i_gnum    = GRP_evmww;
                  i_xtype   = 2'd2;
                  i_att     = 4'b0000;
                  i_att_cr_nocheck = 1'b0;
                  i_has_reg_sets = 1'b1;

                end

              6'h03: // decode instruction 'EVTMASKDECR'
                begin  
                  i_cycles  = 5'd3;
                  i_blocks  = 1'b1;
                  i_untimed = 1'b0;
                  i_src64   = 1'b1;
                  i_has_dst = 1'b1;
                  i_fwrite  = 1'b1;
                  i_xnum    = 8'd0;
                  i_gnum    = GRP_evmw;
                  i_xtype   = 2'd2;
                  i_att     = 4'b0000;
                  i_att_cr_nocheck = 1'b0;
                  i_has_reg_sets = 1'b1;

                end

              6'h04: // decode instruction 'EVTMASKINCR'
                begin  
                  i_cycles  = 5'd3;
                  i_blocks  = 1'b1;
                  i_untimed = 1'b0;
                  i_src64   = 1'b1;
                  i_has_dst = 1'b1;
                  i_fwrite  = 1'b1;
                  i_xnum    = 8'd0;
                  i_gnum    = GRP_evmw;
                  i_xtype   = 2'd2;
                  i_att     = 4'b0000;
                  i_att_cr_nocheck = 1'b0;
                  i_has_reg_sets = 1'b1;

                end

              6'h05: // decode instruction 'EVTMASKSEND'
                begin  
                  i_cycles  = 5'd3;
                  i_blocks  = 1'b1;
                  i_untimed = 1'b0;
                  i_src64   = 1'b1;
                  i_has_dst = 1'b1;
                  i_fwrite  = 1'b1;
                  i_xnum    = 8'd0;
                  i_gnum    = GRP_evm;
                  i_xtype   = 2'd2;
                  i_att     = 4'b0000;
                  i_att_cr_nocheck = 1'b0;
                  i_has_reg_sets = 1'b1;

                end

              6'h06: // decode instruction 'EVTVMCHK'
                begin  
                  i_cycles  = 5'd3;
                  i_blocks  = 1'b1;
                  i_untimed = 1'b0;
                  i_src64   = 1'b1;
                  i_has_dst = 1'b1;
                  i_fwrite  = 1'b1;
                  i_xnum    = 8'd0;
                  i_gnum    = GRP_evmww;
                  i_xtype   = 2'd2;
                  i_att     = 4'b0000;
                  i_att_cr_nocheck = 1'b0;
                  i_has_reg_sets = 1'b1;
                  i_kernel       = 1'b1;

                end


              6'h3f: // all zero operand extensions in group 7
                begin
                 i_sub_opcode = da_swap_zop_code_32;
                case ( da_swap_zop_code_32 )
                  default: i_valid = 1'b0;
                endcase
                end
              default: i_valid = 1'b0;
            endcase
            end
          default: i_valid = 1'b0;
        endcase
      end

    default: i_valid = 1'b0;
  endcase
  
  eia_da_valid       = i_valid & da_swap_valid_r & ~da_swap_kill;
  eia_da_dst_wen     = i_has_dst;
  eia_da_flag_wen    = i_fwrite & da_swap_f_bit;
  eia_da_multi_cycle = (i_untimed | (i_cycles > 1)) & ~i_blocks ;
  eia_da_src64       = i_src64;

end
 



//////////////////////////////////////////////////////////////////////////////
// Instantiate extension modules                                            //
//////////////////////////////////////////////////////////////////////////////

// declarations for instructions
wire          exu_al_to_da;
wire          exu_da_to_sa;
wire          exu_sa_to_x1;
wire          exu_x1_to_x2;
wire          exu_x2_to_x3;
wire          exu_x3_to_ca;
assign exu_al_to_da =              al_pass & da_enable & ~da_holdup;
assign exu_da_to_sa = da_valid_r & da_pass & sa_enable;
assign exu_sa_to_x1 = sa_valid_r & sa_pass & x1_enable;
assign exu_x1_to_x2 = x1_valid_r & x1_pass & x2_enable & ~x1_retain;
assign exu_x2_to_x3 = x2_valid_r & x2_pass & x3_enable & ~x2_retain;
assign exu_x3_to_ca = x3_valid_r & x3_pass & ca_enable & ~x3_retain;

// declarations for instructions
// spyglass disable_block W528
// SMD: Variable set but not read
// SJ:  it will be removed by synthesis
reg           da_is_cond_inst;     // REG_COND_FMT, instr[5]==0
reg           sa_is_cond_inst;     // status pipeline, required for short eia.cc
reg           x1_is_cond_inst;     //
reg           x2_is_cond_inst;     //
reg           x3_is_cond_inst;     //
reg           ca_is_cond_inst;     //
reg           wa_is_cond_inst;     //
// spyglass enable_block W528
reg           eia_sa_valid;
reg           eia_x1_valid;
reg           eia_x2_valid;
reg           eia_x3_valid;
reg           eia_ca_valid;
reg           eia_wb_valid;
reg           eia_ca_blocking;

reg  [ 5:0]   eia_sa_sub_opcode;   // sub_opcode field of instr - for group decode
reg  [31:0]   x2_src_operand_0_lo;
reg  [31:0]   x2_src_operand_0_hi;
reg  [31:0]   x2_src_operand_1_lo;
reg  [31:0]   x2_src_operand_1_hi; 
wire [ 3:0]   bflags_x2_r;         // registered at X2
reg  [ 3:0]   xflags_x2_r;         // registered at X2
reg  [ 5:0]   eia_x2_sub_opcode;
reg           eia_sa_src64;
reg           eia_x1_src64;
reg           eia_x2_src64;
reg  [ 5:0]   eia_x1_sub_opcode;   // sub_opcode field of instr - for group decode
reg           eia_x2_block64;
reg           eia_sa_dst64;
reg           eia_x1_dst64;
reg           eia_x2_dst64;
reg           eia_x3_dst64;
// spyglass disable_block W528
// SMD: Variable set but not read
// SJ:  it will be removed by synthesis
reg           eia_ca_dst64;
// spyglass enable_block W528
// spyglass disable_block W528
// SMD: Variable set but not read
// SJ:  it will be removed by synthesis
always @(posedge clk_ungated or posedge rst_a)
begin : da_is_cond_inst_PROC
  if (rst_a == 1'b1)
  begin
    da_is_cond_inst <=  1'b0;
  end
  else if (exu_al_to_da)   //  al0 -> da0
  begin
    da_is_cond_inst <=  al_is_cond_inst;
  end
end

always @(posedge clk_ungated or posedge rst_a)              
begin : sa_is_cond_inst_PROC
  if (rst_a == 1'b1)
  begin
    sa_is_cond_inst <=  1'b0;
  end
  else if (exu_da_to_sa)   //  da0 -> sa0
  begin
    sa_is_cond_inst <=  eia_da_valid & da_is_cond_inst;
  end
end

always @(posedge clk_ungated or posedge rst_a)              
begin : x1_is_cond_inst_PROC
  if (rst_a == 1'b1)
  begin
    x1_is_cond_inst <=  1'b0;
  end
  else if (exu_sa_to_x1)   //  sa0 -> x10
  begin
    x1_is_cond_inst <=  eia_sa_valid & sa_is_cond_inst;
  end
end

always @(posedge clk_ungated or posedge rst_a)              
begin : x2_is_cond_inst_PROC
  if (rst_a == 1'b1)
  begin
    x2_is_cond_inst <=  1'b0;
  end
  else if (exu_x1_to_x2)   //  x10 -> x20
  begin
    x2_is_cond_inst <=  eia_x1_valid & x1_is_cond_inst;
  end
end

always @(posedge clk_ungated or posedge rst_a)              
begin : x3_is_cond_inst_PROC
  if (rst_a == 1'b1)
  begin
    x3_is_cond_inst <=  1'b0;
  end
  else if (exu_x2_to_x3)   //  x20 -> x30
  begin
    x3_is_cond_inst <=  eia_x2_valid & x2_is_cond_inst;
  end
end

always @(posedge clk_ungated or posedge rst_a)              
begin : ca_is_cond_inst_PROC
  if (rst_a == 1'b1)
  begin
    ca_is_cond_inst <=  1'b0;
  end
  else if (exu_x3_to_ca)   //  x30 -> ca0
  begin
    ca_is_cond_inst <=  eia_x3_valid & x3_is_cond_inst;
  end
end

wire wa_is_cond_inst_nxt;
assign wa_is_cond_inst_nxt = (ca_commit | ca_kill) ? (eia_ca_valid & eia_ca_blocking & ca_is_cond_inst) : 1'b0;
always @(posedge clk_ungated or posedge rst_a)              
begin : wa_is_cond_inst_PROC
  if (rst_a == 1'b1)
  begin
    wa_is_cond_inst <=  1'b0;
  end
  else
  begin
    wa_is_cond_inst <=  wa_is_cond_inst_nxt;
  end
end
// spyglass enable_block W528

always @(posedge clk_ungated or posedge rst_a)
begin : eia_sa_src64_PROC
  if (rst_a == 1'b1)
  begin
    eia_sa_src64 <=  1'b0;
  end
  else if (exu_da_to_sa)   // pipeline enable da->sa
  begin
    eia_sa_src64 <=  eia_da_src64;
  end
end

always @(posedge clk or posedge rst_a)
begin : eia_x1_src64_PROC
  if (rst_a == 1'b1)
  begin
    eia_x1_src64 <=  1'b0;
  end
  else if (exu_sa_to_x1)   // pipeline enable sa->x1
  begin
    eia_x1_src64 <=  eia_sa_src64;
  end
end

always @(posedge clk or posedge rst_a)
begin : eia_x2_src64_PROC
  if (rst_a == 1'b1)
  begin
    eia_x2_src64 <=  1'b0;
  end
  else if (exu_x1_to_x2)   // pipeline enable x1->x2
  begin
    eia_x2_src64 <=  eia_x1_src64;
  end
end

always @(posedge clk_ungated or posedge rst_a)
begin : sub_opcode_PROC
  if (rst_a == 1'b1)
  begin
   eia_sa_sub_opcode <=  6'h0;
  end
  else if (exu_da_to_sa)   // pipeline enable da->sa
  begin
   eia_sa_sub_opcode <=  i_sub_opcode;
  end
end

always @(posedge clk or posedge rst_a)
begin : eia_x1_sub_opcode_PROC
  if (rst_a == 1'b1)
  begin
   eia_x1_sub_opcode <=  6'h0;
  end
  else if (exu_sa_to_x1)   // pipeline enable sa->x1
  begin
   eia_x1_sub_opcode <=  eia_sa_sub_opcode;
  end
end

assign   bflags_x2_r      = x1_src_zncv;
always @(posedge clk or posedge rst_a)
begin : eia_x2_sub_opcode_PROC
  if (rst_a == 1'b1)
  begin
   eia_x2_sub_opcode   <=  6'h0;
   xflags_x2_r         <=  4'h0;
  end
  else if (exu_x1_to_x2)   // pipeline enable sa->x1
  begin
   eia_x2_sub_opcode   <= eia_x1_sub_opcode;
   xflags_x2_r         <= ar_xflags_r;
  end
end


wire eia_sa_dst64_nxt;
assign eia_sa_dst64_nxt = 1'b0
                      | da_rf_wenb0_64
                      | da_rf_wenb1_64
                         ;

always @(posedge clk_ungated or posedge rst_a)
begin : eia_sa_dst64_PROC
  if (rst_a == 1'b1)
  begin
    eia_sa_dst64 <=  1'b0;
  end
  else if (exu_da_to_sa)   // pipeline enable da->sa
  begin
    eia_sa_dst64 <=  eia_sa_dst64_nxt  ;
  end
end

always @(posedge clk or posedge rst_a)
begin : eia_x1_dst64_PROC
  if (rst_a == 1'b1)
  begin
    eia_x1_dst64 <=  1'b0;
  end
  else if (exu_sa_to_x1)   // pipeline enable sa->x1
  begin
    eia_x1_dst64 <=  eia_sa_dst64;
  end
end

always @(posedge clk or posedge rst_a)
begin : eia_x2_dst64_PROC
  if (rst_a == 1'b1)
  begin
    eia_x2_dst64 <=  1'b0;
  end
  else if (exu_x1_to_x2)   // pipeline enable x1->x2
  begin
    eia_x2_dst64 <=  eia_x1_dst64;
  end
end

always @(posedge clk or posedge rst_a)
begin : eia_x3_dst64_PROC
  if (rst_a == 1'b1)
  begin
    eia_x3_dst64 <=  1'b0;
  end
  else if (exu_x2_to_x3)   // pipeline enable x2->x3
  begin
    eia_x3_dst64 <=  eia_x2_dst64;
  end
end
// spyglass disable_block W528
// SMD: Variable set but not read
// SJ:  it will be removed by synthesis
always @(posedge clk or posedge rst_a)
begin : eia_ca_dst64_PROC
  if (rst_a == 1'b1)
  begin
    eia_ca_dst64 <=  1'b0;
  end
  else if (exu_x3_to_ca)   // pipeline enable x3->ca
  begin
    eia_ca_dst64 <=  eia_x3_dst64;
  end
end
// spyglass enable_block W528


// VPOST OFF

always @(posedge clk or posedge rst_a)
begin : type_2_64_operand_shift_PROC
  if (rst_a == 1'b1)
  begin

    evmww_start_r_64 <= 1'b0; 
    evmw_start_r_64 <= 1'b0; 
    evm_start_r_64 <= 1'b0; 
    x2_src_operand_0_lo <=  32'h0;
    x2_src_operand_0_hi <=  32'h0;
    x2_src_operand_1_lo <=  32'h0;
    x2_src_operand_1_hi <=  32'h0;
  end
  else if (exu_x1_to_x2 && eia_x1_valid && ~x1_kill)   // pipeline enable x1->x2
  begin
    evmww_start_r_64 <= evmww_start_nxt; 
    evmw_start_r_64 <= evmw_start_nxt; 
    evm_start_r_64 <= evm_start_nxt; 
    x2_src_operand_0_lo <=  x1_src_operand_0_lo;
    x2_src_operand_0_hi <=  x1_src_operand_0_hi;
    x2_src_operand_1_lo <=  x1_src_operand_1_lo;
    x2_src_operand_1_hi <=  x1_src_operand_1_hi;
  end
  else
  begin
    evmww_start_r_64 <= 1'b0; 
    evmw_start_r_64 <= 1'b0; 
    evm_start_r_64 <= 1'b0; 
  end
end
// VPOST ON
// Instantiating wrapper module for 'EventManager' user extension
//

npuarc_uxEventManager u_uxEventManager (
  .clk (clk),
  .clk_ungated (clk_ungated),
  .sub_opcode_64 (eia_x2_sub_opcode),
  .source1_64 ({x2_src_operand_0_hi, x2_src_operand_0_lo}),
  .source2_64 ({x2_src_operand_1_hi, x2_src_operand_1_lo}),  
  .sub_opcode_64_nxt (eia_x1_sub_opcode),
  .source1_64_nxt ({x1_src_operand_0_hi, x1_src_operand_0_lo}),
  .source2_64_nxt ({x1_src_operand_1_hi, x1_src_operand_1_lo}),
  .bflags_r_64 (bflags_x2_r),
  .xflags_r_64 (xflags_x2_r),
  .evm_event_a (EventManager_evm_event_a),    
  .evm_wakeup (EventManager_evm_wakeup),    
  .evm_sleep (EventManager_evm_sleep),    
  .evm_send (EventManager_evm_send),    
  .vm_grp0_sid (EventManager_vm_grp0_sid),    
  .vm_grp0_ssid (EventManager_vm_grp0_ssid),    
  .vm_grp1_sid (EventManager_vm_grp1_sid),    
  .vm_grp1_ssid (EventManager_vm_grp1_ssid),    
  .vm_grp2_sid (EventManager_vm_grp2_sid),    
  .vm_grp3_sid (EventManager_vm_grp3_sid),    
  .vm_grp2_ssid (EventManager_vm_grp2_ssid),    
  .vm_grp3_ssid (EventManager_vm_grp3_ssid),    
  .evt_vm_irq (EventManager_evt_vm_irq),    
  .evt_vm_sel (EventManager_evt_vm_sel),    
  .evmww_start (evmww_start_r_64 && ~x2_kill),      
  .evmww_start_nxt (evmww_start_nxt),      
  .evmww_decode (i_evmww_decode),
  .evmww_commit (i_evmww_commit),
  .evmww_kill   (i_evmww_kill),
  .evmww_busy   (i_evmww_busy),
  .evmww_end (evmww_end),
  .evmww_stall  (1'b0),
  .evmww_res (evmww_res),
  .evmww_bflags (evmww_bflags),
  .evmww_xflags (evmww_xflags),
  .evmw_start (evmw_start_r_64 && ~x2_kill),      
  .evmw_start_nxt (evmw_start_nxt),      
  .evmw_decode (i_evmw_decode),
  .evmw_commit (i_evmw_commit),
  .evmw_kill   (i_evmw_kill),
  .evmw_busy   (i_evmw_busy),
  .evmw_end (evmw_end),
  .evmw_stall  (1'b0),
  .evmw_res (evmw_res),
  .evmw_bflags (evmw_bflags),
  .evmw_xflags (evmw_xflags),
  .evm_start (evm_start_r_64 && ~x2_kill),      
  .evm_start_nxt (evm_start_nxt),      
  .evm_decode (i_evm_decode),
  .evm_commit (i_evm_commit),
  .evm_kill   (i_evm_kill),
  .evm_busy   (i_evm_busy),
  .evm_end (evm_end),
  .evm_stall  (1'b0),
  .evm_res (evm_res),
  .evm_bflags (evm_bflags),
  .evm_xflags (evm_xflags),
  .EVT_CTRL_ar_rdata    (EVT_CTRL_ar_r),   // user-defined bcr
  .EVT_CTRL_ar_ren      (EVT_CTRL_ar_ren),
  .EVT_CTRL_ar_rd_cmt   (EVT_CTRL_ar_rd_cmt),
  .EVT_CTRL_ar_rd_abort (EVT_CTRL_ar_rd_abort), 
  .EVT_CTRL_ar_wen (EVT_CTRL_ar_wen),
  .EVT_CTRL_ar_wdata (EVT_CTRL_ar_wdata),
  .EVT_FILTER_LO_ar_rdata    (EVT_FILTER_LO_ar_r),   // user-defined bcr
  .EVT_FILTER_LO_ar_ren      (EVT_FILTER_LO_ar_ren),
  .EVT_FILTER_LO_ar_rd_cmt   (EVT_FILTER_LO_ar_rd_cmt),
  .EVT_FILTER_LO_ar_rd_abort (EVT_FILTER_LO_ar_rd_abort), 
  .EVT_FILTER_LO_ar_wen (EVT_FILTER_LO_ar_wen),
  .EVT_FILTER_LO_ar_wdata (EVT_FILTER_LO_ar_wdata),
  .EVT_FILTER_HI_ar_rdata    (EVT_FILTER_HI_ar_r),   // user-defined bcr
  .EVT_FILTER_HI_ar_ren      (EVT_FILTER_HI_ar_ren),
  .EVT_FILTER_HI_ar_rd_cmt   (EVT_FILTER_HI_ar_rd_cmt),
  .EVT_FILTER_HI_ar_rd_abort (EVT_FILTER_HI_ar_rd_abort), 
  .EVT_FILTER_HI_ar_wen (EVT_FILTER_HI_ar_wen),
  .EVT_FILTER_HI_ar_wdata (EVT_FILTER_HI_ar_wdata),
  .EVT_CNT_SEL_ar_rdata    (EVT_CNT_SEL_ar_r),   // user-defined bcr
  .EVT_CNT_SEL_ar_ren      (EVT_CNT_SEL_ar_ren),
  .EVT_CNT_SEL_ar_rd_cmt   (EVT_CNT_SEL_ar_rd_cmt),
  .EVT_CNT_SEL_ar_rd_abort (EVT_CNT_SEL_ar_rd_abort), 
  .EVT_CNT_SEL_ar_wen (EVT_CNT_SEL_ar_wen),
  .EVT_CNT_SEL_ar_wdata (EVT_CNT_SEL_ar_wdata),
  .EVT_CNT_VAL_ar_rdata    (EVT_CNT_VAL_ar_r),   // user-defined bcr
  .EVT_CNT_VAL_ar_ren      (EVT_CNT_VAL_ar_ren),
  .EVT_CNT_VAL_ar_rd_cmt   (EVT_CNT_VAL_ar_rd_cmt),
  .EVT_CNT_VAL_ar_rd_abort (EVT_CNT_VAL_ar_rd_abort), 
  .EVT_CNT_VAL_ar_wen (EVT_CNT_VAL_ar_wen),
  .EVT_CNT_VAL_ar_wdata (EVT_CNT_VAL_ar_wdata),
  .EVT_VM_SEL_ar_rdata    (EVT_VM_SEL_ar_r),   // user-defined bcr
  .EVT_VM_SEL_ar_ren      (EVT_VM_SEL_ar_ren),
  .EVT_VM_SEL_ar_rd_cmt   (EVT_VM_SEL_ar_rd_cmt),
  .EVT_VM_SEL_ar_rd_abort (EVT_VM_SEL_ar_rd_abort), 
  .EVT_VM_SEL_ar_wen (EVT_VM_SEL_ar_wen),
  .EVT_VM_SEL_ar_wdata (EVT_VM_SEL_ar_wdata),
  .EVT_VM_MAP_ar_rdata    (EVT_VM_MAP_ar_r),   // user-defined bcr
  .EVT_VM_MAP_ar_ren      (EVT_VM_MAP_ar_ren),
  .EVT_VM_MAP_ar_rd_cmt   (EVT_VM_MAP_ar_rd_cmt),
  .EVT_VM_MAP_ar_rd_abort (EVT_VM_MAP_ar_rd_abort), 
  .EVT_VM_MAP_ar_wen (EVT_VM_MAP_ar_wen),
  .EVT_VM_MAP_ar_wdata (EVT_VM_MAP_ar_wdata),
  .EVT_GRP_SEL_ar_rdata    (EVT_GRP_SEL_ar_r),   // user-defined bcr
  .EVT_GRP_SEL_ar_ren      (EVT_GRP_SEL_ar_ren),
  .EVT_GRP_SEL_ar_rd_cmt   (EVT_GRP_SEL_ar_rd_cmt),
  .EVT_GRP_SEL_ar_rd_abort (EVT_GRP_SEL_ar_rd_abort), 
  .EVT_GRP_SEL_ar_wen (EVT_GRP_SEL_ar_wen),
  .EVT_GRP_SEL_ar_wdata (EVT_GRP_SEL_ar_wdata),
  .EVT_SID_ar_rdata    (EVT_SID_ar_r),   // user-defined bcr
  .EVT_SID_ar_ren      (EVT_SID_ar_ren),
  .EVT_SID_ar_rd_cmt   (EVT_SID_ar_rd_cmt),
  .EVT_SID_ar_rd_abort (EVT_SID_ar_rd_abort), 
  .EVT_SID_ar_wen (EVT_SID_ar_wen),
  .EVT_SID_ar_wdata (EVT_SID_ar_wdata),
  .EVT_SSID_ar_rdata    (EVT_SSID_ar_r),   // user-defined bcr
  .EVT_SSID_ar_ren      (EVT_SSID_ar_ren),
  .EVT_SSID_ar_rd_cmt   (EVT_SSID_ar_rd_cmt),
  .EVT_SSID_ar_rd_abort (EVT_SSID_ar_rd_abort), 
  .EVT_SSID_ar_wen (EVT_SSID_ar_wen),
  .EVT_SSID_ar_wdata (EVT_SSID_ar_wdata),
  .EVT_IRQ_ar_rdata    (EVT_IRQ_ar_r),   // user-defined bcr
  .EVT_IRQ_ar_ren      (EVT_IRQ_ar_ren),
  .EVT_IRQ_ar_rd_cmt   (EVT_IRQ_ar_rd_cmt),
  .EVT_IRQ_ar_rd_abort (EVT_IRQ_ar_rd_abort), 
  .EVT_IRQ_ar_wen (EVT_IRQ_ar_wen),
  .EVT_IRQ_ar_wdata (EVT_IRQ_ar_wdata),
  .rst_a (rst_a)
);




//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                     Extension Control Pipeline logic                     //
//                                                                          //
// Role of pipe control logic is to keep track of issued user instructions  //
// in two aspects:                                                          //
//  (1) progress in its user-defined pipeline, including count and stalls.  //
//  (2) progress of the instruction in the exu_pipe, including stall, kill, //
//      commit and retirement, including post-commit logic.                 //
//                                                                          //
// Instructions progress through the exu_pipe until reaching commit stage.  // 
// If instruction is completely done then it will commit and retire at the  //
// same time, otherwise the eia_pipe logic would resuest a graduation tag   //
// from exu and allocate a local (in eia_pipe) graduation buffer for it, so //
// that all the handling data of the specific eia instruction is kept and   //
// the instruction can be monitored just as in its pre-commit state.        //
//                                                                          //
// The eia_pipe includes four local graduation buffers if any of the eia    //
// instructions is longer than 4 cycles or is self-timed.                   //
// The data in this buffer complements the data in the exu grad buffer that //
// was also allocated to the same instruction by the exu logic.             //
// The synchronization of post-commit instructions between eia_pipe and exu //
// logic is achieved through the graduation tag that was issued for the     //
// instruction at the commit stage.                                         //
//                                                                          //
// The eia_pipe 8 stage deep at most: 4 stages overlap x1 through CA and 4  //
// optional stages can keep post-commit instructions.                       //
// It is important to understand that only the in-flight instructions are   //
// tracked and analyzed to determine all dependencies in regard to other    //
// instructions, which may be (1) in exu or (2) other eia extensions or     //
// (3) in the same eia extension.                                           //
// The state of each individual instruction pipe can be re-constructed from //
// the tracking information in this 8-stage pipeline.                       //
//                                                                          //
// Stalls are eliminated at the issue point for all timed instructions.     //
// Untimed instructions must support a stall input from eia_pipe. This      //
// only occurs when the untimed instruction is done but cannot retire.      //
//                                                                          //
// Result Pipeline collects the results from in-flight instructions that    //
// have not reached the exu commit stage. The results are not committed to  //
// the state of the machine until actual retirement.                        //
// Note that 1-cycle and blocking instructions are held in X1 and merge the //
// explicit results and flags to the exu datapath early. The exu can bypass //
// these speculative results to following instructions prior to the actual  //
// retirement of the eia instruction.                                       //
// Implicit results are kept in shadow registers until actual retirement.   //
// Exclusive access to the shadow registers of an extension is controlled   //
// by decoded (user-defined) attributes of each eia instruction.            //
//                                                                          //
// The effect of stalled issue due to implicit hazards are magnified by the //
// depth of the exu (or user-defined instruction) pipeline.                 //
// Careful consideration of these stalls is required to achieve optimal eia //
// performance.                                                             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                       Declare EXU Tracking Buffer                        //
//                                                                          //
// This logic keeps track of eia instructions against each exu stage.       //
// Instructions are issued at SA and bacome active in X1.                   //
// Single cycle and Blocking instructions are issued a stall in X1 until    //
// they are done. After finishing, the explicit results are merged into the //
// exu datapath and the instruction moves forward in the EXU pipe until the //
// commit stage. The detailed data is retained in the tracking buffer.      //
// Other non-blocking instructions move in the pipe until their results are //
// complete. Explicit results are merged into the eia Result Pipe and are   //
// maintained until the commit stage, at which time the results are merged  //
// into the exu datapath.                                                   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

  

  


wire     [1:0]           eia_da_xtype   =  i_xtype;
wire     [1:0]   eia_da_gnum    =  i_gnum;   
wire                     eia_da_is_1cyc =  eia_da_valid &
                                           (~i_untimed & (i_cycles == 1) | i_blocks)
                                           & ~(i_src64)
                                           ;

wire    [4:0]   eia_da_cnt     =  i_untimed ? 0 : i_cycles;
wire                     eia_da_untimed =  i_untimed;
wire                     eia_da_has_dst =  i_has_dst;
wire                     eia_da_has_flg =  eia_da_flag_wen;
wire       [3:0]         eia_da_att     =  i_att;
wire                     eia_da_att_cr_nocheck = i_att_cr_nocheck;
wire                     eia_da_has_reg_sets = i_has_reg_sets;

//  valid eia instruction in slot

// defined earlier
assign eia_exu_x1_eia_op = eia_x1_valid;
assign eia_exu_ca_eia_op = eia_ca_valid;

reg                      eia_inst_x1_start;
reg                      eia_inst_x2_start;

// owner extension type:  1 = HS (full featured), 0 = EM (compatibility mode)

reg      [1:0]           eia_sa_xtype;
reg      [1:0]           eia_x1_xtype;
reg      [1:0]           eia_x2_xtype;
reg      [1:0]           eia_x3_xtype;
reg      [1:0]           eia_ca_xtype;
reg      [1:0]           eia_wb_xtype;

// extension identifier

reg    [7:0]     eia_sa_xnum;
reg    [7:0]     eia_x1_xnum;
reg    [7:0]     eia_x2_xnum;
reg    [7:0]     eia_x3_xnum;
reg    [7:0]     eia_ca_xnum;
reg    [7:0]     eia_wb_xnum;

// instruction group (pipe) identifier

reg    [1:0]     eia_x1_gnum;
reg    [1:0]     eia_x2_gnum;
reg    [1:0]     eia_x3_gnum;
reg    [1:0]     eia_ca_gnum;
reg    [1:0]     eia_wb_gnum;

// instruction "opcode" for decoding in multi-instruction group
// reg    [7:0]             eia_sa_inum;   // i_inum at da, registered
 
// Instruction completed (done from untimed or count zero)
// Data and flags results were copied to holding registers

reg                      eia_x1_done;
reg                      eia_x2_done;
reg                      eia_x3_done;
reg                      eia_ca_done;

reg                      eia_sa_src64_inst;
reg                      eia_x1_src64_inst;
reg                      eia_x2_src64_inst;
reg                      eia_x3_src64_inst;
reg                      eia_ca_src64_inst;

// instruction aborted flag
// type 0: _kill signaled at commit
// type 1: tracked until done, results ignored

reg                      eia_x1_kill;
reg                      eia_x2_kill;
reg                      eia_x3_kill;
reg                      eia_ca_kill;
reg                      eia_wb_kill;      // needed for graceful kill

// Instruction results expected to merge into exu data path (and bypass) in X1
// Inlcudes all 1-cycle instructions and all blocking instructions

reg                      eia_sa_is_1cyc;
reg                      eia_x1_is_1cyc;

reg                      eia_sa_blocking;
reg                      eia_x1_blocking;
reg                      eia_x2_blocking;
reg                      eia_x3_blocking;
// reg                      eia_ca_blocking;
reg                      eia_wb_blocking;

// Instruction has 32-bit result

reg                      eia_sa_has_dst;
reg                      eia_x1_has_dst;
reg                      eia_x2_has_dst;
reg                      eia_x3_has_dst;
reg                      eia_ca_has_dst;

// attribute to supress implicit result if condition (of eia_instr.cc) is false

reg                      eia_wb_q_cond;

// Instruction has 4-bit flags

reg                      eia_sa_has_flg;
reg                      eia_x1_has_flg;
reg                      eia_x2_has_flg;
reg                      eia_x3_has_flg;
reg                      eia_ca_has_flg;
reg                      eia_wb_has_flg;

// implicit attributes:  {wr_cr, rd_cr, wr_ar, rd_ar}

reg    [3:0]             eia_sa_att;
reg                      eia_sa_att_cr_nocheck;
reg    [3:0]             eia_x1_att;
reg    [3:0]             eia_x2_att;
reg    [3:0]             eia_x3_att;
reg    [3:0]             eia_ca_att;
reg    [3:0]             eia_wb_att;   // needed for hazard resolution
reg                      eia_sa_has_reg_sets;
reg                      eia_x1_has_reg_sets;
reg                      eia_x2_has_reg_sets;
reg                      eia_x3_has_reg_sets;
reg                      eia_ca_has_reg_sets;
reg                      eia_wb_has_reg_sets;

// instruction control type

reg                      eia_sa_untimed;
reg                      eia_x1_untimed;
reg                      eia_x2_untimed;
reg                      eia_x3_untimed;
reg                      eia_ca_untimed;

// count for (eia_xx_untimed == 1'b0)

reg   [4:0]      eia_sa_cnt;
reg   [4:0]      eia_x1_cnt;
reg   [4:0]      eia_x2_cnt;
reg   [4:0]      eia_x3_cnt;
reg   [4:0]      eia_ca_cnt;

// Place holder for 32-bit result

reg    [31:0]            eia_x1_res_data;
reg    [31:0]            eia_x2_res_data;
reg    [31:0]            eia_x3_res_data;
reg    [31:0]            eia_ca_res_data;
reg    [31:0]            eia_x1_res_data_hi;
reg    [31:0]            eia_x2_res_data_hi;
reg    [31:0]            eia_x3_res_data_hi;
reg    [31:0]            eia_ca_res_data_hi;

// Place holder for 4-bit flags

reg    [3:0]             eia_x1_res_flags;
reg    [3:0]             eia_x2_res_flags;
reg    [3:0]             eia_x3_res_flags;
reg    [3:0]             eia_ca_res_flags;

// Place holder for 4-bit xflags

reg    [3:0]             eia_x1_res_xflags;
reg    [3:0]             eia_x2_res_xflags;
reg    [3:0]             eia_x3_res_xflags;
reg    [3:0]             eia_ca_res_xflags;

reg    [3:0]             eia_x1_res_xflags_pre;  // unregistered
reg    [3:0]             eia_x2_res_xflags_pre;
reg    [3:0]             eia_x3_res_xflags_pre;
reg    [3:0]             eia_ca_res_xflags_pre;



always @(*)
begin :  eia_exu_idle_9_PROC
   eia_exu_idle  = ~( eia_x1_valid |
                      eia_x2_valid |
                      eia_x3_valid |
                      eia_ca_valid |
                      eia_wb_valid
                    );
end



// leda W71 off
// LMD: Case statement without default clause and not all cases are covered
// LJ:  all the register has a initial value
// spyglass disable_block W528
// SMD: Variable set but not read
// SJ:  it will be removed by synthesis
always @*
begin: select_aux_result_PROC 
end
// leda W71 on
// spyglass enable_block W528




wire exu_ca_commit = ca_valid_r & ca_commit;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                    exu_pipe lock-step staging logic                      //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg  eia_x2_end;
reg  eia_x3_end;
reg  eia_ca_end;
assign exu_ca_to_wb  = exu_ca_commit  & ca_q_cond &
                      (eia_ca_done | eia_ca_end) &
                     ~(exu_eia_grad_ack & eia_exu_grad_req);
wire eia_ca_status_commit = eia_ca_valid & exu_ca_commit & ca_q_cond;   // status signal to ux logic
wire eia_ca_false         = eia_ca_valid & exu_ca_commit & (~ca_q_cond);//false condition

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                        exu_pipe kill staging logic                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// This logic is required to move killed instructions in the eia_pipe without
// the equivalent instruction in exu_pipe.
// Special care is taken for killed instructions with non-killed eia instruction
// ahead of them in the eia_pipe (and exu_pipe). The retirement point to grad
// buffer in eia_pipe is only from the ca staging registers. Killed eia instructions
// cannot move forward if a non-killed instruction blocks them but exu may issue
// more eia instructions into the bubbles. This is blocked at sa with a kill hazard.

reg   eia_x1_to_x2;
reg   eia_x2_to_x3;
reg   eia_x3_to_ca;
reg   eia_ca_to_wb_killed;
reg   eia_ca_status_kill;
  
always @ (*)
begin :   eia_inst_kill_staging_PROC
  eia_ca_status_kill  =  eia_ca_valid &
                         (ca_kill | eia_ca_kill) |
                         eia_ca_false;// status signal to ux logic


  eia_ca_to_wb_killed =
                  eia_ca_status_kill  &  // ~ca_pred for state transition
                  (eia_ca_end  | eia_ca_done);
                 
                 
  
  eia_x3_to_ca =    eia_x3_valid & (                           // eia instr in x3
                    (eia_x3_kill) &
                    (~eia_ca_valid | exu_ca_commit | ca_kill)
                  | (~eia_x3_kill) &
                    ~x3_retain &
                    (~ca_valid_r | exu_ca_commit | ca_kill)
                                   ); 
                 
  eia_x2_to_x3 =    eia_x2_valid & (                           // eia instr in x2
                    (eia_x2_kill) &
                    (~eia_x3_valid | exu_x3_to_ca | x3_kill)
                  | (~eia_x2_kill) &
                    ~x2_retain &
                    (~x3_valid_r | exu_x3_to_ca | x3_kill)  
                                   );
                 
   eia_x1_to_x2 =    eia_x1_valid & (                           // eia instr in x1
                    (eia_x1_kill) &
                    (~eia_x2_valid | exu_x2_to_x3 | x2_kill)
                  | (~eia_x1_kill) &
                    ~x1_retain &
                    (~x2_valid_r | exu_x2_to_x3 | x2_kill)
                                   ); 

end

///
///
///
///
///
// DA to SA logic is distributed due to hazard logic
// Most instruction information is handled here

  

  

reg          eia_sa_valid_nxt;
reg          eia_sa_src64_inst_nxt;
reg [1:0]    eia_sa_xtype_nxt;  
reg [7:0] eia_sa_xnum_nxt;
reg [1:0] eia_sa_gnum_nxt;
reg          eia_sa_is_1cyc_nxt; 
reg          eia_sa_blocking_nxt; 
reg          eia_sa_has_dst_nxt; 
reg          eia_sa_has_flg_nxt; 
reg  [3:0]   eia_sa_att_nxt;
reg          eia_sa_has_reg_sets_nxt;
reg          eia_sa_att_cr_nocheck_nxt;
reg          eia_sa_untimed_nxt; 
reg   [4:0]     eia_sa_cnt_nxt; 

// logic for valid - active at any clock

always@(*)
begin : eia_sa_valid_nxt_PROC
  if (exu_da_to_sa)   // pipeline enable da->sa
    eia_sa_valid_nxt   =  eia_da_valid & ~da_swap_kill;  // _kill invalidates the instr
  else if (exu_sa_to_x1)
    eia_sa_valid_nxt   =  1'b0;
  else                                              // stall at sa
    eia_sa_valid_nxt   =  eia_sa_valid & ~sa_kill;  // _kill invalidates the instr, it
end                                                 // will never dispatch to user_pipe

// clock enable for valid

wire da_to_sa_proc_0_cg0 = exu_da_to_sa | exu_sa_to_x1 | eia_sa_valid;

// register for valid

always @(posedge clk_ungated or posedge rst_a)
begin : da_to_sa_valid_PROC
  if (rst_a == 1'b1)
    eia_sa_valid   <=  1'b0;
  else if (da_to_sa_proc_0_cg0)
    eia_sa_valid   <= eia_sa_valid_nxt;  
end

// clock enable for all signals other than valid

wire da_to_sa_proc_1_cg0 = exu_da_to_sa | exu_sa_to_x1;

// logic for all signals other than valid

always@(*)
begin : da_to_sa_9_PROC
  if (exu_da_to_sa)                                 // pipeline enable da->sa
  begin
    eia_sa_xtype_nxt    =  eia_da_xtype;
    eia_sa_src64_inst_nxt = i_src64;
    eia_sa_xnum_nxt     =  i_xnum;
    eia_sa_gnum_nxt     =  eia_da_gnum;
    eia_sa_is_1cyc_nxt  =  eia_da_is_1cyc;
    eia_sa_blocking_nxt =  i_blocks;
    eia_sa_has_dst_nxt  =  eia_da_has_dst;
    eia_sa_has_flg_nxt  =  eia_da_has_flg;
    eia_sa_att_nxt      =  eia_da_att;
    eia_sa_has_reg_sets_nxt = eia_da_has_reg_sets;
    eia_sa_att_cr_nocheck_nxt = eia_da_att_cr_nocheck;
    eia_sa_untimed_nxt  =  eia_da_untimed;
    eia_sa_cnt_nxt      =  eia_da_cnt;
  

  
  end
  else                                              // if (exu_sa_to_x1)
  begin
    eia_sa_xtype_nxt    = 2'd0;
    eia_sa_src64_inst_nxt = 1'b0;
    eia_sa_xnum_nxt     =  8'd0;
    eia_sa_gnum_nxt     =  2'd0;
    eia_sa_is_1cyc_nxt  =  1'b0;
    eia_sa_blocking_nxt =  1'b0;
    eia_sa_has_dst_nxt  =  1'b0;
    eia_sa_has_flg_nxt  =  1'b0;
    eia_sa_att_nxt      =  4'h0;
    eia_sa_has_reg_sets_nxt = 1'b0;
    eia_sa_att_cr_nocheck_nxt = 1'b0;
    eia_sa_untimed_nxt  =  1'b0;
    eia_sa_cnt_nxt      =  5'h0;
  

  
  end
end

// registers for all signals other than valid

always @(posedge clk_ungated or posedge rst_a)
begin : da_to_sa_other_than_valid_PROC
  if (rst_a == 1'b1)
  begin
    eia_sa_xtype    <= 2'd0;
    eia_sa_src64_inst <= 1'b0;
    eia_sa_xnum     <= 8'd0;
    eia_sa_gnum     <= 2'd0;
    eia_sa_is_1cyc  <=  1'b0;
    eia_sa_blocking <=  1'b0;
    eia_sa_has_dst  <=  1'b0;
    eia_sa_has_flg  <=  1'b0;
    eia_sa_att      <=  4'h0;
    eia_sa_has_reg_sets <= 1'b0;
    eia_sa_att_cr_nocheck <= 1'b0;    
    eia_sa_untimed  <=  1'b0;
    eia_sa_cnt      <=  5'h0;
  

  
  end
  else if (da_to_sa_proc_1_cg0)
  begin
    eia_sa_xtype    <= eia_sa_xtype_nxt; 
    eia_sa_src64_inst <= eia_sa_src64_inst_nxt;
    eia_sa_xnum     <= eia_sa_xnum_nxt;   
    eia_sa_gnum     <= eia_sa_gnum_nxt;   
    eia_sa_is_1cyc  <= eia_sa_is_1cyc_nxt;
    eia_sa_blocking <= eia_sa_blocking_nxt;
    eia_sa_has_dst  <= eia_sa_has_dst_nxt;
    eia_sa_has_flg  <= eia_sa_has_flg_nxt;
    eia_sa_att      <= eia_sa_att_nxt;  
    eia_sa_has_reg_sets <= eia_sa_has_reg_sets_nxt;
    eia_sa_att_cr_nocheck <= eia_sa_att_cr_nocheck_nxt;    
    eia_sa_untimed  <= eia_sa_untimed_nxt;
    eia_sa_cnt      <= eia_sa_cnt_nxt;  
  

  
  end
end

// Dispatch candidate instruction to target <instr_group> pipe

reg   eia_instr_32_sa_start_valid;
reg   eia_instr_64_x1_start_valid;

    

always @ (*)
begin :   eia_inst_dispatch_PROC


  eia_instr_32_sa_start_valid = 1'b0;
  eia_instr_64_x1_start_valid = 1'b0;

     i_evmww_decode = 1'b0;     
    evmww_start_nxt = 1'b0;
     i_evmw_decode = 1'b0;     
    evmw_start_nxt = 1'b0;
     i_evm_decode = 1'b0;     
    evm_start_nxt = 1'b0;
  
  case ( eia_x1_gnum )
    2'd0:  
                    begin
                      evmww_start_nxt = eia_x1_valid & ~x1_kill & exu_x1_to_x2;
                      i_evmww_decode  = eia_x1_valid;
                      eia_instr_64_x1_start_valid = eia_x1_valid & ~x1_kill & exu_x1_to_x2;
                    end  
    2'd1:  
                    begin
                      evmw_start_nxt = eia_x1_valid & ~x1_kill & exu_x1_to_x2;
                      i_evmw_decode  = eia_x1_valid;
                      eia_instr_64_x1_start_valid = eia_x1_valid & ~x1_kill & exu_x1_to_x2;
                    end  
    2'd2:  
                    begin
                      evm_start_nxt = eia_x1_valid & ~x1_kill & exu_x1_to_x2;
                      i_evm_decode  = eia_x1_valid;
                      eia_instr_64_x1_start_valid = eia_x1_valid & ~x1_kill & exu_x1_to_x2;
                    end  
  endcase
end


// SA to X1 logic is the dispatch of the eia instruction to user-pipe
// Most instruction information is handled here


// result selection and _end generation for x1 instruction

reg            eia_x1_timed_instr_done;
reg            eia_x1_end;
reg  [31:0]    eia_x1_res_data_mux;     // selected data, from ext mux
reg  [31:0]    eia_x1_res_data_mux_hi;
reg   [3:0]    eia_x1_res_flags_mux;    // selected bflags, from ext mux
reg   [3:0]    eia_x1_res_xflags_mux;   // selected xflags, from ext mux


  // declare x1_<grp>_end
  
reg      x1_evmww_end;
reg      x1_evmw_end;
reg      x1_evm_end;

always @ (*)
begin :   eia_inst_untimed_ready_x1_PROC

  eia_x1_timed_instr_done = eia_x1_valid & ~eia_x1_done & ~eia_x1_untimed & (eia_x1_cnt == 5'h0)
                                         & ~eia_x1_src64
                                         & ~(eia_inst_x1_start & x1_kill)
                            ;

  // assign defaults
      x1_evmww_end   =   1'b0;
      x1_evmw_end   =   1'b0;
      x1_evm_end   =   1'b0;
      eia_x1_end            =  1'b0;
      eia_x1_res_data_mux   = 32'h0;
      eia_x1_res_data_mux_hi= 32'h0;
      eia_x1_res_flags_mux  =  4'h0;
      eia_x1_res_xflags_mux =  4'h0;

      
  // generate active _end logic
  // mux out result and flags of the done x1 instruction
  case ( eia_x1_gnum )
    2'd0:     // group: evmww
      begin

// SRC SIZE [7,0] b4 = 32

        eia_x1_end            =  eia_x1_timed_instr_done;
        x1_evmww_end  = eia_x1_end;
        eia_x1_res_data_mux_hi = evmww_res[63:32];
        eia_x1_res_data_mux    = evmww_res[31: 0];
        eia_x1_res_flags_mux   = evmww_bflags;
        eia_x1_res_xflags_mux  = evmww_xflags;
      end
    2'd1:     // group: evmw
      begin

// SRC SIZE [7,1] b4 = 32

        eia_x1_end            =  eia_x1_timed_instr_done;
        x1_evmw_end  = eia_x1_end;
        eia_x1_res_data_mux_hi = evmw_res[63:32];
        eia_x1_res_data_mux    = evmw_res[31: 0];
        eia_x1_res_flags_mux   = evmw_bflags;
        eia_x1_res_xflags_mux  = evmw_xflags;
      end
    2'd2:     // group: evm
      begin

// SRC SIZE [7,2] b4 = 32

        eia_x1_end            =  eia_x1_timed_instr_done;
        x1_evm_end  = eia_x1_end;
        eia_x1_res_data_mux_hi = evm_res[63:32];
        eia_x1_res_data_mux    = evm_res[31: 0];
        eia_x1_res_flags_mux   = evm_bflags;
        eia_x1_res_xflags_mux  = evm_xflags;
      end
    default:
      begin
        // assign defaults
        x1_evmww_end =   1'b0;
        x1_evmw_end =   1'b0;
        x1_evm_end =   1'b0;
        eia_x1_end             =  1'b0;
        eia_x1_res_data_mux    = 32'h0;
        eia_x1_res_data_mux_hi = 32'h0;
        eia_x1_res_flags_mux   =  4'h0;
        eia_x1_res_xflags_mux  =  4'h0;
      end
  endcase
end


// mux out x1 result to exu and eia_pipe

always @(*)
begin :  eia_exu_x1_res_valid_9_PROC
  eia_exu_x1_res_valid   =   eia_x1_valid              &
                            ~eia_x1_has_flg            & 
                            (eia_x1_done | eia_x1_end) &          
                           ~(eia_x1_kill | x1_kill)    ; 

  eia_exu_x1_fast_op_r   =   eia_x1_valid              &
                            ~eia_x1_has_flg            &        // no bypass for xflags
                            ~eia_x1_dst64              &        // no bypass for hi reg
                            (eia_x1_done | eia_x1_end);         // can be bypassed in x1
  eia_exu_x1_res_data    =   eia_x1_end ? eia_x1_res_data_mux : // new result
                                          eia_x1_res_data;      // keep done result
  eia_exu_x1_res_data_hi =   eia_x1_end ? eia_x1_res_data_mux_hi :
                                          eia_x1_res_data_hi;
  eia_exu_x1_res_flags   =   eia_x1_end ? eia_x1_res_flags_mux :
                                          eia_x1_res_flags;
  eia_x1_res_xflags_pre  =   eia_x1_end ? eia_x1_res_xflags_mux :
                                          eia_x1_res_xflags;
end




// Stall exu_pipe when a 1cyc instr at x1 is not done (multi-cycle blocking)

always @(*)
begin :  eia_exu_x1_hold_9_PROC
    eia_exu_x1_hold  =   eia_x1_valid & eia_x1_is_1cyc &
                         ~(eia_inst_x1_start & x1_kill) &
                       ~eia_x1_src64                   &
                       ~(eia_x1_done | eia_x1_end)     &
                       ~(eia_x1_kill | x1_kill)    ;      // release a killed blocking instr so
                                                          // it vacates the pipe cleanly
end


// X1 to X2 logic moves in-progress or done eia instruction in sync with exu-pipe
// Only 2 cycle or more timed, any untimed (non-blocking) can end at this stage
// Most instruction information is handled here

  

  

reg          eia_x1_valid_nxt; 
reg          eia_x1_src64_inst_nxt;
reg          eia_x1_done_nxt;
reg          eia_x1_kill_nxt;
reg [1:0]    eia_x1_xtype_nxt;  
reg [7:0] eia_x1_xnum_nxt; 
reg [1:0] eia_x1_gnum_nxt; 
reg          eia_x1_is_1cyc_nxt; 
reg          eia_x1_blocking_nxt; 
reg          eia_x1_has_dst_nxt; 
reg          eia_x1_has_flg_nxt; 
reg  [3:0]   eia_x1_att_nxt;    
reg          eia_x1_has_reg_sets_nxt;
reg          eia_x1_untimed_nxt; 
reg   [4:0]      eia_x1_cnt_nxt;     
reg [31:0]   eia_x1_res_data_nxt;
reg [31:0]   eia_x1_res_data_hi_nxt;
reg  [3:0]   eia_x1_res_flags_nxt;
reg  [3:0]   eia_x1_res_xflags_nxt;

// clock enable for all signals

wire sa_to_x1_proc_0_cg0 = exu_sa_to_x1 |
                           exu_x1_to_x2 | eia_x1_to_x2
                        | (eia_x1_valid & x1_kill & eia_x1_src64)
                        | (eia_inst_x1_start & x1_kill) 
                             ;
wire sa_to_x1_proc_1_cg0 = exu_sa_to_x1 |
                           exu_x1_to_x2 | eia_x1_to_x2 |
                           eia_x1_valid;

// logic for all signals

always@(*)
begin :  sa_to_x1_9_PROC
  if (exu_sa_to_x1)   // pipeline enable sa->x1
  begin
    eia_x1_valid_nxt   =  eia_sa_valid & ~sa_kill; // _kill invalidates the instr so it
                                                   // was never dispatched
    eia_x1_done_nxt    =  1'b0;                    // cannot be marked done on dispatch
    eia_x1_kill_nxt    =  eia_sa_valid & sa_kill;
    eia_x1_xtype_nxt   =  eia_sa_xtype;
    eia_x1_src64_inst_nxt = eia_sa_src64_inst;
    eia_x1_xnum_nxt    =  eia_sa_xnum;
    eia_x1_gnum_nxt    =  eia_sa_gnum;
    eia_x1_is_1cyc_nxt =  eia_sa_is_1cyc;
    eia_x1_blocking_nxt=  eia_sa_valid & eia_sa_blocking;
    eia_x1_has_dst_nxt =  eia_sa_has_dst;
    eia_x1_has_flg_nxt =  eia_sa_has_flg;
    eia_x1_att_nxt     =  eia_sa_att;
    eia_x1_has_reg_sets_nxt = eia_sa_has_reg_sets;
    eia_x1_untimed_nxt =  eia_sa_untimed;
// leda W484 off
// leda B_3208 off
// LMD: possible carry in add/sub logic
// LJ:  impossible by design
    eia_x1_cnt_nxt     =  eia_sa_untimed | (eia_sa_cnt == 5'h0)  ? 5'h0 :
                          eia_sa_src64 ?                        eia_sa_cnt :
                                                                eia_sa_cnt - 1;
    eia_x1_res_data_nxt   = 32'h0;                 // no result on transition from sa
    eia_x1_res_data_hi_nxt = 32'h0;
    eia_x1_res_flags_nxt  =  4'h0;
    eia_x1_res_xflags_nxt =  4'h0;
  

  
// leda B_3208 on
// leda W484 on  
  end
  else if (exu_x1_to_x2 || eia_x1_to_x2)           // eia_: _kill moving forward
  begin 
    eia_x1_valid_nxt   =  1'b0;
    eia_x1_done_nxt    =  1'b0;
    eia_x1_kill_nxt    =  1'b0;
    eia_x1_xtype_nxt   = 2'd0;
    eia_x1_src64_inst_nxt = 1'b0;
    eia_x1_xnum_nxt    =  8'd0;
    eia_x1_gnum_nxt    =  2'd0;
    eia_x1_is_1cyc_nxt =  1'b0;
    eia_x1_blocking_nxt=  1'b0;
    eia_x1_has_dst_nxt =  1'b0;
    eia_x1_has_flg_nxt =  1'b0;
    eia_x1_att_nxt     =  4'h0;
    eia_x1_has_reg_sets_nxt = 1'b0;
    eia_x1_untimed_nxt =  1'b0;
    eia_x1_cnt_nxt     =  5'h0;
    eia_x1_res_data_nxt    = 32'h0;    
    eia_x1_res_data_hi_nxt = 32'h0;
    eia_x1_res_flags_nxt  =  4'h0;
    eia_x1_res_xflags_nxt =  4'h0;
  

  

  end
  else                                             // stall at x1 but continue to count down
  begin
    eia_x1_valid_nxt   =  eia_x1_valid
                          & ~(x1_kill & eia_x1_src64) // not dispatched yet, kill it for real
                          & ~(eia_inst_x1_start & x1_kill) // not dispatched yet, kill it for real
                           ;
    eia_x1_done_nxt    =  eia_x1_done |            // hold status on long stall
                          eia_x1_end;              // next cycle user_pipe is marked done
    eia_x1_kill_nxt    =  eia_x1_valid &
                         (x1_kill | eia_x1_kill);  // pending kill, remains valid till CA
    eia_x1_xtype_nxt   =  eia_x1_xtype;
    eia_x1_src64_inst_nxt = eia_x1_src64_inst;
    eia_x1_xnum_nxt    =  eia_x1_xnum;
    eia_x1_gnum_nxt    =  eia_x1_gnum;
    eia_x1_is_1cyc_nxt =  eia_x1_is_1cyc;
    eia_x1_blocking_nxt=  eia_x1_valid & eia_x1_blocking;
    eia_x1_has_dst_nxt =  eia_x1_has_dst;
    eia_x1_has_flg_nxt =  eia_x1_has_flg;
    eia_x1_att_nxt     =  eia_x1_att;
    eia_x1_has_reg_sets_nxt = eia_x1_has_reg_sets;
    eia_x1_untimed_nxt =  eia_x1_untimed;
// leda W484 off
// leda B_3208 off
// LMD: possible carry in add/sub logic
// LJ:  impossible by design
    eia_x1_cnt_nxt     =  eia_x1_untimed | eia_x1_done | ~eia_x1_valid ? 5'h0 :
                          eia_x1_src64 ?                                 eia_x1_cnt :
                                                                         eia_x1_cnt - 1;
    eia_x1_res_data_nxt    =  eia_exu_x1_res_data;
    eia_x1_res_data_hi_nxt =  eia_exu_x1_res_data_hi;
    eia_x1_res_flags_nxt  =  eia_exu_x1_res_flags;
    eia_x1_res_xflags_nxt =  eia_x1_res_xflags_pre;
  

  

// leda B_3208 on
// leda W484 on  
  end
end

// staging registers

always @(posedge clk or posedge rst_a)
begin : sa_to_x1_0_PROC
  if (rst_a == 1'b1)
  begin
    eia_x1_valid     <=  1'b0;
    eia_x1_xtype     <=  2'd0;
    eia_x1_src64_inst <= 1'b0;
    eia_x1_xnum      <=  8'd0;
    eia_x1_gnum      <=  2'd0;
    eia_x1_is_1cyc   <=  1'b0;
    eia_x1_blocking  <=  1'b0;
    eia_x1_has_dst   <=  1'b0;
    eia_x1_has_flg   <=  1'b0;
    eia_x1_att       <=  4'h0;
    eia_x1_has_reg_sets <= 1'b0;
    eia_x1_untimed   <=  1'b0;
  

  
  end
  else if (sa_to_x1_proc_0_cg0)
  begin
    eia_x1_valid     <=  eia_x1_valid_nxt;   
    eia_x1_xtype     <=  eia_x1_xtype_nxt; 
    eia_x1_src64_inst <= eia_x1_src64_inst_nxt; 
    eia_x1_xnum      <=  eia_x1_xnum_nxt;    
    eia_x1_gnum      <=  eia_x1_gnum_nxt;    
    eia_x1_is_1cyc   <=  eia_x1_is_1cyc_nxt; 
    eia_x1_blocking  <=  eia_x1_blocking_nxt;
    eia_x1_has_dst   <=  eia_x1_has_dst_nxt; 
    eia_x1_has_flg   <=  eia_x1_has_flg_nxt; 
    eia_x1_att       <=  eia_x1_att_nxt; 
    eia_x1_has_reg_sets <= eia_x1_has_reg_sets_nxt;
    eia_x1_untimed   <=  eia_x1_untimed_nxt;
  

  
  end
end

always @(posedge clk or posedge rst_a)
begin : sa_to_x1_1_PROC
  if (rst_a == 1'b1)
  begin
    eia_x1_done      <=  1'b0;
    eia_x1_kill      <=  1'b0;
    eia_x1_cnt       <=  5'h0;
    eia_x1_res_data  <= 32'h0;
    eia_x1_res_flags <=  4'h0;
    eia_x1_res_xflags<=  4'h0;
  

  
  
  end
  else if (sa_to_x1_proc_1_cg0)
  begin
    eia_x1_done      <=  eia_x1_done_nxt;
    eia_x1_kill      <=  eia_x1_kill_nxt;
    eia_x1_cnt       <=  eia_x1_cnt_nxt;     
    eia_x1_res_data    <=  eia_x1_res_data_nxt;
// leda NTL_RST03 off
// LMD: no reset for reg
// LJ:  data reg, needs no reset
    eia_x1_res_data_hi <=  eia_x1_res_data_hi_nxt;
// leda NTL_RST03 on
    eia_x1_res_flags <=  eia_x1_res_flags_nxt;
    eia_x1_res_xflags<=  eia_x1_res_xflags_nxt;
  

  
  
  end
end

always @(posedge clk or posedge rst_a)
begin : eia_inst_x1_start_PROC
  if(rst_a == 1'b1)begin
      eia_inst_x1_start <= 1'b0;
  end else begin
      eia_inst_x1_start <= eia_instr_32_sa_start_valid;
  end
end

  // declare x2_<grp>_end
  
reg      x2_evmww_end;
reg      x2_evmw_end;
reg      x2_evm_end;

// result selection and _end generation for x2 instruction

reg  eia_x2_timed_instr_done;

  
reg  [31:0]    eia_x2_res_data_mux;     // selected data, from ext mux
reg  [31:0]    eia_x2_res_data_mux_hi;
reg   [3:0]    eia_x2_res_flags_mux;    // selected bflags, from ext mux
reg   [3:0]    eia_x2_res_xflags_mux;   // selected xflags, from ext mux

always @ (*)
begin :   eia_inst_untimed_ready_x2_PROC
  eia_x2_timed_instr_done = eia_x2_valid & ~eia_x2_done & ~eia_x2_untimed & 
                            (eia_x2_cnt == 5'h0) &
                            ~(eia_inst_x2_start & x2_kill);

  // assign defaults
      x2_evmww_end   =   1'b0;
      x2_evmw_end   =   1'b0;
      x2_evm_end   =   1'b0;
      eia_x2_end            =  1'b0;
      eia_x2_res_data_mux   = 32'h0;
      eia_x2_res_data_mux_hi= 32'h0;
      eia_x2_res_flags_mux  =  4'h0;
      eia_x2_res_xflags_mux =  4'h0;

      
  // generate active _end logic
  // mux out result and flags of the done at x2 instruction
  case ( eia_x2_gnum )
    2'd0:     // group: evmww
      begin
        eia_x2_end            =  eia_x2_timed_instr_done;
        x2_evmww_end  =  eia_x2_end;
        eia_x2_res_data_mux_hi = evmww_res[63:32];
        eia_x2_res_data_mux    = evmww_res[31: 0];
        eia_x2_res_flags_mux  = evmww_bflags;
        eia_x2_res_xflags_mux = evmww_xflags;
     end
    2'd1:     // group: evmw
      begin
        eia_x2_end            =  eia_x2_timed_instr_done;
        x2_evmw_end  =  eia_x2_end;
        eia_x2_res_data_mux_hi = evmw_res[63:32];
        eia_x2_res_data_mux    = evmw_res[31: 0];
        eia_x2_res_flags_mux  = evmw_bflags;
        eia_x2_res_xflags_mux = evmw_xflags;
     end
    2'd2:     // group: evm
      begin
        eia_x2_end            =  eia_x2_timed_instr_done;
        x2_evm_end  =  eia_x2_end;
        eia_x2_res_data_mux_hi = evm_res[63:32];
        eia_x2_res_data_mux    = evm_res[31: 0];
        eia_x2_res_flags_mux  = evm_bflags;
        eia_x2_res_xflags_mux = evm_xflags;
     end
    default:
      begin
        // assign defaults
        x2_evmww_end   =   1'b0;
        x2_evmw_end   =   1'b0;
        x2_evm_end   =   1'b0;
        eia_x2_end             =  1'b0;
        eia_x2_res_data_mux    = 32'h0;
        eia_x2_res_data_mux_hi = 32'h0;
        eia_x2_res_flags_mux   =  4'h0;
        eia_x2_res_xflags_mux  =  4'h0;
      end
  endcase
end


reg  [31:0]   eia_pipe_x2_res_data;
reg  [31:0]   eia_pipe_x2_res_data_hi;
reg   [3:0]   eia_pipe_x2_res_flags;

// mux out x2 result to eia_pipe

always @(*)
begin :  eia_pipe_x2_res_9_PROC
    eia_pipe_x2_res_data    =  eia_x2_end ? eia_x2_res_data_mux :
                                            eia_x2_res_data;
    eia_pipe_x2_res_data_hi =  eia_x2_end ? eia_x2_res_data_mux_hi :
                                            eia_x2_res_data_hi;
    eia_pipe_x2_res_flags   =  eia_x2_end ? eia_x2_res_flags_mux :
                                           eia_x2_res_flags;
    eia_x2_res_xflags_pre   =  eia_x2_end ? eia_x2_res_xflags_mux :
                                           eia_x2_res_xflags;
end

  

  

reg          eia_x2_valid_nxt;   
reg          eia_x2_done_nxt;
reg          eia_x2_kill_nxt;
reg [1:0]    eia_x2_xtype_nxt; 
reg          eia_x2_src64_inst_nxt;
reg [7:0] eia_x2_xnum_nxt; 
reg [1:0] eia_x2_gnum_nxt; 
reg          eia_x2_blocking_nxt; 
reg          eia_x2_block64_nxt; 
reg          eia_x2_has_dst_nxt; 
reg          eia_x2_has_flg_nxt; 
reg  [3:0]   eia_x2_att_nxt;    
reg          eia_x2_has_reg_sets_nxt;
reg          eia_x2_untimed_nxt; 
reg   [4:0]      eia_x2_cnt_nxt;     
reg [31:0]   eia_x2_res_data_nxt;
reg [31:0]   eia_x2_res_data_hi_nxt;
reg  [3:0]   eia_x2_res_flags_nxt;
reg  [3:0]   eia_x2_res_xflags_nxt;

// clock enable for all signals

wire x1_to_x2_proc_0_cg0 = exu_x1_to_x2 | eia_x1_to_x2 |
                           exu_x2_to_x3 | eia_x2_to_x3 |
                           (eia_inst_x2_start & x2_kill);//kill 64 bit inst before start
wire x1_to_x2_proc_1_cg0 = exu_x1_to_x2 | eia_x1_to_x2 |
                           exu_x2_to_x3 | eia_x2_to_x3 |
                           eia_x2_valid;

// logic for all signals

always@(*)
begin :  x1_to_x2_9_PROC 
if (exu_x1_to_x2 || eia_x1_to_x2)                  // pipeline enable x1->x2
                                                   // eia_: _kill moving forward)   
  begin
    eia_x2_valid_nxt   =  eia_x1_valid &
                          ~(eia_inst_x1_start & x1_kill
                          | eia_x1_src64_inst & x1_kill
                          );
    eia_x2_done_nxt    =  eia_x1_done |            // hold status on long stall
                          eia_x1_end;              // next cycle user_pipe is marked done
                                               // cannot be marked done on dispatch
    eia_x2_kill_nxt    =  eia_x1_valid &
                         (x1_kill | eia_x1_kill);  // pending kill, remains valid till CA
    eia_x2_xtype_nxt   =  eia_x1_xtype;
    eia_x2_src64_inst_nxt = eia_x1_src64_inst;
    eia_x2_xnum_nxt    =  eia_x1_xnum;
    eia_x2_gnum_nxt    =  eia_x1_gnum;
    eia_x2_blocking_nxt=  eia_x1_valid & eia_x1_blocking;
    eia_x2_block64_nxt =  eia_x1_valid &
                          eia_x1_blocking & eia_x1_src64;
    eia_x2_has_dst_nxt =  eia_x1_has_dst;
    eia_x2_has_flg_nxt =  eia_x1_has_flg;
    eia_x2_att_nxt     =  eia_x1_att;
    eia_x2_has_reg_sets_nxt = eia_x1_has_reg_sets;
    eia_x2_untimed_nxt =  eia_x1_untimed;
// leda W484 off
// leda B_3208 off
// LMD: possible carry in add/sub logic
// LJ:  impossible by design
    eia_x2_cnt_nxt     =  eia_x1_untimed | (eia_x1_cnt == 5'h0) ? 5'h0 : eia_x1_cnt - 1;
    eia_x2_res_data_nxt    =  eia_exu_x1_res_data;
    eia_x2_res_data_hi_nxt =  eia_exu_x1_res_data_hi;
    eia_x2_res_flags_nxt   =  eia_exu_x1_res_flags;
    eia_x2_res_xflags_nxt  =  eia_x1_res_xflags_pre;
  

  
// leda B_3208 on
// leda W484 on  
  end
  else if (exu_x2_to_x3 || eia_x2_to_x3)           // eia_: _kill moving forward
  begin 
    eia_x2_valid_nxt  =  1'b0;
    eia_x2_done_nxt   =  1'b0;
    eia_x2_kill_nxt    =  1'b0;
    eia_x2_xtype_nxt   = 2'd0;
    eia_x2_src64_inst_nxt = 1'b0;
    eia_x2_xnum_nxt    =  8'd0;
    eia_x2_gnum_nxt    =  2'd0;
    eia_x2_blocking_nxt=  1'b0;
    eia_x2_block64_nxt =  1'b0;
    eia_x2_has_dst_nxt =  1'b0;
    eia_x2_has_flg_nxt =  1'b0;
    eia_x2_att_nxt     =  4'h0;
    eia_x2_has_reg_sets_nxt = 1'b0;
    eia_x2_untimed_nxt =  1'b0;
    eia_x2_cnt_nxt     =  5'h0;
    eia_x2_res_data_nxt    = 32'h0;
    eia_x2_res_data_hi_nxt = 32'h0;
    eia_x2_res_flags_nxt   =  4'h0;
    eia_x2_res_xflags_nxt  =  4'h0;
  

  
  end
  else                                             // stall at x2 but continue to count down
  begin
    eia_x2_valid_nxt   =  eia_x2_valid & 
                          ~(eia_inst_x2_start & x2_kill); // not dispatched yet, kill it for real;
    eia_x2_done_nxt    =  eia_x2_done |            // hold status on long stall
                          eia_x2_end;              // next cycle user_pipe is marked done
    eia_x2_kill_nxt    =  eia_x2_valid &
                         (x2_kill | eia_x2_kill);  // pending kill, remains valid till CA
    eia_x2_xtype_nxt   =  eia_x2_xtype;
    eia_x2_src64_inst_nxt = eia_x2_src64_inst;
    eia_x2_xnum_nxt    =  eia_x2_xnum;
    eia_x2_gnum_nxt    =  eia_x2_gnum;
    eia_x2_blocking_nxt=  eia_x2_valid & eia_x2_blocking;
    eia_x2_block64_nxt =  eia_x2_valid &
                          eia_x2_blocking & eia_x2_src64;
    eia_x2_has_dst_nxt =  eia_x2_has_dst;
    eia_x2_has_flg_nxt =  eia_x2_has_flg;
    eia_x2_att_nxt     =  eia_x2_att;
    eia_x2_has_reg_sets_nxt = eia_x2_has_reg_sets;
    eia_x2_untimed_nxt =  eia_x2_untimed;
// leda W484 off
// leda B_3208 off
// LMD: possible carry in add/sub logic
// LJ:  impossible by design
    eia_x2_cnt_nxt     =  eia_x2_untimed | eia_x2_done | ~eia_x2_valid ? 5'h0 : eia_x2_cnt - 1;
    eia_x2_res_data_nxt    =  eia_pipe_x2_res_data;
    eia_x2_res_data_hi_nxt =  eia_pipe_x2_res_data_hi;
    eia_x2_res_flags_nxt   =  eia_pipe_x2_res_flags;
    eia_x2_res_xflags_nxt  =  eia_x2_res_xflags_pre;
  

  
// leda B_3208 on
// leda W484 on  
  end
end

// staging registers

always @(posedge clk or posedge rst_a)
begin : x1_to_x2_0_PROC
  if (rst_a == 1'b1)
  begin
    eia_x2_valid     <=  1'b0;
    eia_x2_xtype     <= 2'd0;
    eia_x2_src64_inst <= 1'b0;
    eia_x2_xnum      <=  8'd0;
    eia_x2_gnum      <=  2'd0;
    eia_x2_blocking  <=  1'b0;
    eia_x2_block64   <=  1'b0;
    eia_x2_has_dst   <=  1'b0;
    eia_x2_has_flg   <=  1'b0;
    eia_x2_att       <=  4'h0;
    eia_x2_has_reg_sets <= 1'b0;
    eia_x2_untimed   <=  1'b0;
  

  
  end
  else if (x1_to_x2_proc_0_cg0)
  begin
    eia_x2_valid     <=  eia_x2_valid_nxt;   
    eia_x2_xtype     <=  eia_x2_xtype_nxt; 
    eia_x2_src64_inst <= eia_x2_src64_inst_nxt;
    eia_x2_xnum      <=  eia_x2_xnum_nxt;    
    eia_x2_gnum      <=  eia_x2_gnum_nxt;    
    eia_x2_blocking  <=  eia_x2_blocking_nxt;
    eia_x2_block64   <=  eia_x2_block64_nxt;
    eia_x2_has_dst   <=  eia_x2_has_dst_nxt; 
    eia_x2_has_flg   <=  eia_x2_has_flg_nxt; 
    eia_x2_att       <=  eia_x2_att_nxt; 
    eia_x2_has_reg_sets <= eia_x2_has_reg_sets_nxt;
    eia_x2_untimed   <=  eia_x2_untimed_nxt; 
  

  
  end
end

always @(posedge clk or posedge rst_a)
begin : x1_to_x2_1_PROC
  if (rst_a == 1'b1)
  begin
    eia_x2_done         <=  1'b0;
    eia_x2_kill         <=  1'b0;
    eia_x2_cnt          <=  5'h0;
    eia_x2_res_data     <= 32'h0;
    eia_x2_res_data_hi  <= 32'h0;
    eia_x2_res_flags    <=  4'h0;
    eia_x2_res_xflags   <=  4'h0;
  

  
  
  end
  else if (x1_to_x2_proc_1_cg0)
  begin
    eia_x2_done         <=  eia_x2_done_nxt;
    eia_x2_kill         <=  eia_x2_kill_nxt;
    eia_x2_cnt          <=  eia_x2_cnt_nxt;     
    eia_x2_res_data     <=  eia_x2_res_data_nxt;
    eia_x2_res_data_hi  <=  eia_x2_res_data_hi_nxt;
    eia_x2_res_flags    <=  eia_x2_res_flags_nxt;
    eia_x2_res_xflags   <=  eia_x2_res_xflags_nxt;
  

  
  
  end
end

always @(posedge clk or posedge rst_a)
begin : eia_inst_x2_start_PROC
  if(rst_a == 1'b1)begin
      eia_inst_x2_start <= 1'b0;
  end else begin
      eia_inst_x2_start <= eia_instr_64_x1_start_valid;
  end
end

always @(*)
begin :  eia_exu_hold_9_PROC
   // Stall exu_pipe x2 stage when a 64-bit-source blocking instr at x2
   eia_exu_x2_hold  =   eia_x2_valid & eia_x2_block64 &
                       ~(eia_inst_x2_start & x2_kill) &
                       ~(eia_x2_done | eia_x2_end)    &
                       ~(eia_x2_kill | x2_kill)    ;      // release a killed blocking instr so
                                                          // it vacates the pipe cleanly
    eia_exu_sa_hold  =   eia_x1_valid & eia_x1_blocking & (~(eia_x1_end | eia_x1_done) |  x1_is_cond_inst)                    & ~(eia_inst_x1_start & x1_kill)
                       | eia_x2_valid & eia_x2_blocking & (~(eia_x2_end | eia_x2_done) |  x2_is_cond_inst)                    & ~(eia_inst_x2_start & x2_kill)
                       | eia_x3_valid & eia_x3_blocking & (~(eia_x3_end | eia_x3_done) |  x3_is_cond_inst)                    & ~x3_kill
                       | eia_ca_valid & eia_ca_blocking & (~(eia_ca_end | eia_ca_done) | (ca_is_cond_inst & ~ca_predicate_r)) & ~ca_kill
                       |                                                                  wa_is_cond_inst
                          ;
end

// X2 to X3 logic moves in-progress or done eia instruction in sync with exu-pipe
// Only 3 cycle or more timed, any untimed (non-blocking) can end at this stage
// Most instruction information is handled here


  // declare x3_<grp>_end
  
reg      x3_evmww_end;
reg      x3_evmw_end;
reg      x3_evm_end;

// result selection and _end generation for x3 instruction

reg  eia_x3_timed_instr_done;

reg  [31:0]    eia_x3_res_data_mux;     // selected data, from ext mux
reg  [31:0]    eia_x3_res_data_mux_hi;
reg   [3:0]    eia_x3_res_flags_mux;    // selected bflags, from ext mux
reg   [3:0]    eia_x3_res_xflags_mux;   // selected xflags, from ext mux

always @ (*)
begin :   eia_inst_untimed_ready_x3_PROC
  eia_x3_timed_instr_done = eia_x3_valid & ~eia_x3_done & ~eia_x3_untimed & (eia_x3_cnt == 5'h0);

  // assign defaults
      x3_evmww_end   =   1'b0;
      x3_evmw_end   =   1'b0;
      x3_evm_end   =   1'b0;
      eia_x3_end            =  1'b0;
      eia_x3_res_data_mux   = 32'h0;
      eia_x3_res_data_mux_hi= 32'h0;
      eia_x3_res_flags_mux  =  4'h0;
      eia_x3_res_xflags_mux =  4'h0;
      
  // generate active _end logic
  // mux out result and flags of the done at x3 instruction
  case ( eia_x3_gnum )
    2'd0:     // group: evmww
      begin
        eia_x3_end            =  eia_x3_timed_instr_done;
        x3_evmww_end  =  eia_x3_end;
        eia_x3_res_data_mux_hi = evmww_res[63:32];
        eia_x3_res_data_mux    = evmww_res[31: 0];
        eia_x3_res_flags_mux  = evmww_bflags;
        eia_x3_res_xflags_mux = evmww_xflags;
     end
    2'd1:     // group: evmw
      begin
        eia_x3_end            =  eia_x3_timed_instr_done;
        x3_evmw_end  =  eia_x3_end;
        eia_x3_res_data_mux_hi = evmw_res[63:32];
        eia_x3_res_data_mux    = evmw_res[31: 0];
        eia_x3_res_flags_mux  = evmw_bflags;
        eia_x3_res_xflags_mux = evmw_xflags;
     end
    2'd2:     // group: evm
      begin
        eia_x3_end            =  eia_x3_timed_instr_done;
        x3_evm_end  =  eia_x3_end;
        eia_x3_res_data_mux_hi = evm_res[63:32];
        eia_x3_res_data_mux    = evm_res[31: 0];
        eia_x3_res_flags_mux  = evm_bflags;
        eia_x3_res_xflags_mux = evm_xflags;
     end
    default:
      begin
        // assign defaults
        x3_evmww_end   =   1'b0;
        x3_evmw_end   =   1'b0;
        x3_evm_end   =   1'b0;
        eia_x3_end             =  1'b0;
        eia_x3_res_data_mux    = 32'h0;
        eia_x3_res_data_mux_hi = 32'h0;
        eia_x3_res_flags_mux   =  4'h0;
        eia_x3_res_xflags_mux  =  4'h0;
      end
  endcase
end



// mux out x3 result to eia_pipe

reg  [31:0]   eia_pipe_x3_res_data;
reg  [31:0]   eia_pipe_x3_res_data_hi;
reg   [3:0]   eia_pipe_x3_res_flags;

always @(*)
begin :  eia_pipe_x3_res_9_PROC
    eia_pipe_x3_res_data    =  eia_x3_end ? eia_x3_res_data_mux :
                                            eia_x3_res_data;
    eia_pipe_x3_res_data_hi =  eia_x3_end ? eia_x3_res_data_mux_hi :
                                            eia_x3_res_data_hi;
    eia_pipe_x3_res_flags   =  eia_x3_end ? eia_x3_res_flags_mux :
                                            eia_x3_res_flags;
    eia_x3_res_xflags_pre   =  eia_x3_end ? eia_x3_res_xflags_mux :
                                            eia_x3_res_xflags;
end

  

  

reg          eia_x3_valid_nxt;   
reg          eia_x3_done_nxt;
reg          eia_x3_kill_nxt;
reg [1:0]    eia_x3_xtype_nxt;  
reg          eia_x3_src64_inst_nxt;
reg [7:0] eia_x3_xnum_nxt; 
reg [1:0] eia_x3_gnum_nxt; 
reg          eia_x3_blocking_nxt; 
reg          eia_x3_has_dst_nxt; 
reg          eia_x3_has_flg_nxt; 
reg  [3:0]   eia_x3_att_nxt;  
reg          eia_x3_has_reg_sets_nxt;
reg          eia_x3_untimed_nxt; 
reg   [4:0]      eia_x3_cnt_nxt;     
reg [31:0]   eia_x3_res_data_nxt;
reg [31:0]   eia_x3_res_data_hi_nxt;
reg  [3:0]   eia_x3_res_flags_nxt;
reg  [3:0]   eia_x3_res_xflags_nxt;

// clock enable for all signals

wire x2_to_x3_proc_0_cg0 = exu_x2_to_x3 | eia_x2_to_x3 |
                           exu_x3_to_ca | eia_x3_to_ca;
wire x2_to_x3_proc_1_cg0 = exu_x2_to_x3 | eia_x2_to_x3 |
                           exu_x3_to_ca | eia_x3_to_ca |
                           eia_x3_valid;

// logic for all signals

always@(*)
begin :  x2_to_x3_9_PROC
  if (exu_x2_to_x3 || eia_x2_to_x3)                // pipeline enable x2->x3
                                                   // eia_: _kill moving forward)   
  begin
    eia_x3_valid_nxt   =  eia_x2_valid &
                          ~(eia_inst_x2_start & x2_kill);
    eia_x3_done_nxt    =  eia_x2_done |            // hold status on long stall
                          eia_x2_end;              // next cycle user_pipe is marked done
    eia_x3_kill_nxt    =  eia_x2_valid &
                         (x2_kill | eia_x2_kill);  // pending kill, remains valid till CA
    eia_x3_xtype_nxt   =  eia_x2_xtype;
    eia_x3_src64_inst_nxt = eia_x2_src64_inst;
    eia_x3_xnum_nxt    =  eia_x2_xnum;
    eia_x3_gnum_nxt    =  eia_x2_gnum;
    eia_x3_blocking_nxt=  eia_x2_valid & eia_x2_blocking;
    eia_x3_has_dst_nxt =  eia_x2_has_dst;
    eia_x3_has_flg_nxt =  eia_x2_has_flg;
    eia_x3_att_nxt     =  eia_x2_att;
    eia_x3_has_reg_sets_nxt = eia_x2_has_reg_sets;
    eia_x3_untimed_nxt =  eia_x2_untimed;
// leda W484 off
// leda B_3208 off
// LMD: possible carry in add/sub logic
// LJ:  impossible by design
    eia_x3_cnt_nxt     =  eia_x2_untimed | (eia_x2_cnt == 5'h0) ? 5'h0 : eia_x2_cnt - 1;
    eia_x3_res_data_nxt    = eia_pipe_x2_res_data;  // possible done instruction
    eia_x3_res_data_hi_nxt = eia_pipe_x2_res_data_hi;
    eia_x3_res_flags_nxt   = eia_pipe_x2_res_flags;
    eia_x3_res_xflags_nxt  = eia_x2_res_xflags_pre;
  

  
// leda B_3208 on
// leda W484 on  
  end
  else if (exu_x3_to_ca || eia_x3_to_ca)           // eia_: _kill moving forward
  begin 
    eia_x3_valid_nxt   =  1'b0;
    eia_x3_done_nxt    =  1'b0;
    eia_x3_kill_nxt    =  1'b0;
    eia_x3_xtype_nxt   =  2'd0;
    eia_x3_src64_inst_nxt = 1'b0;
    eia_x3_xnum_nxt    =  8'd0;
    eia_x3_gnum_nxt    =  2'd0;
    eia_x3_blocking_nxt=  1'b0;
    eia_x3_has_dst_nxt =  1'b0;
    eia_x3_has_flg_nxt =  1'b0;
    eia_x3_att_nxt     =  4'h0;
    eia_x3_has_reg_sets_nxt = 1'b0;
    eia_x3_untimed_nxt =  1'b0;
    eia_x3_cnt_nxt     =  5'h0;
    eia_x3_res_data_nxt    = 32'h0;
    eia_x3_res_data_hi_nxt = 32'h0;
    eia_x3_res_flags_nxt   = 4'h0;
    eia_x3_res_xflags_nxt  = 4'h0;
  

  

  end
  else                                             // stall at x3 but continue to count down
  begin
    eia_x3_valid_nxt   =  eia_x3_valid;
    eia_x3_done_nxt    =  eia_x3_done |            // hold status on long stall
                          eia_x3_end;              // next cycle user_pipe is marked done
    eia_x3_kill_nxt    =  eia_x3_valid &
                         (x3_kill | eia_x3_kill);  // pending kill, remains valid till CA
    eia_x3_xtype_nxt   =  eia_x3_xtype;
    eia_x3_src64_inst_nxt = eia_x3_src64_inst;
    eia_x3_xnum_nxt    =  eia_x3_xnum;
    eia_x3_gnum_nxt    =  eia_x3_gnum;
    eia_x3_blocking_nxt=  eia_x3_valid & eia_x3_blocking;
    eia_x3_has_dst_nxt =  eia_x3_has_dst;
    eia_x3_has_flg_nxt =  eia_x3_has_flg;
    eia_x3_att_nxt     =  eia_x3_att;
    eia_x3_has_reg_sets_nxt = eia_x3_has_reg_sets;
    eia_x3_untimed_nxt =  eia_x3_untimed;
// leda W484 off
// leda B_3208 off
// LMD: possible carry in add/sub logic
// LJ:  impossible by design
    eia_x3_cnt_nxt     =  eia_x3_untimed | eia_x3_done ? 5'h0 : eia_x3_cnt - 1;
    eia_x3_res_data_nxt    = eia_pipe_x3_res_data;
    eia_x3_res_data_hi_nxt = eia_pipe_x3_res_data_hi;
    eia_x3_res_flags_nxt   = eia_pipe_x3_res_flags;
    eia_x3_res_xflags_nxt  = eia_x3_res_xflags_pre;
  

  
// leda B_3208 on
// leda W484 on  
  end
end

// staging registers

always @(posedge clk or posedge rst_a)
begin : x2_to_x3_0_PROC
  if (rst_a == 1'b1)
  begin
    eia_x3_valid     <=  1'b0;
    eia_x3_xtype     <= 2'd0;
    eia_x3_src64_inst <= 1'b0;
    eia_x3_xnum      <=  8'd0;
    eia_x3_gnum      <=  2'd0;
    eia_x3_blocking  <=  1'b0;
    eia_x3_has_dst   <=  1'b0;
    eia_x3_has_flg   <=  1'b0;
    eia_x3_att       <=  4'h0;
    eia_x3_has_reg_sets <= 1'b0;
    eia_x3_untimed   <=  1'b0;
  

  
  end
  else if (x2_to_x3_proc_0_cg0)
  begin
    eia_x3_valid     <=  eia_x3_valid_nxt;   
    eia_x3_xtype     <=  eia_x3_xtype_nxt; 
    eia_x3_src64_inst <= eia_x3_src64_inst_nxt;
    eia_x3_xnum      <=  eia_x3_xnum_nxt;    
    eia_x3_gnum      <=  eia_x3_gnum_nxt;    
    eia_x3_blocking  <=  eia_x3_blocking_nxt;
    eia_x3_has_dst   <=  eia_x3_has_dst_nxt; 
    eia_x3_has_flg   <=  eia_x3_has_flg_nxt; 
    eia_x3_att       <=  eia_x3_att_nxt;   
    eia_x3_has_reg_sets <= eia_x3_has_reg_sets_nxt;
    eia_x3_untimed   <=  eia_x3_untimed_nxt;
  

  
  end
end

always @(posedge clk or posedge rst_a)
begin : x2_to_x3_1_PROC
  if (rst_a == 1'b1)
  begin
    eia_x3_done        <=  1'b0;
    eia_x3_kill        <=  1'b0;
    eia_x3_cnt         <=  5'h0;
    eia_x3_res_data    <= 32'h0;
    eia_x3_res_data_hi <= 32'h0;
    eia_x3_res_flags   <=  4'h0;
    eia_x3_res_xflags  <=  4'h0;
  

  
  
  end
  else if (x2_to_x3_proc_1_cg0)
  begin
    eia_x3_done        <=  eia_x3_done_nxt;
    eia_x3_kill        <=  eia_x3_kill_nxt;
    eia_x3_cnt         <=  eia_x3_cnt_nxt;     
    eia_x3_res_data    <=  eia_x3_res_data_nxt;
    eia_x3_res_data_hi <=  eia_x3_res_data_hi_nxt;
    eia_x3_res_flags   <=  eia_x3_res_flags_nxt;
    eia_x3_res_xflags  <=  eia_x3_res_xflags_nxt;
  

  

  end
end

// X3 to CA logic moves in-progress or done eia instruction in sync with exu-pipe
// Only 4 cycle or more timed, any untimed (non-blocking) can end at this stage
// Most instruction information is handled here
//
// Actions:
//  _kill &  _done:  terminate tracking
//  _kill & ~_done:  allocate local graduation buffer to track end, no exu graduation
// ~_kill &  _done:  continue to wb, write implicit in wb
// ~_kill & ~_done:  allocate local graduation buffer, request exu graduation


// result selection and _end generation for ca instruction

  // declare ca_<grp>_end
  
reg      ca_evmww_end;
reg      ca_evmw_end;
reg      ca_evm_end;

reg            eia_ca_timed_instr_done;
reg   [3:0]    eia_ca_res_xflags_mux;   // selected xflags, from ext mux

reg  [31:0]    eia_ca_res_data_mux;     // selected data, from ext mux
reg  [31:0]    eia_ca_res_data_mux_hi;
reg   [3:0]    eia_ca_res_flags_mux;    // selected bflags, from ext mux

always @ (*)
begin :   eia_inst_untimed_ready_ca_PROC
  eia_ca_timed_instr_done = eia_ca_valid & ~eia_ca_done & ~eia_ca_untimed & (eia_ca_cnt == 5'h0);

  // assign defaults
      ca_evmww_end   =   1'b0;
      ca_evmw_end   =   1'b0;
      ca_evm_end   =   1'b0;
      eia_ca_end            =  1'b0;
      eia_ca_res_data_mux   = 32'h0;
      eia_ca_res_data_mux_hi= 32'h0;
      eia_ca_res_flags_mux  =  4'h0;
      eia_ca_res_xflags_mux =  4'h0;
      
  // generate active _end logic
  // mux out result and flags of the done at ca instruction
  case ( eia_ca_gnum )
    2'd0:     // group: evmww
      begin
        eia_ca_end            =  eia_ca_timed_instr_done;
        ca_evmww_end  =  eia_ca_timed_instr_done & (eia_ca_blocking | ~eia_ca_blocking & ~eia_ca_status_kill);
        eia_ca_res_data_mux_hi = evmww_res[63:32];
        eia_ca_res_data_mux    = evmww_res[31: 0];
        eia_ca_res_flags_mux  = evmww_bflags;
        eia_ca_res_xflags_mux = evmww_xflags;
      end
    2'd1:     // group: evmw
      begin
        eia_ca_end            =  eia_ca_timed_instr_done;
        ca_evmw_end  =  eia_ca_timed_instr_done & (eia_ca_blocking | ~eia_ca_blocking & ~eia_ca_status_kill);
        eia_ca_res_data_mux_hi = evmw_res[63:32];
        eia_ca_res_data_mux    = evmw_res[31: 0];
        eia_ca_res_flags_mux  = evmw_bflags;
        eia_ca_res_xflags_mux = evmw_xflags;
      end
    2'd2:     // group: evm
      begin
        eia_ca_end            =  eia_ca_timed_instr_done;
        ca_evm_end  =  eia_ca_timed_instr_done & (eia_ca_blocking | ~eia_ca_blocking & ~eia_ca_status_kill);
        eia_ca_res_data_mux_hi = evm_res[63:32];
        eia_ca_res_data_mux    = evm_res[31: 0];
        eia_ca_res_flags_mux  = evm_bflags;
        eia_ca_res_xflags_mux = evm_xflags;
      end
    default:
      begin
        // assign defaults
        ca_evmww_end   =   1'b0;
        ca_evmw_end   =   1'b0;
        ca_evm_end   =   1'b0;
        eia_ca_end             =  1'b0;
        eia_ca_res_data_mux    = 32'h0;
        eia_ca_res_data_mux_hi = 32'h0;
        eia_ca_res_flags_mux   =  4'h0;
        eia_ca_res_xflags_mux  =  4'h0;
      end
  endcase
end


// mux out ca result to eia_pipe

always @(*)
begin :  eia_exu_ca_res_9_PROC
    eia_exu_ca_res_valid    =   eia_ca_valid              &
                               (eia_ca_done | eia_ca_end) &          
                              ~(eia_ca_kill | ca_kill | ~ca_predicate_r | ~ca_q_cond); 
    eia_exu_ca_res_data     =  eia_ca_end & ~eia_ca_done ? eia_ca_res_data_mux :
                                                           eia_ca_res_data;
    eia_exu_ca_res_data_hi  =  eia_ca_end & ~eia_ca_done ? eia_ca_res_data_mux_hi :
                                                           eia_ca_res_data_hi;
    eia_exu_ca_res_flags    =  eia_ca_end & ~eia_ca_done ? eia_ca_res_flags_mux :
                                                           eia_ca_res_flags;
    eia_ca_res_xflags_pre   =  eia_ca_end & ~eia_ca_done ? eia_ca_res_xflags_mux :
                                                           eia_ca_res_xflags;
end

// generate i_<grp>_kill, i_<grp>_commit status signals

always @ (*)
begin :   eia_ux_status_signals_PROC

  // assign defaults


      i_evmww_kill   =  1'b0;
      i_evmww_commit =  1'b0;
      i_evmw_kill   =  1'b0;
      i_evmw_commit =  1'b0;
      i_evm_kill   =  1'b0;
      i_evm_commit =  1'b0;


      
  // generate active _kill and _commit logic
  case ( eia_ca_gnum )


    2'd0:     // group: evmww
      begin
        i_evmww_kill    =  eia_ca_status_kill;
        i_evmww_commit  =  eia_ca_status_commit;
      end
    2'd1:     // group: evmw
      begin
        i_evmw_kill    =  eia_ca_status_kill;
        i_evmw_commit  =  eia_ca_status_commit;
      end
    2'd2:     // group: evm
      begin
        i_evm_kill    =  eia_ca_status_kill;
        i_evm_commit  =  eia_ca_status_commit;
      end


    default:
      begin
        // assign defaults


        i_evmww_kill   =  1'b0;
        i_evmww_commit =  1'b0;
        i_evmw_kill   =  1'b0;
        i_evmw_commit =  1'b0;
        i_evm_kill   =  1'b0;
        i_evm_commit =  1'b0;


      end
  endcase
end

  

  

reg          eia_ca_valid_nxt;   
reg          eia_ca_done_nxt;
reg          eia_ca_kill_nxt;
reg [1:0]    eia_ca_xtype_nxt; 
reg          eia_ca_src64_inst_nxt;
reg [7:0] eia_ca_xnum_nxt; 
reg [1:0] eia_ca_gnum_nxt; 
reg          eia_ca_blocking_nxt; 
reg          eia_ca_has_dst_nxt; 
reg          eia_ca_has_flg_nxt; 
reg  [3:0]   eia_ca_att_nxt;    
reg          eia_ca_has_reg_sets_nxt;
reg          eia_ca_untimed_nxt; 
reg   [4:0]      eia_ca_cnt_nxt;     
reg [31:0]   eia_ca_res_data_nxt;
reg [31:0]   eia_ca_res_data_hi_nxt;
reg  [3:0]   eia_ca_res_flags_nxt;
reg  [3:0]   eia_ca_res_xflags_nxt;


// clock enable for all signals

wire ca_to_wb_proc_0_cg0 =   exu_x3_to_ca | eia_x3_to_ca
                           | exu_ca_to_wb | eia_ca_to_wb_killed
                           ;
wire ca_to_wb_proc_1_cg0 =   exu_x3_to_ca | eia_x3_to_ca
                           | exu_ca_to_wb | eia_ca_to_wb_killed
                           | eia_ca_valid;

// logic for all signals

always@(*)
begin :  x3_to_ca_9_PROC
if (exu_x3_to_ca || eia_x3_to_ca)           // pipeline enable x3->ca
                                                   // eia_: _kill moving forward)   
  begin
    eia_ca_valid_nxt   =  eia_x3_valid;
    eia_ca_done_nxt    =  eia_x3_done |             // hold status on long stall
                          eia_x3_end;               // next cycle user_pipe is marked done
    eia_ca_kill_nxt    =  eia_x3_valid & (x3_kill | eia_x3_kill);
                                                    // pending kill, remains valid till CA
    eia_ca_xtype_nxt   =  eia_x3_xtype;
    eia_ca_src64_inst_nxt = eia_x3_src64_inst;
    eia_ca_xnum_nxt    =  eia_x3_xnum;
    eia_ca_gnum_nxt    =  eia_x3_gnum;
    eia_ca_blocking_nxt=  eia_x3_valid & eia_x3_blocking;
    eia_ca_has_dst_nxt =  eia_x3_has_dst;
    eia_ca_has_flg_nxt =  eia_x3_has_flg;
    eia_ca_att_nxt     =  eia_x3_att;
    eia_ca_has_reg_sets_nxt = eia_x3_has_reg_sets;
    eia_ca_untimed_nxt =  eia_x3_untimed;
// leda W484 off
// leda B_3208 off
// LMD: possible carry in add/sub logic
// LJ:  impossible by design
    eia_ca_cnt_nxt     =  eia_x3_untimed | (eia_x3_cnt == 5'h0) ? 5'h0 : eia_x3_cnt - 1;
    eia_ca_res_data_nxt   =  eia_pipe_x3_res_data;    // possible done instruction
    eia_ca_res_data_hi_nxt=  eia_pipe_x3_res_data_hi;    // possible done instruction
    eia_ca_res_flags_nxt  =  eia_pipe_x3_res_flags;
    eia_ca_res_xflags_nxt =  eia_x3_res_xflags_pre;
  

  
// leda B_3208 on
// leda W484 on  
  end
  else if (  exu_ca_to_wb | eia_ca_to_wb_killed
           )
  begin 
    eia_ca_valid_nxt   =  1'b0;
    eia_ca_done_nxt    =  1'b0;
    eia_ca_kill_nxt    =   1'b0;
    eia_ca_xtype_nxt   =  2'd0;
    eia_ca_src64_inst_nxt = 1'b0;
    eia_ca_xnum_nxt    =   8'd0;
    eia_ca_gnum_nxt    =   2'd0;
    eia_ca_blocking_nxt=   1'b0;
    eia_ca_has_dst_nxt =   1'b0;
    eia_ca_has_flg_nxt =   1'b0;
    eia_ca_att_nxt     =   4'h0;
    eia_ca_has_reg_sets_nxt = 1'b0;
    eia_ca_untimed_nxt =   1'b0;
    eia_ca_cnt_nxt     =   5'h0;
    eia_ca_res_data_nxt   = 32'h0;
    eia_ca_res_data_hi_nxt= 32'h0;
    eia_ca_res_flags_nxt  =  4'h0;
    eia_ca_res_xflags_nxt =  4'h0;
  

  
  end
  else                                             // stall at ca but continue to count down
  begin
    eia_ca_valid_nxt   =  eia_ca_valid;
    eia_ca_done_nxt    =  eia_ca_done |            // hold status on long stall
                          eia_ca_end;              // next cycle user_pipe is marked done
    eia_ca_kill_nxt    =  eia_ca_valid &
                          (ca_kill | eia_ca_kill | ~ca_predicate_r | ~ca_q_cond); // pending kill, remains valid till CA
    eia_ca_xtype_nxt   =  eia_ca_xtype;
    eia_ca_src64_inst_nxt = eia_ca_src64_inst;
    eia_ca_xnum_nxt    =  eia_ca_xnum;
    eia_ca_gnum_nxt    =  eia_ca_gnum;
    eia_ca_blocking_nxt=  eia_ca_valid & eia_ca_blocking;
    eia_ca_has_dst_nxt =  eia_ca_has_dst;
    eia_ca_has_flg_nxt =  eia_ca_has_flg;
    eia_ca_att_nxt     =  eia_ca_att;
    eia_ca_has_reg_sets_nxt = eia_ca_has_reg_sets;
    eia_ca_untimed_nxt =  eia_ca_untimed;
// leda W484 off
// leda B_3208 off
// LMD: possible carry in add/sub logic
// LJ:  impossible by design
    eia_ca_cnt_nxt     =  eia_ca_untimed | eia_ca_done | ~eia_ca_valid ? 5'h0 : eia_ca_cnt - 1;
    eia_ca_res_data_nxt   =  eia_exu_ca_res_data;
    eia_ca_res_data_hi_nxt=  eia_exu_ca_res_data_hi;
    eia_ca_res_flags_nxt  =  eia_exu_ca_res_flags;
    eia_ca_res_xflags_nxt =  eia_ca_res_xflags_pre;
  

  
// leda B_3208 on
// leda W484 on  
  end
end

// staging registers

always @(posedge clk or posedge rst_a)
begin : ca_to_wb_0_PROC
  if (rst_a == 1'b1)
  begin
    eia_ca_valid     <=  1'b0;
    eia_ca_xtype     <= 2'd0;
    eia_ca_src64_inst <= 1'b0;
    eia_ca_xnum      <=  8'd0;
    eia_ca_gnum      <=  2'd0;
    eia_ca_blocking  <=  1'b0;
    eia_ca_has_dst   <=  1'b0;
    eia_ca_has_flg   <=  1'b0;
    eia_ca_att       <=  4'h0;
    eia_ca_has_reg_sets <= 1'b0;
    eia_ca_untimed   <=  1'b0;
  

  
  end
  else if (ca_to_wb_proc_0_cg0)
  begin
    eia_ca_valid     <=  eia_ca_valid_nxt;   
    eia_ca_xtype     <=  eia_ca_xtype_nxt; 
    eia_ca_src64_inst <= eia_ca_src64_inst_nxt;
    eia_ca_xnum      <=  eia_ca_xnum_nxt;    
    eia_ca_gnum      <=  eia_ca_gnum_nxt;    
    eia_ca_blocking  <=  eia_ca_blocking_nxt;
    eia_ca_has_dst   <=  eia_ca_has_dst_nxt; 
    eia_ca_has_flg   <=  eia_ca_has_flg_nxt; 
    eia_ca_att       <=  eia_ca_att_nxt;
    eia_ca_has_reg_sets <= eia_ca_has_reg_sets_nxt;
    eia_ca_untimed   <=  eia_ca_untimed_nxt; 
  

  
  end
end

always @(posedge clk or posedge rst_a)
begin : ca_to_wb_1_PROC
  if (rst_a == 1'b1)
  begin
    eia_ca_done      <=  1'b0;
    eia_ca_kill      <=  1'b0;
    eia_ca_cnt       <=  5'h0;
    eia_ca_res_data  <= 32'h0;
    eia_ca_res_flags <=  4'h0;
    eia_ca_res_xflags<=  4'h0;
  

  

  end
  else if (ca_to_wb_proc_1_cg0)
  begin
    eia_ca_done      <=  eia_ca_done_nxt;
    eia_ca_kill      <=  eia_ca_kill_nxt;
    eia_ca_cnt       <=  eia_ca_cnt_nxt;     
    eia_ca_res_data  <=  eia_ca_res_data_nxt;
// leda NTL_RST03 off
// LMD: no reset for reg
// LJ:  data reg, needs no reset
    eia_ca_res_data_hi<=  eia_ca_res_data_hi_nxt;
// leda NTL_RST03 on
    eia_ca_res_flags <=  eia_ca_res_flags_nxt;
    eia_ca_res_xflags<=  eia_ca_res_xflags_nxt;
  

  

  end
end

// CA to WB logic retires done eia instruction.
// Explicit results are handled by exu_pipe
// eia_pipe maintains implicit attributes for one cycle and updates shadow -> main
reg                      wb_cr_commit_wen;
reg                      wb_ar_commit_wen;
reg    [7:0]     wb_retire_xnum;

wire                     eia_wb_wr_cr = eia_wb_att[3];
wire                     eia_wb_rd_cr = eia_wb_att[2];
wire                     eia_wb_wr_ar = eia_wb_att[1];
wire                     eia_wb_rd_ar = eia_wb_att[0];

// assign retirement info from wa stage, no eia grad buffer in this config

wire   [3:0]             res_xflags        = wb_res_xflags;

  

  
  

reg          eia_wb_valid_nxt;   
reg [1:0]    eia_wb_xtype_nxt;  
reg          eia_wb_kill_nxt;
reg [7:0] eia_wb_xnum_nxt; 
reg [1:0] eia_wb_gnum_nxt; 
reg          eia_wb_blocking_nxt; 
reg          eia_wb_has_flg_nxt; 
reg  [3:0]   wb_res_xflags_nxt;     
reg  [3:0]   eia_wb_att_nxt;  
reg          eia_wb_has_reg_sets_nxt;
reg          eia_wb_q_cond_nxt;

// clock enable for all signals

wire wb_to_nnl_proc_cg0 = exu_ca_to_wb |
                          eia_ca_to_wb_killed |
                          eia_wb_valid;

// logic for all signals

always@(*)
begin :  ca_to_wb_9_PROC
if (exu_ca_to_wb | eia_ca_to_wb_killed)
  begin
    eia_wb_valid_nxt   =  eia_ca_valid;
    eia_wb_xtype_nxt   =  eia_ca_xtype;
    eia_wb_kill_nxt    =  ca_kill | eia_ca_kill |  // pending kill in CA
                         ~ca_predicate_r | ~ca_q_cond;// conditional instruction
    eia_wb_xnum_nxt    =  eia_ca_xnum;
    eia_wb_gnum_nxt    =  eia_ca_gnum;
    eia_wb_blocking_nxt=  eia_ca_blocking;
    eia_wb_has_flg_nxt =  eia_ca_has_flg;
    wb_res_xflags_nxt  =  eia_ca_res_xflags_pre;   // result value of xflags
    eia_wb_att_nxt     =  eia_ca_att;
    eia_wb_has_reg_sets_nxt = eia_ca_has_reg_sets;
    eia_wb_q_cond_nxt  =  ca_q_cond;               // evaluated condition code of <eia_instr>.<cc>
                                                   // do not retire implicit result if false
  

  
  end
  else                                             // no instruction
  begin 
    eia_wb_valid_nxt   =  1'b0;
    eia_wb_xtype_nxt   = 2'd0;
    eia_wb_kill_nxt    =  1'b0;
    eia_wb_xnum_nxt    =  8'd0;
    eia_wb_gnum_nxt    =  2'd0;
    eia_wb_blocking_nxt=  1'b0;
    eia_wb_has_flg_nxt =  1'b0;
    wb_res_xflags_nxt  =  4'h0;
    eia_wb_att_nxt     =  4'h0;
    eia_wb_has_reg_sets_nxt = 1'b0;
    eia_wb_q_cond_nxt  =  1'b0;
  

  
  end
end

// staging registers and logic
// spyglass disable_block W528
// SMD: Variable set but not read
// SJ:  it will be removed by synthesis
always @(posedge clk or posedge rst_a)
begin : ca_to_wb_PROC
  if (rst_a == 1'b1)
  begin
    eia_wb_valid   <=  1'b0;
    eia_wb_xtype   <= 2'd0;
    eia_wb_kill    <=  1'b0;
    eia_wb_xnum    <=  8'd0;
    eia_wb_gnum    <=  2'd0;
    eia_wb_blocking<=  1'b0;
    eia_wb_has_flg <=  1'b0;
    wb_res_xflags  <=  4'h0;
    eia_wb_att     <=  4'h0;
    eia_wb_has_reg_sets <= 1'b0;
    eia_wb_q_cond  <=  1'b0;
  

  
  end
  else if (wb_to_nnl_proc_cg0)
  begin 
    eia_wb_valid   <= eia_wb_valid_nxt;
    eia_wb_xtype   <= eia_wb_xtype_nxt;
    eia_wb_kill    <= eia_wb_kill_nxt;
    eia_wb_xnum    <= eia_wb_xnum_nxt;
    eia_wb_gnum    <= eia_wb_gnum_nxt;
    eia_wb_blocking<= eia_wb_blocking_nxt;
    eia_wb_has_flg <= eia_wb_has_flg_nxt;
    wb_res_xflags  <= wb_res_xflags_nxt;
    eia_wb_att     <= eia_wb_att_nxt;
    eia_wb_has_reg_sets <= eia_wb_has_reg_sets_nxt;
    eia_wb_q_cond  <= eia_wb_q_cond_nxt;
  

  
  end
end
// spyglass enable_block W528

// commit pending implicit updates to state: copy shadow to main
// killed instruction in ca: copy main to shadow
// spyglass disable_block W528
// SMD: Variable set but not read
// SJ:  it will be removed by synthesis
always @ (*)
begin :  wb_cr_commit_wen_9_PROC
  wb_cr_commit_wen = eia_wb_wr_cr & eia_wb_valid & ~eia_wb_kill ;
  wb_ar_commit_wen = eia_wb_wr_ar & eia_wb_valid & ~eia_wb_kill ;
  wb_retire_xnum   = eia_wb_valid ? eia_wb_xnum : 0;
end
// spyglass enable_block W528

// spyglass disable_block W528
// SMD: Variable set but not read
// SJ:  it will be removed by synthesis
assign eia_exu_grad_req            = 1'b0;
assign eia_exu_retire_req          = 1'b0;
assign eia_exu_retire_res_data     = 32'h0;
assign eia_exu_retire_res_data_hi  = 32'h0;
assign eia_exu_retire_res_flags    =  4'h0;
assign eia_exu_retire_tag          = 3'h0;

// spyglass enable_block W528

// or all _end signals of each user pipe

always @(*)
begin :  inst_group_end_9_PROC
  evmww_end  =    x1_evmww_end
                       |  x2_evmww_end
                       |  x3_evmww_end
                       |  ca_evmww_end
                                  ;
  evmw_end  =    x1_evmw_end
                       |  x2_evmw_end
                       |  x3_evmw_end
                       |  ca_evmw_end
                                  ;
  evm_end  =    x1_evm_end
                       |  x2_evm_end
                       |  x3_evm_end
                       |  ca_evm_end
                                  ;
end

// general declarations


wire   [7:0]     i_xnum_da = i_xnum;
reg    [7:0]     i_xnum_sa;



reg                      eia_sa_hazard_del; // extends hazard check in sa upon
                                            // moving next instruction da -> sa
wire                     eia_hazard_sel_sa = (eia_sa_valid | sa_valid_r) &
                                             (eia_sa_hazard |     // see comment
                                              eia_sa_hazard_del); // da was not checked!!!

                            // source for eia_hazard register and credentials.
                            // Normally checked at DA and registered for SA.
                            // If hazard detected then source reverts to SA and
                            // and pipe is stalled at SA until hazard clears.
                            // When that happens, an eia instruction at DA
                            // would move forward to SA with a speculative
                            // hazard stall (term "eia_sa_hazard_del").
                            // If exu_pipe stalls DA then the machine returns
                            // to its normal mode of hazard checking at DA.

wire [7:0] i_sel_xnum = eia_hazard_sel_sa ? i_xnum_sa : i_xnum_da;

// xnum 
always @(posedge clk_ungated or posedge rst_a)
begin : xnum_sa_PROC
  if (rst_a == 1'b1)
  begin
    i_xnum_sa          <=  8'h0;
  end
  else if (exu_da_to_sa)   // pipeline enable da->sa
  begin
    i_xnum_sa          <= i_xnum_da        ;
  end
end
// spyglass disable_block W528
// SMD: Variable set but not read
// SJ:  it will be removed by synthesis
wire                     eia_da_wr_ar = i_att[1];
wire                     eia_da_rd_ar = i_att[0];
wire                     eia_sa_wr_ar = eia_sa_att[1];
wire                     eia_sa_rd_ar = eia_sa_att[0];
wire                     eia_x1_wr_ar = eia_x1_att[1];
wire                     eia_x1_rd_ar = eia_x1_att[0];
wire                     eia_x2_wr_ar = eia_x2_att[1];
wire                     eia_x2_rd_ar = eia_x2_att[0];
wire                     eia_x3_wr_ar = eia_x3_att[1];
wire                     eia_x3_rd_ar = eia_x3_att[0];
wire                     eia_ca_wr_ar = eia_ca_att[1];
wire                     eia_ca_rd_ar = eia_ca_att[0];
// spyglass enable_block W528
reg                      eia_aux_waw_hazard;
reg                      eia_aux_raw_hazard;
reg                      eia_aux_rd_prot;
reg                      eia_aux_wr_prot;

  // There are no extension core registers defined so only driving ports
  //
assign  eia_sa_rf_rdata0     =  32'd0;
assign  eia_sa_rf_rdata0_hi  =  32'd0;
assign  eia_sa_rf_rdata1     =  32'd0;
assign  eia_sa_rf_rdata1_hi  =  32'd0;

assign  eia_da_ra0_ext    =  1'b0;
assign  eia_da_ra1_ext    =  1'b0;
assign  eia_da_wa0_ext    =  1'b0;
assign  eia_da_wa1_ext    =  1'b0;

reg                           illegal_f_bit;
reg                           kernel_inst;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Logic to determine whether kernel privileges are needed by any extension //
// instructions, condition codes or core registers.                         //
// ECR cause is set to "disabled extension" for eia privilege violations.   //
// The ECR parameter is set currently to 8'h0.                              //
//                                                                          //
// Priority:                                                                //
//                                                                          //
// opcode violation, basecase:  basic instruction privilege violation       //
// opcode violation, eia:  disabled extension privilege violation           //
// No opcode violation but extension cc or cr:  disabled extension          //
//                                                                          //
// Note that eia opcode violation is detected here and merged in alb_decode.//
// Exception logic has to check if eia instruction violation is raised with //
// the decode instruction violation and consider it "disabled extension".   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : eia_priv_check_PROC

  kernel_inst = eia_da_valid & i_kernel;
  illegal_f_bit     =  eia_da_valid  & ~i_fwrite & da_swap_f_bit;


  // Determine whether there is any illegal access to a defined extension
  // core register, which may occur if a write is decoded to a read-only
  // register or vice versa.
  //
  eia_da_illegal = 1'b0
                   | illegal_f_bit
                        ;
                          
  // Determine whether kernel privileges are required by the extension
  // instruction or any core registers that are used by the instruction
  // at the decode/execute stage.
  //
  eia_da_kernel_instr = kernel_inst;



end

///
//////////////////////////////////////////////////////////////////////////////
// Prioritize Instruction Exceptions                                        //
//////////////////////////////////////////////////////////////////////////////

reg       [7:0]       i_kernel_ext_xnum;  // decoded extension number
reg       [5:0]               eia_da_kernel_xpu_id;  // = exception parameter
reg       [5:0]               eia_sa_kernel_xpu_id;  // = exception parameter
reg       [5:0]               eia_x1_kernel_xpu_id;  // = exception parameter
reg       [5:0]               eia_x2_kernel_xpu_id;  // = exception parameter
reg       [5:0]               eia_x3_kernel_xpu_id;  // = exception parameter

always@(*)
begin : eia_da_kernel_param_PROC   
casez ({
        eia_da_valid & kernel_inst,
        1'b0,
        4'h0
      })
      
  6'b1_?_??_??:   i_kernel_ext_xnum = i_xnum;
  default:        i_kernel_ext_xnum = 8'd0;

endcase

// xref kernel xnum to xpu_num
case (i_kernel_ext_xnum)
      8'd0:     eia_da_kernel_xpu_id = 6'h1F;
  default:   eia_da_kernel_xpu_id = 6'd0;
endcase

end        // eia_da_kernel_param_PROC   

  // stage kernel param to X3
  always @(posedge clk_ungated or posedge rst_a)
  begin : eia_sa_kernel_xpu_id_PROC
    if (rst_a == 1'b1)
      eia_sa_kernel_xpu_id <=  6'd0;
    else if (exu_da_to_sa)
      eia_sa_kernel_xpu_id <=  eia_da_kernel_xpu_id;
  end

  always @(posedge clk_ungated or posedge rst_a)
  begin : eia_x1_kernel_xpu_id_PROC
    if (rst_a == 1'b1)
      eia_x1_kernel_xpu_id <=  6'd0;
    else if (exu_sa_to_x1)
      eia_x1_kernel_xpu_id <=  eia_sa_kernel_xpu_id;
  end

  always @(posedge clk_ungated or posedge rst_a)
  begin : eia_x2_kernel_xpu_id_PROC
    if (rst_a == 1'b1)
      eia_x2_kernel_xpu_id <=  6'd0;
    else if (exu_x1_to_x2)
      eia_x2_kernel_xpu_id <=  eia_x1_kernel_xpu_id;
  end

  always @(posedge clk_ungated or posedge rst_a)
  begin : eia_x3_kernel_xpu_id_PROC
    if (rst_a == 1'b1)
      eia_x3_kernel_xpu_id <=  6'd0;
    else if (exu_x2_to_x3)
      eia_x3_kernel_xpu_id <=  eia_x2_kernel_xpu_id;
  end


  // Stage kernel data to x3
  // 

// spyglass disable_block W528
// SMD: Variable set but not read
// SJ:  it will be removed by synthesis
  assign eia_x2_kernel_cc = 1'b0;
// spyglass enable_block W528  

  assign eia_x2_kernel_cr = 1'b0;

  assign eia_x2_is_eia_instr = eia_x2_valid;

  assign eia_x3_kernel_param = eia_x3_kernel_xpu_id;

// spyglass disable_block W528
// SMD: Variable set but not read
// SJ:  it will be removed by synthesis
assign eia_inst_valid        = eia_hazard_sel_sa ? eia_sa_valid          : eia_da_valid;
assign eia_att_cr_nocheck    = eia_hazard_sel_sa ? eia_sa_att_cr_nocheck : eia_da_att_cr_nocheck;
assign eia_inst_has_reg_sets = eia_hazard_sel_sa ? eia_sa_has_reg_sets   : eia_da_has_reg_sets;
assign eia_src64_inst        = eia_hazard_sel_sa ? eia_sa_src64_inst     : i_src64;



// spyglass enable_block W528

///
  // Detect implicit-vs-implicit hazard for aux registers: extension 
  // number where the register is declared is checked against valid
  // in-flight instructions from the same extension with specific core
  // register use attributes.
  //
  // Detection is speculative and needs to be qualified.
  // Logic is calculated in DA and registered for use at SA.
  // Logic is re-purposed: normally checks the DA instruction, but if
  // hazard was detected then mux logic changes to check the SA
  // instruction (which slipped with a hazard from DA). In this case
  // the check against the _sa_ instruction is removed and the attributes
  // are converted to _da_ instruction.
  //
 
reg  eia_ar_hazard;
reg  sa_ar_hazard_r;
reg  eia_lr_sr_hazard;
reg  eia_dir_ar_raw_hazard;
reg  eia_dir_ar_waw_hazard;
reg  eia_dir_ar_war_hazard;

// explicit-vs-implicit hazards

reg   eia_drw_after_sr_hazard;


reg   x1_lr_state_r;
reg   x1_sr_state_r;
reg   x2_lr_state_r;
reg   x2_sr_state_r;
reg   x3_sr_state_r;
reg   ca_sr_state_r;
reg   wb_sr_state_r;



always @*
begin : eia_ar_hazard_PROC


  // raw hazard detection for incoming eia instruction
  // note: we do not know if there is a pending SR to eia reg until x3, so
  //  that register must be serializing to avoid hazard with implicit writers
               
// leda W563 off
// LMD: reduction of single bit expression is redundant
// LJ:  configurable field may be a single bit 
  eia_dir_ar_raw_hazard = 1'b0
// leda B_3201 off
// leda B_3219 off
// LMD: Unequal length operand in comparison operator
// LJ:  it is to reduced counter width define  
    | eia_inst_valid & eia_inst_has_reg_sets & (  
      (~eia_hazard_sel_sa & 
      eia_sa_valid  & (eia_sa_xnum == i_sel_xnum) & (1'b0
      ))
    | (eia_x1_valid  & (eia_x1_xnum == i_sel_xnum) & (~eia_x1_kill) & (1'b0
      ))
    | (eia_x2_valid  & (eia_x2_xnum == i_sel_xnum) & (~eia_x2_kill) & (1'b0
      ))
    | (eia_x3_valid  & (eia_x3_xnum == i_sel_xnum) & (~eia_x3_kill) & (1'b0
      ))
    | (eia_ca_valid  & (eia_ca_xnum == i_sel_xnum) & (~eia_ca_kill) & (1'b0
      )) 
      )
// leda B_3201 on
// leda B_3219 on    
  ;
                                          
  // waw/war hazard detection for incoming eia instruction
  eia_dir_ar_waw_hazard = 1'b0
     | eia_inst_valid & eia_inst_has_reg_sets & (  
      (~eia_hazard_sel_sa & 
      eia_sa_valid  & (eia_sa_xnum == i_sel_xnum) & (1'b0
      ))
    | (eia_x1_valid  & (eia_x1_xnum == i_sel_xnum) & (~eia_x1_kill) & (1'b0
      ))
    | (eia_x2_valid  & (eia_x2_xnum == i_sel_xnum) & (~eia_x2_kill) & (1'b0
      ))
    | (eia_x3_valid  & (eia_x3_xnum == i_sel_xnum) & (~eia_x3_kill) & (1'b0
      ))
    | (eia_ca_valid  & (eia_ca_xnum == i_sel_xnum) & (~eia_ca_kill) & (1'b0
      ))
      )
      ;
  eia_dir_ar_war_hazard = 1'b0
// leda B_3201 off
// leda B_3219 off
// LMD: Unequal length operand in comparison operator
// LJ:  it is to reduced counter width define  
    | eia_inst_valid & eia_inst_has_reg_sets & (  
      (~eia_hazard_sel_sa & 
      eia_sa_valid  & (eia_sa_xnum == i_sel_xnum) & (1'b0
      ))
    | (eia_x1_valid  & (eia_x1_xnum == i_sel_xnum) & (~eia_x1_kill) & (1'b0
      ))
    | (eia_x2_valid  & (eia_x2_xnum == i_sel_xnum) & (~eia_x2_kill) & (1'b0
      ))
    | (eia_x3_valid  & (eia_x3_xnum == i_sel_xnum) & (~eia_x3_kill) & (1'b0
      ))
    | (eia_ca_valid  & (eia_ca_xnum == i_sel_xnum) & (~eia_ca_kill) & (1'b0
      )) 
      )
// leda B_3201 on
// leda B_3219 on    
      ;
  
// leda W563 on

  // Detect explicit-vs-implicit hazard for aux registers:  
  // required to avoid deadlock when direct write in x1 while lr/sr in x2.





  eia_drw_after_sr_hazard = eia_sa_valid & ~sa_kill &
                           (eia_sa_rd_ar | eia_sa_wr_ar | eia_sa_has_flg) &
       (  x1_sr_state_r |
          x2_sr_state_r |
          x3_sr_state_r & aux_eia_ren_r & aux_write |
          ca_sr_state_r |
          wb_sr_state_r
       );

  // Accumulate all hazard sources @ sa

  eia_ar_hazard = eia_dir_ar_raw_hazard     |
                  eia_dir_ar_waw_hazard     |
                  eia_dir_ar_war_hazard     ;

  eia_lr_sr_hazard =
                  eia_drw_after_sr_hazard   ;

end


reg   x1_lr_state_nxt;
reg   x1_sr_state_nxt;
reg   x2_lr_state_nxt;
reg   x2_sr_state_nxt;
reg   x3_sr_state_nxt;
reg   ca_sr_state_nxt;
reg   wb_sr_state_nxt;

always @*
begin : aux_lr_sr_state_comb_PROC
    x1_lr_state_nxt = x1_lr_state_r;
    x1_sr_state_nxt = x1_sr_state_r;
    x2_lr_state_nxt = x2_lr_state_r;
    x2_sr_state_nxt = x2_sr_state_r;
    x3_sr_state_nxt = x3_sr_state_r;
    ca_sr_state_nxt = ca_sr_state_r;
    wb_sr_state_nxt = wb_sr_state_r;

    if (exu_sa_to_x1 && !sa_kill)
    begin
      x1_lr_state_nxt =  sa_lr_op_r;
      x1_sr_state_nxt =  sa_sr_op_r;
    end
    else if (exu_x1_to_x2 | x1_kill)
    begin
      x1_lr_state_nxt =  1'b0;
      x1_sr_state_nxt =  1'b0;
    end

    if (exu_x1_to_x2 && !x1_kill)
    begin
      x2_lr_state_nxt =  x1_lr_state_r;
      x2_sr_state_nxt =  x1_sr_state_r;
    end
    else if (exu_x2_to_x3 | x2_kill)
    begin
      x2_lr_state_nxt =  1'b0;
      x2_sr_state_nxt =  1'b0;
    end

    if (exu_x2_to_x3 && !x2_kill)
    begin
      x3_sr_state_nxt =  x2_sr_state_r;
    end
    else if (exu_x3_to_ca | x3_kill)
    begin
      x3_sr_state_nxt =  1'b0;
    end

    if (exu_x3_to_ca && !x3_kill)
      //ca_sr_state_r  <=  aux_eia_wen_r & ~eia_aux_unimpl;
      ca_sr_state_nxt =  ~eia_aux_unimpl & aux_eia_ren_r & aux_write;
    else
    if (exu_ca_commit | ca_kill)
      ca_sr_state_nxt =  1'b0;

    if (exu_ca_commit && !ca_kill && ca_q_cond)
      wb_sr_state_nxt =  ca_sr_state_r;
    else
      wb_sr_state_nxt =  1'b0;

end

always @(posedge clk_ungated or posedge rst_a)
begin : aux_lr_sr_state_PROC
  if (rst_a == 1'b1)
  begin
      x1_lr_state_r  <=  1'b0;
      x1_sr_state_r  <=  1'b0;
      x2_lr_state_r  <=  1'b0;
      x2_sr_state_r  <=  1'b0;
      x3_sr_state_r  <=  1'b0;
      ca_sr_state_r  <=  1'b0;
      wb_sr_state_r  <=  1'b0;
  end
  else
  begin
      x1_lr_state_r  <=  x1_lr_state_nxt;
      x1_sr_state_r  <=  x1_sr_state_nxt;
      x2_lr_state_r  <=  x2_lr_state_nxt;
      x2_sr_state_r  <=  x2_sr_state_nxt;
      x3_sr_state_r  <=  x3_sr_state_nxt;
      ca_sr_state_r  <=  ca_sr_state_nxt;
      wb_sr_state_r  <=  wb_sr_state_nxt;
  end

end

reg sa_ar_hazard_nxt;
always @*
begin : aux_regs_hazard_comb_PROC
  if (exu_da_to_sa)                           // pipeline enable da->sa
    sa_ar_hazard_nxt =  eia_ar_hazard & ~da_swap_kill;  // _kill redundant, invalidated
  else if (exu_sa_to_x1 || sa_kill)
    sa_ar_hazard_nxt =  1'b0;
  else
    sa_ar_hazard_nxt =  eia_ar_hazard & sa_valid_r & ~sa_kill;
end
always @(posedge clk_ungated or posedge rst_a)
begin : aux_regs_hazard_PROC
  if (rst_a == 1'b1)
    sa_ar_hazard_r  <=  1'b0;
  else
    sa_ar_hazard_r  <=  sa_ar_hazard_nxt;
end


  // Detect count of candidate instruction (timed only, count > 4) conflicting 
  // with in-flight instructions and block the issue.
  // Short instruction up to 4 clocks are also included in this logic, but can
  // be optimized if needed.
  // Instructions with 64-bit source operands start at X2 and add 1 to the count.

reg   [5:0]   eia_sa_eff_cnt;
reg                        eia_sa_inst_count_hazard;  
reg                        eia_sa_inst_is_64;
  
always @ (*)
begin :   eia_inst_count_hazard_PROC
// leda W484 off
// LMD: possible carry in add/sub logic
// LJ:  carry does not matter
  eia_sa_eff_cnt = 
                    eia_sa_src64 ? {1'b0,eia_sa_cnt} + 6'h1 :
                    {1'b0,eia_sa_cnt};
// leda W484 on
    
  eia_sa_inst_is_64 = eia_sa_src64;

// leda B3201 off
// LMD: LHS?RHS in comparison logic
// LJ:  correct by design
  eia_sa_inst_count_hazard =  eia_sa_valid & (
                             (eia_sa_inst_is_64 & (eia_sa_cnt > 3)) |
                             (eia_sa_cnt > 4)) &   // check only potential post-commit
      (                                            // retirement conflict
       (eia_x1_valid & (({1'b0,eia_x1_cnt} == eia_sa_eff_cnt) | (eia_sa_inst_is_64 & ({1'b0,eia_x1_cnt} > eia_sa_eff_cnt))))
     | (eia_x2_valid & (({1'b0,eia_x2_cnt} == eia_sa_eff_cnt) | (eia_sa_inst_is_64 & ({1'b0,eia_x2_cnt} > eia_sa_eff_cnt))))
     | (eia_x3_valid & (({1'b0,eia_x3_cnt} == eia_sa_eff_cnt) | (eia_sa_inst_is_64 & ({1'b0,eia_x3_cnt} > eia_sa_eff_cnt))))
     | (eia_ca_valid & (({1'b0,eia_ca_cnt} == eia_sa_eff_cnt) | (eia_sa_inst_is_64 & ({1'b0,eia_ca_cnt} > eia_sa_eff_cnt))))
      );
// leda B3201 on
end

  // Detect killed eia instruction in x1-ca with leading non-killed eia instruction.
  // eia_pipe tracks the killed instructions but exu_pipe considers them bubbles
  // and may issue more instructions to "close the bubbles" up to a non-killed
  // instruction.
  // Interesting scenario can happen on early mispredict, when a bcc instruction
  // is in X2 with an eia instruction in X1 (killed).
  // The bcc instruction remains valid in the exu_pipe and is a bubble in eia_pipe.
  // The killed eia instruction remains valid in the eia_pipe but is a bubble in
  // the exu_pipe.
  // If there are valid eia instructions in x3 and/or ca and they stall, the bcc and
  // the killed eia instruction will queue up in the same slot behind them. 
  // The commit of the bcc coincides with the transfer of the context of the killed
  // eia instruction to the local grad buffer.
  // It is OK to issue non-eia instructions, which are not tracked in the eia_pipe.
  // eia_pipe will propagate the killed eia instructions forward unconditionally and
  // retire them to local grad buffers for completion in their own instruction pipes.
  // The serious corner case is a stalled non-killed eia instruction at ca, for example
  // untimed with no exu graduation buffer available.
  // eia_pipe will push the killed instruction forward until they hit a non-bubble and
  // wait for it to resolve so they can get through ca staging and then to a local
  // grad buffers.

reg     eia_sa_inst_kill_hazard;  

// spyglass disable_block STARC05-2.8.1.3
// SMD: Case labels overlap
// SJ:  Cases have priority so will not trigger multiple cases at once
always @ (*)
begin :   eia_inst_kill_hazard_PROC
   casez ({
          eia_ca_valid & ~eia_ca_kill & ~eia_ca_end,      // Non-killed eia
          eia_x3_valid & ~eia_x3_kill & ~eia_x3_end,
          eia_x2_valid & ~eia_x2_kill & ~eia_x2_end,
          eia_x1_valid & ~eia_x1_kill & ~eia_x1_end,
          eia_ca_valid &  eia_ca_kill & (eia_ca_cnt > 4), // Killed eia
          eia_x3_valid &  eia_x3_kill & (eia_x3_cnt > 4),
          eia_x2_valid &  eia_x2_kill & (eia_x2_cnt > 4),
          eia_x1_valid &  eia_x1_kill & (eia_x1_cnt > 4)
          }  )
    8'b1???_?1??,
    8'b1???_??1?,
    8'b1???_???1,
    8'b01??_??1?,
    8'b01??_???1,
    8'b001?_???1:  eia_sa_inst_kill_hazard = 1'b1;
    default:       eia_sa_inst_kill_hazard = 1'b0;
  endcase
end
// spyglass enable_block STARC05-2.8.1.3 

  // Detect candidate instruction target pipe busy signal.

reg     eia_sa_inst_pipe_busy;         // decode
reg     eia_sa_inst_pipe_busy_hazard;  // qualified hazard signal

always @ (*)
begin :   eia_inst_pipe_busy_hazard_PROC
  case ( eia_sa_gnum )

    2'd0:     // group: evmww
      eia_sa_inst_pipe_busy  =   i_evmww_busy;
    2'd1:     // group: evmw
      eia_sa_inst_pipe_busy  =   i_evmw_busy;
    2'd2:     // group: evm
      eia_sa_inst_pipe_busy  =   i_evm_busy;
    default:
      eia_sa_inst_pipe_busy  =   1'b0;
  endcase

  eia_sa_inst_pipe_busy_hazard =  eia_sa_valid &
                                 (eia_sa_xtype == 1 || eia_sa_xtype == 2) &
                                  eia_sa_inst_pipe_busy;

end
wire            sa_bflags_hazard = eia_sa_valid & ~exu_sa_bflags_ready & (eia_sa_has_flg | ~sa_q_field[4] & (|sa_q_field[3:0]));
wire            sa_xflags_hazard =     (sa_valid_r   & sa_q_field[4]
                                      | eia_sa_valid & eia_sa_has_flg) &  // eia cc at sa
                                   (   eia_x1_valid & eia_x1_has_flg 
                                     | eia_x2_valid & eia_x2_has_flg 
                                     | eia_x3_valid & eia_x3_has_flg 
                                     | eia_ca_valid & eia_ca_has_flg 
                                         );


wire eia_killed_blocking_inst_hazard =
         eia_sa_valid & eia_sa_blocking &  (
         eia_x1_valid & eia_x1_blocking & eia_x1_kill & (eia_sa_gnum == eia_x1_gnum) & ~eia_x1_done |
         eia_x2_valid & eia_x2_blocking & eia_x2_kill & (eia_sa_gnum == eia_x2_gnum) & ~eia_x2_done |
         eia_x3_valid & eia_x3_blocking & eia_x3_kill & (eia_sa_gnum == eia_x3_gnum) & ~eia_x3_done |
         eia_ca_valid & eia_ca_blocking & eia_ca_kill & (eia_sa_gnum == eia_ca_gnum) & ~eia_ca_done
                             );

///
// All hazards are merged at sa to block an issue of a candidate instruction
always @ (*)
begin :  eia_sa_hazard_PROC
 eia_sa_hazard =  sa_bflags_hazard              |   // bflags operand must be valid at sa
                  sa_xflags_hazard              |   // xflags operand must be valid at sa
                   sa_ar_hazard_r               |   // implicit aux  reg
                   eia_sa_inst_pipe_busy_hazard |   // from user pipe
                   eia_lr_sr_hazard             |
                   eia_sa_inst_count_hazard     |   // coincident instruction result
                   eia_sa_inst_kill_hazard      |   // killed eia behind non-killed
                   eia_killed_blocking_inst_hazard; // non-killed eia behind killed
end

                 
wire eia_sa_hazard_del_nxt;
assign eia_sa_hazard_del_nxt = eia_hazard_sel_sa &        // was checking hazard in sa, not da
                         da_swap_valid_r  &         // and da has a valid eia instruction
                         exu_da_to_sa;              // that is moving to sa

always @(posedge clk_ungated or posedge rst_a)
begin : sa_hazard_del_PROC
  if (rst_a == 1'b1)
  begin
    eia_sa_hazard_del <= 1'b0; 
  end
  else
  begin
    eia_sa_hazard_del <= eia_sa_hazard_del_nxt;
  end
end


reg                      eia_aux_read;              // LR accessing EIA aux reg
reg                      eia_aux_write;             // SR accessing EIA aux reg 
reg    [7:0]     i_ar_xnum;                 // extension of aux reg @ x3

//////////////////////////////////////////////////////////////////////////////
// Logic to decode read and write operations to extension aux registers     //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : eia_check_read_ar_PROC

  //////////////////////////////////////////////////////////////////////////
  // Assign default values to all outputs of this process, to avoid any
  // possible latch inference.
  //
  eia_aux_rdata      = 32'd0;
  eia_aux_illegal    = 1'b0;
  eia_aux_unimpl     = 1'b0;
  eia_aux_k_rd       = 1'b0;
  eia_aux_k_wr       = 1'b0;
  eia_aux_serial_sr  = 1'b0;
  eia_aux_strict_sr  = 1'b0;
  eia_aux_raw_hazard = 1'b0;
  eia_aux_waw_hazard = 1'b0;
  eia_aux_rd_prot    = 1'b0;
  eia_aux_wr_prot    = 1'b0;
  i_ar_xnum          = 8'd0;
  
  eia_aux_read       = aux_eia_ren_r & aux_read;
  eia_aux_write      = aux_eia_ren_r & aux_write;
   
  if (eia_aux_read)   // @ x3
    begin
      case (aux_eia_raddr_r[31:0])
        32'h410:    // User mode extension enable register 12'h410
          begin
            eia_aux_rdata   = xpu_r;
            eia_aux_k_rd    = 1'b1;
          end
        32'h44F: // Extension flags register 12'h44F
          begin
            eia_aux_rdata   = {28'h0, ar_xflags_r};
            eia_aux_k_rd    = 1'b1;
          end
        32'hF02: // EVT_CTRL, no comment
          begin
            eia_aux_rdata   = EVT_CTRL_ar_r;
            i_ar_xnum       = 8'd0;
          end
        32'hF04: // EVT_FILTER_LO, no comment
          begin
            eia_aux_rdata   = EVT_FILTER_LO_ar_r;
            i_ar_xnum       = 8'd0;
          end
        32'hF05: // EVT_FILTER_HI, no comment
          begin
            eia_aux_rdata   = EVT_FILTER_HI_ar_r;
            i_ar_xnum       = 8'd0;
          end
        32'hF0A: // EVT_CNT_SEL, no comment
          begin
            eia_aux_rdata   = EVT_CNT_SEL_ar_r;
            i_ar_xnum       = 8'd0;
          end
        32'hF0B: // EVT_CNT_VAL, no comment
          begin
            eia_aux_rdata   = EVT_CNT_VAL_ar_r;
            i_ar_xnum       = 8'd0;
          end
        32'hF00: // EVT_VM_SEL, no comment
          begin
            eia_aux_rdata   = EVT_VM_SEL_ar_r;
            i_ar_xnum       = 8'd0;
            eia_aux_k_rd    = 1'b1;
          end
        32'hF01: // EVT_VM_MAP, no comment
          begin
            eia_aux_rdata   = EVT_VM_MAP_ar_r;
            i_ar_xnum       = 8'd0;
            eia_aux_k_rd    = 1'b1;
          end
        32'hF07: // EVT_GRP_SEL, no comment
          begin
            eia_aux_rdata   = EVT_GRP_SEL_ar_r;
            i_ar_xnum       = 8'd0;
            eia_aux_k_rd    = 1'b1;
          end
        32'hF08: // EVT_SID, no comment
          begin
            eia_aux_rdata   = EVT_SID_ar_r;
            i_ar_xnum       = 8'd0;
            eia_aux_k_rd    = 1'b1;
          end
        32'hF09: // EVT_SSID, no comment
          begin
            eia_aux_rdata   = EVT_SSID_ar_r;
            i_ar_xnum       = 8'd0;
            eia_aux_k_rd    = 1'b1;
          end
        32'hF03: // EVT_IRQ, no comment
          begin
            eia_aux_rdata   = EVT_IRQ_ar_r;
            i_ar_xnum       = 8'd0;
            eia_aux_k_rd    = 1'b1;
          end
        default:
          begin
            eia_aux_unimpl = 1'b1; // aux_addr not implemented in EIA
            i_ar_xnum      = 8'd0;
          end
      endcase
 
      // check explicit lr at x3/ca vs pending implicit (no flags)
               
      eia_aux_raw_hazard = eia_aux_rd_prot &
          ((    
            eia_ca_valid & ((eia_ca_xnum == i_ar_xnum) & eia_ca_wr_ar | eia_ca_has_flg) & (~eia_ca_kill)) 
         | (eia_wb_valid & ((eia_wb_xnum == i_ar_xnum) & eia_wb_wr_ar | eia_wb_has_flg) & (~eia_wb_kill)) 
                                        );
    end



  if (eia_aux_write == 1'b1)   // @ x3: explicit credential check only
                               // actual write repeats addr/data @wb
    begin
      case (aux_eia_raddr_r[31:0])
        32'h410:    // User mode extension enable register 12'h410
            begin
            eia_aux_k_wr      = 1'b1;
          end
        32'h44F: // Extension flags register 12'h44F
          begin
            eia_aux_k_wr      = 1'b1;
            eia_aux_strict_sr = 1'b1;    
          end
        32'hF02: // EVT_CTRL, no comment
          begin
            eia_aux_serial_sr = 1'b1;
            i_ar_xnum       = 8'd0;
          end
        32'hF04: // EVT_FILTER_LO, no comment
          begin
            eia_aux_serial_sr = 1'b1;
            i_ar_xnum       = 8'd0;
          end
        32'hF05: // EVT_FILTER_HI, no comment
          begin
            eia_aux_serial_sr = 1'b1;
            i_ar_xnum       = 8'd0;
          end
        32'hF0A: // EVT_CNT_SEL, no comment
          begin
            eia_aux_serial_sr = 1'b1;
            i_ar_xnum       = 8'd0;
          end
        32'hF0B: // EVT_CNT_VAL, no comment
          begin
            eia_aux_serial_sr = 1'b1;
            i_ar_xnum       = 8'd0;
          end
        32'hF00: // EVT_VM_SEL, no comment
          begin
            eia_aux_serial_sr = 1'b1;
            i_ar_xnum       = 8'd0;
            eia_aux_k_wr    = 1'b1;
          end
        32'hF01: // EVT_VM_MAP, no comment
          begin
            eia_aux_serial_sr = 1'b1;
            i_ar_xnum       = 8'd0;
            eia_aux_k_wr    = 1'b1;
          end
        32'hF07: // EVT_GRP_SEL, no comment
          begin
            eia_aux_serial_sr = 1'b1;
            i_ar_xnum       = 8'd0;
            eia_aux_k_wr    = 1'b1;
          end
        32'hF08: // EVT_SID, no comment
          begin
            eia_aux_serial_sr = 1'b1;
            i_ar_xnum       = 8'd0;
            eia_aux_k_wr    = 1'b1;
          end
        32'hF09: // EVT_SSID, no comment
          begin
            eia_aux_serial_sr = 1'b1;
            i_ar_xnum       = 8'd0;
            eia_aux_k_wr    = 1'b1;
          end
        32'hF03: // EVT_IRQ, no comment
          begin
            eia_aux_serial_sr = 1'b1;
            i_ar_xnum       = 8'd0;
            eia_aux_k_wr    = 1'b1;
          end
        default:
          begin
            eia_aux_unimpl = 1'b1; // aux_addr not implemented in EIA
            i_ar_xnum      = 8'd0;
          end
      endcase

      // check explicit sr at x3/ca vs pending implicit (no flags)
                                          
      eia_aux_waw_hazard = eia_aux_wr_prot &
        ((   
         eia_ca_valid & ((eia_ca_xnum == i_ar_xnum) & (eia_ca_rd_ar | eia_ca_wr_ar) | eia_ca_has_flg) & (~eia_ca_kill)) 
      | (eia_wb_valid & ((eia_wb_xnum == i_ar_xnum) & (eia_wb_rd_ar | eia_wb_wr_ar) | eia_wb_has_flg) & (~eia_wb_kill)) 
                                        );
    end

    eia_aux_stall  =  (eia_aux_raw_hazard | eia_aux_waw_hazard) &
                     ~(eia_aux_illegal    | eia_aux_unimpl    );
end

  //////////////////////////////////////////////////////////////////////////
  //   
  //   Generate user-define AUX read enables
  //

always @*
begin : eia_check_ud_read_ar_PROC
  EVT_CTRL_ar_ren = 1'b0;
  EVT_CTRL_ar_rd_cmt = 1'b0;
  EVT_CTRL_ar_rd_abort = 1'b0;
  EVT_FILTER_LO_ar_ren = 1'b0;
  EVT_FILTER_LO_ar_rd_cmt = 1'b0;
  EVT_FILTER_LO_ar_rd_abort = 1'b0;
  EVT_FILTER_HI_ar_ren = 1'b0;
  EVT_FILTER_HI_ar_rd_cmt = 1'b0;
  EVT_FILTER_HI_ar_rd_abort = 1'b0;
  EVT_CNT_SEL_ar_ren = 1'b0;
  EVT_CNT_SEL_ar_rd_cmt = 1'b0;
  EVT_CNT_SEL_ar_rd_abort = 1'b0;
  EVT_CNT_VAL_ar_ren = 1'b0;
  EVT_CNT_VAL_ar_rd_cmt = 1'b0;
  EVT_CNT_VAL_ar_rd_abort = 1'b0;
  EVT_VM_SEL_ar_ren = 1'b0;
  EVT_VM_SEL_ar_rd_cmt = 1'b0;
  EVT_VM_SEL_ar_rd_abort = 1'b0;
  EVT_VM_MAP_ar_ren = 1'b0;
  EVT_VM_MAP_ar_rd_cmt = 1'b0;
  EVT_VM_MAP_ar_rd_abort = 1'b0;
  EVT_GRP_SEL_ar_ren = 1'b0;
  EVT_GRP_SEL_ar_rd_cmt = 1'b0;
  EVT_GRP_SEL_ar_rd_abort = 1'b0;
  EVT_SID_ar_ren = 1'b0;
  EVT_SID_ar_rd_cmt = 1'b0;
  EVT_SID_ar_rd_abort = 1'b0;
  EVT_SSID_ar_ren = 1'b0;
  EVT_SSID_ar_rd_cmt = 1'b0;
  EVT_SSID_ar_rd_abort = 1'b0;
  EVT_IRQ_ar_ren = 1'b0;
  EVT_IRQ_ar_rd_cmt = 1'b0;
  EVT_IRQ_ar_rd_abort = 1'b0;
  //at X3 stage lr inst is pass to ca stage, assert *_ar_en signal
  if(aux_eia_ren_r & aux_read & exu_x3_to_ca & (~x3_kill))begin
// leda W71 off
// LMD: Case statement without default clause
// LJ:  regs have initial value at beggining      
      case(aux_eia_raddr_r[31:0])
        32'hF02: // EVT_CTRL, no comment
          begin
            EVT_CTRL_ar_ren = 1'b1;
          end
        32'hF04: // EVT_FILTER_LO, no comment
          begin
            EVT_FILTER_LO_ar_ren = 1'b1;
          end
        32'hF05: // EVT_FILTER_HI, no comment
          begin
            EVT_FILTER_HI_ar_ren = 1'b1;
          end
        32'hF0A: // EVT_CNT_SEL, no comment
          begin
            EVT_CNT_SEL_ar_ren = 1'b1;
          end
        32'hF0B: // EVT_CNT_VAL, no comment
          begin
            EVT_CNT_VAL_ar_ren = 1'b1;
          end
        32'hF00: // EVT_VM_SEL, no comment
          begin
            EVT_VM_SEL_ar_ren = 1'b1;
          end
        32'hF01: // EVT_VM_MAP, no comment
          begin
            EVT_VM_MAP_ar_ren = 1'b1;
          end
        32'hF07: // EVT_GRP_SEL, no comment
          begin
            EVT_GRP_SEL_ar_ren = 1'b1;
          end
        32'hF08: // EVT_SID, no comment
          begin
            EVT_SID_ar_ren = 1'b1;
          end
        32'hF09: // EVT_SSID, no comment
          begin
            EVT_SSID_ar_ren = 1'b1;
          end
        32'hF03: // EVT_IRQ, no comment
          begin
            EVT_IRQ_ar_ren = 1'b1;
          end
      endcase
// leda W71 on      
  end   

  //at CA stage, if current lr inst is commit, assert _cmt signal
  if(exu_ca_commit & ca_q_cond)begin
       EVT_CTRL_ar_rd_cmt = EVT_CTRL_ca_ar_ren_r;
       EVT_FILTER_LO_ar_rd_cmt = EVT_FILTER_LO_ca_ar_ren_r;
       EVT_FILTER_HI_ar_rd_cmt = EVT_FILTER_HI_ca_ar_ren_r;
       EVT_CNT_SEL_ar_rd_cmt = EVT_CNT_SEL_ca_ar_ren_r;
       EVT_CNT_VAL_ar_rd_cmt = EVT_CNT_VAL_ca_ar_ren_r;
       EVT_VM_SEL_ar_rd_cmt = EVT_VM_SEL_ca_ar_ren_r;
       EVT_VM_MAP_ar_rd_cmt = EVT_VM_MAP_ca_ar_ren_r;
       EVT_GRP_SEL_ar_rd_cmt = EVT_GRP_SEL_ca_ar_ren_r;
       EVT_SID_ar_rd_cmt = EVT_SID_ca_ar_ren_r;
       EVT_SSID_ar_rd_cmt = EVT_SSID_ca_ar_ren_r;
       EVT_IRQ_ar_rd_cmt = EVT_IRQ_ca_ar_ren_r;
  end 

  //at CA stage, if current lr inst is killed, assert _abort signal
  if(exu_ca_commit & ~ca_q_cond | ca_kill)begin
       EVT_CTRL_ar_rd_abort = EVT_CTRL_ca_ar_ren_r;
       EVT_FILTER_LO_ar_rd_abort = EVT_FILTER_LO_ca_ar_ren_r;
       EVT_FILTER_HI_ar_rd_abort = EVT_FILTER_HI_ca_ar_ren_r;
       EVT_CNT_SEL_ar_rd_abort = EVT_CNT_SEL_ca_ar_ren_r;
       EVT_CNT_VAL_ar_rd_abort = EVT_CNT_VAL_ca_ar_ren_r;
       EVT_VM_SEL_ar_rd_abort = EVT_VM_SEL_ca_ar_ren_r;
       EVT_VM_MAP_ar_rd_abort = EVT_VM_MAP_ca_ar_ren_r;
       EVT_GRP_SEL_ar_rd_abort = EVT_GRP_SEL_ca_ar_ren_r;
       EVT_SID_ar_rd_abort = EVT_SID_ca_ar_ren_r;
       EVT_SSID_ar_rd_abort = EVT_SSID_ca_ar_ren_r;
       EVT_IRQ_ar_rd_abort = EVT_IRQ_ca_ar_ren_r;
  end
end

always @*
begin:eia_check_ud_read_ca_ar_ren_comb_PROC
      EVT_CTRL_ca_ar_ren_nxt = EVT_CTRL_ca_ar_ren_r;
      EVT_FILTER_LO_ca_ar_ren_nxt = EVT_FILTER_LO_ca_ar_ren_r;
      EVT_FILTER_HI_ca_ar_ren_nxt = EVT_FILTER_HI_ca_ar_ren_r;
      EVT_CNT_SEL_ca_ar_ren_nxt = EVT_CNT_SEL_ca_ar_ren_r;
      EVT_CNT_VAL_ca_ar_ren_nxt = EVT_CNT_VAL_ca_ar_ren_r;
      EVT_VM_SEL_ca_ar_ren_nxt = EVT_VM_SEL_ca_ar_ren_r;
      EVT_VM_MAP_ca_ar_ren_nxt = EVT_VM_MAP_ca_ar_ren_r;
      EVT_GRP_SEL_ca_ar_ren_nxt = EVT_GRP_SEL_ca_ar_ren_r;
      EVT_SID_ca_ar_ren_nxt = EVT_SID_ca_ar_ren_r;
      EVT_SSID_ca_ar_ren_nxt = EVT_SSID_ca_ar_ren_r;
      EVT_IRQ_ca_ar_ren_nxt = EVT_IRQ_ca_ar_ren_r;
  if(exu_x3_to_ca)begin
      EVT_CTRL_ca_ar_ren_nxt = EVT_CTRL_ar_ren;
      EVT_FILTER_LO_ca_ar_ren_nxt = EVT_FILTER_LO_ar_ren;
      EVT_FILTER_HI_ca_ar_ren_nxt = EVT_FILTER_HI_ar_ren;
      EVT_CNT_SEL_ca_ar_ren_nxt = EVT_CNT_SEL_ar_ren;
      EVT_CNT_VAL_ca_ar_ren_nxt = EVT_CNT_VAL_ar_ren;
      EVT_VM_SEL_ca_ar_ren_nxt = EVT_VM_SEL_ar_ren;
      EVT_VM_MAP_ca_ar_ren_nxt = EVT_VM_MAP_ar_ren;
      EVT_GRP_SEL_ca_ar_ren_nxt = EVT_GRP_SEL_ar_ren;
      EVT_SID_ca_ar_ren_nxt = EVT_SID_ar_ren;
      EVT_SSID_ca_ar_ren_nxt = EVT_SSID_ar_ren;
      EVT_IRQ_ca_ar_ren_nxt = EVT_IRQ_ar_ren;
  end else if(exu_ca_commit | ca_kill)begin
      EVT_CTRL_ca_ar_ren_nxt = 1'b0;
      EVT_FILTER_LO_ca_ar_ren_nxt = 1'b0;
      EVT_FILTER_HI_ca_ar_ren_nxt = 1'b0;
      EVT_CNT_SEL_ca_ar_ren_nxt = 1'b0;
      EVT_CNT_VAL_ca_ar_ren_nxt = 1'b0;
      EVT_VM_SEL_ca_ar_ren_nxt = 1'b0;
      EVT_VM_MAP_ca_ar_ren_nxt = 1'b0;
      EVT_GRP_SEL_ca_ar_ren_nxt = 1'b0;
      EVT_SID_ca_ar_ren_nxt = 1'b0;
      EVT_SSID_ca_ar_ren_nxt = 1'b0;
      EVT_IRQ_ca_ar_ren_nxt = 1'b0;
  end
end

always @(posedge clk_ungated or posedge rst_a)
begin:eia_check_ud_read_ca_ar_ren_r_PROC
  if(rst_a == 1'b1)begin
      EVT_CTRL_ca_ar_ren_r <= 1'b0;
      EVT_FILTER_LO_ca_ar_ren_r <= 1'b0;
      EVT_FILTER_HI_ca_ar_ren_r <= 1'b0;
      EVT_CNT_SEL_ca_ar_ren_r <= 1'b0;
      EVT_CNT_VAL_ca_ar_ren_r <= 1'b0;
      EVT_VM_SEL_ca_ar_ren_r <= 1'b0;
      EVT_VM_MAP_ca_ar_ren_r <= 1'b0;
      EVT_GRP_SEL_ca_ar_ren_r <= 1'b0;
      EVT_SID_ca_ar_ren_r <= 1'b0;
      EVT_SSID_ca_ar_ren_r <= 1'b0;
      EVT_IRQ_ca_ar_ren_r <= 1'b0;
  end else begin
      EVT_CTRL_ca_ar_ren_r <= EVT_CTRL_ca_ar_ren_nxt;
      EVT_FILTER_LO_ca_ar_ren_r <= EVT_FILTER_LO_ca_ar_ren_nxt;
      EVT_FILTER_HI_ca_ar_ren_r <= EVT_FILTER_HI_ca_ar_ren_nxt;
      EVT_CNT_SEL_ca_ar_ren_r <= EVT_CNT_SEL_ca_ar_ren_nxt;
      EVT_CNT_VAL_ca_ar_ren_r <= EVT_CNT_VAL_ca_ar_ren_nxt;
      EVT_VM_SEL_ca_ar_ren_r <= EVT_VM_SEL_ca_ar_ren_nxt;
      EVT_VM_MAP_ca_ar_ren_r <= EVT_VM_MAP_ca_ar_ren_nxt;
      EVT_GRP_SEL_ca_ar_ren_r <= EVT_GRP_SEL_ca_ar_ren_nxt;
      EVT_SID_ca_ar_ren_r <= EVT_SID_ca_ar_ren_nxt;
      EVT_SSID_ca_ar_ren_r <= EVT_SSID_ca_ar_ren_nxt;
      EVT_IRQ_ca_ar_ren_r <= EVT_IRQ_ca_ar_ren_nxt;
  end 
end


  //////////////////////////////////////////////////////////////////////////
  //   
  //   Generate read-only AUX read enables
  //


  //////////////////////////////////////////////////////////////////////////
  //   
  //   Generate user-define AUX write interface
  // 

always @*
begin : eia_check_ud_write_ar_PROC
  EVT_CTRL_ar_wen = 1'b0;
  EVT_CTRL_ar_wdata = 32'b0;
  EVT_FILTER_LO_ar_wen = 1'b0;
  EVT_FILTER_LO_ar_wdata = 32'b0;
  EVT_FILTER_HI_ar_wen = 1'b0;
  EVT_FILTER_HI_ar_wdata = 32'b0;
  EVT_CNT_SEL_ar_wen = 1'b0;
  EVT_CNT_SEL_ar_wdata = 32'b0;
  EVT_CNT_VAL_ar_wen = 1'b0;
  EVT_CNT_VAL_ar_wdata = 32'b0;
  EVT_VM_SEL_ar_wen = 1'b0;
  EVT_VM_SEL_ar_wdata = 32'b0;
  EVT_VM_MAP_ar_wen = 1'b0;
  EVT_VM_MAP_ar_wdata = 32'b0;
  EVT_GRP_SEL_ar_wen = 1'b0;
  EVT_GRP_SEL_ar_wdata = 32'b0;
  EVT_SID_ar_wen = 1'b0;
  EVT_SID_ar_wdata = 32'b0;
  EVT_SSID_ar_wen = 1'b0;
  EVT_SSID_ar_wdata = 32'b0;
  EVT_IRQ_ar_wen = 1'b0;
  EVT_IRQ_ar_wdata = 32'b0;
  //@WB stage, SR instruction write AUX register
  if(aux_eia_wen_r)begin
      case(aux_eia_waddr_r[31:0])
        32'hF02: // EVT_CTRL, no comment
          begin
            EVT_CTRL_ar_wen = 1'b1;
            EVT_CTRL_ar_wdata = aux_eia_wdata_r[31:0];
          end
        32'hF04: // EVT_FILTER_LO, no comment
          begin
            EVT_FILTER_LO_ar_wen = 1'b1;
            EVT_FILTER_LO_ar_wdata = aux_eia_wdata_r[31:0];
          end
        32'hF05: // EVT_FILTER_HI, no comment
          begin
            EVT_FILTER_HI_ar_wen = 1'b1;
            EVT_FILTER_HI_ar_wdata = aux_eia_wdata_r[31:0];
          end
        32'hF0A: // EVT_CNT_SEL, no comment
          begin
            EVT_CNT_SEL_ar_wen = 1'b1;
            EVT_CNT_SEL_ar_wdata = aux_eia_wdata_r[31:0];
          end
        32'hF0B: // EVT_CNT_VAL, no comment
          begin
            EVT_CNT_VAL_ar_wen = 1'b1;
            EVT_CNT_VAL_ar_wdata = aux_eia_wdata_r[31:0];
          end
        32'hF00: // EVT_VM_SEL, no comment
          begin
            EVT_VM_SEL_ar_wen = 1'b1;
            EVT_VM_SEL_ar_wdata = aux_eia_wdata_r[31:0];
          end
        32'hF01: // EVT_VM_MAP, no comment
          begin
            EVT_VM_MAP_ar_wen = 1'b1;
            EVT_VM_MAP_ar_wdata = aux_eia_wdata_r[31:0];
          end
        32'hF07: // EVT_GRP_SEL, no comment
          begin
            EVT_GRP_SEL_ar_wen = 1'b1;
            EVT_GRP_SEL_ar_wdata = aux_eia_wdata_r[31:0];
          end
        32'hF08: // EVT_SID, no comment
          begin
            EVT_SID_ar_wen = 1'b1;
            EVT_SID_ar_wdata = aux_eia_wdata_r[31:0];
          end
        32'hF09: // EVT_SSID, no comment
          begin
            EVT_SSID_ar_wen = 1'b1;
            EVT_SSID_ar_wdata = aux_eia_wdata_r[31:0];
          end
        32'hF03: // EVT_IRQ, no comment
          begin
            EVT_IRQ_ar_wen = 1'b1;
            EVT_IRQ_ar_wdata = aux_eia_wdata_r[31:0];
          end
      endcase
  end    
end


//////////////////////////////////////////////////////////////////////////////
// Logic for explicit and implicit write of extension aux registers         //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : eia_writeback_ar_PROC

  //////////////////////////////////////////////////////////////////////////
  // Assign default values to all outputs of this process, to avoid any
  // possible latch inference.
  //

  xpu_sr       = 1'b0;
  i_xflags_sr  = 1'b0;
  
  
  //////////////////////////////////////////////////////////////////////////
  //   
  //   Generate write enables
  //   
  if (aux_eia_wen_r)   // @ wb: explicit writeback addr/data
    begin
      case (aux_eia_waddr_r[31:0])
        32'h410:    // User mode extension enable register 12'h410
          xpu_sr             = 1'b1;
        32'h44F: // Extension flags register 12'h44F
          i_xflags_sr        = 1'b1;
        default:                // should never happen, code to avoid a latch
          begin
            xpu_sr           = 1'b0;
            i_xflags_sr      = 1'b0;           
          end
      endcase
    end

  i_xflags_en = i_xflags_sr
                | eia_wb_valid & ~eia_wb_kill & eia_wb_has_flg
                        ;

  // decode the target regs at extension retirement for commit update
  // from shadow to main

                            // i_ar_commit_wen is a global retire signal
                            // only active if retired eia instruction has
                            // the "implicitAuxWrite" attribute

   // dirty register uncommit - clear shadow reg wr enables


  //////////////////////////////////////////////////////////////////////////
  // Gate the ca_aux_sr_data_r signals with the SR operation control signal
  // to minimize spurious transitions when not performing SR operations.
  //

  i_xpu_nxt         = xpu_sr ?  aux_eia_wdata_r : 32'h0;

  
  // Select the next value for the architectural xflag value based on
  // the result from flag-modifying eia instruction or SR to XFLAGS.
  //
  i_xflags_nxt      = i_xflags_sr ? aux_eia_wdata_r[3:0] : res_xflags;

  
  // Determine when each extension aux register is to be written a
  // new value. This will be when an explicit SR instruction selects the
  // register (handshake in X3 by aux_regs), or when an eia instruction
  // from the same extension with a direct write attribute is retired (i.e.
  // results are committed to the state of the machine).
  //
end


//////////////////////////////////////////////////////////////////////////////
// Extension condition code logic                                           //
//////////////////////////////////////////////////////////////////////////////
// leda W488 off
// LMD: not all ses list bus bits used in blocks
// LJ:  used indirectly for assigning default values to signals
always @(da_swap_q_field)
begin : ext_cond_PROC
  eia_da_illegal_cond  = da_swap_q_field[4];       // no eia cc and q_field[4]
  eia_x1_ext_cond      = 1'b0;
  eia_ca_ext_cond      = 1'b0;
end
// leda W488 on


//////////////////////////////////////////////////////////////////////////////
// Synchronous process defining the XPU -  user-mode extension permissions  //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk_ungated or posedge rst_a)
begin : aux_xpu_PROC
  if (rst_a == 1'b1)
  begin
    xpu_r <= 32'h0; 
  end
  else if (xpu_sr)
  begin
    xpu_r <= i_xpu_nxt;
  end
end

//////////////////////////////////////////////////////////////////////////////
// Synchronous process defining the XFLAGS - extension flags register       //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk_ungated or posedge rst_a)
begin : aux_xflags_PROC
  if (rst_a == 1'b1)
  begin
    ar_xflags_r <= 4'd0;
  end
  else if (i_xflags_en)
  begin
    ar_xflags_r <= i_xflags_nxt;
  end
end

//////////////////////////////////////////////////////////////////////////////
// Synchronous process defining all extension aux registers                 //
//                                                                          //
// All extension aux registers are defined within the eia_pipe module, and  //
// are protected from speculative updates if so defined.                    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : aux_regs_comb_PROC
end

always @(posedge clk_ungated or posedge rst_a)
begin : aux_regs_PROC
  if (rst_a == 1'b1)
    begin

    end
  else
  begin
    end
end


//generate eia clock gate enable signal

// spyglass enable_block W528

endmodule


