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
// Certain materials incorporated herein are copyright (C) 2010 - 2011, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//                   
//                   
//                   
//  ALB_DMP_DCCM                
//                   
//                   
//
// ===========================================================================
//
// Description:
//  This module implements the core dccm structure.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_dccm.vpp
//
// ===========================================================================
// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 }, edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

//D: error_signal { name: "alb_dmp_dccm_aux_err" }
//D: error_signal { name: "alb_dmp_shift_fifo_err" }

module npuarc_alb_dmp_dccm (
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used
// spyglass disable_block W193
// SMD: empty statements
// SJ:  empty default statements kept and empty statements cause no problems

  ////////// General input signals ///////////////////////////////////////////
  //
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                           l1_clock_active,
// spyglass enable_block W240
  input                           clk,            // clock
  input                           rst_a,          // reset

  input                           dccm_dmi_priority,  // dmi priority pin
  ////////// DCCM interface ////////////////////////////////////////////////
  //
  output reg                      core_bank0_cs_lo_r,   
  output reg                      core_bank0_cs_hi_r,   
  output reg [`npuarc_DCCM_ADDR_RANGE]   core_bank0_addr_lo_r, 
  output reg [`npuarc_DCCM_ADDR_RANGE]   core_bank0_addr_hi_r, 
  output reg                      core_bank0_we_lo_r,   
  output reg                      core_bank0_we_hi_r,   
  output reg [`npuarc_DBL_DCCM_BE_RANGE] core_bank0_wem_r,  
  output reg [`npuarc_DBL_DCCM_RANGE]    core_bank0_din_r,
  
  output reg                      core_bank0_busy_lo_nxt,   
  output reg                      core_bank0_busy_hi_nxt,   
  input                           dccm_bank0_wait_lo,
  input                           dccm_bank0_wait_hi,
  
  input  [`npuarc_DBL_DCCM_RANGE]        dccm_bank0_dout,  
  output reg                      core_bank1_cs_lo_r,   
  output reg                      core_bank1_cs_hi_r,   
  output reg [`npuarc_DCCM_ADDR_RANGE]   core_bank1_addr_lo_r, 
  output reg [`npuarc_DCCM_ADDR_RANGE]   core_bank1_addr_hi_r, 
  output reg                      core_bank1_we_lo_r,   
  output reg                      core_bank1_we_hi_r,   
  output reg [`npuarc_DBL_DCCM_BE_RANGE] core_bank1_wem_r,  
  output reg [`npuarc_DBL_DCCM_RANGE]    core_bank1_din_r,
  
  output reg                      core_bank1_busy_lo_nxt,   
  output reg                      core_bank1_busy_hi_nxt,   
  input                           dccm_bank1_wait_lo,
  input                           dccm_bank1_wait_hi,
  
  input  [`npuarc_DBL_DCCM_RANGE]        dccm_bank1_dout,  
  ////////// Interface to the X1 stage /////////////////////////////////
  //
  input                         x1_valid_r,     // X1 has valid instruction
  input                         x1_pass,        // X1  passing on ints
  input                         x1_load_r,      // X1 load
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                         x1_store_r,     // X1 load
// spyglass enable_block W240
  input  [`npuarc_DMP_TARGET_RANGE]    dc1_target,            // DC1 mem target
  input  [`npuarc_DCCM_BANK_RANGE]     dc1_data_bank_sel_lo,  // DC1 DCCM bank select
  input  [`npuarc_DCCM_BANK_RANGE]     dc1_data_bank_sel_hi,  // DC1 DCCM bank select
  input  [`npuarc_DCCM_ADR_RANGE]      dc1_dccm_addr0,        // DC1 mem addr0
  input  [`npuarc_DCCM_ADR_RANGE]      dc1_dccm_addr1,        // DC1 mem addr1
  input  [3:0]                  dc1_rmw,               // DC1 partial store
  output reg                    dc1_bank_conflict, // DC1 bank conflict
  output reg                    dc1_stall,         // DC1 stall
  ////////// Interface to the X2 stage /////////////////////////////////
  //
  input                        x2_valid_r,     // X2 has valid instruction
  input                        x2_pass,        // X2 passing on instruction
  input                        x2_enable,      // X2 accepts new instruction
  input                        x2_exu_stall,   // X2 EXU stall
  input                        x2_load_r,      // X2 load  
  input                        x2_store_r,     // X2 store  
  input  [`npuarc_DMP_TARGET_RANGE]   dc2_target_r,   // DC2  target
  input  [3:0]                 dc2_data_bank_sel_r, // DC2 bank sel
  input                        dc2_stuck,      // DC2 inst held up by EXU
  input [3:0]                  dc2_rmw,        // DC2 r-m-w, partial store
  input                        dc2_cft_stall,
  output reg                   dc2_stall,    // DC2 stall 
 
  ////////// Interface to the X3 stage /////////////////////////////////
  //
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input [`npuarc_DCCM_ADR_RANGE]      x3_mem_addr0_r,  // X3 Addr0
  input [`npuarc_DCCM_ADR_RANGE]      dc3_mem_addr1_r, // X3 Addr1
// spyglass enable_block W240
  input                        x3_valid_r,     // X3 has valid instruction 
  input                        x3_pass,        // X3 passing on instruction
  input                        x3_load_r,      // X3 load  
  input                        x3_store_r,     // X3 load  
  input  [`npuarc_DMP_TARGET_RANGE]   dc3_target_r,   // DC3 target
  input                        dc3_stall_r,    // DC3 stall 
  input                        dc3_partial_or_multi_conflict,
  input  [3:0]                 dc3_bank_sel_r, // DC3 bank sel information
  input  [3:0]                 dc3_rmw_r,      // DC3 read modify write
  input                        dc3_dccm_poisoned,

  ////////// Interface to the SKID STATE ////////////////////////////////
 //
  input [`npuarc_DCCM_DATA_ECC_RANGE] dc3_dccm_data_even_lo,
  input [`npuarc_DCCM_DATA_ECC_RANGE] dc3_dccm_data_even_hi,
  input [`npuarc_DCCM_DATA_ECC_RANGE] dc3_dccm_data_odd_lo,
  input [`npuarc_DCCM_DATA_ECC_RANGE] dc3_dccm_data_odd_hi,

  input                        dc3_enable, 
  input [3:0]                  dc3_skid_ecc_valid, 
  input                        dc3_excpn,
  ////////// Interface to the CA stage //////////////////////////////////
  //
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
   input [`npuarc_ADDR_RANGE]         ca_mem_addr0_r,  // CA Addr0
   input [`npuarc_PADDR_RANGE]        dc4_mem_addr1_r, // CA Addr1
// spyglass enable_block W240
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                        ca_valid_r,     // CA has valid instruction
  input                        ca_load_r,      // CA load
// spyglass enable_block W240
  input                        ca_store_r,     // CA store  
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                        ca_uop_inst_r, // CA is UOP
// spyglass enable_block W240
  input                        ca_enable,      // CA accepts new instruction
  input                        ca_pass,        // CA pass
  input  [`npuarc_DMP_TARGET_RANGE]   dc4_target_r,   // DC4 target
  input                        dc4_stall_r,
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input  [3:0]                 dc4_rmw_r,      // Partial store
// spyglass enable_block W240
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input [3:0]                  dc4_bank_sel_r, // DC4 bank sel information
// spyglass enable_block W240
  input [3:0]                  dc4_ecc_skid_sb_error_r,
  input [3:0]                  dc4_ecc_skid_db_error_r,
  input [`npuarc_SYNDROME_MSB:0]      dc_skid_bank0_syndrome_r,
  input [`npuarc_SYNDROME_MSB:0]      dc_skid_bank1_syndrome_r,
  input [`npuarc_SYNDROME_MSB:0]      dc_skid_bank2_syndrome_r,
  input [`npuarc_SYNDROME_MSB:0]      dc_skid_bank3_syndrome_r,
  ////////// Interface to the writeback stage ///////////////////////
  //
  input                        wa_restart_r,   // WB restart the pipeline
  
  ////////// Interface to the write queue /////////////////////////////////
  
  input [3:0]                  wq_top_bank_req_mask,       
  input [3:0]                  wq_sec_bank_req_mask,       
  
  input                        wq_req_even_lo,  
  input [`npuarc_DCCM_ADR_RANGE]      wq_addr_even_lo, 
  input [`npuarc_DATA_RANGE]          wq_din_even_lo,  
  input [3:0]                  wq_wem_even_lo,  
  
  input                        wq_req_even_hi, 
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs 
  input [`npuarc_DCCM_ADR_RANGE]      wq_addr_even_hi, 
// spyglass enable_block W240
  input [`npuarc_DATA_RANGE]          wq_din_even_hi,  
  input [3:0]                  wq_wem_even_hi,  
  
  input                        wq_req_odd_lo,  
  input [`npuarc_DCCM_ADR_RANGE]      wq_addr_odd_lo, 
  input [`npuarc_DATA_RANGE]          wq_din_odd_lo,  
  input [3:0]                  wq_wem_odd_lo,  
  
  input                        wq_req_odd_hi,  
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input [`npuarc_DCCM_ADR_RANGE]      wq_addr_odd_hi, 
// spyglass enable_block W240
  input [`npuarc_DATA_RANGE]          wq_din_odd_hi,  
  input [3:0]                  wq_wem_odd_hi,  

  input                        wq_dc_entry,
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                        wq_empty,
// spyglass enable_block W240
  
  output reg                   wq_dccm_read_one,
  output reg                   wq_dccm_read_two,
  ////////// Interface with Data cache ///////////////////////////////////////
  //
  input                        dmu_empty,
  input                        lq_empty_r,
  ////////// Interface to the DMI interface /////////////////////////////////
  //
  input                        dmi_cmd_valid_r,
  output reg                   dmi_cmd_accept,              
  input                        dmi_cmd_read_r,
  input [`npuarc_CCM_AW-1:3]          dmi_cmd_addr_r,
  
  output reg                   dmi_rd_valid,
  output wire [`npuarc_DOUBLE_RANGE]  dmi_rd_data,
  output reg                   dmi_rd_err,

  input                        dmi_wr_valid_r,
  output reg                   dmi_wr_accept,
  input  [`npuarc_DOUBLE_RANGE]       dmi_wr_data_r,
  input  [`npuarc_DOUBLE_BE_RANGE]    dmi_wr_mask_r,
  output reg                   dmi_wr_done_r,
  output reg                   dmi_err_wr_r,

  ////////// Interface to the dmp_result bus (dc3 info) ///////////////////////
  //
  output reg                    dccm_rb_req,
  
  output reg [`npuarc_DBL_DCCM_LO_RANGE] dccm_rb_data0_lo_r, 
  output reg [`npuarc_DBL_DCCM_LO_RANGE] dccm_rb_data0_hi_r, 
  output reg [`npuarc_DBL_DCCM_LO_RANGE] dccm_rb_data1_lo_r, 
  output reg [`npuarc_DBL_DCCM_LO_RANGE] dccm_rb_data1_hi_r,
  ////////// ECC Interface to the DC4 stage (dc3 info) ///////////////////////
  //
  output reg [3:0]             dc4_dccm_ecc_sb_error,        
  output reg                   dc4_dmi_scrubbing_conflict,
 input                         ecc_dmp_disable,
 input                         ecc_dmp_expn_disable,
      
  output reg                   dc4_dccm_ecc_db_error,
  output reg [`npuarc_SYNDROME_MSB:0] fs_dccm_bank0_syndrome_r, 
  output reg [`npuarc_SYNDROME_MSB:0] fs_dccm_bank1_syndrome_r, 
  output reg [`npuarc_SYNDROME_MSB:0] fs_dccm_bank2_syndrome_r, 
  output reg [`npuarc_SYNDROME_MSB:0] fs_dccm_bank3_syndrome_r, 

  output reg                   fs_dccm_bank0_ecc_sb_error_r,      
  output reg                   fs_dccm_bank1_ecc_sb_error_r,      
  output reg                   fs_dccm_bank2_ecc_sb_error_r,      
  output reg                   fs_dccm_bank3_ecc_sb_error_r,      

  output reg                   fs_dccm_bank0_ecc_db_error_r,
  output reg                   fs_dccm_bank1_ecc_db_error_r,
  output reg                   fs_dccm_bank2_ecc_db_error_r,
  output reg                   fs_dccm_bank3_ecc_db_error_r,
//  `endif               // }
  output reg                   dc4_dccm_ecc_excpn_r,
  output     [`npuarc_DATA_RANGE]     dc4_ecc_data_even_lo,        
  output     [`npuarc_DATA_RANGE]     dc4_ecc_data_even_hi,        
  output     [`npuarc_DATA_RANGE]     dc4_ecc_data_odd_lo,        
  output     [`npuarc_DATA_RANGE]     dc4_ecc_data_odd_hi,        

  output reg                   dc4_dccm_ecc_replay,

  ////////// Interface performance counters ///////////////////////////////////
  //
  output reg                   dccm_pct_dcbc,  // Bank conflicts

  ////////// Interface with aux ctl ///////////////////////////////////////////
  //
  input                        aux_ren_r,       //  (X3) Aux region select
  input                        aux_wen_r,       //  (WA) Aux region select
  input  [`npuarc_DATA_RANGE]         aux_wdata_r,     //  (WA) Aux write data
  
  output [`npuarc_DATA_RANGE]         aux_rdata,       //  (X3) LR read data
  output                       aux_illegal,     //  (X3) SR/LR illegal
  output                       aux_k_rd,        //  (X3) needs Kernel Read
  output                       aux_k_wr,        //  (X3) needs Kernel Write
  output                       aux_unimpl,      //  (X3) Invalid Reg
  output                       aux_serial_sr,   //  (X3) SR group flush pipe
  output                       aux_strict_sr,   //  (X3) SR flush pipe

  output [3:0]                 aux_dccm_r
// leda NTL_CON37 on
// leda NTL_CON13C on
);

// Local declarations
//

reg                             core_bank0_cs_lo_next;
reg                             core_bank0_cs_hi_next;
reg    [`npuarc_DCCM_ADDR_RANGE]       core_bank0_addr_lo_next;
reg                             core_bank0_cs_lo_nxt;
reg                             core_bank0_cs_hi_nxt;
reg    [`npuarc_DCCM_ADDR_RANGE]       core_bank0_addr_lo_nxt;
reg    [`npuarc_DCCM_ADDR_RANGE]       core_bank0_addr_hi_nxt;
reg    [`npuarc_DCCM_ADDR_RANGE]       core_bank0_addr_hi_next;
reg                             core_bank0_we_lo_nxt;
reg                             core_bank0_we_hi_nxt;
reg    [`npuarc_DBL_DCCM_BE_RANGE]     core_bank0_wem_nxt;
reg    [`npuarc_DBL_DCCM_RANGE]        core_bank0_din_nxt;
reg                             core_bank0_we_lo_next;
reg                             core_bank0_we_hi_next;
reg    [`npuarc_DBL_DCCM_BE_RANGE]     core_bank0_wem_next;
reg    [`npuarc_DBL_DCCM_RANGE]        core_bank0_din_next;

reg                             core_bank1_cs_lo_next;
reg                             core_bank1_cs_hi_next;
reg    [`npuarc_DCCM_ADDR_RANGE]       core_bank1_addr_lo_next;
reg                             core_bank1_cs_lo_nxt;
reg                             core_bank1_cs_hi_nxt;
reg    [`npuarc_DCCM_ADDR_RANGE]       core_bank1_addr_lo_nxt;
reg    [`npuarc_DCCM_ADDR_RANGE]       core_bank1_addr_hi_nxt;
reg    [`npuarc_DCCM_ADDR_RANGE]       core_bank1_addr_hi_next;
reg                             core_bank1_we_lo_nxt;
reg                             core_bank1_we_hi_nxt;
reg    [`npuarc_DBL_DCCM_BE_RANGE]     core_bank1_wem_nxt;
reg    [`npuarc_DBL_DCCM_RANGE]        core_bank1_din_nxt;
reg                             core_bank1_we_lo_next;
reg                             core_bank1_we_hi_next;
reg    [`npuarc_DBL_DCCM_BE_RANGE]     core_bank1_wem_next;
reg    [`npuarc_DBL_DCCM_RANGE]        core_bank1_din_next;


reg                           dc1_target_dccm;
reg                           dc1_load_valid;
reg [`npuarc_DCCM_BANK_RANGE]        dc1_bank_req_lo;
reg [`npuarc_DCCM_BANK_RANGE]        dc2_bank_req_lo_r;
reg [`npuarc_DCCM_BANK_RANGE]        dc1_bank_req_hi;
reg [`npuarc_DCCM_BANK_RANGE]        dc2_bank_req_hi_r;
reg [`npuarc_DCCM_BANK_RANGE]        dc1_bank_ack_lo;
reg [`npuarc_DCCM_BANK_RANGE]        dc1_bank_ack_hi;
reg [`npuarc_DCCM_ADR_RANGE]         dc2_dccm_addr0_r;  
reg [`npuarc_DCCM_ADR_RANGE]         dc2_dccm_addr1_r;  

reg                           dmi_rd_err_prel;
reg [1:0]                     dmi_bank_req_mask;
reg [1:0]                     dmi_bank_ack_mask;
reg                           dmi_full_ack;

reg [`npuarc_DCCM_BANK_RANGE]        dmi_cg0;
reg [`npuarc_DCCM_BANK_RANGE]        dmi_ack_cg0;
reg [`npuarc_DCCM_BANK_RANGE]        dmi_rd_valid_cg0;

reg [`npuarc_DCCM_BANK_RANGE]        dmi_bank_req;  
reg [`npuarc_DCCM_BANK_RANGE]        dmi_hp_bank_req;  
reg [`npuarc_DCCM_BANK_RANGE]        dmi_bank_ack;  
reg [`npuarc_DCCM_BANK_RANGE]        dmi_bank_ack_lo; 
reg [`npuarc_DCCM_BANK_RANGE]        dmi_bank_ack_hi; 
reg [`npuarc_DCCM_BANK_RANGE]        dmi_bank_ack_r_nxt;
reg [`npuarc_DCCM_BANK_RANGE]        dmi_bank_ack_rr_nxt;
reg [`npuarc_DCCM_BANK_RANGE]        dmi_bank_ack_rrr_nxt;
reg [`npuarc_DCCM_BANK_RANGE]        dmi_bank_ack_r;
reg [`npuarc_DCCM_BANK_RANGE]        dmi_bank_ack_rr;
reg [`npuarc_DCCM_BANK_RANGE]        dmi_bank_ack_rrr;

wire [`npuarc_DOUBLE_RANGE]          dmi_wr_data;
wire  [`npuarc_DOUBLE_BE_RANGE]      dmi_wr_mask;
wire [`npuarc_DOUBLE_BE_RANGE]       dmi_wr_mask_prel;
reg  [`npuarc_DOUBLE_RANGE]          dmi_rd_data_nxt;
wire [`npuarc_DATA_RANGE]            dmi_ecc_data_lo;
wire [`npuarc_DATA_RANGE]            dmi_ecc_data_hi;
reg                           scrubbing_in_progress_r;
reg                           scrubbing_in_progress_next;
reg                           scrubbing_in_progress_prel;
reg [11:0]                dmi_cmd_addr_qual;

reg                           dmi_cmd_valid_qual;
//reg [11:0]                dmi_cmd_addr_qual;
reg                           dc1_dmi_full_write;
reg                           dc1_dmi_read;

reg                           dc2_dmi_cg0;
reg                           dc2_dmi_valid_next;
reg                           dc2_dmi_read_next;
reg                           dc2_dmi_delayed_next;
reg                           dc2_dmi_wr_retry_next;
reg                           dc2_dmi_rmw_next;
reg [`npuarc_DOUBLE_BE_RANGE]        dc2_dmi_wr_mask_next;
reg [11:0]                dc2_dmi_cmd_addr_next;
reg [`npuarc_DOUBLE_RANGE]           dc2_dmi_wr_data_next;
reg                           dc2_dmi_valid_r;
reg                           dc2_dmi_read_r;
reg                           dc2_dmi_delayed_r;
reg                           dc2_dmi_wr_retry_nxt;
reg                           dc2_dmi_wr_retry_r;
reg                           dc2_dmi_rmw_r;
reg [`npuarc_DOUBLE_BE_RANGE]        dc2_dmi_wr_mask_r;
reg [11:0]                dc2_dmi_cmd_addr_r;
reg [`npuarc_DOUBLE_RANGE]           dc2_dmi_wr_data_r;

reg                           dc3_dmi_cg0;
reg                           dc3_dmi_valid_nxt;
reg                           dc3_dmi_read_nxt;
reg                           dc3_dmi_delayed_nxt;
reg                           dc3_dmi_wr_retry_nxt;
reg                           dc3_dmi_rmw_nxt;
reg [`npuarc_DOUBLE_BE_RANGE]        dc3_dmi_wr_mask_nxt;
reg [11:0]                dc3_dmi_cmd_addr_nxt;
reg [`npuarc_DOUBLE_RANGE]           dc3_dmi_wr_data_nxt;
reg                           dc3_dmi_valid_r;
reg                           dc3_dmi_read_r;
reg                           dc3_dmi_delayed_r;
reg                           dc3_dmi_wr_retry_r;
reg                           dc3_dmi_rmw_r;
reg [`npuarc_DOUBLE_BE_RANGE]        dc3_dmi_wr_mask_r;
reg [11:0]                dc3_dmi_cmd_addr_r;
reg [`npuarc_DOUBLE_RANGE]           dc3_dmi_wr_data_r;

reg                           dc4_dmi_cg0;
reg                           dc4_dmi_valid_nxt;
reg                           dc4_dmi_read_nxt;
reg                           dc4_dmi_delayed_nxt;
reg                           dc4_dmi_wr_retry_nxt;
reg                           dc4_dmi_rmw_nxt;
reg [`npuarc_DOUBLE_BE_RANGE]        dc4_dmi_wr_mask_nxt;
reg [11:0]                dc4_dmi_cmd_addr_nxt;
reg [`npuarc_DOUBLE_RANGE]           dc4_dmi_wr_data_nxt;
reg                           dc4_dmi_valid_r;
reg                           dc4_dmi_read_r;
reg                           dc4_dmi_delayed_r;
reg                           dc4_dmi_wr_retry_r;
reg                           dc4_dmi_rmw_r;
reg [`npuarc_DOUBLE_BE_RANGE]        dc4_dmi_wr_mask_r;
wire[`npuarc_DOUBLE_BE_RANGE]        dc4_dmi_wr_mask_qual;
reg [11:0]                dc4_dmi_cmd_addr_r;
reg [`npuarc_DOUBLE_RANGE]           dc4_dmi_wr_data_r;


reg                           dc1_state_r;
reg                           dc1_state_nxt;
reg                           dc1_state_next;

reg                           dc2_req_cg0;
reg                           dc2_kill;
reg                           dc2_ld_target_dccm;
reg                           dc2_st_target_dccm;
reg                           dc2_target_dccm;
reg                           dc2_req_even_lo;
reg                           dc2_req_even_hi;
reg                           dc2_req_odd_lo;
reg                           dc2_req_odd_hi;
reg                           dc2_stuck_r;
reg                           dc2_stuck_next;

reg [1:0]                     dc2_conflict_ack_lo;
reg [1:0]                     dc2_conflict_ack_hi;
 
reg [3:0]                     dc2_data_mem_valid_r;
reg [3:0]                     dc2_data_mem_valid_next;

reg [3:0]                     dc1_bank_req_mask;
reg [3:0]                     dc1_bank_not_ack;
reg [3:0]                     dc1_bank_ack_mask;
reg [3:0]                     dc1_dc2_bank_common;
reg                           dc1_dc2_bank_common_set_cg0;
reg                           dc1_dc2_bank_common_clr_cg0;
reg [3:0]                     dc1_dc2_bank_common_r;
reg [3:0]                     dc1_dc2_bank_common_next;
reg [3:0]                     dc2_bank_not_ack_r;
reg [3:0]                     dc2_bank_req_mask;
reg [3:0]                     dc2_bank_ack_mask;
reg                           dc1_full_ack; 
reg                           dc2_full_ack; 

reg                           dc3_ld_target_dccm;
reg                           dc3_st_target_dccm;
reg                           dc3_target_dccm;
reg [3:0]                     dc3_data_mem_valid_r;
reg [3:0]                     dc3_data_mem_valid_next;


reg [`npuarc_DCCM_BANK_RANGE]        wq_bank_req_lo;
reg [`npuarc_DCCM_BANK_RANGE]        wq_bank_ack_lo;

reg [`npuarc_DCCM_BANK_RANGE]        wq_bank_req_hi;
reg [`npuarc_DCCM_BANK_RANGE]        wq_bank_ack_hi;

reg                           wq_full_ack;


reg [`npuarc_DCCM_BANK_RANGE]        dccm_bank_cs_lo_cg0;
reg [`npuarc_DCCM_BANK_RANGE]        dccm_bank_cs_hi_cg0;

reg [`npuarc_DCCM_BANK_RANGE]        dccm_bank_addr_lo_cg0;
reg [`npuarc_DCCM_BANK_RANGE]        dccm_bank_addr_hi_cg0;
reg [`npuarc_DCCM_BANK_RANGE]        dccm_bank_data_lo_cg0;
reg [`npuarc_DCCM_BANK_RANGE]        dccm_bank_data_hi_cg0;

reg [`npuarc_DCCM_BANK_RANGE]        dccm_bank_busy_lo;
reg [`npuarc_DCCM_BANK_RANGE]        dccm_bank_busy_hi; 
reg                           dc4_ld_target_dccm;
reg                           dc4_target_dccm;

reg                           dc4_data_even_lo_cg0;
reg                           dc4_data_even_hi_cg0;
reg                           dc4_data_odd_lo_cg0; 
reg                           dc4_data_odd_hi_cg0;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg [`npuarc_DBL_DCCM_LO_RANGE]      dc4_data_even_lo_nxt;
reg [`npuarc_DBL_DCCM_LO_RANGE]      dc4_data_even_hi_nxt;
reg [`npuarc_DBL_DCCM_LO_RANGE]      dc4_data_odd_lo_nxt;
reg [`npuarc_DBL_DCCM_LO_RANGE]      dc4_data_odd_hi_nxt;
reg [`npuarc_DBL_DCCM_LO_RANGE]      dc4_data_even_lo_r;
reg [`npuarc_DBL_DCCM_LO_RANGE]      dc4_data_even_hi_r;
reg [`npuarc_DBL_DCCM_LO_RANGE]      dc4_data_odd_lo_r;
reg [`npuarc_DBL_DCCM_LO_RANGE]      dc4_data_odd_hi_r;
reg                           dmi_data_lo_cg0;
reg [`npuarc_DBL_DCCM_LO_RANGE]      dmi_data_lo_r;
reg [`npuarc_DBL_DCCM_LO_RANGE]      dmi_data_lo_nxt;
reg [`npuarc_DBL_DCCM_LO_RANGE]      dmi_data_lo_next;

reg                           dmi_data_hi_cg0;
reg [`npuarc_DBL_DCCM_LO_RANGE]      dmi_data_hi_r;
reg [`npuarc_DBL_DCCM_LO_RANGE]      dmi_data_hi_nxt;
reg [`npuarc_DBL_DCCM_LO_RANGE]      dmi_data_hi_next;

// leda NTL_CON32 on
reg [1:0]                     dc3_dmi_ecc_valid;
reg [1:0]                     dc4_dmi_ecc_valid_r;
reg [1:0]                     dc4_dmi_ecc_db_error;
reg                           dc4_dmi_ecc_error_cg0;



// Module definition

reg [3:0]                     dc4_skid_ecc_valid_r;
reg                           dc4_skid_ecc_valid_cg0;
reg                           dmi_full_mask;

//`let `DMP_SHIFT_FIFO_WIDTH      =    1              // dc4_dmi_valid_r
//                  +    1              // dc4_dmi_read_r
//                  +    1              // dc4_dmi_rmw_r
//                  +    1              // dc4_dmi_rd_err_r
//                  +    1              // dc4_dmi_wr_retry_r
//                  +   `DOUBLE_BE_SIZE // dc4_dmi_wr_mask_r   
//                  +   `DOUBLE_SIZE    // dc4_dmi_wr_data_r
//                  +   `CCM_AW-3       // dc4_dmi_cmd_addr_r
// `let `DMP_SHIFT_FIFO_WIDTH = 1 + 1 + 1 + 1 + 1 + `DOUBLE_BE_SIZE + `DOUBLE_SIZE + `DCCM_ADDR_BITS+1;

wire                          pop;
wire                          push;
wire [2:0]                    fifo_entry_valid_r;
reg                           fifo_full_qual;
reg                           fifo_threshold;
reg                           fifo_select;
wire                          fifo_full;
wire                          fifo_one_empty;
wire                          fifo_two_empty;
wire                          fifo_valid; 
wire [`npuarc_DMP_SHIFT_FIFO_WIDTH-1:0]            fifo_data_in;
wire [`npuarc_DMP_SHIFT_FIFO_WIDTH-1:0]            fifo_data_out;
wire [`npuarc_DMP_SHIFT_FIFO_WIDTH-1:0]            fifo_entry0_data_out;
wire [`npuarc_DMP_SHIFT_FIFO_WIDTH-1:0]            fifo_entry1_data_out;
wire [`npuarc_DMP_SHIFT_FIFO_WIDTH-1:0]            fifo_entry2_data_out;

reg  [1:0]                    fifo_bank_req;
reg                           dc1_dc2_dmi_addr_match;  
reg                           dc1_dc3_dmi_addr_match;  
reg                           dc1_dc4_dmi_addr_match; 
reg                           dc1_entry0_dmi_addr_match;
reg                           dc1_entry1_dmi_addr_match;
reg                           dc1_entry2_dmi_addr_match;
reg                           dmi_addr_match_qual;
reg                           dc2_dmi_delayed_nxt;
reg                           dmi_partial_write_in_pipe;
reg                           dmi_delayed_read_in_pipe;
reg                           dmi_wr_retry_in_pipe;
reg  [`npuarc_DOUBLE_RANGE]          dmi_wr_data_qual;
reg  [`npuarc_DOUBLE_BE_RANGE]       dmi_wr_mask_qual;



   assign dmi_wr_data      = dmi_wr_data_r; 
   assign dmi_wr_mask_prel = dmi_wr_mask_r; 
   assign dmi_rd_data      = dmi_rd_data_nxt; 
  
   
//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Asynchronous block defining the dc1 logic               
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc1_bank_req_PROC
  //
  //
  dc1_load_valid   = (  (x1_load_r & x1_valid_r)
                      | ( (|dc1_rmw) & x1_valid_r) 
                     ) 
                   & dc1_target_dccm;

  // Bank even
  //
  dc1_bank_req_lo[0] = ((   dc1_load_valid 
                         | dc1_rmw[0]
                       )
                       & (  dc1_data_bank_sel_lo[0]
                          ) 
                       & x1_pass)
                       ;
  
  dc1_bank_req_hi[0] = ((   dc1_load_valid 
                         | dc1_rmw[1]
                       )
                       & (  dc1_data_bank_sel_hi[0]
                         )     
                       & x1_pass)
                       ;
  // Bank odd
  //
  dc1_bank_req_lo[1] = ((   dc1_load_valid 
                         | dc1_rmw[2]
                       )  
                       & (  dc1_data_bank_sel_lo[1]
                         ) 
                       & x1_pass)
                       ;
  
  dc1_bank_req_hi[1] = ((   dc1_load_valid 
                         | dc1_rmw[3]
                       )  
                      & (  dc1_data_bank_sel_hi[1]
                         )
                         
                      & x1_pass)
                      ;

end


//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Asynchronous block defining the dccm bank busy information              
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dccm_bank_busy_PROC
  dccm_bank_busy_lo[0] = dccm_bank0_wait_lo;
  dccm_bank_busy_hi[0] = dccm_bank0_wait_hi;
  dccm_bank_busy_lo[1] = dccm_bank1_wait_lo;
  dccm_bank_busy_hi[1] = dccm_bank1_wait_hi;
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Asynchronous block defining  dc1 and dc2 targets         
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc1_dc2_dc3_target_dccm_PROC
  dc1_target_dccm = (dc1_target   == `npuarc_DMP_TARGET_DCCM);
  dc2_target_dccm = (dc2_target_r == `npuarc_DMP_TARGET_DCCM);
  dc3_target_dccm = (dc3_target_r == `npuarc_DMP_TARGET_DCCM);
  dc4_target_dccm = (dc4_target_r == `npuarc_DMP_TARGET_DCCM);
end

//////////////////////////////////////////////////////////////////////////////
//                                                                           
//  Asynchronous block defining DC1 stall       
//                                                                           
//////////////////////////////////////////////////////////////////////////////
parameter DC1_DEFAULT = 1'b0;
parameter DC1_BLOCK   = 1'b1;

always @*
begin : dc1_stall_PROC
  //
  //
  dc1_stall =  1'b0;

  dc1_state_nxt = dc1_state_r;
  
  case (dc1_state_r)
  DC1_DEFAULT:
  begin
    if (dc4_dccm_ecc_replay)
    begin
      dc1_state_nxt       = DC1_BLOCK;
    end
  end
  
  default: // DC1_BLOCK
  begin
    dc1_stall = x1_load_r | x1_store_r;
    
    if (wq_empty)
    begin
      dc1_state_nxt = DC1_DEFAULT;
    end
  end                
  endcase
end

reg       dc1_wq_conflict;
reg       dc1_wq_dmi_conflict;
reg       dc1_dmi_conflict;
reg [3:0] dc1_ack_qual; // qualified ack;
//////////////////////////////////////////////////////////////////////////////
//                                                                           
//  Asynchronous block defining DC1 bank conflict       
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc1_bank_conflict_PROC
   dc1_bank_conflict = {dc1_bank_req_hi[1], dc1_bank_req_lo[1],   
                        dc1_bank_req_hi[0], dc1_bank_req_lo[0]}   
                    != {dc1_bank_ack_hi[1], dc1_bank_ack_lo[1],   
                        dc1_bank_ack_hi[0], dc1_bank_ack_lo[0]}; 
  // DC1 accessing banks that have been given to the write queue the previous
  // cycle
  //
  dc1_wq_conflict = (dc1_bank_req_mask[0] & core_bank0_cs_lo_r & core_bank0_we_lo_r)
                  | (dc1_bank_req_mask[1] & core_bank0_cs_hi_r & core_bank0_we_hi_r)
                  | (dc1_bank_req_mask[2] & core_bank1_cs_lo_r & core_bank1_we_lo_r)
                  | (dc1_bank_req_mask[3] & core_bank1_cs_hi_r & core_bank1_we_hi_r)
                  ;

  dc1_dmi_conflict = (dc1_bank_req_mask[0] & core_bank0_cs_lo_r & dmi_bank_ack_r[0])
                   | (dc1_bank_req_mask[1] & core_bank0_cs_hi_r & dmi_bank_ack_r[0])
                   | (dc1_bank_req_mask[2] & core_bank1_cs_lo_r & dmi_bank_ack_r[1])
                   | (dc1_bank_req_mask[3] & core_bank1_cs_hi_r & dmi_bank_ack_r[1])
                   ;

  dc1_wq_dmi_conflict =  dc1_wq_conflict
                      |  dc1_dmi_conflict
                      ;  
    
  // We only fire partial acked memory banks when the DC1 load doesn't 
  // experience a bank conflict with a bank that has been just written
  //
  dc1_ack_qual    = {(dc1_bank_ack_hi[1] & (~dc1_wq_dmi_conflict)),
                     (dc1_bank_ack_lo[1] & (~dc1_wq_dmi_conflict)),
                     (dc1_bank_ack_hi[0] & (~dc1_wq_dmi_conflict)),
                     (dc1_bank_ack_lo[0] & (~dc1_wq_dmi_conflict))};
end

//////////////////////////////////////////////////////////////////////////////
//
// Asynchronous block defining  ld targetting DCCM
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc_ld_target_dccm_PROC
  dc2_ld_target_dccm       =   (  x2_load_r
                                | (x2_store_r & (|dc2_rmw))
                               ) 
                              & x2_valid_r
                              & dc2_target_dccm
                              ;
 
  dc2_st_target_dccm       =   x2_store_r
                             & x2_valid_r
                             & dc2_target_dccm;

  dc3_ld_target_dccm       =   ( x3_load_r
                                | (x3_store_r & (|dc3_rmw_r))
                               ) 
                              & x3_valid_r
                              & dc3_target_dccm
                              & (~dc3_dccm_poisoned)
                              ;
 
  dc3_st_target_dccm       =   x3_store_r
                             & x3_valid_r
                             & dc3_target_dccm
                             & (~dc3_dccm_poisoned)
                             ;
 
  dc4_ld_target_dccm       =   ( ca_load_r
                                | (ca_store_r & (|dc4_rmw_r))
                               ) 
                              & ca_valid_r
                              & (dc4_target_r == `npuarc_DMP_TARGET_DCCM);
end   
  
always @*
begin : dc2_kill_PROC
  //
  //
  dc2_kill                 =  wa_restart_r
                           | (~(x2_load_r | x2_store_r));
end 

always @*
begin : dc2_req_cg0_PROC
  //
  //
  dc2_req_cg0        = (dc1_load_valid & x1_pass)
                     | (dc2_ld_target_dccm & x2_pass)
                     ;
end


reg                   dc3_data_mem_valid_cg0;

always @*
begin : dc3_data_mem_valid_cg0_PROC
  //
  //
  // DC3 Data clock gates
  //
  dc3_data_mem_valid_cg0   = ((dc2_ld_target_dccm | dc2_st_target_dccm) & x2_pass)  // Open
                           | wa_restart_r
                           ;   
end


wire       dc2_ignore_bank_conflict;
wire [3:0] dc2_dc3_bank_common_match; 

assign dc2_ignore_bank_conflict  = 1'b0;
assign dc2_dc3_bank_common_match = 4'b0000;
//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Asynchronous block defining next valid for the DC2 stalls              
//                                                                           
//////////////////////////////////////////////////////////////////////////////
parameter DC2_DEFAULT                  = 2'b00;
parameter DC2_BANK_CONFLICT            = 2'b01;
parameter DC2_WAIT_WQ_DMI              = 2'b10;
parameter DC2_REGAIN_OWNERSHIP         = 2'b11;

reg [1:0]    dc2_state_r;
reg [1:0]    dc2_state_nxt;
reg [1:0]    dc2_state_next;
reg          dc2_lost_ownership;
reg          dc2_lost_ownership_to_wq;
reg          dc2_lost_ownership_to_dmi;

wire         dc2_dcache_stall;
reg [3:0]    dc2_keep_bank_busy;
reg          dc2_full_ack_prev_r;
reg          dc2_full_ack_prev_next;

assign dc2_dcache_stall    = (dc2_target_r == `npuarc_DMP_TARGET_DC) & dc2_cft_stall;
assign dc4_st_target_dc    =   ca_store_r
                             & (dc4_target_r == `npuarc_DMP_TARGET_DCCM)
                             ;
always @*
begin : dc2_lost_ownership_PROC
  // Clock enable
  //
  dc2_lost_ownership_to_dmi  = (  1'b0
                                | pop
                                | dmi_cmd_valid_qual
                               )
//                               & (~wq_dc_entry)
                               & ( | ( {dmi_bank_req[1], dmi_bank_req[1],
                                        dmi_bank_req[0], dmi_bank_req[0]}
                                      & (dc1_dc2_bank_common_r | dc2_data_bank_sel_r)
                                     )
                                 )    
                               & dc2_ld_target_dccm
                               & (  dc2_stuck
                                  | ( dccm_dmi_priority                // when dccm_dmi_priority is set
                                     & (~scrubbing_in_progress_prel)   // make sure that there is no scrubbing in progress
                                     & dc2_stall))
                               ;
  dc2_lost_ownership         =  dc2_lost_ownership_to_wq 
                              | dc2_lost_ownership_to_dmi
                              ;
end

always @*
begin : dc2_conflict_nxt_PROC
  // Clock enable
  //
  dc2_lost_ownership_to_wq  =   (   wq_dc_entry
                                 |  (dc4_st_target_dc & ca_pass)
                                )
                                & dc2_ld_target_dccm
                                & (   1'b0
                                   |  (dc3_stall_r & dc3_partial_or_multi_conflict)    // when dc3 is stalling
                                   |  (~dmu_empty)
                                   |  (~lq_empty_r)
                                   |  dc4_stall_r    // when dc4 is stalling 
                                  )
                                & dc2_stuck
                                ; 
  // Register the individual bank requests
  //
  dc2_req_even_lo          = 1'b0;
  dc2_req_even_hi          = 1'b0;
  dc2_req_odd_lo           = 1'b0;
  dc2_req_odd_hi           = 1'b0;
  
  dc2_keep_bank_busy       = 4'h0;
  dccm_pct_dcbc           = 1'b0;
  
  dc2_state_nxt           = dc2_state_r;
  
  dc2_stall               = 1'b0;
 
  case (dc2_state_r)
  DC2_DEFAULT:
  begin
    
    if (   dc1_bank_conflict 
         & dc1_target_dccm
         & x2_enable)
    begin
      // We have a load in DC1 and DC2 is able to accept it. The load
      // however has a bank conflict and therefore the memory input
      // has not been set up yet. Lets prepare to stall in DC2
      //
     
      dc2_state_nxt            = DC2_BANK_CONFLICT;
    end
    else if (dc2_lost_ownership)
    begin
      // When WQ wants to start during a stall, DC2 will no longer be the owner
      //
      dc2_state_nxt           = DC2_WAIT_WQ_DMI;
    end
  end  
  
  DC2_BANK_CONFLICT:
  begin
    dc2_stall                = (~dc2_ignore_bank_conflict);

    dccm_pct_dcbc            = (~dc2_ignore_bank_conflict);
    
    dc2_req_even_lo          = dc2_bank_not_ack_r[0] & (~dc2_dc3_bank_common_match[0]);
    dc2_req_even_hi          = dc2_bank_not_ack_r[1] & (~dc2_dc3_bank_common_match[1]);
    dc2_req_odd_lo           = dc2_bank_not_ack_r[2] & (~dc2_dc3_bank_common_match[2]);
    dc2_req_odd_hi           = dc2_bank_not_ack_r[3] & (~dc2_dc3_bank_common_match[3]);
  
    // (1) In case of DC1 and DC2 have a bank addr common, then DC1 would not have requested
    //     for the bank that had it common with DC2, hence, in order to prevent the WQ from stealing
    //     the common bank (DC1-DC2). DC2 should keep that bank as well busy
    //

    // Only the banks that were acked by the DC1 arbiter are kept busy
    //
    dc2_keep_bank_busy  = {dc2_bank_req_hi_r[1],
                           dc2_bank_req_lo_r[1],
                           dc2_bank_req_hi_r[0],
                           dc2_bank_req_lo_r[0]}
                         & (  (~dc2_bank_not_ack_r)
                           | dc2_dc3_bank_common_match)   // (1)
                         ;

    if (dc2_lost_ownership)
    begin
      // During a conflict stall, when DMU wants to start, then
      // DC2 will no longer be the owner
      //
      dccm_pct_dcbc           = 1'b0;
      dc2_state_nxt           = DC2_WAIT_WQ_DMI;
    end   
    else if (  dc1_bank_conflict 
             & dc1_target_dccm
             & x1_pass)
    begin
      // Stay here
      //
      dc2_state_nxt           = DC2_BANK_CONFLICT;
    end
    // If X3 is enabled and wait for the LD in DC2 to access the banks and get
    // the dc2_full ack  
    // If X3 is enabled and the LD in DC1, didn't move to DC2. hence it doesn't
    // accessed the banks 
    // 
    else if (  (    dc3_enable          // LD can move forward
//                 & (~x2_exu_stall)    // EXU is not stalling LD in X2
                 & (~dc2_dcache_stall)// No DC2 d-dcache stall
                 & (  dc2_full_ack 
                    | dc2_ignore_bank_conflict
                    | dc2_full_ack_prev_r  // prevents re-acecss in case
                                           // of a DC2 hold-up
                   )
               ) 
             | (dc2_target_r != `npuarc_DMP_TARGET_DCCM)
             | dc3_dccm_poisoned
             | dc2_kill
            )
    begin
      // We request the bank until we get the dc2_full_ack and dc3_enable
      //
      // After X3 is enabled, and after receiving dc2_full_ack, keep requesting the all bank
      // so that dc1 or WQ does not steal the banks during transistion 
      //
      dc2_keep_bank_busy       =  {dc2_bank_req_hi_r[1],
                                   dc2_bank_req_lo_r[1],
                                   dc2_bank_req_hi_r[0],
                                   dc2_bank_req_lo_r[0]};

      dc2_state_nxt            = DC2_DEFAULT;
    end
  end
  
  DC2_WAIT_WQ_DMI:
  begin
    dc2_stall                 = 1'b1;
    
    // when this is set, this will make sure that WQ gets the ACk and it completes
    //
    dc2_lost_ownership_to_wq = 1'b1;

    if (  (dc2_target_r != `npuarc_DMP_TARGET_DCCM)
        | dc2_kill)
    begin
      dc2_state_nxt           = DC2_DEFAULT;
    end
    else if (~wq_dc_entry)
    begin
      dc2_state_nxt           = DC2_REGAIN_OWNERSHIP;
    end
  end
  
  default: // DC2_REGAIN_OWNERSHIP:
  begin
    dc2_stall                = 1'b1;
    
    dc2_req_even_lo          = dc2_bank_req_lo_r[0]; 
    dc2_req_even_hi          = dc2_bank_req_hi_r[0];
    dc2_req_odd_lo           = dc2_bank_req_lo_r[1];
    dc2_req_odd_hi           = dc2_bank_req_hi_r[1];
    
    if (  (dc2_target_r != `npuarc_DMP_TARGET_DCCM)
        | dc2_kill)
    begin
      dc2_state_nxt           = DC2_DEFAULT;
    end
    else if (dc2_lost_ownership)
    begin
      dc2_state_nxt           = DC2_WAIT_WQ_DMI;
    end
    else if (  (    dc3_enable        // LD can move forward
                 & (~x2_exu_stall)    // EXU is not stalling LD in X2
                 & (~dc2_dcache_stall)// No DC2 d-dcache stall
                 &  dc2_full_ack      // Got hold of the banks
               ) 
             | dc3_dccm_poisoned
            )
    begin
      dc2_state_nxt           = DC2_DEFAULT;
    end
  end  
  endcase
end

//////////////////////////////////////////////////////////////////////////////
//
// DC3 Stuck
// 
/////////////////////////////////////////////////////////////////////////////
reg      dc3_stuck;
reg      dc3_target_dc;

always @*
begin : dc3_stuck_PROC
  // Load stuck in DC3
  //
  dc3_target_dc      =   (x3_load_r | x3_store_r)
                       & (  (dc3_target_r == `npuarc_DMP_TARGET_DCCM)
                          | (dc3_target_r == `npuarc_DMP_TARGET_DC));
                          
  dc3_stuck          =   dc3_target_dc
                       & (~(x3_pass & ca_enable));
end  



//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Asynchronous block for the wq bank request               
//                                                                           
//////////////////////////////////////////////////////////////////////////////

always @*
begin : wq_bank_req_PROC
  wq_bank_req_lo[0]      = wq_req_even_lo;
  wq_bank_req_lo[1]      = wq_req_odd_lo;
  
  wq_bank_req_hi[0]      = wq_req_even_hi;
  wq_bank_req_hi[1]      = wq_req_odd_hi;
end

//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Asynchronous block for the dmi bank request               
//                                                                           
//////////////////////////////////////////////////////////////////////////////

always @*
begin : dc2_dmi_delayed_nxt_PROC
  //
  // This determines whether a delayed read/write needs to happen
  //

  // Check for address match between DMI with DC2_DMI, DC3_DMI, DC4_DMI
  //
  dc1_dc2_dmi_addr_match = (dmi_cmd_addr_r[`npuarc_DCCM_DWRD_MSB:3] == dc2_dmi_cmd_addr_r);
  dc1_dc3_dmi_addr_match = (dmi_cmd_addr_r[`npuarc_DCCM_DWRD_MSB:3] == dc3_dmi_cmd_addr_r); 
  dc1_dc4_dmi_addr_match = (dmi_cmd_addr_r[`npuarc_DCCM_DWRD_MSB:3] == dc4_dmi_cmd_addr_r); 

  dc1_entry0_dmi_addr_match = (dmi_cmd_addr_r[`npuarc_DCCM_DWRD_MSB:3] == fifo_entry0_data_out[11:0]);
  dc1_entry1_dmi_addr_match = (dmi_cmd_addr_r[`npuarc_DCCM_DWRD_MSB:3] == fifo_entry1_data_out[11:0]);
  dc1_entry2_dmi_addr_match = (dmi_cmd_addr_r[`npuarc_DCCM_DWRD_MSB:3] == fifo_entry2_data_out[11:0]);

  // Now qualify the address match
  //
  dmi_addr_match_qual = (dc1_dc2_dmi_addr_match & dc2_dmi_valid_r & (~dc2_dmi_read_r))
                      | (dc1_dc3_dmi_addr_match & dc3_dmi_valid_r & (~dc3_dmi_read_r))
                      | (dc1_dc4_dmi_addr_match & dc4_dmi_valid_r & (~dc4_dmi_read_r))
                      | (fifo_entry_valid_r[0] & dc1_entry0_dmi_addr_match & (~fifo_entry0_data_out[87]))
                      | (fifo_entry_valid_r[1] & dc1_entry1_dmi_addr_match & (~fifo_entry1_data_out[87]))
                      | (fifo_entry_valid_r[2] & dc1_entry2_dmi_addr_match & (~fifo_entry2_data_out[87]))
                      ; 

  // Check for partial writes that are already in pipe and fifo's
  //
  dmi_partial_write_in_pipe = (dc2_dmi_valid_r & (~dc2_dmi_read_r) & dc2_dmi_delayed_r)  
                            | (dc3_dmi_valid_r & (~dc3_dmi_read_r) & dc3_dmi_delayed_r)
                            | (dc4_dmi_valid_r & (~dc4_dmi_read_r) & dc4_dmi_delayed_r)
                            | (fifo_valid)
                            ; 

  // check for any delayed read transaction that are in the pipeline
  //
  dmi_delayed_read_in_pipe = (dc2_dmi_read_r & dc2_dmi_delayed_r)
                           | (dc3_dmi_read_r & dc3_dmi_delayed_r)
                           | (dc4_dmi_read_r & dc4_dmi_delayed_r)
                           | (fifo_entry_valid_r[0] & fifo_entry0_data_out[87])
                           | (fifo_entry_valid_r[1] & fifo_entry1_data_out[87])
                           | (fifo_entry_valid_r[2] & fifo_entry2_data_out[87])
                           ;

  // check for retry write in pipe
  //
  dmi_wr_retry_in_pipe = dc2_dmi_wr_retry_r
                       | dc3_dmi_wr_retry_r
                       | dc4_dmi_wr_retry_r
                       | (fifo_entry_valid_r[0] & fifo_entry0_data_out[84])
                       | (fifo_entry_valid_r[1] & fifo_entry1_data_out[84])
                       | (fifo_entry_valid_r[2] & fifo_entry2_data_out[84])
                       ;

  // delayed transaction is based on the following
  //    
  // (1) converting a read transaction to a delayed read, in case of address match
  //
  // (2) converting a write transaction to a delayed write, in case of already existing delayed writes
  //
  // (3) dmi_wr_mask is not a full mask.
  //    
  dc2_dmi_delayed_nxt = (dmi_cmd_valid_r & dmi_cmd_read_r    & dmi_addr_match_qual)       // (1)
                      | (dmi_cmd_valid_r & (~dmi_cmd_read_r) & dmi_partial_write_in_pipe) // (2)
                      | (dmi_cmd_valid_r & (~dmi_cmd_read_r) & (~dmi_full_mask))          // (3)
                      ;

  // Partial write addresss matches with the existing delayed write
  // then re-try the partial write
  //      
  dc2_dmi_wr_retry_nxt = (dmi_cmd_valid_r & (~dmi_cmd_read_r) & (~dmi_full_mask) & dmi_addr_match_qual);

end

always @*
begin : fifo_bank_req_PROC

  fifo_bank_req[0] = fifo_valid & (fifo_data_out[0] == 1'b0);
  fifo_bank_req[1] = fifo_valid & (fifo_data_out[0] == 1'b1);

  // Do not accept new commands when any of the following satisfies
  // (1) fifo_full qualifier
  //
  // (2) There is delayed read in pipe
  //
  // (3) There is a retry write in pipe

  // when there are three or more entries in fifo and pipe combined, then the threshold is reached
  //  
  fifo_full_qual = fifo_full
                 | (fifo_one_empty & (dc2_dmi_valid_r | dc3_dmi_valid_r | dc4_dmi_valid_r))
                 | (dc2_dmi_valid_r & dc3_dmi_valid_r & dc4_dmi_valid_r) 
                 | (  fifo_two_empty 
                    & (  (dc2_dmi_valid_r & dc3_dmi_valid_r)
                       | (dc3_dmi_valid_r & dc4_dmi_valid_r) 
                       | (dc2_dmi_valid_r & dc4_dmi_valid_r)))       
                 ; 

  fifo_threshold = fifo_full_qual               // (1) 
                 | dmi_delayed_read_in_pipe     // (2)
                 | dmi_wr_retry_in_pipe         // (3)
                 ;

  // fifo entries are selected upon the following
  // (1a) when threshold is reached
  //
  // (1b) when there are no dmi transaction, but fifo is valid
  // 
  fifo_select = fifo_threshold              // (1a)
              | (~dmi_cmd_valid_r)          // (1b)
              ;

end    


always @*
begin : dmi_bank_req_PROC
  //
  //
  if (fifo_select)
  begin
    //
    //
    dmi_bank_req[0]    = fifo_bank_req[0]
                       & l1_clock_active
                       ;
    dmi_bank_req[1]    = fifo_bank_req[1]
                       & l1_clock_active
                       ;
    dmi_cmd_valid_qual = fifo_valid;
    dmi_cmd_addr_qual  = fifo_data_out[11:0];
    dc1_dmi_full_write = fifo_valid & (~fifo_data_out[87]) & (~fifo_data_out[84]);
    dc1_dmi_read       = fifo_valid & (fifo_data_out[87] | fifo_data_out[84]);
    dmi_wr_data_qual   = fifo_data_out[75:12];
    dmi_wr_mask_qual   = dmi_rd_err_prel ? 8'h0 : fifo_data_out[83:76];
  end
  else
  begin
    //
    //
    dmi_bank_req[0]    =  dmi_cmd_valid_r 
                       & (dmi_cmd_addr_r[3] == 1'b0)
                       & l1_clock_active
                       ;
    dmi_bank_req[1]    = dmi_cmd_valid_r 
                       & (dmi_cmd_addr_r[3] == 1'b1)
                       & l1_clock_active
                       ;
    dmi_cmd_valid_qual = dmi_cmd_valid_r;
    dmi_cmd_addr_qual  = dmi_cmd_addr_r[`npuarc_DCCM_DWRD_MSB:3];
    dc1_dmi_full_write = !dmi_cmd_read_r & (~dmi_partial_write_in_pipe) & dmi_full_mask;
    dc1_dmi_read       = dmi_cmd_read_r 
                       | (~dmi_cmd_read_r & (~dmi_full_mask));
    dmi_wr_data_qual   = dmi_wr_data;
    dmi_wr_mask_qual   = dmi_wr_mask;      
  end


  // DMI high priority bank req
  //
  dmi_hp_bank_req = dmi_bank_req & {2{dccm_dmi_priority}}
                  & ({2{~scrubbing_in_progress_prel}})
                  ;
end

always @*
begin : dmi_full_ack_PROC
  dmi_bank_ack[0]   = dmi_bank_ack_lo[0] & dmi_bank_ack_hi[0];
  dmi_bank_ack[1]   = dmi_bank_ack_lo[1] & dmi_bank_ack_hi[1];
  
  dmi_bank_req_mask = {dmi_bank_req[1], dmi_bank_req[0]};
  dmi_bank_ack_mask = {dmi_bank_ack[1], dmi_bank_ack[0]};
  
  dmi_full_ack      = (dmi_bank_req_mask == dmi_bank_ack_mask)
                    & l1_clock_active
                    ;
end

//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Asynchronous block to respond to the dmi              
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dmi_cmd_accept_PROC
  // Single cycle write transaction (allowed by the internal bus protocol spec)
  //
  // Do not accept new commands when any of the following satisfies
  // (1) shift fifo is full with 3 entries
  //   
  // (2) in case of rd command, when there is an already pending delayed read in pipe or in fifo
  //     do not accept the read
  //   
  // (3)  in case of incoming read command and there is delayed read in pipe
  //
  dmi_cmd_accept = dmi_full_ack 
                 & (!fifo_threshold)
                 ;
 
  dmi_wr_accept  = (dmi_full_ack 
                 & (!dmi_cmd_read_r) 
                 & (!fifo_threshold));
end

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: some variable are not used in certain configurations
reg  dc2_data_mem_valid;
// leda NTL_CON13A on
reg  dc2_data_mem_valid_cg0;

always @*
begin : dc2_data_mem_valid_PROC

  dc2_data_mem_valid     = (| dc2_data_mem_valid_r);
  dc2_data_mem_valid_cg0 = (  dc1_load_valid & x1_pass);

end

//////////////////////////////////////////////////////////////////////////////
//
// Asynchronous block defining WQ ack
//
//////////////////////////////////////////////////////////////////////////////

reg [3:0] wq_bank_ack;
reg       wq_top_full_ack;
reg       wq_sec_full_ack;
reg       wq_sec_no_conflict;


always @*
begin : wq_full_ack_PROC
  wq_bank_ack =       {wq_bank_ack_hi[1], wq_bank_ack_lo[1],    
                       wq_bank_ack_hi[0], wq_bank_ack_lo[0]};  

  
  // Ack for the first entry in WQ 
  //
  wq_top_full_ack = (    (wq_top_bank_req_mask & wq_bank_ack)
                      ==  wq_top_bank_req_mask)
                   ;

  // No Conflict detection between the two bank requests
  //
  wq_sec_no_conflict =  (wq_top_bank_req_mask ^ wq_sec_bank_req_mask)
                     == (wq_top_bank_req_mask | wq_sec_bank_req_mask);

  // Ack for the second entry in WQ
  // The second should get ack, only after the first ack and
  // there should not be any bank conflict between first and 
  // second request 
  //
  wq_sec_full_ack =       wq_top_full_ack
                      &   wq_sec_no_conflict
                      & (   (wq_sec_bank_req_mask & wq_bank_ack)
                         ==  wq_sec_bank_req_mask);

  // When first or both gets ack
  //
  wq_full_ack = wq_top_full_ack | wq_sec_full_ack;
end

//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Asynchronous block defining clients ack              
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dccm_full_ack_PROC
  // Handy vectors (req)
  //
  dc1_bank_req_mask[0] =   (  dc1_data_bank_sel_lo[0]
                            ) 
                         & (  x1_load_r 
                            | dc1_rmw[0]
                           )
                           ;
 
  dc1_bank_req_mask[1] =   (  dc1_data_bank_sel_hi[0]
                            ) 
                         & (  x1_load_r 
                            | dc1_rmw[1]
                           )
                           ;
 
  dc1_bank_req_mask[2] =   (  dc1_data_bank_sel_lo[1]
                            )  
                         & (  x1_load_r 
                            | dc1_rmw[2]
                           )
                           ;
  
  dc1_bank_req_mask[3] =   (  dc1_data_bank_sel_hi[1]
                            ) 
                         & (  x1_load_r 
                            | dc1_rmw[3]
                           )
                           ;
  
  dc2_bank_req_mask     = {dc2_req_odd_hi, dc2_req_odd_lo,
                           dc2_req_even_hi, dc2_req_even_lo};
  
  
  // Handy vectors (ack)
  //
  dc1_bank_ack_mask     = {dc1_bank_ack_hi[1], dc1_bank_ack_lo[1],
                           dc1_bank_ack_hi[0], dc1_bank_ack_lo[0]};

  // Banks that DC1 and DC2 require are not given to WQ.
  // Lets assume a scenario where there is a bank match between two
  // instructions, (dc1 would not have requested the bank, it just uses the bank activated by DC2)
  // then dc2_keep_bank_busy comes in to play after the instruction moves to DC2
  // during this transistion from DC1 to DC2, the following dc1_dc2_bank_common makes sures that WQ does not come in 
  // and steal the banks
  //
  // This could have been handled by dc2_keep_bank_busy, but that would have an impact on the pipeline LD's
  // Hence we do that in wq ack, so that it does not affect the pipeline LD's  
  // 
  // In case of lost ownership, there is no bank common
  //

  dc1_bank_not_ack      = dc1_wq_dmi_conflict 
                        ? dc1_bank_req_mask
                        : (dc1_bank_ack_mask ^ dc1_bank_req_mask);

  dc1_dc2_bank_common   = (dc1_bank_req_mask | dc2_data_bank_sel_r)
                        & {4{dc1_load_valid  | dc2_ld_target_dccm}}
                        & {4{(~dc2_lost_ownership)}};

  // (1) Make sure that the WQ does not steal the banks that are required by DC2    
  //     after the dc2_stall goes away
  //
  dc1_dc2_bank_common_set_cg0 = (dc1_load_valid & x1_pass)
                              | (dc2_full_ack & dc3_enable);   // (1)
  
  
  dc1_dc2_bank_common_clr_cg0 = (|dc1_dc2_bank_common_r)
                              & (  (dc2_ld_target_dccm & x2_pass)
                                 | dc2_kill
                                 | dc2_lost_ownership);
  dc2_bank_ack_mask     = {dc2_conflict_ack_hi[1], dc2_conflict_ack_lo[1],
                           dc2_conflict_ack_hi[0], dc2_conflict_ack_lo[0]};
end

always @*
begin : dc2_full_ack_PROC
  //
  // A full ack indicates the client was granted all the banks it have requested
  // On a full ack, the client is 'ready' to proceed. We do not fire a memory
  // bank on a partial ack!
  //
  dc1_full_ack          =   (dc1_bank_req_mask == dc1_bank_ack_mask) 
                          & x1_pass;

  dc2_full_ack          =   (dc2_bank_req_mask == dc2_bank_ack_mask) 
                          & (|dc2_bank_req_mask);
end

//////////////////////////////////////////////////////////////////////////////
// 
// Accessing the 2*2-way interleaved two cycle DCCM
//
// mapping of addresses into banks:
//
// bank0 lo   bank0 hi         bank1 lo  bank1 hi   
// 0x00       0x04             0x08      0x0c  
// 0x10       0x14             0x18      0x1c  
// 0x20       0x24             0x28      0x2c  
// 0x30       0x35             0x38      0x3c  
////////////////////////////////////////////////////////////////////////////////
wire [1:0]           dc2_req_lo;
wire [1:0]           dc2_req_hi;

assign dc2_req_lo = {dc2_req_odd_lo, dc2_req_even_lo};
assign dc2_req_hi = {dc2_req_odd_hi, dc2_req_even_hi};

// spyglass disable_block W553
always @*
begin : bank0arb_PROC
  dc1_bank_ack_lo[0]          = 1'b0;  
  dc1_bank_ack_hi[0]          = 1'b0;  
  wq_bank_ack_lo[0]           = 1'b0;  
  wq_bank_ack_hi[0]           = 1'b0;  
  dmi_bank_ack_lo[0]          = 1'b0;  
  dmi_bank_ack_hi[0]          = 1'b0;  
  
  // These are the ack for the conflict loads that are stalled in DC2
  //
  dc2_conflict_ack_lo[0]      = 1'b0;
  dc2_conflict_ack_hi[0]      = 1'b0;
 
  // (1) the bank busy might not work in case of 3 back to back loads to same address
  // because, first load would have kept the bank busy and second load wouldn't have requested
  // the bank, but instead would have re-used the data from earlier Load, when the third load arrives
  // it does not see bank busy (since second LD have not requested the banks) and get the ack
  // This would corrupt the data for the second load. hence use the bank common match to give ack to dc1
  // 
  
  // lo arbiter
  //
  casez ({
          dmi_hp_bank_req[0],
          dc2_req_lo[0],
          dc1_bank_req_lo[0],
          wq_bank_req_lo[0],
          dmi_bank_req[0]
          })
  // when dccm_dmi_priority is set, dmi has hig priority comapred to the LD/ST's
  //
  5'b1????: dmi_bank_ack_lo[0]     =  (~dccm_bank0_wait_lo) 
//                                     & (~dc1_dc2_bank_common_r[0])
                                     & (~scrubbing_in_progress_prel)       // (1)
                                     ;
  5'b01???: dc2_conflict_ack_lo[0] =   (~dccm_bank0_wait_lo)
                                      & dc3_enable;
                                     
  5'b001??: dc1_bank_ack_lo[0]     =   (~dccm_bank0_wait_lo)
                                     & (~dc2_dc3_bank_common_match[0])  // (1)
                                     ;                                     
  5'b0001?: 
  // (1) when there is a dc1 dc2 bank common, WQ can wait
  //   
           wq_bank_ack_lo[0]      =   (~dccm_bank0_wait_lo)
                                     & (~dc1_dc2_bank_common_r[0]);  // (1)
  5'b00001:
    // DMI will get access to the banks when a load already accessed 
    // the banks  and is stalling in X2 (this is taken care by 
    // dc2_lost_ownership_to_dmi.
    // Similarly when a load is stuck in X3, DMI gets access 
    // to the banks as the data for X3, LD  is in skid buffer
    //
    // DMI should not get access while there is a scrubbing in progress (1)
    //
    //
           dmi_bank_ack_lo[0]     =  (~dccm_bank0_wait_lo)         
                                    & (~dc1_dc2_bank_common_r[0])
                                    & (~scrubbing_in_progress_prel)       // (1)
                                    ;

  default:
    ;
  endcase
  

  // hi arbiter
  //
  casez ({
          dmi_hp_bank_req[0],
          dc2_req_hi[0],
          dc1_bank_req_hi[0],
          wq_bank_req_hi[0],
          dmi_bank_req[0]
          })
  // when dccm_dmi_priority is set, dmi has hig priority comapred to the LD/ST's
  //    
  5'b1????: dmi_bank_ack_hi[0]     =  (~dccm_bank0_wait_hi)
//                                     & (~dc1_dc2_bank_common_r[1])
                                     & (~scrubbing_in_progress_prel)       // (1)
                                     ;
  5'b01???: dc2_conflict_ack_hi[0] =   (~dccm_bank0_wait_hi) & dc3_enable;
  5'b001??: dc1_bank_ack_hi[0]     =   (~dccm_bank0_wait_hi)
                                     & (~dc2_dc3_bank_common_match[1]) // (1)
                                     ;                                   
  5'b0001?: 
  // (1) when there is a dc1 dc2 bank common, WQ can wait
  //   
          wq_bank_ack_hi[0]      =   (~dccm_bank0_wait_hi)
                                    & (~dc1_dc2_bank_common_r[1]);  // (1)
  5'b00001:
    // DMI will get access to the banks when a load already accessed           
    // the banks  and is stalling in X2 (this is taken care by 
    // dc2_lost_ownership_to_dmi.
    // Similarly when a load is stuck in X3, DMI gets access          
    // to the banks as the data for X3, LD  is in skid buffer
    //
    // DMI should not get access while there is a scrubbing in progress (1)
    //
    
          dmi_bank_ack_hi[0]     =   (~dccm_bank0_wait_hi)
                                    & (~dc1_dc2_bank_common_r[1])
                                    & (~scrubbing_in_progress_prel)       // (1)
                                    ;   
  default:
    ;
  endcase
end
always @*
begin : bank1arb_PROC
  dc1_bank_ack_lo[1]          = 1'b0;  
  dc1_bank_ack_hi[1]          = 1'b0;  
  wq_bank_ack_lo[1]           = 1'b0;  
  wq_bank_ack_hi[1]           = 1'b0;  
  dmi_bank_ack_lo[1]          = 1'b0;  
  dmi_bank_ack_hi[1]          = 1'b0;  
  
  // These are the ack for the conflict loads that are stalled in DC2
  //
  dc2_conflict_ack_lo[1]      = 1'b0;
  dc2_conflict_ack_hi[1]      = 1'b0;
 
  // (1) the bank busy might not work in case of 3 back to back loads to same address
  // because, first load would have kept the bank busy and second load wouldn't have requested
  // the bank, but instead would have re-used the data from earlier Load, when the third load arrives
  // it does not see bank busy (since second LD have not requested the banks) and get the ack
  // This would corrupt the data for the second load. hence use the bank common match to give ack to dc1
  // 
  
  // lo arbiter
  //
  casez ({
          dmi_hp_bank_req[1],
          dc2_req_lo[1],
          dc1_bank_req_lo[1],
          wq_bank_req_lo[1],
          dmi_bank_req[1]
          })
  // when dccm_dmi_priority is set, dmi has hig priority comapred to the LD/ST's
  //
  5'b1????: dmi_bank_ack_lo[1]     =  (~dccm_bank1_wait_lo) 
//                                     & (~dc1_dc2_bank_common_r[2])
                                     & (~scrubbing_in_progress_prel)       // (1)
                                     ;
  5'b01???: dc2_conflict_ack_lo[1] =   (~dccm_bank1_wait_lo)
                                      & dc3_enable;
                                     
  5'b001??: dc1_bank_ack_lo[1]     =   (~dccm_bank1_wait_lo)
                                     & (~dc2_dc3_bank_common_match[2])  // (1)
                                     ;                                     
  5'b0001?: 
  // (1) when there is a dc1 dc2 bank common, WQ can wait
  //   
           wq_bank_ack_lo[1]      =   (~dccm_bank1_wait_lo)
                                     & (~dc1_dc2_bank_common_r[2]);  // (1)
  5'b00001:
    // DMI will get access to the banks when a load already accessed 
    // the banks  and is stalling in X2 (this is taken care by 
    // dc2_lost_ownership_to_dmi.
    // Similarly when a load is stuck in X3, DMI gets access 
    // to the banks as the data for X3, LD  is in skid buffer
    //
    // DMI should not get access while there is a scrubbing in progress (1)
    //
    //
           dmi_bank_ack_lo[1]     =  (~dccm_bank1_wait_lo)         
                                    & (~dc1_dc2_bank_common_r[2])
                                    & (~scrubbing_in_progress_prel)       // (1)
                                    ;

  default:
    ;
  endcase
  

  // hi arbiter
  //
  casez ({
          dmi_hp_bank_req[1],
          dc2_req_hi[1],
          dc1_bank_req_hi[1],
          wq_bank_req_hi[1],
          dmi_bank_req[1]
          })
  // when dccm_dmi_priority is set, dmi has hig priority comapred to the LD/ST's
  //    
  5'b1????: dmi_bank_ack_hi[1]     =  (~dccm_bank1_wait_hi)
//                                     & (~dc1_dc2_bank_common_r[3])
                                     & (~scrubbing_in_progress_prel)       // (1)
                                     ;
  5'b01???: dc2_conflict_ack_hi[1] =   (~dccm_bank1_wait_hi) & dc3_enable;
  5'b001??: dc1_bank_ack_hi[1]     =   (~dccm_bank1_wait_hi)
                                     & (~dc2_dc3_bank_common_match[3]) // (1)
                                     ;                                   
  5'b0001?: 
  // (1) when there is a dc1 dc2 bank common, WQ can wait
  //   
          wq_bank_ack_hi[1]      =   (~dccm_bank1_wait_hi)
                                    & (~dc1_dc2_bank_common_r[3]);  // (1)
  5'b00001:
    // DMI will get access to the banks when a load already accessed           
    // the banks  and is stalling in X2 (this is taken care by 
    // dc2_lost_ownership_to_dmi.
    // Similarly when a load is stuck in X3, DMI gets access          
    // to the banks as the data for X3, LD  is in skid buffer
    //
    // DMI should not get access while there is a scrubbing in progress (1)
    //
    
          dmi_bank_ack_hi[1]     =   (~dccm_bank1_wait_hi)
                                    & (~dc1_dc2_bank_common_r[3])
                                    & (~scrubbing_in_progress_prel)       // (1)
                                    ;   
  default:
    ;
  endcase
end
// spyglass enable_block W553

//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Asynchronous block to respond to the wq              
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_dccm_read_PROC
  // DCCM ack the WQ when the WQ is req a bank and it gets a full ack
  //
  wq_dccm_read_one =      wq_top_full_ack
                     & (| wq_top_bank_req_mask);

  wq_dccm_read_two =      wq_sec_full_ack
                     & (| wq_sec_bank_req_mask);
end




//////////////////////////////////////////////////////////////////////////////
//
// Detecting partial writes     
//    
/////////////////////////////////////////////////////////////////////////////

always @*
begin : dmi_full_mask_PROC
  // A partial write contain "wholes" in the wr_mask
  //
  dmi_full_mask =      (dmi_wr_mask_prel[7:0] == 8'b0000_1111)
                     | (dmi_wr_mask_prel[7:0] == 8'b1111_0000)
                     | (dmi_wr_mask_prel[7:0] == 8'b1111_1111)
                     | (dmi_wr_mask_prel[7:0] == 8'b0000_0000)
                     | ecc_dmp_disable
                     ;     
end

wire dmi_wr_done;
wire dmi_err_wr;

//////////////////////////////////////////////////////////////////////////////
//
// Derive final write mask   
//    
/////////////////////////////////////////////////////////////////////////////
// (1) In case of partial WR mask, zero out the mask, so that memory
//     is not corrupted
// (2) When ECC is disabled, use the actual WR mask
//

assign dmi_wr_mask =  dmi_wr_mask_prel;


// Generate the dmi_wr_done when there is a wr_valid_r and wr_accept
//
assign dmi_wr_done = (  dmi_wr_valid_r 
                      & dmi_wr_accept
                      & (~dc2_dmi_delayed_nxt)
                      & (dmi_full_mask | ecc_dmp_disable)
                    )
                  | (  pop
                     & (~fifo_data_out[87])
                     & (~fifo_data_out[84])
                     & (~fifo_data_out[85]) // read_error
                    )    
                    ;

assign dmi_err_wr  =  (  dmi_wr_valid_r 
                       & dmi_wr_accept 
                       & (~ecc_dmp_disable)
                       & (1'b0)
                     )
                  | (  pop
                     & (~fifo_data_out[87])
                     & (~fifo_data_out[84])
                     & fifo_data_out[85]  // read error
                    )     
                    ;                       


//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Asynchronous process to select the DMI read data      
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dmi_rd_data_PROC
  // DMI transactions to the DCCM are always aligned. Furthermore, it is 
  // assumed here that the target BIU is always ready to accept the 
  // rd_data, i.e.  dmi_rd_accept is always high
  //
  
  dmi_rd_err_prel  =     (|dmi_bank_ack_rrr)
                   &  (  1'b0 
                       | (|dc4_dmi_ecc_db_error)
                      )
                   ;

  dmi_rd_err    = dmi_rd_err_prel
                & (~dc4_dmi_valid_r)
                ;
  
  dmi_rd_valid  =  ((| dmi_bank_ack_rrr) & (~dmi_rd_err_prel))
                & (~dc4_dmi_valid_r)
                ;

  dmi_rd_data_nxt =  ecc_dmp_disable ? {dmi_data_hi_r[31:0], dmi_data_lo_r[31:0]} : {dmi_ecc_data_hi, dmi_ecc_data_lo};
end

//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Asynchronous block defining the clock enable for ctl information            
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dmi_cg0_PROC
  // DMI clockgates
  //
  dmi_cg0[0]            =        dmi_bank_ack[0]
                                | dmi_bank_ack_r[0];
  
  dmi_ack_cg0[0]        =        dmi_bank_ack_r[0]
                                | dmi_bank_ack_rr[0];
                                
  dmi_rd_valid_cg0[0]   =        dmi_bank_ack_rr[0]
                                | dmi_bank_ack_rrr[0];
  dmi_cg0[1]            =        dmi_bank_ack[1]
                                | dmi_bank_ack_r[1];
  
  dmi_ack_cg0[1]        =        dmi_bank_ack_r[1]
                                | dmi_bank_ack_rr[1];
                                
  dmi_rd_valid_cg0[1]   =        dmi_bank_ack_rr[1]
                                | dmi_bank_ack_rrr[1];
end

always @*
begin : dc_dmi_cg0_PROC
  //
  // 
  dc2_dmi_cg0 = (   (~fifo_full)                                     // Set
                  & (  pop
                     | (dmi_cmd_accept & dc2_dmi_delayed_nxt)) )                           
              | (~fifo_full & dc2_dmi_valid_r & (~pop))              // Re-set 
              ;

  dc3_dmi_cg0 = (   (~fifo_full)                                     // Set
                  &  dc2_dmi_valid_r)
              | (~fifo_full & dc3_dmi_valid_r)                       // Re-set 
              ;

  dc4_dmi_cg0 = (   (~fifo_full)                                     // Set
                  &  dc3_dmi_valid_r)
              | (~fifo_full & dc4_dmi_valid_r)                       // Re-set 
              ;
end


//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Asynchronous block defining the clock enable for ctl information (lo)           
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dccm_bank_lo_cg0_PROC
  dccm_bank_cs_lo_cg0[0] =    dccm_bank_busy_lo[0]
                            | dc2_stall
                            | (dc1_bank_req_lo[0])
                            | dc2_req_lo[0]
                            | (wq_bank_req_lo[0])
                            | (dmi_bank_req[0])
                            ;
 
  dccm_bank_cs_lo_cg0[1] =   dccm_bank_busy_lo[1]
                           | dc2_stall
                           | (dc1_bank_req_lo[1])
                           | dc2_req_lo[1]
                           | (wq_bank_req_lo[1])
                           | (dmi_bank_req[1])
                           ;

  dccm_bank_addr_lo_cg0[0] =   dc1_bank_req_lo[0] 
                             | dc2_req_lo[0]
                             | (wq_bank_ack_lo[0]  & wq_full_ack)
                             | (dmi_bank_req[0]    & dmi_full_ack)
                             ;
 
  dccm_bank_addr_lo_cg0[1] =    dc1_bank_req_lo[1]
                             | dc2_req_lo[1]
                             | (wq_bank_ack_lo[1]  & wq_full_ack)
                             | (dmi_bank_req[1]    & dmi_full_ack)
                             ;
  // This clock enable controls the din when writing into the memory
  //
  dccm_bank_data_lo_cg0[0] =   (wq_top_bank_req_mask[0]) 
                             | (wq_sec_bank_req_mask[0])
                             | (dmi_bank_req[0] & dc1_dmi_full_write)
                             ;    
  
  dccm_bank_data_lo_cg0[1] =   (wq_top_bank_req_mask[2]) 
                             | (wq_sec_bank_req_mask[2])
                             | (dmi_bank_req[1] & dc1_dmi_full_write)
                             ;    
end

//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Asynchronous block defining the clock enable for ctl information (hi)           
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dccm_bank_hi_cg0_PROC
  dccm_bank_cs_hi_cg0[0] =    dccm_bank_busy_hi[0]
                            | dc2_stall
                            | (dc1_bank_req_hi[0])
                            | dc2_req_hi[0]
                            | (wq_bank_req_hi[0])
                            | (dmi_bank_req[0])
                            ;
 
  dccm_bank_cs_hi_cg0[1] =    dccm_bank_busy_hi[1]
                            | dc2_stall
                            | (dc1_bank_req_hi[1])
                            | dc2_req_hi[1]
                            | (wq_bank_req_hi[1])
                            | (dmi_bank_req[1])
                            ;

  dccm_bank_addr_hi_cg0[0] =   dc1_bank_req_hi[0] 
                            | dc2_req_hi[0]
                            | (wq_bank_ack_hi[0] & wq_full_ack)
                            | (dmi_bank_req[0]   & dmi_full_ack)
                           ;
 
  dccm_bank_addr_hi_cg0[1] =    dc1_bank_req_hi[1]
                             | dc2_req_hi[1]
                             | (wq_bank_ack_hi[1] & wq_full_ack)
                             | (dmi_bank_req[1]   & dmi_full_ack)
                             ;
  // This chick enable controls the din when writing into the memory
  //
  dccm_bank_data_hi_cg0[0] =   (wq_top_bank_req_mask[1]) 
                             | (wq_sec_bank_req_mask[1])
                             | (dmi_bank_req[0] & dc1_dmi_full_write)
                             ;    
  
  dccm_bank_data_hi_cg0[1] =   (wq_top_bank_req_mask[3]) 
                             | (wq_sec_bank_req_mask[3]) 
                             | (dmi_bank_req[1] & dc1_dmi_full_write)
                             ;    

end

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// ctl memory flops (nxt values of cs)
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : core_bank_cs_nxt_PROC
  // bank0 (hi, lo)
  //
  core_bank0_cs_lo_nxt =  
         (dc1_ack_qual[0]         & dc1_target_dccm)                // dc1
       | (dc2_conflict_ack_lo[0]  & dc2_full_ack & dc2_target_dccm) // dc2
       | (wq_top_bank_req_mask[0] & wq_top_full_ack)           // wq top
       | (wq_sec_bank_req_mask[0] & wq_sec_full_ack)           // wq sec
       | (dmi_bank_ack_lo[0] & dmi_full_ack)
       ;
  
  
  core_bank0_cs_hi_nxt = 
         (dc1_ack_qual[1]         & dc1_target_dccm)                // dc1
       | (dc2_conflict_ack_hi[0]  & dc2_full_ack & dc2_target_dccm) // dc2
       | (wq_top_bank_req_mask[1] & wq_top_full_ack)           // wq top
       | (wq_sec_bank_req_mask[1] & wq_sec_full_ack)           // wq sec
       | (dmi_bank_ack_hi[0] & dmi_full_ack)
       ;

  // bank1 (hi, lo)
  //
  core_bank1_cs_lo_nxt =  
         (dc1_ack_qual[2]         & dc1_target_dccm)                // dc1
       | (dc2_conflict_ack_lo[1]  & dc2_full_ack & dc2_target_dccm) // dc2
       | (wq_top_bank_req_mask[2] & wq_top_full_ack)           // wq top
       | (wq_sec_bank_req_mask[2] & wq_sec_full_ack)           // wq sec
       | (dmi_bank_ack_lo[1] & dmi_full_ack)
      ;
  
  
  core_bank1_cs_hi_nxt =  
         (dc1_ack_qual[3]         & dc1_target_dccm)                // dc1
       | (dc2_conflict_ack_hi[1]  & dc2_full_ack & dc2_target_dccm) // dc2
       | (wq_top_bank_req_mask[3] & wq_top_full_ack)           // wq top
       | (wq_sec_bank_req_mask[3] & wq_sec_full_ack)           // wq sec
       | (dmi_bank_ack_hi[1] & dmi_full_ack)
       ;
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// ctl memory flops (nxt values of we)
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : core_bank_we_nxt_PROC
  // bank0 (hi, lo)
  //
  core_bank0_we_lo_nxt =   (wq_top_bank_req_mask[0] & wq_top_full_ack) // wq top
                         | (wq_sec_bank_req_mask[0] & wq_sec_full_ack) // wq sec
                         | (dmi_bank_ack_lo[0] & dmi_full_ack & dc1_dmi_full_write)
                         ;  
  core_bank0_we_hi_nxt =   (wq_top_bank_req_mask[1] & wq_top_full_ack) // wq top
                         | (wq_sec_bank_req_mask[1] & wq_sec_full_ack) // wq sec
                         | (dmi_bank_ack_hi[0] & dmi_full_ack & dc1_dmi_full_write) 
                         ;  
  
  // bank1 (hi, lo)
  //
  core_bank1_we_lo_nxt =   (wq_top_bank_req_mask[2] & wq_top_full_ack) // wq top
                         | (wq_sec_bank_req_mask[2] & wq_sec_full_ack) // wq sec
                         | (dmi_bank_ack_lo[1] & dmi_full_ack & dc1_dmi_full_write) 
                         ;  
  core_bank1_we_hi_nxt =   (wq_top_bank_req_mask[3] & wq_top_full_ack) // wq top
                         | (wq_sec_bank_req_mask[3] & wq_sec_full_ack) // wq sec
                         | (dmi_bank_ack_hi[1] & dmi_full_ack & dc1_dmi_full_write) 
                         ;  
 end
  
//////////////////////////////////////////////////////////////////////////////
//                                                                          
//  addr  flops (nxt values of addr)
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : core_bank_addr_nxt_PROC
  // Bank0 lo
  //
  case (1'b1)
  wq_bank_ack_lo[0]:      core_bank0_addr_lo_nxt = wq_addr_even_lo;
  dmi_bank_ack[0]:        core_bank0_addr_lo_nxt = dmi_cmd_addr_qual[11:1];
  dc2_conflict_ack_lo[0]: core_bank0_addr_lo_nxt = dc2_dccm_addr0_r;
  default:                core_bank0_addr_lo_nxt = dc1_dccm_addr0;
  endcase 

  // Bank0 hi
  //
  case (1'b1)
  wq_bank_ack_hi[0]:      core_bank0_addr_hi_nxt = wq_addr_even_hi;
  dmi_bank_ack[0]:        core_bank0_addr_hi_nxt = dmi_cmd_addr_qual[11:1];
  dc2_conflict_ack_hi[0]: core_bank0_addr_hi_nxt = dc2_dccm_addr0_r;
  default:                core_bank0_addr_hi_nxt = dc1_dccm_addr0;
  endcase
  // Bank1 lo
  //
  case (1'b1)
  wq_bank_ack_lo[1]:      core_bank1_addr_lo_nxt = wq_addr_odd_lo;
  dmi_bank_ack[1]:        core_bank1_addr_lo_nxt = dmi_cmd_addr_qual[11:1];
  dc2_conflict_ack_lo[1]: core_bank1_addr_lo_nxt = dc2_dccm_addr1_r;
  default:                core_bank1_addr_lo_nxt = dc1_dccm_addr1;
  endcase

  // Bank1 hi
  //
  case (1'b1)
  wq_bank_ack_hi[1]:      core_bank1_addr_hi_nxt = wq_addr_odd_hi;
  dmi_bank_ack[1]:        core_bank1_addr_hi_nxt = dmi_cmd_addr_qual[11:1];
  dc2_conflict_ack_hi[1]: core_bank1_addr_hi_nxt = dc2_dccm_addr1_r;
  default:                core_bank1_addr_hi_nxt = dc1_dccm_addr1;
  endcase
  
end

reg [`npuarc_DOUBLE_RANGE] dc4_dmi_rmw_data;

always @*
begin : dc4_dmi_rmw_data_PROC
  //
  // merge the read-modify-write data with wr data 
  if (ecc_dmp_disable | dc4_dmi_wr_retry_r | (~dc4_dmi_rmw_r))
  begin
    dc4_dmi_rmw_data = dc4_dmi_wr_data_r;
  end
  else
  begin  
    dc4_dmi_rmw_data[7:0]   = dc4_dmi_wr_mask_r[0] ? dc4_dmi_wr_data_r[7:0]   : dmi_rd_data_nxt[7:0];  
    dc4_dmi_rmw_data[15:8]  = dc4_dmi_wr_mask_r[1] ? dc4_dmi_wr_data_r[15:8]  : dmi_rd_data_nxt[15:8];  
    dc4_dmi_rmw_data[23:16] = dc4_dmi_wr_mask_r[2] ? dc4_dmi_wr_data_r[23:16] : dmi_rd_data_nxt[23:16];  
    dc4_dmi_rmw_data[31:24] = dc4_dmi_wr_mask_r[3] ? dc4_dmi_wr_data_r[31:24] : dmi_rd_data_nxt[31:24];  
    dc4_dmi_rmw_data[39:32] = dc4_dmi_wr_mask_r[4] ? dc4_dmi_wr_data_r[39:32] : dmi_rd_data_nxt[39:32];  
    dc4_dmi_rmw_data[47:40] = dc4_dmi_wr_mask_r[5] ? dc4_dmi_wr_data_r[47:40] : dmi_rd_data_nxt[47:40];  
    dc4_dmi_rmw_data[55:48] = dc4_dmi_wr_mask_r[6] ? dc4_dmi_wr_data_r[55:48] : dmi_rd_data_nxt[55:48];  
    dc4_dmi_rmw_data[63:56] = dc4_dmi_wr_mask_r[7] ? dc4_dmi_wr_data_r[63:56] : dmi_rd_data_nxt[63:56];  
  end
end  


//////////////////////////////////////////////////////////////////////////////
//
// DCCM_DMI and DCCM_ECC
//
/////////////////////////////////////////////////////////////////////////////
wire [`npuarc_ECC_CODE_MSB:0]         dmi_ecc_data_bank_lo;
wire [`npuarc_ECC_CODE_MSB:0]         dmi_ecc_data_bank_hi;


npuarc_alb_ecc_gen_32 u_alb_dmp_ecc_gen32_dmi_bank_lo (
  .data_in        (dmi_wr_data_qual[`npuarc_DBL_LO_RANGE]),
  .ecc_code       (dmi_ecc_data_bank_lo      )
);

npuarc_alb_ecc_gen_32 u_alb_dmp_ecc_gen32_dmi_bank_hi (
   .data_in        (dmi_wr_data_qual[`npuarc_DBL_HI_RANGE]),
  .ecc_code       (dmi_ecc_data_bank_hi      )
);

wire [`npuarc_ECC_CODE_MSB:0]         wq_ecc_data_even_lo;
wire [`npuarc_ECC_CODE_MSB:0]         wq_ecc_data_even_hi;
wire [`npuarc_ECC_CODE_MSB:0]         wq_ecc_data_odd_lo;
wire [`npuarc_ECC_CODE_MSB:0]         wq_ecc_data_odd_hi;


npuarc_alb_ecc_gen_32 u_alb_dmp_ecc_gen32_wq_even_lo (
  .data_in        (wq_din_even_lo              ),
  .ecc_code       (wq_ecc_data_even_lo         )
);
 
npuarc_alb_ecc_gen_32 u_alb_dmp_ecc_gen32_wq_even_hi (
  .data_in        (wq_din_even_hi              ),
  .ecc_code       (wq_ecc_data_even_hi         )
);

npuarc_alb_ecc_gen_32 u_alb_dmp_ecc_gen32_wq_odd_lo (
  .data_in        (wq_din_odd_lo               ),
  .ecc_code       (wq_ecc_data_odd_lo          )
);

npuarc_alb_ecc_gen_32 u_alb_dmp_ecc_gen32_wq_odd_hi (
  .data_in        (wq_din_odd_hi               ),
  .ecc_code       (wq_ecc_data_odd_hi          )
);


  
//////////////////////////////////////////////////////////////////////////////
//                                                                          
//   data memory flops (nxt values of wem and din)
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : core_bank_wem_din_nxt_PROC
  // Bank 0 lo
  //
  casez ({
          {wq_bank_req_lo[0] & (~dmi_hp_bank_req[0])}, 
          1'b0,
          dmi_bank_req[0]
         })
  3'b1??:
  begin
    core_bank0_wem_nxt[`npuarc_DBL_DCCM_BE_LO_RANGE]  = {{~ecc_dmp_disable & (|wq_wem_even_lo)}, 
                                                    wq_wem_even_lo};
    core_bank0_din_nxt[`npuarc_DBL_DCCM_LO_RANGE]     = {
                                                  wq_ecc_data_even_lo,
                                                  wq_din_even_lo};
  end


  3'b0?1:
  begin
    core_bank0_wem_nxt[`npuarc_DBL_DCCM_BE_LO_RANGE] = {{~ecc_dmp_disable & (|dmi_wr_mask_qual[`npuarc_DBL_BE_LO_RANGE])}, 
                                                   dmi_wr_mask_qual[`npuarc_DBL_BE_LO_RANGE]};
    core_bank0_din_nxt[`npuarc_DBL_DCCM_LO_RANGE]    = {dmi_ecc_data_bank_lo,
                                                 dmi_wr_data_qual[`npuarc_DBL_LO_RANGE]};
  end
  default:
  begin
    core_bank0_wem_nxt[`npuarc_DBL_DCCM_BE_LO_RANGE] = core_bank0_wem_r[`npuarc_DBL_DCCM_BE_LO_RANGE];
    core_bank0_din_nxt[`npuarc_DBL_DCCM_LO_RANGE]    = core_bank0_din_r[`npuarc_DBL_DCCM_LO_RANGE];
  end
  endcase

  // Bank 0 hi
  //
  casez ({
          {wq_bank_req_hi[0] & (~dmi_hp_bank_req[0])}, 
          1'b0,
          dmi_bank_req[0]
         })
  3'b1??:
  begin
    core_bank0_wem_nxt[`npuarc_DBL_DCCM_BE_HI_RANGE]  = {{~ecc_dmp_disable & (|wq_wem_even_hi)},
                                                    wq_wem_even_hi};
    core_bank0_din_nxt[`npuarc_DBL_DCCM_HI_RANGE]     = {
                                                  wq_ecc_data_even_hi,
                                                  wq_din_even_hi};
  end


  3'b0?1:
  begin
    core_bank0_wem_nxt[`npuarc_DBL_DCCM_BE_HI_RANGE] = {{~ecc_dmp_disable & (|dmi_wr_mask_qual[`npuarc_DBL_BE_HI_RANGE])}, 
                                                   dmi_wr_mask_qual[`npuarc_DBL_BE_HI_RANGE]};
    core_bank0_din_nxt[`npuarc_DBL_DCCM_HI_RANGE]    = {dmi_ecc_data_bank_hi,
                                                 dmi_wr_data_qual[`npuarc_DBL_HI_RANGE]};
  end
  default:
  begin
    core_bank0_wem_nxt[`npuarc_DBL_DCCM_BE_HI_RANGE] = core_bank0_wem_r[`npuarc_DBL_DCCM_BE_HI_RANGE];
    core_bank0_din_nxt[`npuarc_DBL_DCCM_HI_RANGE]    = core_bank0_din_r[`npuarc_DBL_DCCM_HI_RANGE];
  end
  endcase
  
  // Bank 1 lo
  //
  casez ({
          {wq_bank_req_lo[1] & (~dmi_hp_bank_req[1])},
          1'b0,
          dmi_bank_req[1]
         })
  3'b1??:
  begin
    core_bank1_wem_nxt[`npuarc_DBL_DCCM_BE_LO_RANGE]  = {{~ecc_dmp_disable & (|wq_wem_odd_lo)}, 
                                                    wq_wem_odd_lo};
    core_bank1_din_nxt[`npuarc_DBL_DCCM_LO_RANGE]     = {
                                                  wq_ecc_data_odd_lo,
                                                  wq_din_odd_lo};
  end


  3'b0?1:
  begin
    core_bank1_wem_nxt[`npuarc_DBL_DCCM_BE_LO_RANGE] = {{~ecc_dmp_disable & (|dmi_wr_mask_qual[`npuarc_DBL_BE_LO_RANGE])}, 
                                                   dmi_wr_mask_qual[`npuarc_DBL_BE_LO_RANGE]};
    core_bank1_din_nxt[`npuarc_DBL_DCCM_LO_RANGE]    = {dmi_ecc_data_bank_lo,
                                                 dmi_wr_data_qual[`npuarc_DBL_LO_RANGE]};
  end
  default:
  begin
    core_bank1_wem_nxt[`npuarc_DBL_DCCM_BE_LO_RANGE] = core_bank1_wem_r[`npuarc_DBL_DCCM_BE_LO_RANGE];
    core_bank1_din_nxt[`npuarc_DBL_DCCM_LO_RANGE]    = core_bank1_din_r[`npuarc_DBL_DCCM_LO_RANGE];
  end
  endcase

  // Bank 1 hi
  //
  casez ({
          {wq_bank_req_hi[1] & (~dmi_hp_bank_req[1])},  
          1'b0,
          dmi_bank_req[1]
         })
  3'b1??:
  begin
    core_bank1_wem_nxt[`npuarc_DBL_DCCM_BE_HI_RANGE]  = {{~ecc_dmp_disable & (|wq_wem_odd_hi)},
                                                    wq_wem_odd_hi};
    core_bank1_din_nxt[`npuarc_DBL_DCCM_HI_RANGE]     = {
                                                  wq_ecc_data_odd_hi,
                                                  wq_din_odd_hi};
  end


  3'b0?1:
  begin
    core_bank1_wem_nxt[`npuarc_DBL_DCCM_BE_HI_RANGE] = {{~ecc_dmp_disable & (|dmi_wr_mask_qual[`npuarc_DBL_BE_HI_RANGE])},
                                                   dmi_wr_mask_qual[`npuarc_DBL_BE_HI_RANGE]};
    core_bank1_din_nxt[`npuarc_DBL_DCCM_HI_RANGE]    = {dmi_ecc_data_bank_hi,
                                                 dmi_wr_data_qual[`npuarc_DBL_HI_RANGE]};
  end
  default:
  begin
    core_bank1_wem_nxt[`npuarc_DBL_DCCM_BE_HI_RANGE] = core_bank1_wem_r[`npuarc_DBL_DCCM_BE_HI_RANGE];
    core_bank1_din_nxt[`npuarc_DBL_DCCM_HI_RANGE]    = core_bank1_din_r[`npuarc_DBL_DCCM_HI_RANGE];
  end
  endcase
end

//////////////////////////////////////////////////////////////////////////////
//
// Detection of Single or Double Bit errors
//
/////////////////////////////////////////////////////////////////////////////

wire                ecc_sb_error_even_lo;
wire                ecc_sb_error_even_hi;
wire                ecc_sb_error_odd_lo;
wire                ecc_sb_error_odd_hi;

wire                ecc_db_error_even_lo;
wire                ecc_db_error_even_hi;
wire                ecc_db_error_odd_lo;
wire                ecc_db_error_odd_hi;

wire                i_parity_0;
wire                i_parity_1;
wire                i_parity_2;
wire                i_parity_3;

reg                 i_parity_0_nxt;
reg                 i_parity_1_nxt;
reg                 i_parity_2_nxt;
reg                 i_parity_3_nxt;

reg                 i_parity_0_r;
reg                 i_parity_1_r;
reg                 i_parity_2_r;
reg                 i_parity_3_r;

wire [`npuarc_SYNDROME_MSB:0]     syndrome_0;
wire [`npuarc_SYNDROME_MSB:0]     syndrome_1;
wire [`npuarc_SYNDROME_MSB:0]     syndrome_2;
wire [`npuarc_SYNDROME_MSB:0]     syndrome_3;

reg  [`npuarc_SYNDROME_MSB:0]     syndrome_0_nxt;
reg  [`npuarc_SYNDROME_MSB:0]     syndrome_1_nxt;
reg  [`npuarc_SYNDROME_MSB:0]     syndrome_2_nxt;
reg  [`npuarc_SYNDROME_MSB:0]     syndrome_3_nxt;

reg  [`npuarc_SYNDROME_MSB:0]     syndrome_0_r;
reg  [`npuarc_SYNDROME_MSB:0]     syndrome_1_r;
reg  [`npuarc_SYNDROME_MSB:0]     syndrome_2_r;
reg  [`npuarc_SYNDROME_MSB:0]     syndrome_3_r;

reg  [3:0]                 dc4_ecc_valid_r;
wire [3:0]                 ecc_valid;

assign ecc_valid  = dc4_skid_ecc_valid_r & dc4_ecc_valid_r & {4{~wa_restart_r}};


npuarc_alb_dmp_ecc_combined_a u_alb_dmp_ecc_combined_a_0 (
  .data_in                        (dc3_dccm_data_even_lo[`npuarc_DATA_RANGE] ),  // Data bits
  .ecc_code_in                    (dc3_dccm_data_even_lo[38:32]       ),  // ECC bits   
  .i_parity                       (i_parity_0                         ),  // SB error
  .syndrome                       (syndrome_0                         )  // DB error
);

npuarc_alb_dmp_ecc_combined_a u_alb_dmp_ecc_combined_a_1 (
  .data_in                        (dc3_dccm_data_even_hi[`npuarc_DATA_RANGE] ),  // Data bits
  .ecc_code_in                    (dc3_dccm_data_even_hi[38:32]       ),  // ECC bits  
  .i_parity                       (i_parity_1                         ),  // SB error
  .syndrome                       (syndrome_1                         )  // DB error
);

npuarc_alb_dmp_ecc_combined_a u_alb_dmp_ecc_combined_a_2 (
  .data_in                        (dc3_dccm_data_odd_lo[`npuarc_DATA_RANGE]  ),  // Data bits
  .ecc_code_in                    (dc3_dccm_data_odd_lo[38:32]        ),  // ECC bits
  .i_parity                       (i_parity_2                         ),  // SB error
  .syndrome                       (syndrome_2                         )  // DB error
);

npuarc_alb_dmp_ecc_combined_a u_alb_dmp_ecc_combined_a_3 (
  .data_in                        (dc3_dccm_data_odd_hi[`npuarc_DATA_RANGE]  ),  // Data bits
  .ecc_code_in                    (dc3_dccm_data_odd_hi[38:32]        ),  // ECC bits
  .i_parity                       (i_parity_3                         ),  // SB error
  .syndrome                       (syndrome_3                         )  // DB error
);


npuarc_alb_dmp_ecc_combined_b u_alb_dmp_ecc_combined_b_0 (
  .data_in                        (dc4_data_even_lo_r[`npuarc_DATA_RANGE] ),  // Data bits
  .ecc_code_in                    (dc4_data_even_lo_r[38:32]        ),  // ECC code
  .i_parity                       (i_parity_0_r                         ),  // SB error
  .syndrome                       (syndrome_0_r                         ),  // DB error
  .ecc_dmp_disable                (~ecc_valid[0] | ecc_dmp_disable ),  // ECC Disabled
  .sb_error                       (ecc_sb_error_even_lo),  // SB error
  .db_error                       (ecc_db_error_even_lo),  // DB error
  .data_out                       (dc4_ecc_data_even_lo)   // Syndrome
);

npuarc_alb_dmp_ecc_combined_b u_alb_dmp_ecc_combined_b_1 (
  .data_in                        (dc4_data_even_hi_r[`npuarc_DATA_RANGE] ),  // Data bits
  .ecc_code_in                    (dc4_data_even_hi_r[38:32]        ),  // ECC code
  .i_parity                       (i_parity_1_r                         ),  // SB error
  .syndrome                       (syndrome_1_r                         ),  // DB error
  .ecc_dmp_disable                (~ecc_valid[1] | ecc_dmp_disable ),  // ECC Disabled
  .sb_error                       (ecc_sb_error_even_hi),  // SB error
  .db_error                       (ecc_db_error_even_hi),  // DB error
  .data_out                       (dc4_ecc_data_even_hi)   // Syndrome
);

npuarc_alb_dmp_ecc_combined_b u_alb_dmp_ecc_combined_b_2 (
  .data_in                        (dc4_data_odd_lo_r[`npuarc_DATA_RANGE]  ),  // Data bits
  .ecc_code_in                    (dc4_data_odd_lo_r[38:32]         ),  // ECC code
  .i_parity                       (i_parity_2_r                         ),  // SB error
  .syndrome                       (syndrome_2_r                         ),  // DB error
  .ecc_dmp_disable                (~ecc_valid[2] | ecc_dmp_disable ),  // ECC Disabled
  .sb_error                       (ecc_sb_error_odd_lo),  // SB error
  .db_error                       (ecc_db_error_odd_lo),  // DB error
  .data_out                       (dc4_ecc_data_odd_lo)   // Syndrome
);

npuarc_alb_dmp_ecc_combined_b u_alb_dmp_ecc_combined_b_3 (
  .data_in                        (dc4_data_odd_hi_r[`npuarc_DATA_RANGE]  ),  // Data bits
  .ecc_code_in                    (dc4_data_odd_hi_r[38:32]         ),  // ECC code
  .i_parity                       (i_parity_3_r                         ),  // SB error
  .syndrome                       (syndrome_3_r                         ),  // DB error
  .ecc_dmp_disable                (~ecc_valid[3] | ecc_dmp_disable ),  // ECC Disabled
  .sb_error                       (ecc_sb_error_odd_hi),  // SB error
  .db_error                       (ecc_db_error_odd_hi),  // DB error
  .data_out                       (dc4_ecc_data_odd_hi)   // Syndrome
);

reg [3:0]                         dc3_ecc_valid;
reg [3:0]                         dc4_dccm_ecc_db_error_prel;
reg                               dc4_ecc_error_cg0;
reg                               dc4_dccm_ecc_replay_cg0;

wire       dmi_ecc_sb_error_lo;
wire       dmi_ecc_sb_error_hi;
wire       dmi_ecc_db_error_lo;
wire       dmi_ecc_db_error_hi;
always @*
begin : dc3_ecc_error_PROC
  // In case of a single bit error detected in X3, a dc3_dccm_ecc_replay signal gets 
  // asserted, dc4_ecc_replay_cg0 is enabled and the dc3_dccm_ecc_replay information
  // is available in dc4 as a flop (dc4_dccm_ecc_replay)
  //
  // The dc3_ecc_error is generated by receiving the ecc_error_odd/even_lo/hi
  // signals from alb_dmp_ecc_detection module and they are qualified with
  // x3_load_r or partial store(dc3_rmw_r). Since error detection is done on
  // all the data banks(even_lo, even_hi, odd_lo, odd_high), some of the banks
  // dout might be XX(since they are not accessed). Hence this is qualified with
  // dc3_bank_sel_r signal. Thus only the required banks are selected,
  // similarly the error signals
  //

  // to relax the timing on DC3 stage, the error detection is happening on individual bank basis
  //
  
  dc3_ecc_valid             =  dc3_bank_sel_r
                             & {4{dc3_ld_target_dccm}}
                             & {4{~dc3_excpn}}
                             & {4{~wa_restart_r}};

  dc4_dccm_ecc_sb_error     = (  (  {ecc_sb_error_odd_hi,  ecc_sb_error_odd_lo,
                                     ecc_sb_error_even_hi, ecc_sb_error_even_lo}
                                 )  
                               |  dc4_ecc_skid_sb_error_r)
                            ;

  dc4_dccm_ecc_db_error_prel = (  (  {ecc_db_error_odd_hi,  ecc_db_error_odd_lo,
                                     ecc_db_error_even_hi, ecc_db_error_even_lo}
                                  )
                               |  dc4_ecc_skid_db_error_r)
                            ;

  dc3_dmi_ecc_valid        =   {2{(|dmi_bank_ack_rr)}}
                             & {2{~ecc_dmp_disable}};

  dc4_dmi_ecc_db_error     = (  {dmi_ecc_db_error_hi,  dmi_ecc_db_error_lo})
                           & dc4_dmi_ecc_valid_r;

  dc4_dmi_ecc_error_cg0    =  (|dmi_bank_ack_rr);

  dc4_ecc_error_cg0        =  (   (x3_load_r | x3_store_r) 
                                & (dc3_target_r == `npuarc_DMP_TARGET_DCCM)  
                                & (|dc3_bank_sel_r)
                                & x3_pass)                              // Set
                             | (  ~(dc3_ld_target_dccm | dc3_st_target_dccm) 
                                 & (dc4_target_r == `npuarc_DMP_TARGET_DCCM) 
                                 & ca_pass)                             // Clear 
                             | wa_restart_r     
                             ;     
                                  
  // The dc4_replay_cg0 is enabled only when there is a single bit error 
  // and there is a x3_load or partial store (dc3_rmw_r) targetting DCCM.
  // This will set the replay bit.
  // After the replay, the dc3_dccm_ecc_replay should be reset. Hence
  // wa_restart_r signal is used to indicate a pipe flush and the 
  //dc3_dccm_ecc_replay is reset
  //

  dc4_dccm_ecc_replay      =   (|dc4_dccm_ecc_sb_error)
                             & (~(|dc4_dccm_ecc_db_error_prel))
                             & (~wa_restart_r)
                             & dc4_ld_target_dccm
                             ;
     
  dc4_dccm_ecc_replay_cg0  =  (  dc3_ld_target_dccm
                               & x3_pass
                              )
                            | (dc4_dccm_ecc_replay)
                            ;
end   




always @*
begin : dc4_dccm_ecc_db_error_PROC

  dc4_dccm_ecc_db_error   =   1'b0
                            | (  ~ecc_dmp_disable 
                               & (|dc4_dccm_ecc_db_error_prel))
                            ;

  dc4_dccm_ecc_excpn_r    =   1'b0
                            | (  ~ecc_dmp_disable & (~ecc_dmp_expn_disable)
                               & (|dc4_dccm_ecc_db_error_prel))
                            ;

end

always @*
begin : dc4_dmi_scrubbing_conflict_PROC
  //
  // We avoid scrubbing when there is a single bit error, and therefore
  // a ecc replay and there is a conflict with a DMI write
  //
  dc4_dmi_scrubbing_conflict = (dc4_dccm_ecc_replay) & (~scrubbing_in_progress_r);
end

reg scrubbing_set_cg0;
reg scrubbing_clr_cg0;
always @*
begin : scrubbing_set_cg0_PROC
  // Setting and Clearing of clock gate to indicate the scrubbing in progress
  //
  // SET : When there is an ecc replay due to scrubbing
  // CLR : When there is no dccm entry in WQ
  //
  scrubbing_set_cg0 = dc4_dccm_ecc_replay
                    & (~scrubbing_in_progress_r)
                    & (~wa_restart_r);

  scrubbing_clr_cg0 = scrubbing_in_progress_r 
                    & (  (ca_load_r | ca_store_r) 
                       & (  ~ca_uop_inst_r
                          | (ca_uop_inst_r & dc4_dccm_ecc_replay)))    
                    & (~wa_restart_r);
//  scrubbing_clr_cg0 = scrubbing_in_progress_r & (~wq_dc_entry);
end

always @*
begin : scrubbing_in_progress_prel_PROC
  //
  // when there is no x1,x2,x3,ca ld/st, dmi transaction can be accepted
  //
  scrubbing_in_progress_prel = scrubbing_in_progress_r
                             & (x1_load_r | x1_store_r |
                                x2_load_r | x2_store_r |  
                                x3_load_r | x3_store_r |     
                                ca_load_r | ca_store_r  );    
 
end

//`if (`DCCM_ECC == 1)
//always @*
//begin : dc4_dccm_ecc_replay_PROC
  //
  //
//  dc4_dccm_ecc_replay = ~dc4_dccm_ecc_db_error & (|dc4_dccm_ecc_replay_r);
//end
//`endif

//////////////////////////////////////////////////////////////////////////////
//                                                                           
// dc3 logic requesting the dmp result bus        
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dccm_rb_req_PROC
  // Request the result bus in dc3
  //
  dccm_rb_req      =  x3_load_r 
                    & x3_pass 
                    & ca_enable 
                    & (dc3_target_r == `npuarc_DMP_TARGET_DCCM);
  
  dccm_rb_data0_lo_r    = dc4_data_even_lo_r; // bank0_dout;
  dccm_rb_data0_hi_r    = dc4_data_even_hi_r; // bank1_dout;
  
  dccm_rb_data1_lo_r    = dc4_data_odd_lo_r;  // bank0_dout;
  dccm_rb_data1_hi_r    = dc4_data_odd_hi_r;  // bank1_dout;
end

//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Asynchronous logic for the next value of the bank busy    
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : core_bank_busy_nxt_PROC
  // Banks are set to busy for one cycle after they are accessed
  //
  core_bank0_busy_lo_nxt = core_bank0_cs_lo_nxt | dc2_keep_bank_busy[0];
 
  core_bank0_busy_hi_nxt = core_bank0_cs_hi_nxt | dc2_keep_bank_busy[1]; 
  
  core_bank1_busy_lo_nxt = core_bank1_cs_lo_nxt | dc2_keep_bank_busy[2]; 
  
  core_bank1_busy_hi_nxt = core_bank1_cs_hi_nxt | dc2_keep_bank_busy[3]; 
end

//////////////////////////////////////////////////////////////////////////////
//  Asynchronous processes that determines the enabling of dc4_data registers   
//  In case of a dc4_stall, the dc3 data is stored in dc4 data registers
//  and the dc2 data stays in the memory output      
//                                                                           
//////////////////////////////////////////////////////////////////////////////
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: some variable are not used in certain configurations
reg dc3_data_mem_valid;
// leda NTL_CON13A on

always @*
begin : dc3_data_mem_valid_PROC

  dc3_data_mem_valid       = (| dc3_data_mem_valid_r);

  // In case of DMI request, enable the dc4_data flops only when there is 
  // ca_enable.
  // 
  dc4_data_even_lo_cg0     = (  dc3_ld_target_dccm
                              & dc3_data_mem_valid_r[0]
                              & x3_pass)
                              ;
  
  dc4_data_even_hi_cg0     = (  dc3_ld_target_dccm
                              & dc3_data_mem_valid_r[1]
                              & x3_pass)
                              ;
  
  dc4_data_odd_lo_cg0      = (  dc3_ld_target_dccm
                              & dc3_data_mem_valid_r[2]
                              & x3_pass)
                              ;
 
  dc4_data_odd_hi_cg0      = (  dc3_ld_target_dccm
                              & dc3_data_mem_valid_r[3]
                              & x3_pass)
                              ;

end

//////////////////////////////////////////////////////////////////////////////
//                                                                           
// @       
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dmi_data_PROC
  dmi_data_lo_cg0 = | dmi_bank_ack_rr;
  dmi_data_lo_nxt =  dmi_bank_ack_rr[0]
                   ? dccm_bank0_dout[`npuarc_DBL_DCCM_LO_RANGE]
                   : dccm_bank1_dout[`npuarc_DBL_DCCM_LO_RANGE];
  
  dmi_data_hi_cg0 = | dmi_bank_ack_rr;
  dmi_data_hi_nxt =  dmi_bank_ack_rr[0]
                   ? dccm_bank0_dout[`npuarc_DBL_DCCM_HI_RANGE]
                   : dccm_bank1_dout[`npuarc_DBL_DCCM_HI_RANGE];
  
end

wire [`npuarc_SYNDROME_MSB:0] dmi_syndrome_lo;
wire [`npuarc_SYNDROME_MSB:0] dmi_syndrome_hi;
npuarc_alb_ecc_combined u_alb_dmp_ecc_combined_dmi_data_lo (
  .data_in                        (dmi_data_lo_r[31:0] ),  // Data bits
  .ecc_code_in                    (dmi_data_lo_r[38:32]),  // ECC  bits
  .ecc_dmp_disable                (ecc_dmp_disable       ),  // ECC Disabled
  .syndrome                       (dmi_syndrome_lo       ), // Syndrome
  .sb_error                       (dmi_ecc_sb_error_lo   ),  // SB error
  .db_error                       (dmi_ecc_db_error_lo   ),  // DB error
  .data_out                       (dmi_ecc_data_lo   )   // Syndrome
);

npuarc_alb_ecc_combined u_alb_dmp_ecc_combined_dmi_data_hi (
  .data_in                        (dmi_data_hi_r[31:0] ),  // Data bits
  .ecc_code_in                    (dmi_data_hi_r[38:32]),  // ECC  bits
  .ecc_dmp_disable                (ecc_dmp_disable       ),  // ECC Disabled
  .syndrome                       (dmi_syndrome_hi       ), // Syndrome
  .sb_error                       (dmi_ecc_sb_error_hi   ),  // SB error
  .db_error                       (dmi_ecc_db_error_hi   ),  // DB error
  .data_out                       (dmi_ecc_data_hi   )   // Syndrome
);


always @*
begin : dc4_skid_ecc_valid_cg0_PROC
  //
  //
  dc4_skid_ecc_valid_cg0 = dc3_ld_target_dccm
                         & x3_pass; 
end


//////////////////////////////////////////////////////////////////////////////
//                                                                           
// AUX instantiation         
//                                                                           
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_dccm_aux u_alb_dmp_dccm_aux (
  .clk                (clk              ),    
  .rst_a              (rst_a            ),  

  .aux_ren_r          (aux_ren_r        ),  
  .aux_wen_r          (aux_wen_r        ),  
  .aux_wdata_r        (aux_wdata_r      ),  
  
  .aux_rdata          (aux_rdata        ),  
  .aux_illegal        (aux_illegal      ),  
  .aux_k_rd           (aux_k_rd         ),  
  .aux_k_wr           (aux_k_wr         ),  
  .aux_unimpl         (aux_unimpl       ),  
  .aux_serial_sr      (aux_serial_sr    ), 
  .aux_strict_sr      (aux_strict_sr    ), 
  
  .aux_dccm_r         (aux_dccm_r       )
);


assign dc4_dmi_wr_mask_qual = (ecc_dmp_disable | dc4_dmi_wr_retry_r | (~dc4_dmi_rmw_r))
                            ? dc4_dmi_wr_mask_r
                            : 8'hFF;

assign push         = dc4_dmi_valid_r 
                    & dc4_dmi_delayed_r
                    & (~fifo_full);

assign fifo_data_in = {  dc4_dmi_valid_r,
                         dc4_dmi_read_r,
                         dc4_dmi_rmw_r,
                         dmi_rd_err_prel, 
                         dc4_dmi_wr_retry_r, 
                         dc4_dmi_wr_mask_qual,
                         dc4_dmi_rmw_data, 
                         dc4_dmi_cmd_addr_r
                      };

assign pop = fifo_valid 
           & fifo_select
           & (|dmi_bank_ack);  

///////////////////////////////////////////////////////////////////////////////
//
//                   Instantiate FIFO
//
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_shift_fifo u_alb_dmp_shift_fifo (

  .clk         (clk                 ),
  .rst_a       (rst_a               ),

  .push        (push                ),
  .pop         (pop                 ),

  .data_in     (fifo_data_in        ),

  .valid_out   (fifo_valid          ),
  .data_out    (fifo_data_out       ),

  .data0_r     (fifo_entry0_data_out),
  .data1_r     (fifo_entry1_data_out),
  .data2_r     (fifo_entry2_data_out),


  .valid_r     (fifo_entry_valid_r  ),

  .one_empty   (fifo_one_empty      ),
  .two_empty   (fifo_two_empty      ),
  .full        (fifo_full           )
);


//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Synchronous processes            
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc1_state_comb_PROC
  begin
    dc1_state_next = dc1_state_nxt;
  end
end
always @(posedge clk or posedge rst_a)
begin : dc1_state_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc1_state_r <= DC1_DEFAULT;
  end
  else
  begin
    dc1_state_r <= dc1_state_next;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc2_req_dt_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc2_dccm_addr0_r      <= {`npuarc_DCCM_ADDR_BITS{1'b0}}; 
    dc2_dccm_addr1_r      <= {`npuarc_DCCM_ADDR_BITS{1'b0}};
    dc2_bank_req_lo_r     <= 2'b00;
    dc2_bank_req_hi_r     <= 2'b00;
    dc2_bank_not_ack_r    <= 4'b0000;
  end
  else if (dc2_req_cg0)
  begin
      dc2_dccm_addr0_r      <= dc1_dccm_addr0;
      dc2_dccm_addr1_r      <= dc1_dccm_addr1;
      dc2_bank_req_lo_r     <= {dc1_bank_req_mask[2],
                                dc1_bank_req_mask[0]} ; //dc1_bank_req_lo;
      dc2_bank_req_hi_r     <= {dc1_bank_req_mask[3],
                                dc1_bank_req_mask[1]};  //dc1_bank_req_hi;
      dc2_bank_not_ack_r    <=  dc1_bank_not_ack;
  end
end

always @*
begin : dc2_state_comb_PROC
  begin
    begin
      dc2_state_next         = dc2_state_nxt;
      dc2_stuck_next         = dc2_stuck & dc2_ld_target_dccm; 
      dc2_full_ack_prev_next = dc2_target_dccm & dc2_full_ack & dc2_stuck;
    end
  end
end

always @(posedge clk or posedge rst_a)
begin : dc2_state_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc2_state_r           <= DC2_DEFAULT;
    dc2_stuck_r           <= 1'b0; 
    dc2_full_ack_prev_r   <= 1'b0;
  end
  else
  begin
    dc2_state_r           <= dc2_state_next;
    dc2_stuck_r           <= dc2_stuck_next; 
    dc2_full_ack_prev_r   <= dc2_full_ack_prev_next;
  end
end

always @*
begin : dc1_dc2_bank_common_comb_PROC
    dc1_dc2_bank_common_next = dc1_dc2_bank_common_r;
    if (dc1_dc2_bank_common_set_cg0)
    begin
      dc1_dc2_bank_common_next   = dc1_dc2_bank_common;
    end
    else if (dc1_dc2_bank_common_clr_cg0)
    begin
      dc1_dc2_bank_common_next   = 4'b0000;
    end
end

always @(posedge clk or posedge rst_a)
begin : dc1_dc2_bank_common_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc1_dc2_bank_common_r    <= 4'b0000;
  end
  else
  begin
    dc1_dc2_bank_common_r     <= dc1_dc2_bank_common_next;
  end
end

always @*
begin : dc2_data_mem_valid_comb_PROC
   dc2_data_mem_valid_next = dc2_data_mem_valid_r;
  begin
    if (dc2_data_mem_valid_cg0)
    begin
      dc2_data_mem_valid_next   = { dc1_data_bank_sel_hi[1],
                                    dc1_data_bank_sel_lo[1],
                                    dc1_data_bank_sel_hi[0],
                                    dc1_data_bank_sel_lo[0]};
    end  
  end
end

always @(posedge clk or posedge rst_a)
begin : dc2_data_mem_valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc2_data_mem_valid_r <= 4'b0000;
  end
  else
  begin
    dc2_data_mem_valid_r     <= dc2_data_mem_valid_next;
  end
end

always @*
begin : dc3_data_mem_valid_comb_PROC
   dc3_data_mem_valid_next = dc3_data_mem_valid_r;
  begin
    if (dc3_data_mem_valid_cg0)
    begin
      dc3_data_mem_valid_next  = dc2_data_mem_valid_r; 
    end
  end
end

always @(posedge clk or posedge rst_a)
begin : dc3_data_mem_valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_data_mem_valid_r    <= 4'b0000;
  end
  else
  begin
    dc3_data_mem_valid_r    <= dc3_data_mem_valid_next; 
  end
end

always @(posedge clk or posedge rst_a)
begin : dc4_ecc_data_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_ecc_valid_r           <= 4'd0;
  end
  else if (dc4_ecc_error_cg0)
  begin
    dc4_ecc_valid_r         <= dc3_ecc_valid;
  end   
end

always @(posedge clk or posedge rst_a)
begin : dc4_dmi_ecc_valid_reg_PROC 
  if (rst_a == 1'b1)
  begin
    dc4_dmi_ecc_valid_r    <= 2'b00;
  end
  else if (dc4_dmi_ecc_error_cg0)
  begin
    dc4_dmi_ecc_valid_r  <= dc3_dmi_ecc_valid;
  end
end  
  
always @*
begin  : scrubbing_to_this_bank_comb_PROC
  scrubbing_in_progress_next = scrubbing_in_progress_r;
  begin
    if (scrubbing_set_cg0)
    begin
      scrubbing_in_progress_next = 1'b1;
    end
    else if (scrubbing_clr_cg0)
    begin
      scrubbing_in_progress_next = 1'b0;
    end
  end
end  
always @(posedge clk or posedge rst_a)
begin  : scrubbing_to_this_bank_reg_PROC
  if (rst_a == 1'b1)
  begin
    scrubbing_in_progress_r   <= 1'b0;
  end
  else
  begin
    scrubbing_in_progress_r <= scrubbing_in_progress_next;
  end
end  

always @*
begin : dc4_data_comb_PROC
    dc4_data_even_lo_nxt = dc4_data_even_lo_r;
    dc4_data_even_hi_nxt = dc4_data_even_hi_r;
    dc4_data_odd_lo_nxt  = dc4_data_odd_lo_r;
    dc4_data_odd_hi_nxt  = dc4_data_odd_hi_r;
      i_parity_0_nxt      = i_parity_0_r;
      syndrome_0_nxt      = syndrome_0_r;
      i_parity_1_nxt      = i_parity_1_r;
      syndrome_1_nxt      = syndrome_1_r;
      i_parity_2_nxt      = i_parity_2_r;
      syndrome_2_nxt      = syndrome_2_r;
      i_parity_3_nxt      = i_parity_3_r;
      syndrome_3_nxt      = syndrome_3_r;
    if (dc4_data_even_lo_cg0)
    begin
      dc4_data_even_lo_nxt  = dc3_dccm_data_even_lo;
      i_parity_0_nxt      = i_parity_0;
      syndrome_0_nxt      = syndrome_0;
    end
    
    if (dc4_data_even_hi_cg0)
    begin
      dc4_data_even_hi_nxt= dc3_dccm_data_even_hi;
      i_parity_1_nxt      = i_parity_1;
      syndrome_1_nxt      = syndrome_1;
    end

    if (dc4_data_odd_lo_cg0)
    begin
      dc4_data_odd_lo_nxt = dc3_dccm_data_odd_lo;
      i_parity_2_nxt      = i_parity_2;
      syndrome_2_nxt      = syndrome_2;
    end

    if (dc4_data_odd_hi_cg0)
    begin
      dc4_data_odd_hi_nxt = dc3_dccm_data_odd_hi;
      i_parity_3_nxt      = i_parity_3;
      syndrome_3_nxt      = syndrome_3;
    end
end

always @(posedge clk or posedge rst_a)
begin : dc4_data_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_data_even_lo_r <= {`npuarc_DBL_DCCM_LO_SIZE{1'b0}};
    dc4_data_even_hi_r <= {`npuarc_DBL_DCCM_LO_SIZE{1'b0}};
    dc4_data_odd_lo_r  <= {`npuarc_DBL_DCCM_LO_SIZE{1'b0}};
    dc4_data_odd_hi_r  <= {`npuarc_DBL_DCCM_LO_SIZE{1'b0}};
    i_parity_0_r       <= 1'b0;
    i_parity_1_r       <= 1'b0;
    i_parity_2_r       <= 1'b0;
    i_parity_3_r       <= 1'b0;
    
    syndrome_0_r       <= 6'd0; 
    syndrome_1_r       <= 6'd0; 
    syndrome_2_r       <= 6'd0; 
    syndrome_3_r       <= 6'd0; 
  end
  else
  begin
      dc4_data_even_lo_r <= dc4_data_even_lo_nxt;
      dc4_data_even_hi_r <= dc4_data_even_hi_nxt;
      dc4_data_odd_lo_r  <= dc4_data_odd_lo_nxt;
      dc4_data_odd_hi_r  <= dc4_data_odd_hi_nxt;
      i_parity_0_r       <= i_parity_0_nxt;
      syndrome_0_r       <= syndrome_0_nxt;
      i_parity_1_r       <= i_parity_1_nxt;
      syndrome_1_r       <= syndrome_1_nxt;
      i_parity_2_r       <= i_parity_2_nxt;
      syndrome_2_r       <= syndrome_2_nxt;
      i_parity_3_r       <= i_parity_3_nxt;
      syndrome_3_r       <= syndrome_3_nxt;
  end
end

always @*
begin : dmi_bank_ack_comb_PROC
    dmi_bank_ack_r_nxt   = dmi_bank_ack_r    ;
    dmi_bank_ack_rr_nxt  = dmi_bank_ack_rr   ;
    dmi_bank_ack_rrr_nxt = dmi_bank_ack_rrr  ;
  begin
    if (dmi_cg0[0])
    begin
      dmi_bank_ack_r_nxt[0]   = dmi_bank_ack[0] & dc1_dmi_read;
    end
   
    if (dmi_ack_cg0[0])
    begin
      dmi_bank_ack_rr_nxt[0]  = dmi_bank_ack_r[0];
    end
    
    if (dmi_rd_valid_cg0[0])
    begin
      dmi_bank_ack_rrr_nxt[0] = dmi_bank_ack_rr[0];
    end   
    if (dmi_cg0[1])
    begin
      dmi_bank_ack_r_nxt[1]   = dmi_bank_ack[1] & dc1_dmi_read;
    end
   
    if (dmi_ack_cg0[1])
    begin
      dmi_bank_ack_rr_nxt[1]  = dmi_bank_ack_r[1];
    end
    
    if (dmi_rd_valid_cg0[1])
    begin
      dmi_bank_ack_rrr_nxt[1] = dmi_bank_ack_rr[1];
    end   
  end
end 

always @(posedge clk or posedge rst_a)
begin : dmi_bank_ack_reg_PROC
  if (rst_a == 1'b1)
  begin
    dmi_bank_ack_r      <= 2'b00;
    dmi_bank_ack_rr     <= 2'b00;
    dmi_bank_ack_rrr    <= 2'b00;
  end
  else
  begin
    dmi_bank_ack_r     <= dmi_bank_ack_r_nxt   ;
    dmi_bank_ack_rr    <= dmi_bank_ack_rr_nxt  ;
    dmi_bank_ack_rrr   <= dmi_bank_ack_rrr_nxt ;
  end
end 




// leda NTL_RST03 off
// leda S_1C_R off
// LMD: A flipflop without reset
// LJ:  Datapath element, doesn't require reset
//
// leda G_551_1_K off
// LMD: There should be at most one synchronous reset/set/load signal in a sequential block
// LJ:  Each register is loaded once, with an independent enable
//  
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk)
begin : dmi_data_reg_PROC
  if (dmi_data_lo_cg0 == 1'b1)
  begin
    dmi_data_lo_r <= dmi_data_lo_nxt;
  end
  
  if (dmi_data_hi_cg0 == 1'b1)
  begin
    dmi_data_hi_r <= dmi_data_hi_nxt;
  end
end
// leda G_551_1_K on
// leda S_1C_R on
// leda NTL_RST03 on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

reg   dmi_wr_done_nxt;
reg   dmi_err_wr_nxt;
always @*
begin : dmi_wr_done_comb_PROC
  begin
    dmi_wr_done_nxt = dmi_wr_done;
    dmi_err_wr_nxt  = dmi_err_wr;
  end
end  
    
always @(posedge clk or posedge rst_a)
begin : dmi_wr_done_reg_PROC
  if (rst_a == 1'b1)
  begin
    dmi_wr_done_r  <= 1'b0;
    dmi_err_wr_r   <= 1'b0;
  end
  else
  begin
    dmi_wr_done_r  <= dmi_wr_done_nxt;
    dmi_err_wr_r   <= dmi_err_wr_nxt;
  end
end  
    
  
always @*
begin : core_bank_interface_comb_PROC
    core_bank0_cs_lo_next  = core_bank0_cs_lo_r;
    core_bank0_we_lo_next  = core_bank0_we_lo_r;
    core_bank0_cs_hi_next  = core_bank0_cs_hi_r;
    core_bank0_we_hi_next  = core_bank0_we_hi_r;
    core_bank0_addr_lo_next= core_bank0_addr_lo_r;
    core_bank0_addr_hi_next= core_bank0_addr_hi_r;
    core_bank0_din_next    = core_bank0_din_r;
    core_bank0_wem_next    = core_bank0_wem_r;


    if (dccm_bank_cs_lo_cg0[0])
    begin
      core_bank0_cs_lo_next  = core_bank0_cs_lo_nxt; 
      core_bank0_we_lo_next  = core_bank0_we_lo_nxt; 
    end
    
    if (dccm_bank_cs_hi_cg0[0])
    begin
      core_bank0_cs_hi_next  = core_bank0_cs_hi_nxt;   
      core_bank0_we_hi_next  = core_bank0_we_hi_nxt; 
    end
    
    if (dccm_bank_addr_lo_cg0[0])
    begin
      core_bank0_addr_lo_next = core_bank0_addr_lo_nxt;
    end

    if (dccm_bank_addr_hi_cg0[0])
    begin
      core_bank0_addr_hi_next = core_bank0_addr_hi_nxt;
    end

    if (dccm_bank_data_lo_cg0[0])
    begin
      core_bank0_din_next[`npuarc_DBL_DCCM_LO_RANGE]    = core_bank0_din_nxt[`npuarc_DBL_DCCM_LO_RANGE];
      core_bank0_wem_next[`npuarc_DBL_DCCM_BE_LO_RANGE] = core_bank0_wem_nxt[`npuarc_DBL_DCCM_BE_LO_RANGE]; 
    end
    
    if (dccm_bank_data_hi_cg0[0])
    begin
      core_bank0_din_next[`npuarc_DBL_DCCM_HI_RANGE]    = core_bank0_din_nxt[`npuarc_DBL_DCCM_HI_RANGE];
      core_bank0_wem_next[`npuarc_DBL_DCCM_BE_HI_RANGE] = core_bank0_wem_nxt[`npuarc_DBL_DCCM_BE_HI_RANGE]; 
    end
    
    core_bank1_cs_lo_next  = core_bank1_cs_lo_r;
    core_bank1_we_lo_next  = core_bank1_we_lo_r;
    core_bank1_cs_hi_next  = core_bank1_cs_hi_r;
    core_bank1_we_hi_next  = core_bank1_we_hi_r;
    core_bank1_addr_lo_next= core_bank1_addr_lo_r;
    core_bank1_addr_hi_next= core_bank1_addr_hi_r;
    core_bank1_din_next    = core_bank1_din_r;
    core_bank1_wem_next    = core_bank1_wem_r;


    if (dccm_bank_cs_lo_cg0[1])
    begin
      core_bank1_cs_lo_next  = core_bank1_cs_lo_nxt; 
      core_bank1_we_lo_next  = core_bank1_we_lo_nxt; 
    end
    
    if (dccm_bank_cs_hi_cg0[1])
    begin
      core_bank1_cs_hi_next  = core_bank1_cs_hi_nxt;   
      core_bank1_we_hi_next  = core_bank1_we_hi_nxt; 
    end
    
    if (dccm_bank_addr_lo_cg0[1])
    begin
      core_bank1_addr_lo_next = core_bank1_addr_lo_nxt;
    end

    if (dccm_bank_addr_hi_cg0[1])
    begin
      core_bank1_addr_hi_next = core_bank1_addr_hi_nxt;
    end

    if (dccm_bank_data_lo_cg0[1])
    begin
      core_bank1_din_next[`npuarc_DBL_DCCM_LO_RANGE]    = core_bank1_din_nxt[`npuarc_DBL_DCCM_LO_RANGE];
      core_bank1_wem_next[`npuarc_DBL_DCCM_BE_LO_RANGE] = core_bank1_wem_nxt[`npuarc_DBL_DCCM_BE_LO_RANGE]; 
    end
    
    if (dccm_bank_data_hi_cg0[1])
    begin
      core_bank1_din_next[`npuarc_DBL_DCCM_HI_RANGE]    = core_bank1_din_nxt[`npuarc_DBL_DCCM_HI_RANGE];
      core_bank1_wem_next[`npuarc_DBL_DCCM_BE_HI_RANGE] = core_bank1_wem_nxt[`npuarc_DBL_DCCM_BE_HI_RANGE]; 
    end
    
end
always @(posedge clk or posedge rst_a)
begin : core_bank_interface_reg_PROC
  if (rst_a == 1'b1)
  begin
    core_bank0_cs_lo_r    <= 1'b0;  
    core_bank0_cs_hi_r    <= 1'b0;  
    core_bank0_addr_lo_r  <= `npuarc_DCCM_ADDR_BITS'd0;
    core_bank0_addr_hi_r  <= `npuarc_DCCM_ADDR_BITS'd0;
    core_bank0_we_lo_r    <= 1'b0;
    core_bank0_we_hi_r    <= 1'b0;
    core_bank0_wem_r      <= `npuarc_DBL_DCCM_BE_SIZE'd0; 
    core_bank0_din_r      <= `npuarc_DBL_DCCM_SIZE'd0;
    core_bank1_cs_lo_r    <= 1'b0;  
    core_bank1_cs_hi_r    <= 1'b0;  
    core_bank1_addr_lo_r  <= `npuarc_DCCM_ADDR_BITS'd0;
    core_bank1_addr_hi_r  <= `npuarc_DCCM_ADDR_BITS'd0;
    core_bank1_we_lo_r    <= 1'b0;
    core_bank1_we_hi_r    <= 1'b0;
    core_bank1_wem_r      <= `npuarc_DBL_DCCM_BE_SIZE'd0; 
    core_bank1_din_r      <= `npuarc_DBL_DCCM_SIZE'd0;
  end
  else
  begin
      core_bank0_cs_lo_r    <= core_bank0_cs_lo_next; 
      core_bank0_we_lo_r    <= core_bank0_we_lo_next; 
      core_bank0_cs_hi_r    <= core_bank0_cs_hi_next;   
      core_bank0_we_hi_r    <= core_bank0_we_hi_next; 
      core_bank0_addr_lo_r  <= core_bank0_addr_lo_next;
      core_bank0_addr_hi_r  <= core_bank0_addr_hi_next;

      core_bank0_din_r  <= core_bank0_din_next;
      core_bank0_wem_r  <= core_bank0_wem_next; 
      core_bank1_cs_lo_r    <= core_bank1_cs_lo_next; 
      core_bank1_we_lo_r    <= core_bank1_we_lo_next; 
      core_bank1_cs_hi_r    <= core_bank1_cs_hi_next;   
      core_bank1_we_hi_r    <= core_bank1_we_hi_next; 
      core_bank1_addr_lo_r  <= core_bank1_addr_lo_next;
      core_bank1_addr_hi_r  <= core_bank1_addr_hi_next;

      core_bank1_din_r  <= core_bank1_din_next;
      core_bank1_wem_r  <= core_bank1_wem_next; 
  end
end
// spyglass enable_block W193


always @ (posedge clk or posedge rst_a)
begin : dc4_skid_ecc_valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_skid_ecc_valid_r   <= 4'b0000; 
  end
  else if (dc4_skid_ecc_valid_cg0)
  begin
    dc4_skid_ecc_valid_r <= dc3_skid_ecc_valid;
  end
end

always @* 
begin : dc2_dmi_valid_comb_PROC
    dc2_dmi_valid_next     = dc2_dmi_valid_r     ;
    dc2_dmi_read_next      = dc2_dmi_read_r      ;
    dc2_dmi_delayed_next   = dc2_dmi_delayed_r   ;
    dc2_dmi_wr_retry_next  = dc2_dmi_wr_retry_r  ;
    dc2_dmi_rmw_next       = dc2_dmi_rmw_r       ;
    dc2_dmi_wr_mask_next   = dc2_dmi_wr_mask_r   ;
    dc2_dmi_cmd_addr_next  = dc2_dmi_cmd_addr_r  ;
    dc2_dmi_wr_data_next   = dc2_dmi_wr_data_r   ;
  begin
     if (dc2_dmi_cg0)
     begin 
      dc2_dmi_valid_next   = (pop & fifo_data_out[84])
                           ? fifo_data_out[88]
                           : (dmi_cmd_valid_r & dmi_cmd_accept & dc2_dmi_delayed_nxt);
      dc2_dmi_read_next    = (pop & fifo_data_out[84])
                           ? fifo_data_out[87]
                           : (dmi_cmd_valid_r & dmi_cmd_accept & dmi_cmd_read_r);
      dc2_dmi_delayed_next = (pop & fifo_data_out[84])
                           ? fifo_data_out[84]
                           : (dmi_cmd_valid_r & dmi_cmd_accept & dc2_dmi_delayed_nxt); 
      dc2_dmi_wr_retry_next= (pop & fifo_data_out[84])
                           ? 1'b0
                           : (dmi_cmd_valid_r & dmi_cmd_accept & dc2_dmi_wr_retry_nxt);
      dc2_dmi_rmw_next     = (pop & fifo_data_out[84])
                           ? fifo_data_out[86] 
                           : (dmi_cmd_valid_r & dmi_wr_accept & (~dmi_full_mask));
      dc2_dmi_wr_mask_next = (pop & fifo_data_out[84])
                           ? fifo_data_out[83:76]
                           : dmi_wr_mask;  
      dc2_dmi_cmd_addr_next= (pop & fifo_data_out[84])
                           ? fifo_data_out[11:0] 
                           : dmi_cmd_addr_r[`npuarc_DCCM_DWRD_MSB:3];
      dc2_dmi_wr_data_next = (pop & fifo_data_out[84])
                           ? fifo_data_out[75:12]
                           : dmi_wr_data;
    end
  end
end

always @ (posedge clk or posedge rst_a)
begin : dc2_dmi_valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc2_dmi_valid_r     <= 1'b0;
    dc2_dmi_read_r      <= 1'b0;
    dc2_dmi_delayed_r   <= 1'b0;
    dc2_dmi_wr_retry_r  <= 1'b0;
    dc2_dmi_rmw_r       <= 1'b0;
    dc2_dmi_wr_mask_r   <= {`npuarc_DOUBLE_BE_SIZE{1'b0}};  
    dc2_dmi_cmd_addr_r  <= {12{1'b0}};
    dc2_dmi_wr_data_r   <= {`npuarc_DOUBLE_SIZE{1'b0}};
  end
  else 
  begin
    dc2_dmi_valid_r     <= dc2_dmi_valid_next     ;
    dc2_dmi_read_r      <= dc2_dmi_read_next      ;
    dc2_dmi_delayed_r   <= dc2_dmi_delayed_next   ;
    dc2_dmi_wr_retry_r  <= dc2_dmi_wr_retry_next  ;
    dc2_dmi_rmw_r       <= dc2_dmi_rmw_next       ;
    dc2_dmi_wr_mask_r   <= dc2_dmi_wr_mask_next   ;
    dc2_dmi_cmd_addr_r  <= dc2_dmi_cmd_addr_next  ;
    dc2_dmi_wr_data_r   <= dc2_dmi_wr_data_next   ;
  end
end

always @* 
begin : dc3_dmi_valid_comb_PROC
    dc3_dmi_valid_nxt      = dc3_dmi_valid_r     ;
    dc3_dmi_read_nxt       = dc3_dmi_read_r      ;
    dc3_dmi_delayed_nxt    = dc3_dmi_delayed_r   ;
    dc3_dmi_wr_retry_nxt   = dc3_dmi_wr_retry_r  ;
    dc3_dmi_rmw_nxt        = dc3_dmi_rmw_r       ;
    dc3_dmi_wr_mask_nxt    = dc3_dmi_wr_mask_r   ;
    dc3_dmi_cmd_addr_nxt   = dc3_dmi_cmd_addr_r  ;
    dc3_dmi_wr_data_nxt    = dc3_dmi_wr_data_r   ;
  begin
    if (dc3_dmi_cg0)
    begin 
      dc3_dmi_valid_nxt     = dc2_dmi_valid_r;   
      dc3_dmi_read_nxt      = dc2_dmi_read_r;
      dc3_dmi_delayed_nxt   = dc2_dmi_delayed_r; 
      dc3_dmi_wr_retry_nxt  = dc2_dmi_wr_retry_r; 
      dc3_dmi_rmw_nxt       = dc2_dmi_rmw_r;
      dc3_dmi_wr_mask_nxt   = dc2_dmi_wr_mask_r;
      dc3_dmi_cmd_addr_nxt  = dc2_dmi_cmd_addr_r;
      dc3_dmi_wr_data_nxt   = dc2_dmi_wr_data_r;
    end
  end
end

always @ (posedge clk or posedge rst_a)
begin : dc3_dmi_valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_dmi_valid_r     <= 1'b0;
    dc3_dmi_read_r      <= 1'b0;
    dc3_dmi_delayed_r   <= 1'b0;
    dc3_dmi_wr_retry_r  <= 1'b0;
    dc3_dmi_rmw_r       <= 1'b0;
    dc3_dmi_wr_mask_r   <= {`npuarc_DOUBLE_BE_SIZE{1'b0}};
    dc3_dmi_cmd_addr_r  <= {12{1'b0}};
    dc3_dmi_wr_data_r   <= {`npuarc_DOUBLE_SIZE{1'b0}};
  end
  else 
  begin
    dc3_dmi_valid_r     <= dc3_dmi_valid_nxt     ;
    dc3_dmi_read_r      <= dc3_dmi_read_nxt      ;
    dc3_dmi_delayed_r   <= dc3_dmi_delayed_nxt   ;
    dc3_dmi_wr_retry_r  <= dc3_dmi_wr_retry_nxt  ;
    dc3_dmi_rmw_r       <= dc3_dmi_rmw_nxt       ;
    dc3_dmi_wr_mask_r   <= dc3_dmi_wr_mask_nxt   ;
    dc3_dmi_cmd_addr_r  <= dc3_dmi_cmd_addr_nxt  ;
    dc3_dmi_wr_data_r   <= dc3_dmi_wr_data_nxt   ;
  end
end

always @* 
begin : dc4_dmi_valid_comb_PROC
    dc4_dmi_valid_nxt        = dc4_dmi_valid_r     ;
    dc4_dmi_read_nxt         = dc4_dmi_read_r      ;
    dc4_dmi_delayed_nxt      = dc4_dmi_delayed_r   ;
    dc4_dmi_wr_retry_nxt     = dc4_dmi_wr_retry_r  ;
    dc4_dmi_rmw_nxt          = dc4_dmi_rmw_r       ;
    dc4_dmi_wr_mask_nxt      = dc4_dmi_wr_mask_r   ;
    dc4_dmi_cmd_addr_nxt     = dc4_dmi_cmd_addr_r  ;
    dc4_dmi_wr_data_nxt      = dc4_dmi_wr_data_r   ;
  begin
    if (dc4_dmi_cg0)
    begin 
      dc4_dmi_valid_nxt        = dc3_dmi_valid_r;
      dc4_dmi_read_nxt         = dc3_dmi_read_r;
      dc4_dmi_delayed_nxt      = dc3_dmi_delayed_r; 
      dc4_dmi_wr_retry_nxt     = dc3_dmi_wr_retry_r; 
      dc4_dmi_rmw_nxt          = dc3_dmi_rmw_r; 
      dc4_dmi_wr_mask_nxt      = dc3_dmi_wr_mask_r;
      dc4_dmi_cmd_addr_nxt     = dc3_dmi_cmd_addr_r;
      dc4_dmi_wr_data_nxt      = dc3_dmi_wr_data_r;
    end
  end
end
always @ (posedge clk or posedge rst_a)
begin : dc4_dmi_valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_dmi_valid_r     <= 1'b0;
    dc4_dmi_read_r      <= 1'b0;
    dc4_dmi_delayed_r   <= 1'b0;
    dc4_dmi_wr_retry_r  <= 1'b0;
    dc4_dmi_rmw_r       <= 1'b0;
    dc4_dmi_wr_mask_r   <= {`npuarc_DOUBLE_BE_SIZE{1'b0}};
    dc4_dmi_cmd_addr_r  <= {12{1'b0}};
    dc4_dmi_wr_data_r   <= {`npuarc_DOUBLE_SIZE{1'b0}};
  end
  else 
  begin
    dc4_dmi_valid_r     <= dc4_dmi_valid_nxt        ;
    dc4_dmi_read_r      <= dc4_dmi_read_nxt         ;
    dc4_dmi_delayed_r   <= dc4_dmi_delayed_nxt      ;
    dc4_dmi_wr_retry_r  <= dc4_dmi_wr_retry_nxt     ;
    dc4_dmi_rmw_r       <= dc4_dmi_rmw_nxt          ;
    dc4_dmi_wr_mask_r   <= dc4_dmi_wr_mask_nxt      ;
    dc4_dmi_cmd_addr_r  <= dc4_dmi_cmd_addr_nxt     ;
    dc4_dmi_wr_data_r   <= dc4_dmi_wr_data_nxt      ;
  end
end

//`if (`HAS_SAFETY == 1) // {

always @ (posedge clk or posedge rst_a)
begin : dccm_syndrome_reg_PROC
  if (rst_a == 1'b1)
  begin
    fs_dccm_bank0_syndrome_r <= {`npuarc_SYNDROME_MSB+1{1'b0}};
    fs_dccm_bank1_syndrome_r <= {`npuarc_SYNDROME_MSB+1{1'b0}};
    fs_dccm_bank2_syndrome_r <= {`npuarc_SYNDROME_MSB+1{1'b0}};
    fs_dccm_bank3_syndrome_r <= {`npuarc_SYNDROME_MSB+1{1'b0}};
  end
  else
  begin
    fs_dccm_bank0_syndrome_r <= dc4_ecc_skid_sb_error_r[0] ? dc_skid_bank0_syndrome_r : syndrome_0_r;
    fs_dccm_bank1_syndrome_r <= dc4_ecc_skid_sb_error_r[1] ? dc_skid_bank1_syndrome_r : syndrome_1_r;
    fs_dccm_bank2_syndrome_r <= dc4_ecc_skid_sb_error_r[2] ? dc_skid_bank2_syndrome_r : syndrome_2_r;
    fs_dccm_bank3_syndrome_r <= dc4_ecc_skid_sb_error_r[3] ? dc_skid_bank3_syndrome_r : syndrome_3_r;
  end  
end

always @ (posedge clk or posedge rst_a)
begin : fs_dccm_bank0_ecc_sb_error_reg_PROC
  if (rst_a == 1'b1)
  begin
    fs_dccm_bank0_ecc_sb_error_r  <= 1'b0; 
    fs_dccm_bank1_ecc_sb_error_r  <= 1'b0; 
    fs_dccm_bank2_ecc_sb_error_r  <= 1'b0; 
    fs_dccm_bank3_ecc_sb_error_r  <= 1'b0; 
  end
  else
  begin
    fs_dccm_bank0_ecc_sb_error_r  <= dc4_dccm_ecc_sb_error[0];
    fs_dccm_bank1_ecc_sb_error_r  <= dc4_dccm_ecc_sb_error[1];
    fs_dccm_bank2_ecc_sb_error_r  <= dc4_dccm_ecc_sb_error[2];
    fs_dccm_bank3_ecc_sb_error_r  <= dc4_dccm_ecc_sb_error[3];
  end
end

always @ (posedge clk or posedge rst_a)
begin : fs_dccm_bank0_ecc_db_error_reg_PROC
  if (rst_a == 1'b1)
  begin
    fs_dccm_bank0_ecc_db_error_r  <= 1'b0;
    fs_dccm_bank1_ecc_db_error_r  <= 1'b0;
    fs_dccm_bank2_ecc_db_error_r  <= 1'b0;
    fs_dccm_bank3_ecc_db_error_r  <= 1'b0;
  end
  else
  begin
    fs_dccm_bank0_ecc_db_error_r  <= dc4_dccm_ecc_db_error_prel[0];
    fs_dccm_bank1_ecc_db_error_r  <= dc4_dccm_ecc_db_error_prel[1];
    fs_dccm_bank2_ecc_db_error_r  <= dc4_dccm_ecc_db_error_prel[2];
    fs_dccm_bank3_ecc_db_error_r  <= dc4_dccm_ecc_db_error_prel[3];
  end
end

//`endif               // }
endmodule // alb_dmp_dccm
