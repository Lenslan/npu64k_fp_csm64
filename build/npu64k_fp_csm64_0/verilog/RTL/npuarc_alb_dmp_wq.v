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
//   ALB_DMP_WQ                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  Store instructions enter the write queue when they pass the commit point. 
//  As such, all instructions in the write queue are already commited.
//  The store instructions entering the queue contain an identifier: dmp_wq_target
//  This is used to retire the store from the queue to either the DCCM, ICCM, ext.
//  memory, or dcache. Store instructions are retired in the same order they
//  have committed. 
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_wq.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"



//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

//D: error_signal { name: "alb_dmp_wq_fifo_edc_err" }

module npuarc_alb_dmp_wq (
// leda NTL_CON37 off
// leda NTL_CON13C off
// LMD: non driving port
// LJ: some inputs are not used in certain configurations
  ////////// General input signals ///////////////////////////////////////////
  //
  input                         clk,                 // clock
  input                         rst_a,               // reset

  input                         holdup_excpn_r,
  output                        st_instrs_discarded,
  input                         st_instrs_discarded_r,
  input                         ecc_dmp_disable,     // ECC disable

  ////////// Interface to the SA stage //////////////////////////////////////
  //
  input                         sa_dsync_op_r,        // SA is a DSYNC insn.
  input                         sa_dmb_op_r,          // SA is a DMB insn.
  input                         sa_dmb_stall,         // SA stall due to DMB

  input  [`npuarc_ADDR_RANGE]          x2_mem_addr0_r,
  input                         x2_load_r,
  input  [1:0]                  x2_size_r,            
  input                         x2_pass,
  input  [3:0]                  dc2_rmw_r,
  input  [3:0]                  dc2_data_bank_sel_r,   
  input  [`npuarc_ADDR_RANGE]          dc2_mem_addr1_r,          
  ////////// Interface to the X2 //////////////////////////////////////////
  //
  input                         dc2_dc_uop_stall,    // X2 uop stall

  ////////// Interface to the X3 //////////////////////////////////////////
  //
  input                         x3_pass,             // X3 pass
  input                         x3_load_r,           // X3 load  
  input                         x3_store_r,          // X3 store
  input                         x3_store_may_grad,   //  
  input  [`npuarc_PADDR_RANGE]         x3_mem_addr0_r,      // X3 memory address
  input  [`npuarc_PADDR_RANGE]         x3_mem_addr1_r,      // X3 memory address
  input                         x3_uop_inst_r,
  output                        dmp_dc3_stall_r,
  output                        dc3_partial_or_multi_conflict,
  input                         x3_sync_op_r,
  input                         x3_brk_op_r,
  input  [2:0]                  dc3_size0_r,         // DC3 aln size for ld0
  input  [2:0]                  dc3_size1_r,         // DC3 aln size for ld1
  input  [3:0]                  dc3_bank_sel_r,      // DC3 bank info for load
  input  [`npuarc_DMP_TARGET_RANGE]    dc3_target_r,        // DC3 target
  input                         dc3_dt_any_hit,
  input  [3:0]                  dc3_rmw_r,
  input                         dc3_fwd_allowed_r,    // uncached st->ld fwd
  
  output                        wq_fwd_replay,
  output  [3:0]                 wq_fwd_bank,
  output  [`npuarc_DATA_RANGE]         wq_fwd_data_bank0_lo,
  output  [`npuarc_DATA_RANGE]         wq_fwd_data_bank0_hi,
  output  [`npuarc_DATA_RANGE]         wq_fwd_data_bank1_lo,
  output  [`npuarc_DATA_RANGE]         wq_fwd_data_bank1_hi,
  
  output [15:0]                 wq_skid_ctrl_mask,  // mux control to skid buff
  
  ////////// Interface to the DC4 (commit stage) ////////////////////////////
  //
  input                         db_active_r,         // CA debug active
  input                         db_exception_r,      // CA signal
  
  input                         ca_enable,           // CA enable
  input                         ca_pass_prel,        // CA passing on inst
  input                         ca_store_r,          // CA store  
  input                         ca_load_r,           // CA load 
  input                         ca_locked_r,         // CA LLOCK/SCOND
  input                         ca_scond_go,         // CA scond proceed
  input [`npuarc_GRAD_TAG_RANGE]       ca_grad_tag,         // CA grad tag 
  input [1:0]                   ca_size_r,           // 00-b, 01-h, 10-w, 11-dw
  input                         ca_user_mode_r,      // CA user mode
  input                         ca_cache_byp_r,      // CA cache byp  
  input [`npuarc_PADDR_RANGE]          ca_mem_addr0_r,      // CA memory address
  input [`npuarc_DMP_DATA_RANGE]       ca_wr_data_r,        // CA write data
  input [1:0]                   ca_store_grad_r,     // CA store graduates
  input [1:0]                   ca_store_grad_swap_r,// CA store data comes from // hi to lo, lo to hi
  input [`npuarc_GRAD_TAG_RANGE]       ca_store_grad_tag_lo_r, // CA store tag
  input [`npuarc_GRAD_TAG_RANGE]       ca_store_grad_tag_hi_r, // CA store tag
  
  input                         dc4_grad_req,        // DC4 graduation
  input [2:0]                   dc4_size0_r,         // DC4 aligned size0
  input [2:0]                   dc4_size1_r,         // DC4 size of l/s + size
  input [`npuarc_PADDR_RANGE]          dc4_mem_addr1_r,     // DC4 addr + size
  input [`npuarc_DMP_TARGET_RANGE]     dc4_target_r,        // DC4 memory target
  input                         dc4_volatile_r,      // DC4 volatile region
  input                         dc4_strict_order_r,  // DC4 strict order 
  input                         dc4_data_mem_attr_r, // DC4 bufferable bit
  input [1:0]                   dc4_data_bank_sel_lo_r,  //
  input [1:0]                   dc4_data_bank_sel_hi_r,  //
  input [3:0]                   dc4_rmw_r,           // dc4_ read modify write              
  input [`npuarc_DBL_DCCM_LO_RANGE]    dc4_data_even_lo_r,              // dc4_data
  input [`npuarc_DBL_DCCM_LO_RANGE]    dc4_data_even_hi_r,              // dc4_data
  input [`npuarc_DBL_DCCM_LO_RANGE]    dc4_data_odd_lo_r,               // dc4_data
  input [`npuarc_DBL_DCCM_LO_RANGE]    dc4_data_odd_hi_r,               // dc4_data
  input [3:0]                   dc4_dccm_ecc_sb_error_r,         // 1bit Error
  input [3:0]                   dc4_ecc_skid_sb_error_r,
  input                         dc4_dccm_ecc_db_error_r,         // 2bit Error
  input                         dc4_dmi_scrubbing_conflict,      // conflict with DMI 
  input [`npuarc_DATA_RANGE]           dc4_ecc_data_even_lo,            // dc4 ecc corrected data
  input [`npuarc_DATA_RANGE]           dc4_ecc_data_even_hi,            // dc4 ecc corrected data
  input [`npuarc_DATA_RANGE]           dc4_ecc_data_odd_lo,             // dc4 ecc corrected data
  input [`npuarc_DATA_RANGE]           dc4_ecc_data_odd_hi,             // dc4 ecc corrected data
  input [`npuarc_DC_WAY_DATA_ECC_RANGE]  dc4_dd_data_even_lo_r,        // dc4_dd_data
  input [`npuarc_DC_WAY_DATA_ECC_RANGE]  dc4_dd_data_even_hi_r,        // dc4_dd_data
  input [`npuarc_DC_WAY_DATA_ECC_RANGE]  dc4_dd_data_odd_lo_r,         // dc4_dd_data
  input [`npuarc_DC_WAY_DATA_ECC_RANGE]  dc4_dd_data_odd_hi_r,         // dc4_dd_data
  input [3:0]                   wq_fwd_bank_r,                   // WQ_fwd_bank
  input [`npuarc_DATA_RANGE]           wq_fwd_data_bank0_lo_r,          // WQ fwd bank0 lo
  input [`npuarc_DATA_RANGE]           wq_fwd_data_bank0_hi_r,          // WQ fwd bank0 hi
  input [`npuarc_DATA_RANGE]           wq_fwd_data_bank1_lo_r,          // WQ fwd bank1 lo
  input [`npuarc_DATA_RANGE]           wq_fwd_data_bank1_hi_r,          // WQ fwd bank1 hi
  input                         dc4_dt_line_cross_r,
  input [1:0]                   dc4_dt_bank_sel_r,
  input [`npuarc_DC_WAY_RANGE]         dc4_hit_even_way_hot_r,
  input [`npuarc_DC_WAY_RANGE]         dc4_hit_odd_way_hot_r,
  
  input                         dc4_stall_r,      // DC4 stall

  output reg [3:0]              ecc_dccm_sbe_count_r, // Count single bit errors
  input                         dccm_ecc_sbe_clr,

  ////////// Interface to the result bus ////////////////////////////////////
  //
  output                        wq_scond_rb_req,  // Request retirement
  output  [`npuarc_GRAD_TAG_RANGE]     wq_scond_rb_tag,  // Retiremnt tag
  output                        wq_scond_rb_flag, // Retirement data  (z flag)
  
  input                         wq_scond_rb_ack,  // Retirement ack

  ////////// WQ replay ////////////////////////////////////////////////
  //
  output reg                    dc4_wq_ovf_replay_r,   // DC4 WQ replay 
  output reg                    dc4_wq_order_replay_r, // DC4 WQ replay 
  output reg                    wq_dc4_fwd_replay_r,   // WQ unable to fwd
  
  /////////// Interface to the WA stage ////////////////////////////////////
  //

  input                         wa_retire1_valid,
  input                         wa_retire1_garbage,
  input [`npuarc_GRAD_TAG_RANGE]       wa_retire1_tag,
  input [`npuarc_DOUBLE_RANGE]         wa_retire1_data,


  output [1:0]                  ca_store_grad_tag,
 
  output                        dmp_st_retire0,
  output [1:0]                  dmp_st_retire0_tag,
  output [`npuarc_DMP_DATA_RANGE]      dmp_st_retire0_data,

  output                        dmp_st_retire1,
  output [1:0]                  dmp_st_retire1_tag,
  output [`npuarc_DMP_DATA_RANGE]      dmp_st_retire1_data,


  input                         wa_restart_r,
  input                         wa_hlt_restart_r,

  output reg                    wq_req_even_lo,  
  output reg [`npuarc_DCCM_ADR_RANGE]  wq_addr_even_lo, 
  output reg [`npuarc_DATA_RANGE]      wq_din_even_lo,  
  output reg [3:0]              wq_wem_even_lo,  
  
  output reg                    wq_req_even_hi,  
  output reg [`npuarc_DCCM_ADR_RANGE]  wq_addr_even_hi, 
  output reg [`npuarc_DATA_RANGE]      wq_din_even_hi,  
  output reg [3:0]              wq_wem_even_hi,  
  
  output reg                    wq_req_odd_lo,  
  output reg [`npuarc_DCCM_ADR_RANGE]  wq_addr_odd_lo, 
  output reg [`npuarc_DATA_RANGE]      wq_din_odd_lo,  
  output reg [3:0]              wq_wem_odd_lo,  
  
  output reg                    wq_req_odd_hi,  
  output reg [`npuarc_DCCM_ADR_RANGE]  wq_addr_odd_hi, 
  output reg [`npuarc_DATA_RANGE]      wq_din_odd_hi,  
  output reg [3:0]              wq_wem_odd_hi,  
 
  output [3:0]                  wq_dccm_top_bank_req_mask,
  output [3:0]                  wq_dccm_sec_bank_req_mask,
  
  input                         wq_dccm_read_one,
  input                         wq_dccm_read_two,
//  input [3:0]                   dc3_dccm_ecc_sb_error,

  ////////// Interface to external memory //////////////////////////
  //
  output                        wq_mem_cmd_valid,
  output                        wq_mem_cmd_cache,
  output reg                    wq_mem_cmd_burst_size,
  output reg [`npuarc_PADDR_RANGE]     wq_mem_cmd_addr,
  input                         wq_mem_cmd_accept,
  output reg                    wq_mem_cmd_lock,               
  output reg                    wq_mem_cmd_excl,               
  output reg [1:0]              wq_mem_cmd_data_size,               
  output reg                    wq_mem_cmd_prot,    

  
  output                        wq_mem_wr_valid,  
  output                        wq_mem_wr_last,  
  input                         wq_mem_wr_accept,
  output [`npuarc_DOUBLE_BE_RANGE]     wq_mem_wr_mask,       
  output [`npuarc_DOUBLE_RANGE]        wq_mem_wr_data,  
  
  input                         wq_mem_wr_done,
  input                         wq_mem_wr_excl_done,
  input                         wq_mem_err_wr,
  output                        wq_mem_wr_resp_accept,

  ////////// Interface to the  Dcache ///////////////////////////////////////
  //
  output reg                     wq_req_dd_even_lo, 
  output reg [`npuarc_DC_ADR_RANGE]     wq_dd_addr_even_lo,
  output reg [`npuarc_DATA_RANGE]       wq_dd_din_even_lo, 
  output reg [`npuarc_DC_BE_RANGE]      wq_dd_wem_even_lo, 

  output reg                     wq_req_dd_even_hi, 
  output reg [`npuarc_DC_ADR_RANGE]     wq_dd_addr_even_hi,
  output reg [`npuarc_DATA_RANGE]       wq_dd_din_even_hi, 
  output reg [`npuarc_DC_BE_RANGE]      wq_dd_wem_even_hi, 

  output reg                     wq_req_dd_odd_lo,  
  output reg [`npuarc_DC_ADR_RANGE]     wq_dd_addr_odd_lo, 
  output reg [`npuarc_DATA_RANGE]       wq_dd_din_odd_lo,  
  output reg [`npuarc_DC_BE_RANGE]      wq_dd_wem_odd_lo,  

  output reg                     wq_req_dd_odd_hi,  
  output reg [`npuarc_DC_ADR_RANGE]     wq_dd_addr_odd_hi, 
  output reg [`npuarc_DATA_RANGE]       wq_dd_din_odd_hi,  
  output reg [`npuarc_DC_BE_RANGE]      wq_dd_wem_odd_hi, 

  output reg [`npuarc_DC_WAY_RANGE]     wq_dd_way_hot,    

  input                          wq_dc_read,
  ////////// WQ forwarding  ////////////////////////////////////////
  //
  output                         dc3_fwd_req,

  ////////// DMU status /////////////////////////////////////////////
  //
  input                         dmu_empty,
  input [`npuarc_DC_SET_RANGE]         dmu_set_addr,
  
  ////////// Error reporting /////////////////////////////////////////////
  //
  output                        wq_err_r,
  output                        wq_err_user_mode_r,
  output [`npuarc_PADDR_RANGE]         wq_err_addr_r,       
  input                         wq_err_ack,        
  
  //////////  Outputs to LQ synchronization //////////////////////////////////
  // 
  output [`npuarc_DMP_FIFO_RANGE]      wq_order_ptr_1h,      // WQ most recent external entry
  output                        dc4_raw_hazard,       // RAW hazard

  output                        wq_mem_per_iccm_read, // WQ entry processed
  output [`npuarc_WQ_PTR_RANGE]        wq_rdentry0,          // WQ processed entry
 
  output                        wq_mem_retire,        // WQ mem entry retired
  output [`npuarc_WQ_PTR_RANGE]        wq_mem_entry_id,      // WQ retired  entry
 
 

  
  //////////  Inputs for WQ  synchronization /////////////////////////////////
  //
  input [`npuarc_DMP_FIFO_RANGE]       lq_order_ptr_1h,      // LQ most recent entry
  input                         dc4_war_hazard,       // WAR hazard

  input                         lq_cmd_read,         // LQ command  popped
  input [`npuarc_LQ_PTR_RANGE]         lq_cmd_rd_ptr,       // LQ command read pointer

  input                         lq_data_retire,      // LQ data retired
  input                         lq_data_err,         // LQ data retired with an error
  input [`npuarc_LQ_PTR_RANGE]         lq_data_rd_ptr,      // LQ data read pointer
  
  ////////// Write Queue status //////////////////////////////////////
  //
  output                        wq_dc_entry,
  output                        wq_scond_entry,
  output                        wq_target_dc,
  output                        wq_dmu_set_conflict,
  output reg                    dc4_wq_full,
  output reg                    dc4_wq_one_empty,
  output                        wq_non_dc_entry,
  output                        wq_retire,
  output reg                    wq_empty,
  output reg                    wq_more_than_one_empty
// leda NTL_CON13C on  
// leda NTL_CON37 on  
);

// Local declarations

reg                       wq_full;

reg                       dc3_dc_wr_one; 
reg                       dc3_dc_wr_two; 
reg                       dc3_target_dc;
reg                       dc3_target_dccm;

wire                      ca_store_go;

wire  [`npuarc_DMP_TARGET_RANGE] wq_ext_target;
wire  [`npuarc_DMP_TARGET_RANGE] wq_dc_target;
wire                      dc4_wq_write0;
wire  [2:0]               dc4_wq_size0;
wire  [`npuarc_DMP_DATA_RANGE]   dc4_wq_data0;   
wire  [`npuarc_PADDR_RANGE]      dc4_wq_addr0;    
wire  [`npuarc_DMP_TARGET_RANGE] dc4_wq_target0;  
wire  [1:0]               dc4_wq_bank_lo0; 
wire  [1:0]               dc4_wq_bank_hi0;
wire  [`npuarc_DC_WAY_RANGE]     dc4_wq_way_hot0;
wire  [`npuarc_DC_WAY_RANGE]     dc4_wq_way_hot1;
wire [`npuarc_DMP_BE_RANGE]      dc4_wq_ecc_data_mask0;
wire [`npuarc_DMP_BE_RANGE]      dc4_wq_ecc_data_mask1;
wire                      dc4_wq_write1;
wire  [2:0]               dc4_wq_size1;
wire  [`npuarc_DMP_DATA_RANGE]   dc4_wq_data1;   
wire  [`npuarc_PADDR_RANGE]      dc4_wq_addr1;    
wire  [`npuarc_DMP_TARGET_RANGE] dc4_wq_target1;  
wire  [1:0]               dc4_wq_bank_lo1; 
wire  [1:0]               dc4_wq_bank_hi1;

reg                       wq_one_empty;
reg                       wq_two_empty;
reg                       wq_three_empty;

// leda NTL_CON13A off
// LMD: undriven internal net Range:8-12,31
// LJ:  code readibility
wire                      wq_ext_valid; 
wire                      wq_ext_bufferable;
wire                      wq_dc_valid; 

wire                      wq_sec_valid; 
wire [`npuarc_DMP_TARGET_RANGE]  wq_sec_target;
wire [3:0]                wq_sec_bank_req_mask;
wire [`npuarc_PADDR_RANGE]       wq_sec_addr;
wire [`npuarc_DOUBLE_BE_RANGE]   wq_sec_mask_bank0;
wire [`npuarc_DOUBLE_BE_RANGE]   wq_sec_mask_bank1;

wire [`npuarc_DOUBLE_RANGE]      wq_sec_data_bank0;
wire [`npuarc_DOUBLE_RANGE]      wq_sec_data_bank1;


wire [`npuarc_DC_WAY_RANGE]      wq_way_hot;                  
wire [`npuarc_DOUBLE_RANGE]      wq_ext_data_bank0;
wire [`npuarc_DOUBLE_RANGE]      wq_dc_data_bank0;

wire [`npuarc_DOUBLE_RANGE]      wq_ext_data_bank1;
wire [`npuarc_DOUBLE_RANGE]      wq_dc_data_bank1;

wire [`npuarc_DOUBLE_BE_RANGE]   wq_ext_mask_bank0;
wire [`npuarc_DOUBLE_BE_RANGE]   wq_dc_mask_bank0;

wire [`npuarc_DOUBLE_BE_RANGE]   wq_ext_mask_bank1;
wire [`npuarc_DOUBLE_BE_RANGE]   wq_dc_mask_bank1;
wire [`npuarc_PADDR_RANGE]       wq_ext_addr;
wire [`npuarc_PADDR_RANGE]       wq_dc_addr;
wire [1:0]                wq_ext_size;
wire                      wq_ext_user_mode;

wire [3:0]                wq_ext_top_bank_req_mask;
wire [3:0]                wq_dc_top_bank_req_mask;

// leda NTL_CON13A on

wire                     wq_dc_retire_one;
wire                     wq_dc_retire_two;

wire                     wq_mem_read;

wire                     wq_ext_scond;
wire                     wq_mem_scond;
reg [`npuarc_DC_WAY_RANGE]      dc4_hit0_way_hot;
reg [`npuarc_DC_WAY_RANGE]      dc4_hit1_way_hot;


reg                      dc4_wr_one;
reg                      dc4_wr_two;
reg                      dc4_target_ext;
//reg                      dc4_wq_non_dc_entry;
reg                      dc4_wq_ex_non_dc_entry;
reg                      wq_dc4_fwd_replay_cg0;
reg                      wq_dc4_fwd_replay_nxt;
reg                      dc4_wq_order_replay_cg0;
reg                      dc4_wq_order_replay_nxt;
reg                      dc4_wq_ovf_replay_set_cg0;
reg                      dc4_wq_ovf_replay_clr_cg0;
reg                      dc4_wq_ovf_replay_nxt;
reg                      dc4_wq_ovf_replay_next;






wire [`npuarc_DMP_FIFO_RANGE]   wq_valid_r;

wire                     wq_ex_non_dc_entry;

// ca_pass generation
// (1) It depends on the actual ca_pass_prel
// (2) In case of `DCCM_ECC/`DC_ECC  option, when there is only a single bit error
//     and no double bit error, the corrected data should enter the WQ Fifo
// 
wire [3:0]         dc3_ecc_sb_error;
wire [3:0]         dc4_ecc_sb_error_r;
wire               dc4_ecc_db_error_r;

wire [`npuarc_DATA_RANGE] dccm_ecc_data0_lo;
wire [`npuarc_DATA_RANGE] dccm_ecc_data0_hi;
wire [`npuarc_DATA_RANGE] dccm_ecc_data1_lo;
wire [`npuarc_DATA_RANGE] dccm_ecc_data1_hi;

wire [`npuarc_DATA_RANGE] dccm_rb_data0_lo;
wire [`npuarc_DATA_RANGE] dccm_rb_data0_hi;
wire [`npuarc_DATA_RANGE] dccm_rb_data1_lo;
wire [`npuarc_DATA_RANGE] dccm_rb_data1_hi;

wire [`npuarc_DATA_RANGE] dc_rb_data0_lo;
wire [`npuarc_DATA_RANGE] dc_rb_data0_hi;
wire [`npuarc_DATA_RANGE] dc_rb_data1_lo;
wire [`npuarc_DATA_RANGE] dc_rb_data1_hi;


assign dccm_rb_data1_hi = dc4_data_odd_hi_r[`npuarc_DATA_RANGE]; 
assign dccm_rb_data1_lo = dc4_data_odd_lo_r[`npuarc_DATA_RANGE];
assign dccm_rb_data0_hi = dc4_data_even_hi_r[`npuarc_DATA_RANGE];
assign dccm_rb_data0_lo = dc4_data_even_lo_r[`npuarc_DATA_RANGE];
assign dccm_ecc_data1_hi = dc4_ecc_data_odd_hi[`npuarc_DATA_RANGE]; 
assign dccm_ecc_data1_lo = dc4_ecc_data_odd_lo[`npuarc_DATA_RANGE];
assign dccm_ecc_data0_hi = dc4_ecc_data_even_hi[`npuarc_DATA_RANGE];
assign dccm_ecc_data0_lo = dc4_ecc_data_even_lo[`npuarc_DATA_RANGE];
assign dc_rb_data1_hi = dc4_dd_data_odd_hi_r[`npuarc_DATA_RANGE]; 
assign dc_rb_data1_lo = dc4_dd_data_odd_lo_r[`npuarc_DATA_RANGE];
assign dc_rb_data0_hi = dc4_dd_data_even_hi_r[`npuarc_DATA_RANGE];
assign dc_rb_data0_lo = dc4_dd_data_even_lo_r[`npuarc_DATA_RANGE];
   
//////////////////////////////////////////////////////////////////////////////
// ECC stuff
//////////////////////////////////////////////////////////////////////////////
// 
assign dc3_ecc_sb_error      =   4'd0;//dc3_dccm_ecc_sb_error;

assign dc4_ecc_sb_error_r    =   dc4_dccm_ecc_sb_error_r
                             & {4{~(|dc4_ecc_skid_sb_error_r)}};
assign dc4_ecc_db_error_r    =   dc4_dccm_ecc_db_error_r;

wire ca_pass;
// When the WQ is full, there shouldn't be any ca_pass, as this will corrupt
// contents of the WQ. (1)
//
// When we there is a more than one match in the WQ for a partial store
// that store should be replayed (2)
//
// When there is a dc4_ecc_replay_r due to the detection of a sb_error, the load/
// store in DC3 shouldn't enter the WQ. Because X3_pass will be high when dc4_replay
// is asserted, and X3_pass becomes low in the next cycle. In the meantime, the X3 
// information might enter the WQ. Hence ca_pass is disabled on a wa_restart_r. (3)
//
// In case of data cache, the correction of single bit error is handled in DMU
// Hence the store enters the WQ, when there is no error
//
assign ca_pass =  ca_pass_prel
                | (  (|dc4_ecc_sb_error_r   ) 
                   & (wq_two_empty | wq_empty) // has space for scrubbing    
                   & (~dc4_ecc_db_error_r   )     // no double bit error
                   & (ca_load_r | ca_store_r)
                   & (~dc4_wq_ovf_replay_r  )     // (1)  
                   & (~wq_dc4_fwd_replay_r  )     // (2)
                   & (~wa_restart_r         )     // (3) 
                   & (~wa_hlt_restart_r     ))    // (3) 
                ;   


///////////////////////////////////////////////////////////////////////////////////////////
//
// Single bit error counter
//
//////////////////////////////////////////////////////////////////////////////////////////
wire       ecc_dccm_sbe_count_set_cg0;
wire       ecc_dccm_sbe_count_clr_cg0;

wire [3:0] ecc_dccm_sbe_count_nxt;
reg  [3:0]  ecc_dccm_sbe_count_next;
wire [3:0]  ecc_dccm_sbe_count_comb;

// start incrementing the saturating counter
//
assign ecc_dccm_sbe_count_set_cg0 = ca_pass
                                  & (~ca_pass_prel)
                                  & (~dc4_dmi_scrubbing_conflict)
                                  & (ecc_dccm_sbe_count_r != 4'b1111)
                                  & (~ecc_dccm_sbe_count_clr_cg0);  

// reset the counter
// 
assign ecc_dccm_sbe_count_clr_cg0 = dccm_ecc_sbe_clr; 

// spyglass disable_block W164a
// SMD: LHS width < RHS in assignment
// SJ:  correct width will be used

assign ecc_dccm_sbe_count_nxt = ecc_dccm_sbe_count_r 
                              + {1{dc4_ecc_sb_error_r[0]}}
                              + {1{dc4_ecc_sb_error_r[1]}}
                              + {1{dc4_ecc_sb_error_r[2]}}
                              + {1{dc4_ecc_sb_error_r[3]}};
// spyglass enable_block W164a


assign   ca_store_go =   (ca_store_r & ca_locked_r) 
                       ? ca_scond_go
                       : ca_store_r & (~db_exception_r);

// In case of a ca_load_r that has a single bit error, then it should enter 
// the WQ for scrubbing the data
//

wire   ca_store_prel;
assign ca_store_prel =   ca_store_go
                       | (ca_load_r & (|dc4_ecc_sb_error_r))
                       ;

//////////////////////////////////////////////////////////////////////////////
// Module instantiation:
// The pre alignment of data for the write queue when it crosses
// from odd to even banks
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_dmp_pre_store_aligner u_alb_dmp_pre_store_aligner_0 (
  .ecc_dmp_disable              (ecc_dmp_disable            ),
  .ca_load_r                    (ca_load_r                  ),
  .ca_store_r                   (ca_store_r                 ),
  .ca_cache_byp_r               (ca_cache_byp_r             ),
  .ca_mem_addr0_r               (ca_mem_addr0_r             ),
  .ca_size_r                    (ca_size_r                  ),
  .ca_wr_data_r                 (ca_wr_data_r               ),
  .dc4_mem_addr1_r              (dc4_mem_addr1_r            ),
  .dc4_size0_r                  (dc4_size0_r                ),
  .dc4_size1_r                  (dc4_size1_r                ),
  
  .dc4_target_r                 (dc4_target_r               ),
  .dc4_hit0_way_hot             (dc4_hit0_way_hot           ),
  .dc4_hit1_way_hot             (dc4_hit1_way_hot           ),
  .dc4_data_bank_sel_lo_r       (dc4_data_bank_sel_lo_r     ),
  .dc4_data_bank_sel_hi_r       (dc4_data_bank_sel_hi_r     ),
  .dc4_dt_line_cross_r          (dc4_dt_line_cross_r        ),
  .dc4_rmw_r                    (dc4_rmw_r                  ),
  .dc4_data_even_lo_r           (dccm_rb_data0_lo[`npuarc_DATA_RANGE]),
  .dc4_data_even_hi_r           (dccm_rb_data0_hi[`npuarc_DATA_RANGE]),
  .dc4_data_odd_lo_r            (dccm_rb_data1_lo[`npuarc_DATA_RANGE]),
  .dc4_data_odd_hi_r            (dccm_rb_data1_hi[`npuarc_DATA_RANGE]),
  .dc4_dd_data_even_lo_r        (dc_rb_data0_lo[`npuarc_DATA_RANGE]),
  .dc4_dd_data_even_hi_r        (dc_rb_data0_hi[`npuarc_DATA_RANGE]),
  .dc4_dd_data_odd_lo_r         (dc_rb_data1_lo[`npuarc_DATA_RANGE]),
  .dc4_dd_data_odd_hi_r         (dc_rb_data1_hi[`npuarc_DATA_RANGE]),
  .dc4_ecc_sb_error_r           (dc4_ecc_sb_error_r       ),
  .dc4_ecc_db_error_r           (dc4_ecc_db_error_r       ),
  .dc4_ecc_data_even_lo         (dccm_ecc_data0_lo        ),
  .dc4_ecc_data_even_hi         (dccm_ecc_data0_hi        ),
  .dc4_ecc_data_odd_lo          (dccm_ecc_data1_lo        ),
  .dc4_ecc_data_odd_hi          (dccm_ecc_data1_hi        ),
  .wq_fwd_bank_r                (wq_fwd_bank_r              ),
  .wq_fwd_data_bank0_lo_r       (wq_fwd_data_bank0_lo_r     ),
  .wq_fwd_data_bank0_hi_r       (wq_fwd_data_bank0_hi_r     ),
  .wq_fwd_data_bank1_lo_r       (wq_fwd_data_bank1_lo_r     ),
  .wq_fwd_data_bank1_hi_r       (wq_fwd_data_bank1_hi_r     ),
  
  .dc4_wq_write0                (dc4_wq_write0              ),
  .dc4_wq_size0                 (dc4_wq_size0               ),
  .dc4_wq_data0                 (dc4_wq_data0               ),
  .dc4_wq_target0               (dc4_wq_target0             ),
  .dc4_wq_bank_lo0              (dc4_wq_bank_lo0            ),
  .dc4_wq_bank_hi0              (dc4_wq_bank_hi0            ),
  .dc4_wq_way_hot0              (dc4_wq_way_hot0            ),
  .dc4_wq_addr0                 (dc4_wq_addr0               ),
  .dc4_wq_ecc_data_mask0        (dc4_wq_ecc_data_mask0      ),
  .dc4_wq_write1                (dc4_wq_write1              ),
  .dc4_wq_size1                 (dc4_wq_size1               ),
  .dc4_wq_data1                 (dc4_wq_data1               ),
  .dc4_wq_target1               (dc4_wq_target1             ),
  .dc4_wq_bank_lo1              (dc4_wq_bank_lo1            ),
  .dc4_wq_bank_hi1              (dc4_wq_bank_hi1            ),
  .dc4_wq_way_hot1              (dc4_wq_way_hot1            ),
  .dc4_wq_ecc_data_mask1        (dc4_wq_ecc_data_mask1      ),

  .dc4_wq_addr1                 (dc4_wq_addr1               )
);

//////////////////////////////////////////////////////////////////////////////
// 
// 
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc3_dc_wr_PROC
  dc3_target_dc    =   1'b0
                     | (dc3_target_r == `npuarc_DMP_TARGET_DC)
                     ;

  dc3_target_dccm    =   1'b0
                     | (dc3_target_r == `npuarc_DMP_TARGET_DCCM)
                     ;
  dc3_dc_wr_one    =  (  x3_store_r
                       | (|dc3_ecc_sb_error)           // Incase of a load that has 1b error
                      ) 
                      & (dc3_target_dc | dc3_target_dccm)
                      ;
  dc3_dc_wr_two    =   (  x3_store_r
                        | (|dc3_ecc_sb_error)
                       ) 
                       & (dc3_target_dc | dc3_target_dccm)
                       & (  (dc3_bank_sel_r[3] & dc3_bank_sel_r[0])    // bank 10 cross
                          | (  dc3_bank_sel_r[2] & dc3_bank_sel_r[1]
                              & ((|dc3_ecc_sb_error) | (|dc3_rmw_r)) )  // bank 01 cross
                          | (dc3_bank_sel_r[2] & dc3_bank_sel_r[1] & (|dc3_rmw_r)) // bank 01 cross
                         );
end
//////////////////////////////////////////////////////////////////////////////
// Size table
//
//////////////////////////////////////////////////////////////////////////////
//                         |
//        Size[2:0]        |           Read Value
//-------------------------|-------------------------------------------------
//          000            |             1 - Byte
//          001            |             2 - Bytes (Half Word)
//          010            |             4 - Bytes (Word)
//          011            |             8 - Bytes (Double Word)
//          100            |             3 - Bytes
//          101            |             5 - Bytes
//          110            |             6 - Bytes
//          111            |             7 - Bytes
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//  Asynchronous logic that deals with double writes
//  Mux to select the inputs to the WQ based on the odd to even bank crossing
// 
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_hot0_hit1_PROC
  // This indicates the store is for the the Data Cache
  //
//`if (`HAS_DCACHE == 1)  
  case (dc4_dt_bank_sel_r)
  2'b01: 
  begin
    // Even
    //
    dc4_hit0_way_hot = dc4_hit_even_way_hot_r;
    dc4_hit1_way_hot = 2'b00;
  end  
  2'b10:
  begin
    // Odd
    //
    dc4_hit0_way_hot = dc4_hit_odd_way_hot_r;
    dc4_hit1_way_hot = 2'b00;
  end
  2'b11:
  begin
    if (ca_mem_addr0_r[`npuarc_DC_TAG_BANK_ID])
    begin
      // Odd to even
      //
      dc4_hit0_way_hot = dc4_hit_odd_way_hot_r;
      dc4_hit1_way_hot = dc4_hit_even_way_hot_r;
    end
    else
    begin
      // Even to odd
      //
      dc4_hit0_way_hot = dc4_hit_even_way_hot_r;
      dc4_hit1_way_hot = dc4_hit_odd_way_hot_r;
    end  
  end
  default:
  begin
    dc4_hit0_way_hot = 2'b00;
    dc4_hit1_way_hot = 2'b00;
  end
  endcase
//`else
//  // Don't care
//  //
//  dc4_hit0_way_hot = 2'b00;
//  dc4_hit1_way_hot = 2'b00;

end
//////////////////////////////////////////////////////////////////////////////
// WQ STATUS
// 
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_status_PROC
  // 
  //
  wq_one_empty           =    (wq_valid_r == 4'b0111)
                            | (wq_valid_r == 4'b1011)
                            | (wq_valid_r == 4'b1101)
                            | (wq_valid_r == 4'b1110)
                            ;
  wq_two_empty           =    (wq_valid_r == 4'b0011)
                            | (wq_valid_r == 4'b0101)
                            | (wq_valid_r == 4'b1001)
                            | (wq_valid_r == 4'b0110)
                            | (wq_valid_r == 4'b1010)
                            | (wq_valid_r == 4'b1100)
                            ;
  wq_three_empty         =    (wq_valid_r == 4'b0001)
                            | (wq_valid_r == 4'b0010)         
                            | (wq_valid_r == 4'b0100)         
                            | (wq_valid_r == 4'b1000)
                            ;
// In case of bus error, do not become empty
//   
  wq_empty               = ~(| wq_valid_r)
                         & (~wq_err_r);
  wq_more_than_one_empty =  wq_empty
                          | wq_two_empty
                          | wq_three_empty;
  wq_full                = &(wq_valid_r);
end


//////////////////////////////////////////////////////////////////////////////
// 
// 
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_wr_PROC
  dc4_wr_one    = dc4_wq_write0 ^ dc4_wq_write1;
  dc4_wr_two    = dc4_wq_write0 & dc4_wq_write1;
end

//////////////////////////////////////////////////////////////////////////////
// 
// 
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_wq_PROC
  dc4_target_ext         =   (dc4_target_r != `npuarc_DMP_TARGET_DC)
                           & (dc4_target_r != `npuarc_DMP_TARGET_DCCM)
                           ;

  dc4_wq_full            =   (wq_full)
                           | (wq_one_empty & (dc4_wr_one | dc4_wr_two))
                           | (wq_two_empty & dc4_wr_two)
                           ;
  
  dc4_wq_one_empty       =   (wq_one_empty)
                           | (wq_two_empty   & dc4_wr_one)
                           | (wq_three_empty & dc4_wr_two)
                           ;
  dc4_wq_ex_non_dc_entry =  (ca_load_r & ca_store_r & dc4_target_ext)
                           | wq_ex_non_dc_entry
                           ;
end
  
//////////////////////////////////////////////////////////////////////////////
// Replays
// 
//////////////////////////////////////////////////////////////////////////////
wire   x3_load_or_partial_store;
assign x3_load_or_partial_store =  x3_load_r
                               | (x3_store_r & (|dc3_rmw_r))
                               ;
always @*
begin : dc4_wq_replay_nxt_PROC
  wq_dc4_fwd_replay_cg0   =    (x3_load_or_partial_store & x3_pass & ca_enable)
                             |  wq_dc4_fwd_replay_r
                             ; 
                            
  wq_dc4_fwd_replay_nxt   = x3_load_or_partial_store & wq_fwd_replay;
  
  
  // Set them when the instruction moves from X3 to CA
  //
  dc4_wq_ovf_replay_set_cg0   =   ( (  x3_store_r 
                                     | (|dc3_ecc_sb_error)
                                    )
                                   & x3_pass & ca_enable);

  //
  // Clear them on the following conditions
  //
  // (1) when there is a replay and no dc4_stall_r
  // (2) when there is a dc4_stall, and the WQ is no no longer full
  //
  dc4_wq_ovf_replay_clr_cg0 = (dc4_wq_ovf_replay_r & (~dc4_stall_r))  // (1)   
                            | (  dc4_stall_r                          // (2)
                                & (  (wq_retire & (~dc4_wr_two))
                                   | wq_more_than_one_empty
                                   | wa_restart_r
                                  )  
                               );
 
  dc4_wq_ovf_replay_nxt   = (dc4_wq_full      & dc3_dc_wr_one & (~wq_dc_retire_one))
                          | (dc4_wq_full      & dc3_dc_wr_two & (~wq_dc_retire_two))
                          | (dc4_wq_one_empty & dc3_dc_wr_two & (~wq_dc_retire_one))
                          ;
  
  // When there is an uncached entry in the WQ, we cant put a cached entry in 
  // the WQ. This creates a read/write dependnecy on the system bus. 
  //
  dc4_wq_order_replay_cg0 =  (x3_store_r & x3_pass & ca_enable)
                            | dc4_wq_order_replay_r
                            ;
  dc4_wq_order_replay_nxt =   x3_store_r
                            & (~x3_uop_inst_r)
                            & dc3_target_dc
                            & dc3_dt_any_hit
                            & dc4_wq_ex_non_dc_entry
                            ;
end
//////////////////////////////////////////////////////////////////////////////
// Module instantiation:
// The storage elements for the write queue is inside this module
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_dmp_wq_fifo u_dmp_wq_fifo (
  .holdup_excpn_r          (holdup_excpn_r         ),
  .st_instrs_discarded     (st_instrs_discarded    ),
  .st_instrs_discarded_r   (st_instrs_discarded_r  ),
  .clk                  (clk                  ),   
  .rst_a                (rst_a                ),  

  .ecc_dmp_disable      (ecc_dmp_disable      ),

  .ca_pass              (ca_pass              ),
  .ca_store_r           (ca_store_prel        ),
  .ca_load_r            (ca_load_r            ),
  .ca_locked_r          (ca_locked_r          ),
  .ca_mem_addr0_r       (ca_mem_addr0_r       ),
  .ca_wr_data_r         (ca_wr_data_r         ),
  .dc4_mem_addr1_r      (dc4_mem_addr1_r      ),
  .dc4_size0_r          (dc4_size0_r          ),
  .dc4_size1_r          (dc4_size1_r          ),

  .ca_size_r            (ca_size_r            ),
  .ca_user_mode_r       (ca_user_mode_r       ),
  .ca_data_bank_sel_r   ({dc4_data_bank_sel_hi_r[1],
                          dc4_data_bank_sel_lo_r[1],
                          dc4_data_bank_sel_hi_r[0],
                          dc4_data_bank_sel_lo_r[0]}),
  
  .ca_volatile_r        (dc4_volatile_r       ),
  .ca_strict_order_r    (dc4_strict_order_r   ),
  .ca_data_mem_attr_r   (dc4_data_mem_attr_r  ),
  .ca_dmi_scrubbing_conflict (dc4_dmi_scrubbing_conflict),
  .ca_store_grad_r      (ca_store_grad_r      ),      
  .ca_store_grad_swap_r (ca_store_grad_swap_r ),      
  .ca_store_grad_tag_lo_r(ca_store_grad_tag_lo_r),
  .ca_store_grad_tag_hi_r(ca_store_grad_tag_hi_r),
  

  .wa_retire1_valid     (wa_retire1_valid     ),
  .wa_retire1_garbage   (wa_retire1_garbage   ),
  .wa_retire1_tag       (wa_retire1_tag       ),
  .wa_retire1_data      (wa_retire1_data      ),


  .ca_store_grad_tag    (ca_store_grad_tag    ),
  .dmp_st_retire0_r     (dmp_st_retire0       ),
  .dmp_st_retire0_tag_r (dmp_st_retire0_tag   ),
  .dmp_st_retire0_data_r(dmp_st_retire0_data  ),

  .dmp_st_retire1_r     (dmp_st_retire1       ),
  .dmp_st_retire1_tag_r (dmp_st_retire1_tag   ),
  .dmp_st_retire1_data_r(dmp_st_retire1_data  ),


  .db_active_r          (db_active_r          ),
  .wa_restart_r         (wa_restart_r         ),
 
  .dmp_wq_write0        (dc4_wq_write0        ),  
  .dmp_wq_data0         (dc4_wq_data0         ),   
  .dmp_wq_size0         (dc4_wq_size0         ),  
  .dmp_wq_addr0         (dc4_wq_addr0         ),  
  .dmp_wq_target0       (dc4_wq_target0       ), 
  .dmp_wq_bank_lo0      (dc4_wq_bank_lo0      ),
  .dmp_wq_bank_hi0      (dc4_wq_bank_hi0      ),
  .dmp_wq_way_hot0      (dc4_wq_way_hot0      ),  
  .dmp_wq_ecc_data_mask0 (dc4_wq_ecc_data_mask0),
  .dmp_wq_write1        (dc4_wq_write1        ),
  .dmp_wq_data1         (dc4_wq_data1         ),  
  .dmp_wq_size1         (dc4_wq_size1         ),  
  .dmp_wq_addr1         (dc4_wq_addr1         ),  
  .dmp_wq_target1       (dc4_wq_target1       ), 
  .dmp_wq_bank_lo1      (dc4_wq_bank_lo1      ),
  .dmp_wq_bank_hi1      (dc4_wq_bank_hi1      ),
  .dmp_wq_way_hot1      (dc4_wq_way_hot1      ),  
  .dmp_wq_ecc_data_mask1 (dc4_wq_ecc_data_mask1), 
  .sa_dsync_op_r        (sa_dsync_op_r        ), 
  .sa_dmb_op_r          (sa_dmb_op_r          ),   
  .sa_dmb_stall         (sa_dmb_stall         ),   

  .x2_mem_addr0_r       (x2_mem_addr0_r       ),
  .x2_load_r            (x2_load_r            ),
  .x2_size_r            (x2_size_r            ),
  .x2_pass              (x2_pass              ),
  .dc2_rmw_r            (dc2_rmw_r            ),
  .dc2_data_bank_sel_r  (dc2_data_bank_sel_r  ),
  .dc2_mem_addr1_r      (dc2_mem_addr1_r      ),
  .dc2_dc_uop_stall     (dc2_dc_uop_stall     ),
  
  .dmu_empty            (dmu_empty            ),
  .dmu_set_addr         (dmu_set_addr         ),

  .x3_load_r            (x3_load_r            ),    
  .x3_store_r           (x3_store_r           ),
  .x3_store_may_grad    (x3_store_may_grad    ),
  .x3_pass              (x3_pass              ),   
  .dc3_stall_r          (dmp_dc3_stall_r      ),
  .dc3_partial_or_multi_conflict (dc3_partial_or_multi_conflict),
  .x3_sync_op_r         (x3_sync_op_r         ), 
  .x3_brk_op_r          (x3_brk_op_r          ), 
  .x3_mem_addr0_r       (x3_mem_addr0_r       ), 
  .x3_mem_addr1_r       (x3_mem_addr1_r       ),
  .dc3_size0_r          (dc3_size0_r          ),    
  .dc3_size1_r          (dc3_size1_r          ),    
  .dc3_bank_sel_r       (dc3_bank_sel_r       ),
  .dc3_target_r         (dc3_target_r         ), 
  .dc3_rmw_r            (dc3_rmw_r            ), 
  .dc3_fwd_allowed_r    (dc3_fwd_allowed_r    ),
  
  .dc4_stall_r           (dc4_stall_r         ),
  .dc4_target_r          (dc4_target_r        ),
  .dc4_ecc_sb_error_r    (|dc4_ecc_sb_error_r ),
  
  .wq_fwd_replay         (wq_fwd_replay       ),
  .wq_fwd_bank           (wq_fwd_bank         ),
  .wq_fwd_data_bank0_lo  (wq_fwd_data_bank0_lo),
  .wq_fwd_data_bank0_hi  (wq_fwd_data_bank0_hi),
  .wq_fwd_data_bank1_lo  (wq_fwd_data_bank1_lo),
  .wq_fwd_data_bank1_hi  (wq_fwd_data_bank1_hi),
  
  .wq_skid_ctrl_mask     (wq_skid_ctrl_mask   ),
  
  .wq_mem_read           (wq_mem_read         ),         
  .wq_mem_wr_done        (wq_mem_wr_done      ),      
  .wq_mem_wr_excl_done   (wq_mem_wr_excl_done ), 
  .wq_mem_err_wr         (wq_mem_err_wr       ),       
  .wq_dc_read            (wq_dc_read          ),       
  .wq_dccm_read_one      (wq_dccm_read_one    ),  
  .wq_dccm_read_two      (wq_dccm_read_two    ), 
  
  .wq_dc_retire_one      (wq_dc_retire_one    ),
  .wq_dc_retire_two      (wq_dc_retire_two    ),
  .wq_retire             (wq_retire           ),
  
  .wq_ext_valid          (wq_ext_valid        ),
  .wq_ext_bufferable     (wq_ext_bufferable   ),
  .wq_ext_data_bank0     (wq_ext_data_bank0   ),  
  .wq_ext_data_bank1     (wq_ext_data_bank1   ),  
  .wq_ext_mask_bank0     (wq_ext_mask_bank0   ),  
  .wq_ext_mask_bank1     (wq_ext_mask_bank1   ),  
  .wq_ext_addr           (wq_ext_addr         ),  
  .wq_ext_size           (wq_ext_size         ),  
  .wq_ext_user_mode      (wq_ext_user_mode    ),  
  .wq_ext_target         (wq_ext_target       ), 
  .wq_ext_top_bank_req_mask  (wq_ext_top_bank_req_mask),
  .wq_ext_scond          (wq_ext_scond        ),

  .wq_dc_valid           (wq_dc_valid         ),
  .wq_way_hot            (wq_way_hot          ),
  .wq_dc_data_bank0      (wq_dc_data_bank0    ),  
  .wq_dc_data_bank1      (wq_dc_data_bank1    ),  
  .wq_dc_mask_bank0      (wq_dc_mask_bank0    ),  
  .wq_dc_mask_bank1      (wq_dc_mask_bank1    ), 
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Outputs connected to floating net
// SJ: Not all bits of address used in this design
  .wq_dc_addr            (wq_dc_addr          ),  
// spyglass enable_block UnloadedOutTerm-ML
  .wq_dc_target          (wq_dc_target        ), 
  .wq_dc_top_bank_req_mask  (wq_dc_top_bank_req_mask),
  .wq_dccm_top_bank_req_mask (wq_dccm_top_bank_req_mask),
  .wq_dccm_sec_bank_req_mask (wq_dccm_sec_bank_req_mask),
  .wq_sec_valid          (wq_sec_valid        ),
  .wq_sec_target         (wq_sec_target       ),
  .wq_sec_bank_req_mask  (wq_sec_bank_req_mask),
  .wq_sec_addr           (wq_sec_addr         ),
  .wq_sec_mask_bank0     (wq_sec_mask_bank0   ),
  .wq_sec_mask_bank1     (wq_sec_mask_bank1   ),
  .wq_sec_data_bank0     (wq_sec_data_bank0   ),
  .wq_sec_data_bank1     (wq_sec_data_bank1   ),
  .wq_mem_scond          (wq_mem_scond        ),


  .dc3_fwd_req           (dc3_fwd_req         ),
  
  
  .wq_err_r              (wq_err_r            ),
  .wq_err_user_mode_r    (wq_err_user_mode_r  ),
  .wq_err_addr_r         (wq_err_addr_r       ),      
  .wq_err_ack            (wq_err_ack          ),       

  .wq_order_ptr_1h       (wq_order_ptr_1h     ),      
  .dc4_raw_hazard        (dc4_raw_hazard      ),      
  .wq_mem_per_iccm_read  (wq_mem_per_iccm_read), 
  .wq_ext_rdentry0       (wq_rdentry0         ),          
  .wq_mem_retire         (wq_mem_retire       ),        
  .wq_mem_entry_id       (wq_mem_entry_id     ),      
  
  .lq_order_ptr_1h       (lq_order_ptr_1h     ),
  .dc4_war_hazard        (dc4_war_hazard      ),      
  .lq_cmd_read           (lq_cmd_read         ),      
  .lq_cmd_rd_ptr         (lq_cmd_rd_ptr       ),    
  .lq_data_retire        (lq_data_retire      ),   
  .lq_data_err           (lq_data_err         ),   
  .lq_data_rd_ptr        (lq_data_rd_ptr      ),   
  .wq_dc_entry           (wq_dc_entry         ),
  .wq_scond_entry        (wq_scond_entry      ),
  .wq_target_dc          (wq_target_dc        ),
  .wq_dmu_set_conflict   (wq_dmu_set_conflict ),
  .wq_non_dc_entry       (wq_non_dc_entry     ),
  .wq_ex_non_dc_entry    (wq_ex_non_dc_entry  ),
  .wq_valid_r            (wq_valid_r          )
);


//////////////////////////////////////////////////////////////////////////////
// Module instantiation:
// Retirement of SCOND
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_wq_scond u_alb_dmp_wq_scond (
  .clk                        (clk                      ),
  .rst_a                      (rst_a                    ),

  .ca_store_r                 (ca_store_r               ),
  .ca_pass                    (ca_pass                  ),
  .ca_locked_r                (ca_locked_r              ),
  .ca_grad_tag                (ca_grad_tag              ),

  .dc4_grad_req               (dc4_grad_req             ),
  
  
  .wq_mem_scond               (wq_mem_scond             ),     
  .wq_mem_wr_done             (wq_mem_wr_done           ),   
  .wq_mem_wr_excl_done        (wq_mem_wr_excl_done      ), 
  .wq_mem_err_wr              (wq_mem_err_wr            ), 

 
  .wq_scond_rb_req            (wq_scond_rb_req          ), 
  .wq_scond_rb_tag            (wq_scond_rb_tag          ), 
  .wq_scond_rb_flag           (wq_scond_rb_flag         ), 
  
  .wq_scond_rb_ack            (wq_scond_rb_ack          )  
);
// spyglass disable_block STARC05-2.8.1.3
// spyglass disable_block W398
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, code more readable, optimized by synthesizer.
//////////////////////////////////////////////////////////////////////////////
// Interface to the targets
// 
//////////////////////////////////////////////////////////////////////////////

// leda W547 on
// spyglass enable_block STARC05-2.8.1.3
// spyglass enable_block W398

reg  [`npuarc_DOUBLE_BE_RANGE] wq_wr_mask;
reg  [`npuarc_DOUBLE_RANGE]    wq_wr_data;
reg                     wq_unaligned;

//////////////////////////////////////////////////////////////////////////////
// 
// 
//////////////////////////////////////////////////////////////////////////////
// spyglass disable_block STARC05-2.8.1.3  
// SMD: case label overlaps with another case label
// SJ:  Done on purpose to cover multiple cases except 4'b0000
always @*
begin : wq_wr_mask_wr_data_PROC 
  wq_unaligned           = 1'b0;
  
  casez (wq_ext_top_bank_req_mask)
  4'b0001,
  4'b0010,
  4'b0011:
  begin
    // Bank 0_lo and/or 0_hi
    //
    wq_wr_mask        = wq_ext_mask_bank0;     
    wq_wr_data        = wq_ext_data_bank0; 
  end
  
  4'b0100,
  4'b1000,
  4'b1100:
  begin
    // Bank 1_lo and/or 1_hi
    //
    wq_wr_mask        = wq_ext_mask_bank1;     
    wq_wr_data        = wq_ext_data_bank1;
  end
  
  4'b?11?:
  begin
    // Bank even to odd crossing (unaligned access)
    //
    wq_wr_mask       = wq_ext_mask_bank0;     
    wq_wr_data       = wq_ext_data_bank0; 
    wq_unaligned     = 1'b1;
  end
  
  default:
  begin
    wq_wr_mask        = {`npuarc_DOUBLE_BE_SIZE{1'b0}};  
    wq_wr_data        = {`npuarc_DOUBLE_SIZE{1'b0}};     
  end  
  endcase
end
// spyglass enable_block STARC05-2.8.1.3  
//////////////////////////////////////////////////////////////////////////////
// 
////////////////////////////////////////////////////////////////////////////// 
reg [1:0] wq_cmd_data_size;

always @*
begin : wq_size_PROC
  case (wq_ext_size)
  2'b11:   wq_cmd_data_size = 2'b11;
  2'b10:   wq_cmd_data_size = (wq_ext_addr[1:0] == 2'b00) ? 2'b10 : 2'b11;
  2'b01:   wq_cmd_data_size = (wq_ext_addr[0] == 1'b0)    ? 2'b01 : 2'b11;
  default: wq_cmd_data_size = 2'b00;
  endcase
end

// debug
//
//wire [31:3] addr_aligned;
//assign addr_aligned = {wq_ext_addr[31:3]};

reg  wq_mem_target;
//////////////////////////////////////////////////////////////////////////////
// 
////////////////////////////////////////////////////////////////////////////// 
always @*
begin : wq_mem_default_PROC

  // Default assignments
  //
  wq_mem_cmd_addr       = wq_ext_addr;
  wq_mem_cmd_lock       = 1'b0; 
  wq_mem_cmd_excl       = wq_ext_scond;               
  wq_mem_cmd_burst_size = wq_unaligned;
  wq_mem_cmd_data_size  = wq_cmd_data_size; 
  wq_mem_cmd_prot       = ~wq_ext_user_mode;
  
  wq_mem_target         = (wq_ext_target == `npuarc_DMP_TARGET_MEM);
end  

//////////////////////////////////////////////////////////////////////////////
// Module instantiation
////////////////////////////////////////////////////////////////////////////// 

npuarc_alb_dmp_wq_port u_alb_dmp_wq_port_0 (
  .clk               (clk                ), 
  .rst_a             (rst_a              ), 

  .wq_valid          (wq_ext_valid       ),   
  .wq_target         (wq_mem_target      ),   
  .wq_bufferable     (wq_ext_bufferable  ), 
  .wq_unaligned      (wq_unaligned       ),  
  .wq_mask_bank1     (wq_ext_mask_bank1  ),  
  .wq_data_bank1     (wq_ext_data_bank1  ),  
  .wq_empty          (wq_empty           ),
  
  .wq_cmd_valid      (wq_mem_cmd_valid   ),   
  .wq_cmd_cache      (wq_mem_cmd_cache   ), 
  .wq_cmd_accept     (wq_mem_cmd_accept  ),   
  .wq_wr_mask_prel   (wq_wr_mask         ),
  .wq_wr_data_prel   (wq_wr_data         ),
  .wq_wr_valid       (wq_mem_wr_valid    ),  
  .wq_wr_last        (wq_mem_wr_last     ),
  .wq_wr_mask        (wq_mem_wr_mask     ),
  .wq_wr_data        (wq_mem_wr_data     ),
  .wq_wr_accept      (wq_mem_wr_accept   ),   
  .wq_read           (wq_mem_read        )
);




//////////////////////////////////////////////////////////////////////////////
// DCCM access 
// 
//////////////////////////////////////////////////////////////////////////////

reg                     pre_wq_req_even_lo;
reg [`npuarc_DATA_RANGE]       pre_din_even_lo; 
reg [`npuarc_DC_BE_RANGE]      pre_wem_even_lo; 

reg                     pre_wq_req_even_hi;
reg [`npuarc_DATA_RANGE]       pre_din_even_hi; 
reg [`npuarc_DC_BE_RANGE]      pre_wem_even_hi; 

reg                     pre_wq_req_odd_lo;
reg [`npuarc_DATA_RANGE]       pre_din_odd_lo;  
reg [`npuarc_DC_BE_RANGE]      pre_wem_odd_lo;  

reg                     pre_wq_req_odd_hi;
reg [`npuarc_DATA_RANGE]       pre_din_odd_hi;  
reg [`npuarc_DC_BE_RANGE]      pre_wem_odd_hi; 

always @*
begin : wq_addr_even_PROC
  // Bank 0_lo
  //
  
  case (wq_dc_top_bank_req_mask[0])
  1'b1:
  begin
    pre_wq_req_even_lo =    wq_dc_valid
                         & (wq_dc_target == `npuarc_DMP_TARGET_DCCM);
    pre_wem_even_lo    = wq_dc_mask_bank0[`npuarc_DBL_BE_LO_RANGE];
    wq_addr_even_lo    = wq_dc_addr[`npuarc_DCCM_ADR_RANGE];
    pre_din_even_lo    = wq_dc_data_bank0[`npuarc_DBL_LO_RANGE];
  end
  default:   // wq_sec_bank_req_mask[0]
  begin
    pre_wq_req_even_lo =    wq_sec_valid
                         & (wq_sec_target == `npuarc_DMP_TARGET_DCCM)
                         &  wq_sec_bank_req_mask[0];
    pre_wem_even_lo    = wq_sec_mask_bank0[`npuarc_DBL_BE_LO_RANGE];
    wq_addr_even_lo    = wq_sec_addr[`npuarc_DCCM_ADR_RANGE];
    pre_din_even_lo    = wq_sec_data_bank0[`npuarc_DBL_LO_RANGE];
  end
  endcase

  // Bank 0_hi
  //
  case (wq_dc_top_bank_req_mask[1])
  1'b1:
  begin
    pre_wq_req_even_hi  =    wq_dc_valid
                          & (wq_dc_target == `npuarc_DMP_TARGET_DCCM);
    pre_wem_even_hi     = wq_dc_mask_bank0[`npuarc_DBL_BE_HI_RANGE];
    wq_addr_even_hi     = wq_dc_addr[`npuarc_DCCM_ADR_RANGE];
    pre_din_even_hi     = wq_dc_data_bank0[`npuarc_DBL_HI_RANGE];
  end
  default:  // wq_sec_bank_req_mask[1]
  begin
    pre_wq_req_even_hi  =   wq_sec_valid
                          & (wq_sec_target == `npuarc_DMP_TARGET_DCCM)
                          & wq_sec_bank_req_mask[1];
    pre_wem_even_hi     = wq_sec_mask_bank0[`npuarc_DBL_BE_HI_RANGE];
    wq_addr_even_hi     = wq_sec_addr[`npuarc_DCCM_ADR_RANGE];
    pre_din_even_hi     = wq_sec_data_bank0[`npuarc_DBL_HI_RANGE];
  end
  endcase

  // Bank 1_lo
  //
  case (wq_dc_top_bank_req_mask[2])
  1'b1:
  begin
    pre_wq_req_odd_lo  =    wq_dc_valid
                         & (wq_dc_target == `npuarc_DMP_TARGET_DCCM);
    pre_wem_odd_lo     = wq_dc_mask_bank1[`npuarc_DBL_BE_LO_RANGE];
    wq_addr_odd_lo     = wq_dc_addr[`npuarc_DCCM_ADR_RANGE];
    pre_din_odd_lo     = wq_dc_data_bank1[`npuarc_DBL_LO_RANGE];
  end
  default:  // wq_sec_bank_req_mask[2]
  begin
    pre_wq_req_odd_lo  =    wq_sec_valid
                         & (wq_sec_target == `npuarc_DMP_TARGET_DCCM)
                         & wq_sec_bank_req_mask[2];
    pre_wem_odd_lo     = wq_sec_mask_bank1[`npuarc_DBL_BE_LO_RANGE];
    wq_addr_odd_lo     = wq_sec_addr[`npuarc_DCCM_ADR_RANGE];
    pre_din_odd_lo     = wq_sec_data_bank1[`npuarc_DBL_LO_RANGE];
  end
  endcase

  // Bank 1_hi
  //
  case (wq_dc_top_bank_req_mask[3])
  1'b1:
  begin
    pre_wq_req_odd_hi  =    wq_dc_valid
                          & (wq_dc_target == `npuarc_DMP_TARGET_DCCM);
    pre_wem_odd_hi     = wq_dc_mask_bank1[`npuarc_DBL_BE_HI_RANGE];
    wq_addr_odd_hi     = wq_dc_addr[`npuarc_DCCM_ADR_RANGE];
    pre_din_odd_hi     = wq_dc_data_bank1[`npuarc_DBL_HI_RANGE];
  end
  default:  // wq_sec_bank_req_mask[3]
  begin
    pre_wq_req_odd_hi  =    wq_sec_valid
                         & (wq_sec_target == `npuarc_DMP_TARGET_DCCM)
                         & wq_sec_bank_req_mask[3];
    pre_wem_odd_hi     = wq_sec_mask_bank1[`npuarc_DBL_BE_HI_RANGE];
    wq_addr_odd_hi     = wq_sec_addr[`npuarc_DCCM_ADR_RANGE];
    pre_din_odd_hi     = wq_sec_data_bank1[`npuarc_DBL_HI_RANGE];
  end
  endcase
end
//////////////////////////////////////////////////////////////////////////////
// WQ is little endian --> change to big endian to DCCM & DC
//                     --> ICCM & PER & MEM are little endian, no change
//                     --> result bus expects little endian, no change
//////////////////////////////////////////////////////////////////////////////
// 
always @*
begin : wq_dccm_PROC

  wq_req_even_lo            = pre_wq_req_even_lo;
  wq_req_even_hi            = pre_wq_req_even_hi;
  wq_req_odd_lo             = pre_wq_req_odd_lo; 
  wq_req_odd_hi             = pre_wq_req_odd_hi;

   wq_din_even_lo = pre_din_even_lo;
   wq_din_even_hi = pre_din_even_hi;
   wq_din_odd_lo = pre_din_odd_lo;
   wq_din_odd_hi = pre_din_odd_hi;

   wq_wem_even_lo = pre_wem_even_lo;
   wq_wem_even_hi = pre_wem_even_hi;
   wq_wem_odd_lo = pre_wem_odd_lo;
   wq_wem_odd_hi = pre_wem_odd_hi;
end


//////////////////////////////////////////////////////////////////////////////
// Data cache data (dd) access 
// 
//////////////////////////////////////////////////////////////////////////////
reg [`npuarc_DATA_RANGE]       pre_dd_din_even_lo; 
reg [`npuarc_DC_BE_RANGE]      pre_dd_wem_even_lo; 
reg [`npuarc_DATA_RANGE]       pre_dd_din_even_hi; 
reg [`npuarc_DC_BE_RANGE]      pre_dd_wem_even_hi; 
reg [`npuarc_DATA_RANGE]       pre_dd_din_odd_lo;  
reg [`npuarc_DC_BE_RANGE]      pre_dd_wem_odd_lo;  
reg [`npuarc_DATA_RANGE]       pre_dd_din_odd_hi;  
reg [`npuarc_DC_BE_RANGE]      pre_dd_wem_odd_hi; 

always @*
begin : wq_dd_addr_PROC
  wq_dd_way_hot      = wq_way_hot;
  
  // Bank 0_lo
  //
  wq_req_dd_even_lo  =   wq_dc_valid 
                      & (wq_dc_target == `npuarc_DMP_TARGET_DC)
                      & wq_dc_top_bank_req_mask[0]
                      ;
  wq_dd_addr_even_lo  = wq_dc_addr[`npuarc_DC_ADR_RANGE];
  pre_dd_din_even_lo  = wq_dc_data_bank0[`npuarc_DBL_LO_RANGE];
  pre_dd_wem_even_lo  = wq_dc_mask_bank0[`npuarc_DBL_BE_LO_RANGE];
  
  // Bank 0_hi
  //
  wq_req_dd_even_hi  =   wq_dc_valid 
                      & (wq_dc_target == `npuarc_DMP_TARGET_DC)
                      & wq_dc_top_bank_req_mask[1]
                      ;
  wq_dd_addr_even_hi  = wq_dc_addr[`npuarc_DC_ADR_RANGE];
  pre_dd_din_even_hi  = wq_dc_data_bank0[`npuarc_DBL_HI_RANGE];
  pre_dd_wem_even_hi  = wq_dc_mask_bank0[`npuarc_DBL_BE_HI_RANGE];
  
  // Bank 1_lo
  //
  wq_req_dd_odd_lo  =   wq_dc_valid 
                      & (wq_dc_target == `npuarc_DMP_TARGET_DC)
                      & wq_dc_top_bank_req_mask[2]
                      ;
  wq_dd_addr_odd_lo  = wq_dc_addr[`npuarc_DC_ADR_RANGE];
  pre_dd_din_odd_lo  = wq_dc_data_bank1[`npuarc_DBL_LO_RANGE];
  pre_dd_wem_odd_lo  = wq_dc_mask_bank1[`npuarc_DBL_BE_LO_RANGE];
  
  // Bank 1_hi
  //
  wq_req_dd_odd_hi  =   wq_dc_valid 
                      & (wq_dc_target == `npuarc_DMP_TARGET_DC)
                      & wq_dc_top_bank_req_mask[3]
                      ;
  wq_dd_addr_odd_hi  = wq_dc_addr[`npuarc_DC_ADR_RANGE];
  pre_dd_din_odd_hi  = wq_dc_data_bank1[`npuarc_DBL_HI_RANGE];
  pre_dd_wem_odd_hi  = wq_dc_mask_bank1[`npuarc_DBL_BE_HI_RANGE];
end

//////////////////////////////////////////////////////////////////////////////
// WQ is little endian --> change to big endian to DCCM & DC
//                     --> ICCM & PER & MEM are little endian, no change
//                     --> result bus expects little endian, no change
//////////////////////////////////////////////////////////////////////////////
// 
always @*
begin : wq_dd_din_endian_PROC
   wq_dd_din_even_lo = pre_dd_din_even_lo;
   wq_dd_din_even_hi = pre_dd_din_even_hi;
   wq_dd_din_odd_lo = pre_dd_din_odd_lo;
   wq_dd_din_odd_hi = pre_dd_din_odd_hi;

   wq_dd_wem_even_lo = pre_dd_wem_even_lo;
   wq_dd_wem_even_hi = pre_dd_wem_even_hi;
   wq_dd_wem_odd_lo = pre_dd_wem_odd_lo;
   wq_dd_wem_odd_hi = pre_dd_wem_odd_hi;
end


//////////////////////////////////////////////////////////////////////////////
// Output assignments
// 
//////////////////////////////////////////////////////////////////////////////

assign wq_mem_wr_resp_accept  = 1'b1;


always @*
begin : dc4_wq_ovf_replay_nxt_PROC
  //
  // Default Value
  dc4_wq_ovf_replay_next = dc4_wq_ovf_replay_r;
  
  if (dc4_wq_ovf_replay_set_cg0)
  begin
    dc4_wq_ovf_replay_next = dc4_wq_ovf_replay_nxt;
  end
  else if (dc4_wq_ovf_replay_clr_cg0)
  begin
    dc4_wq_ovf_replay_next = 1'b0;
  end
end


always @*
begin : ecc_dccm_sbe_count_nxt_PROC
  //
  // Default Value
  ecc_dccm_sbe_count_next = ecc_dccm_sbe_count_r;
  
 if (ecc_dccm_sbe_count_set_cg0 == 1'b1)
 begin
   ecc_dccm_sbe_count_next = ((ecc_dccm_sbe_count_r[3:2] == 2'b11) && (ecc_dccm_sbe_count_nxt[3:2] == 2'b00))
                           ? 4'b1111
                           : ecc_dccm_sbe_count_nxt;
 end
 else if (ecc_dccm_sbe_count_clr_cg0 == 1'b1)
 begin
   ecc_dccm_sbe_count_next = 4'b0000;
 end
end

//////////////////////////////////////////////////////////////////////////////
// Synchronous processes
// 
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : wq_dc4_fwd_replay_reg_PROC
  if (rst_a == 1'b1)
  begin
    wq_dc4_fwd_replay_r <= 1'b0;
  end
  else if (wq_dc4_fwd_replay_cg0)
  begin
    wq_dc4_fwd_replay_r <= wq_dc4_fwd_replay_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc4_wq_ovf_replay_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_wq_ovf_replay_r <= 1'b0;
  end
  else
  begin
    dc4_wq_ovf_replay_r <= dc4_wq_ovf_replay_next;
  end
end
// leda TEST_975 off
// LMD: Latch enabled by a clock affects data input of flipflops clocked by the trailing edge of the same clock
// LJ:
always @(posedge clk or posedge rst_a)
begin : dc4_wq_order_replay_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_wq_order_replay_r <= 1'b0;
  end
  else if (dc4_wq_order_replay_cg0)
  begin
    dc4_wq_order_replay_r <= dc4_wq_order_replay_nxt;
  end
end
// leda TEST_975 on



assign  ecc_dccm_sbe_count_comb =
                        ecc_dccm_sbe_count_next;

always @(posedge clk or posedge rst_a)
begin : ecc_dccm_sbe_count_reg_PROC
  if (rst_a == 1'b1)
  begin
    ecc_dccm_sbe_count_r   <= 4'b0000;
  end
  else
  begin
    ecc_dccm_sbe_count_r   <= ecc_dccm_sbe_count_comb;
  end  
end

endmodule // alb_wq

