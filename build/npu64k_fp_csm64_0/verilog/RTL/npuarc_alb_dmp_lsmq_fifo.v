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
//   ALB_DMP_LSMQ_FIFO                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements the Load Store Miss Queue (LSMQ) Fifo.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_lsmq_fifo.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//

// Set simulation timescale
//
// synopsys translate_off

///////////////////////////////////////////////////////////////////////////
// Common Verilog definitions
///////////////////////////////////////////////////////////////////////////

// Verilog simulator timescale definition for all modules
//
`timescale 1 ns / 10 ps

// synopsys translate_on



//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  rst: "rst_a", edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }


module npuarc_alb_dmp_lsmq_fifo (
// leda NTL_CON13C off
// LMD: non driving port
  ////////// General input signals /////////////////////////////////////////
  //
  input                         clk,            // clock
  input                         rst_a,          // reset

  ////////// Entry of the FIFO /////////////////////////////////////////////
  //
  input [1:0]                   dmp_mq_write,          // miss instr enters mq
  input [1:0]                   dmp_lsmq_write,        // miss instr enters lsmq
  input [63:0]       dmp_lsmq_data,         // write data load/store

  input [2:0]       ca_grad_tag,      
  input                         ca_pass,         // No Stall - Late  
  input                         ca_store_r,      // CA store  
  input                         ca_load_r,       // CA load  
  input                         ca_sex_r,        // CA sign extension  
  input [1:0]                   ca_size_r,       // 00-b; 01-h; 10-w; 11-dw
  input [39:0]          ca_mem_addr0_r,  // CA memory address
  input [39:0]          ca_mem_addr1,  // CA memory address
  input                         dc4_mq_addr_match, 
  input                         dc4_mq_set_match, 

  input                         dc4_dt_line_cross_r,
  input                         dc4_dt_miss_r,

  input [2:0]        mq_match0_val,  // MSB=match; MQ pointer 
  input [2:0]        mq_match1_val,  // MSB=match; MQ pointer 
  input [1:0]         mq_wrptr0,      // MSB=valid; entry number
  input [1:0]         mq_wrptr1,      // MSB=valid; entry number
  
  ////////// Input data from MQ and line buffer ////////////////////////////
  //
  input                         mq_valid,      // valid MQ entry
  input [1:0]         mq_rdptr,      // Top MQ entry number
  input [15:0]      lb_valid_r,    // Valid words in Lbuf
  input                         lb_err_r,      // Error in Lbuf
  input [127:0]        lbuf_fwd_data, // read data --> DC or load 

  output wire                   lsmq_done,     // Lbuf can write to DC
  output wire                   lsmq_match0,
  output wire                   lsmq_match1,
  
  output wire                   dc4_lsmq_nomatch_replay, 
  
  output wire                   lsmq_ld_req,   // load request to Lbuf 
  output reg                    lsmq_st_req,   // store request to Lbuf 
  output wire                   lsmq_st_err,   // store miss bus error
  output reg [11:0] lsmq_wr_mask,  // write mask (64-bit)
  output [5:2]    lsmq_addr,     // Address of first word
  output [5:2]    lsmq_st_addr,  // St addr of first word
  output [95:0]     lsmq_data,     // store miss to lbuf
  output wire [63:0] lsmq_ld_data,  // load data to result bus

  output wire [7:0]             lsmq_fwd_bank, // bank select for Lbuf 
  output reg                    lsmq_bank_hi,  // bank select with lbuf
  output reg                    lsmq_bank_lo, 
  output wire [1:0]             mq_size,       // size of load data
  output wire                   mq_sex,        // size extension for load 
  output wire [39:0]    mq_rb_addr,    // Address of load data
  output wire [2:0] mq_rb_tag,     // Retire Grad buffer tag

  output wire                   mq_rb_req,      // ld request to result bus 
  output wire                   mq_rb_err,      // Bus error in line buffer 
  input                         mq_rb_ack,      // result bus ack

  ////////// FIFO status ////////////////////////////////////////////////////
  //
  output wire                   lsmq_full,
  output wire                   lsmq_empty,
  output wire                   lsmq_two_empty
// leda NTL_CON13C on   
);
  
// Local declarations.
reg  [3:0]       lsmq_valid0_r;   
reg  [3:0]       lsmq_valid1_r;   
reg                           lsmq_part_err_r;   
reg  [3:0]       lsmq_store_r;   
reg  [3:0]       lsmq_load_r;   
reg  [3:0]       lsmq_valid0_nxt;   
reg  [3:0]       lsmq_valid1_nxt;   
reg                           lsmq_part_err_nxt;   
reg  [3:0]       lsmq_store_nxt;   
reg  [3:0]       lsmq_load_nxt;   
reg  [3:0]       lsmq_sex_r;   
reg  [3:0]       lsmq_sex_nxt;   
reg  [1:0]                    lsmq_size_r0;   
reg  [3:0]       lsmq_pend00_r0;   
reg  [3:0]       lsmq_pend01_r0;   
reg  [3:0]       lsmq_pend10_r0;   
reg  [3:0]       lsmq_pend11_r0;   
reg  [1:0]          lsmq_mfifo0_r0;   
reg  [1:0]          lsmq_mfifo1_r0;   
reg  [2:0]        lsmq_gtag_r0;   
reg  [39:0]           lsmq_addr0_r0;   
reg  [39:0]           lsmq_addr1_r0;   
reg  [63:0]        lsmq_data_r0;   
reg  [1:0]                    lsmq_size_nxt0;   
reg  [3:0]       lsmq_pend00_nxt0;   
reg  [3:0]       lsmq_pend01_nxt0;   
reg  [3:0]       lsmq_pend10_nxt0;   
reg  [3:0]       lsmq_pend11_nxt0;   
reg  [1:0]          lsmq_mfifo0_nxt0;   
reg  [1:0]          lsmq_mfifo1_nxt0;   
reg  [2:0]        lsmq_gtag_nxt0;   
reg  [39:0]           lsmq_addr0_nxt0;   
reg  [39:0]           lsmq_addr1_nxt0;   
reg  [63:0]        lsmq_data_nxt0;   
reg  [1:0]                    lsmq_size_r1;   
reg  [3:0]       lsmq_pend00_r1;   
reg  [3:0]       lsmq_pend01_r1;   
reg  [3:0]       lsmq_pend10_r1;   
reg  [3:0]       lsmq_pend11_r1;   
reg  [1:0]          lsmq_mfifo0_r1;   
reg  [1:0]          lsmq_mfifo1_r1;   
reg  [2:0]        lsmq_gtag_r1;   
reg  [39:0]           lsmq_addr0_r1;   
reg  [39:0]           lsmq_addr1_r1;   
reg  [63:0]        lsmq_data_r1;   
reg  [1:0]                    lsmq_size_nxt1;   
reg  [3:0]       lsmq_pend00_nxt1;   
reg  [3:0]       lsmq_pend01_nxt1;   
reg  [3:0]       lsmq_pend10_nxt1;   
reg  [3:0]       lsmq_pend11_nxt1;   
reg  [1:0]          lsmq_mfifo0_nxt1;   
reg  [1:0]          lsmq_mfifo1_nxt1;   
reg  [2:0]        lsmq_gtag_nxt1;   
reg  [39:0]           lsmq_addr0_nxt1;   
reg  [39:0]           lsmq_addr1_nxt1;   
reg  [63:0]        lsmq_data_nxt1;   
reg  [1:0]                    lsmq_size_r2;   
reg  [3:0]       lsmq_pend00_r2;   
reg  [3:0]       lsmq_pend01_r2;   
reg  [3:0]       lsmq_pend10_r2;   
reg  [3:0]       lsmq_pend11_r2;   
reg  [1:0]          lsmq_mfifo0_r2;   
reg  [1:0]          lsmq_mfifo1_r2;   
reg  [2:0]        lsmq_gtag_r2;   
reg  [39:0]           lsmq_addr0_r2;   
reg  [39:0]           lsmq_addr1_r2;   
reg  [63:0]        lsmq_data_r2;   
reg  [1:0]                    lsmq_size_nxt2;   
reg  [3:0]       lsmq_pend00_nxt2;   
reg  [3:0]       lsmq_pend01_nxt2;   
reg  [3:0]       lsmq_pend10_nxt2;   
reg  [3:0]       lsmq_pend11_nxt2;   
reg  [1:0]          lsmq_mfifo0_nxt2;   
reg  [1:0]          lsmq_mfifo1_nxt2;   
reg  [2:0]        lsmq_gtag_nxt2;   
reg  [39:0]           lsmq_addr0_nxt2;   
reg  [39:0]           lsmq_addr1_nxt2;   
reg  [63:0]        lsmq_data_nxt2;   
reg  [1:0]                    lsmq_size_r3;   
reg  [3:0]       lsmq_pend00_r3;   
reg  [3:0]       lsmq_pend01_r3;   
reg  [3:0]       lsmq_pend10_r3;   
reg  [3:0]       lsmq_pend11_r3;   
reg  [1:0]          lsmq_mfifo0_r3;   
reg  [1:0]          lsmq_mfifo1_r3;   
reg  [2:0]        lsmq_gtag_r3;   
reg  [39:0]           lsmq_addr0_r3;   
reg  [39:0]           lsmq_addr1_r3;   
reg  [63:0]        lsmq_data_r3;   
reg  [1:0]                    lsmq_size_nxt3;   
reg  [3:0]       lsmq_pend00_nxt3;   
reg  [3:0]       lsmq_pend01_nxt3;   
reg  [3:0]       lsmq_pend10_nxt3;   
reg  [3:0]       lsmq_pend11_nxt3;   
reg  [1:0]          lsmq_mfifo0_nxt3;   
reg  [1:0]          lsmq_mfifo1_nxt3;   
reg  [2:0]        lsmq_gtag_nxt3;   
reg  [39:0]           lsmq_addr0_nxt3;   
reg  [39:0]           lsmq_addr1_nxt3;   
reg  [63:0]        lsmq_data_nxt3;   
reg  [1:0]                    lsmq_size_r[3:0];   
reg  [3:0]       lsmq_pend00_r[3:0];   
reg  [3:0]       lsmq_pend01_r[3:0];   
reg  [3:0]       lsmq_pend10_r[3:0];   
reg  [3:0]       lsmq_pend11_r[3:0];   
reg  [1:0]          lsmq_mfifo0_r[3:0];   
reg  [1:0]          lsmq_mfifo1_r[3:0];   
reg  [2:0]        lsmq_gtag_r[3:0];   
reg  [39:0]           lsmq_addr0_r[3:0];   
reg  [39:0]           lsmq_addr1_r[3:0];   
reg  [63:0]        lsmq_data_r[3:0];   
reg  [2:0]       valid_cnt;

wire [3:0]       dc4_pend00_nxt;
wire [3:0]       dc4_pend01_nxt;
wire [3:0]       dc4_pend10_nxt;
wire [3:0]       dc4_pend11_nxt;
wire [3:0]       lsmq_pend0;
wire [3:0]       lsmq_pend1;
   
wire [3:0]       match0;
wire [3:0]       match1;
wire [3:0]       match0_done;
wire [3:0]       match1_done;
wire [3:0]       lsmq_valid;
wire [3:0]       lsmq_dvalid0;
wire [3:0]       lsmq_dvalid1;
wire [3:0]       lsmq_drdy;
reg  [3:0]       lsmq_drdy_nxt;
wire [3:0]       st_nxt;
wire [3:0]       ld_nxt;
wire [3:0]       ptr_dec;
reg  [3:0]       lsmq_line_cross; 
reg  [7:0]                    fwd_bank[3:0];
reg  [11:0]       byte_mask[3:0];
reg  [11:0]       align_mask[3:0];
wire [11:0]       wr_mask_nxt; 
reg  [2:0]                    word_valid[3:0];
reg [15:0]        word0_mask[3:0];
reg [15:0]        word1_mask[3:0];
reg [15:0]        word2_mask[3:0];
reg [15:0]        lsmq_wd0mask[3:0];
reg [15:0]        lsmq_wd1mask[3:0];
reg [3:0]        last_word;
reg [3:0]        nxt_last_word;

wire [63:0]        data_nxt;   
reg  [95:0]       data0_shf;   
reg  [95:0]       data1_shf;   
wire [63:0]        fwd_data_nxt;   

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: some variables used in certain configurations

reg  [1:0]        wrentry;
reg  [1:0]        ldentry;   
reg  [1:0]        stentry;   
reg  [1:0]        st_entry_r;   
reg  [1:0]        st_entry_next;   
reg  [11:0]       lsmq_wr_mask_next;  // write mask (64-bit)
wire [1:0]        rdentry;   
reg  [1:0]        pend_entry_r;
reg  [1:0]        pend_entry_next;
reg                           wrentry_selected;
reg                           ldentry_selected;
reg                           stentry_selected;
// leda NTL_CON13A on

reg                           pend_req_r;
reg                           lsmq_match0_r;
reg                           lsmq_match1_r;
reg                           pend_req_next;
reg                           lsmq_match0_next;
reg                           lsmq_match1_next;
reg                           lsmq_st_req_next;
//wire                          lsmq_match0;
//wire                          lsmq_match1;
reg                           rb_ack_r;
reg                           rb_ack_next;
reg                           lsmq_bank_hi_next;  // bank select with lbuf
reg                           lsmq_bank_lo_next; 
reg                           part_ld_r;
reg                           part_ld_next;
wire                          part_ld_nxt;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg  [3:2]                    fwd_addr_r;
reg  [3:2]                    fwd_addr_next;
// leda NTL_CON32 on

wire                          lsmq_not_full;
wire                          lsmq_st_clr0;
wire                          lsmq_st_clr1;
wire                          lsmq_ld_clr0;
wire                          lsmq_ld_clr1;
wire                          wr_lb_data;
wire                          wrenable;
wire                          mq_wr_two;
wire                          lsmq_wr_two;
wire                          lsmq_write;
wire [1:0]          mq_entry0;
reg  [1:0]          mq_entry1;

wire                          lsmq_ld_done;

//////////////////////////////////////////////////////////////////////////////
// Synchronous process for writing new information into the FIFO
//  Unaligned 64-bit store, 2 cache lines, takes 2 entries
//////////////////////////////////////////////////////////////////////////////

//leda FM_1_7 off
//LMD: Signal assigned more than once in a single flow of control
//LJ:  register file with multiple write ports, conflict covered by assertions
//
// spyglass disable_block STARC05-2.2.3.3
// SMD: Flipflop value assigned more than once over same signal in always construct
// SJ:  Conflit covered by assertions
always @*
begin : lsmq_pend_comb_PROC
    lsmq_pend00_r[0] = lsmq_pend00_r0;
    lsmq_pend01_r[0] = lsmq_pend01_r0;
    lsmq_pend10_r[0] = lsmq_pend10_r0;
    lsmq_pend11_r[0] = lsmq_pend11_r0;
    lsmq_pend00_r[1] = lsmq_pend00_r1;
    lsmq_pend01_r[1] = lsmq_pend01_r1;
    lsmq_pend10_r[1] = lsmq_pend10_r1;
    lsmq_pend11_r[1] = lsmq_pend11_r1;
    lsmq_pend00_r[2] = lsmq_pend00_r2;
    lsmq_pend01_r[2] = lsmq_pend01_r2;
    lsmq_pend10_r[2] = lsmq_pend10_r2;
    lsmq_pend11_r[2] = lsmq_pend11_r2;
    lsmq_pend00_r[3] = lsmq_pend00_r3;
    lsmq_pend01_r[3] = lsmq_pend01_r3;
    lsmq_pend10_r[3] = lsmq_pend10_r3;
    lsmq_pend11_r[3] = lsmq_pend11_r3;
end

always @*
begin : lsmq_sync_comb_PROC
    lsmq_valid0_nxt    = lsmq_valid0_r;
    lsmq_valid1_nxt    = lsmq_valid1_r;
    lsmq_pend00_nxt0 = lsmq_pend00_r0;
    lsmq_pend01_nxt0 = lsmq_pend01_r0;
    lsmq_pend10_nxt0 = lsmq_pend10_r0;
    lsmq_pend11_nxt0 = lsmq_pend11_r0;
    lsmq_pend00_nxt1 = lsmq_pend00_r1;
    lsmq_pend01_nxt1 = lsmq_pend01_r1;
    lsmq_pend10_nxt1 = lsmq_pend10_r1;
    lsmq_pend11_nxt1 = lsmq_pend11_r1;
    lsmq_pend00_nxt2 = lsmq_pend00_r2;
    lsmq_pend01_nxt2 = lsmq_pend01_r2;
    lsmq_pend10_nxt2 = lsmq_pend10_r2;
    lsmq_pend11_nxt2 = lsmq_pend11_r2;
    lsmq_pend00_nxt3 = lsmq_pend00_r3;
    lsmq_pend01_nxt3 = lsmq_pend01_r3;
    lsmq_pend10_nxt3 = lsmq_pend10_r3;
    lsmq_pend11_nxt3 = lsmq_pend11_r3;
    lsmq_load_nxt      = lsmq_load_r;
    lsmq_store_nxt     = lsmq_store_r;
    lsmq_part_err_nxt  = lsmq_part_err_r;
// leda NTL_RST03 off
// LMD: A flipflop without reset
// LJ:  Valid is reset but Control, Address, Data should not be reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
//
  begin
  // dmp_lsmq_data is from 2 different sources:
  //  - Store data directly from EXU
  //  - Partial load data from first 2 banks or last 2 banks of memory banks
  //
    // Separate writing of valid bit to lessen the load on ca_pass
    //
    if (lsmq_write & (wrentry == 0))
    begin
      lsmq_valid0_nxt[0]   = dmp_lsmq_write[0];     
      lsmq_valid1_nxt[0]   = dmp_lsmq_write[1];     
      lsmq_pend00_nxt0     = dc4_pend00_nxt;
      lsmq_pend01_nxt0     = dc4_pend01_nxt;    
      lsmq_pend10_nxt0     = dc4_pend10_nxt;
      lsmq_pend11_nxt0     = dc4_pend11_nxt;    
    end
    if (lsmq_not_full && wrenable && (wrentry == 0))
    begin
      lsmq_load_nxt[0]     =  ca_load_r
                                 ;
      lsmq_store_nxt[0]    = ca_store_r;     
    end
    if (lsmq_write & (wrentry == 1))
    begin
      lsmq_valid0_nxt[1]   = dmp_lsmq_write[0];     
      lsmq_valid1_nxt[1]   = dmp_lsmq_write[1];     
      lsmq_pend00_nxt1     = dc4_pend00_nxt;
      lsmq_pend01_nxt1     = dc4_pend01_nxt;    
      lsmq_pend10_nxt1     = dc4_pend10_nxt;
      lsmq_pend11_nxt1     = dc4_pend11_nxt;    
    end
    if (lsmq_not_full && wrenable && (wrentry == 1))
    begin
      lsmq_load_nxt[1]     =  ca_load_r
                                 ;
      lsmq_store_nxt[1]    = ca_store_r;     
    end
    if (lsmq_write & (wrentry == 2))
    begin
      lsmq_valid0_nxt[2]   = dmp_lsmq_write[0];     
      lsmq_valid1_nxt[2]   = dmp_lsmq_write[1];     
      lsmq_pend00_nxt2     = dc4_pend00_nxt;
      lsmq_pend01_nxt2     = dc4_pend01_nxt;    
      lsmq_pend10_nxt2     = dc4_pend10_nxt;
      lsmq_pend11_nxt2     = dc4_pend11_nxt;    
    end
    if (lsmq_not_full && wrenable && (wrentry == 2))
    begin
      lsmq_load_nxt[2]     =  ca_load_r
                                 ;
      lsmq_store_nxt[2]    = ca_store_r;     
    end
    if (lsmq_write & (wrentry == 3))
    begin
      lsmq_valid0_nxt[3]   = dmp_lsmq_write[0];     
      lsmq_valid1_nxt[3]   = dmp_lsmq_write[1];     
      lsmq_pend00_nxt3     = dc4_pend00_nxt;
      lsmq_pend01_nxt3     = dc4_pend01_nxt;    
      lsmq_pend10_nxt3     = dc4_pend10_nxt;
      lsmq_pend11_nxt3     = dc4_pend11_nxt;    
    end
    if (lsmq_not_full && wrenable && (wrentry == 3))
    begin
      lsmq_load_nxt[3]     =  ca_load_r
                                 ;
      lsmq_store_nxt[3]    = ca_store_r;     
    end

    // Clear entry once the store is written to line buffer
    //
    if (lsmq_st_clr0)
    begin
      lsmq_valid0_nxt[rdentry]      =   1'b0;
      // Clear pending bits when entry is done.
      //
       lsmq_pend00_nxt0[rdentry] =  1'b0;
       lsmq_pend10_nxt0[rdentry] =  1'b0;
       lsmq_pend00_nxt1[rdentry] =  1'b0;
       lsmq_pend10_nxt1[rdentry] =  1'b0;
       lsmq_pend00_nxt2[rdentry] =  1'b0;
       lsmq_pend10_nxt2[rdentry] =  1'b0;
       lsmq_pend00_nxt3[rdentry] =  1'b0;
       lsmq_pend10_nxt3[rdentry] =  1'b0;
    end

    if (lsmq_st_clr1) 
    begin
      lsmq_valid1_nxt[rdentry]      =  1'b0;    
   
      // Clear pending bits when entry is done.
      //
       lsmq_pend01_nxt0[rdentry]  =  1'b0;
       lsmq_pend11_nxt0[rdentry]  =  1'b0;
       lsmq_pend01_nxt1[rdentry]  =  1'b0;
       lsmq_pend11_nxt1[rdentry]  =  1'b0;
       lsmq_pend01_nxt2[rdentry]  =  1'b0;
       lsmq_pend11_nxt2[rdentry]  =  1'b0;
       lsmq_pend01_nxt3[rdentry]  =  1'b0;
       lsmq_pend11_nxt3[rdentry]  =  1'b0;
    end

   
    // Clear entry once the load is retired
    // If it is not exchange instruction
    //
    if (lsmq_ld_clr0 & (~lsmq_store_r[pend_entry_r])) 
    begin
      lsmq_valid0_nxt[pend_entry_r]    = 1'b0;    
      lsmq_part_err_nxt                = part_ld_r & lb_err_r;

      // Clear pending bits when entry is done.
      //
       lsmq_pend00_nxt0[pend_entry_r] =  1'b0;
       lsmq_pend10_nxt0[pend_entry_r] =  1'b0;
       lsmq_pend00_nxt1[pend_entry_r] =  1'b0;
       lsmq_pend10_nxt1[pend_entry_r] =  1'b0;
       lsmq_pend00_nxt2[pend_entry_r] =  1'b0;
       lsmq_pend10_nxt2[pend_entry_r] =  1'b0;
       lsmq_pend00_nxt3[pend_entry_r] =  1'b0;
       lsmq_pend10_nxt3[pend_entry_r] =  1'b0;
    end
    if (lsmq_ld_clr1 & (~lsmq_store_r[pend_entry_r])) 
    begin
      lsmq_valid1_nxt[pend_entry_r]  = 1'b0;    
      lsmq_part_err_nxt              = 1'b0;

      // Clear pending bits when entry is done.
      //
       lsmq_pend01_nxt0[pend_entry_r] =  1'b0;
       lsmq_pend11_nxt0[pend_entry_r] =  1'b0;
       lsmq_pend01_nxt1[pend_entry_r] =  1'b0;
       lsmq_pend11_nxt1[pend_entry_r] =  1'b0;
       lsmq_pend01_nxt2[pend_entry_r] =  1'b0;
       lsmq_pend11_nxt2[pend_entry_r] =  1'b0;
       lsmq_pend01_nxt3[pend_entry_r] =  1'b0;
       lsmq_pend11_nxt3[pend_entry_r] =  1'b0;
    end

    // Clear the load operation for exchange instruction
    //
    if (lsmq_ld_clr0 & lsmq_store_r[pend_entry_r]) 
    begin
      lsmq_load_nxt[pend_entry_r]  =  1'b0;    
    end

  end
end

always @(posedge clk or posedge rst_a)
begin : lsmq_sync_PROC
  if (rst_a == 1'b1)
  begin
    lsmq_valid0_r     <= {4{1'b0}};
    lsmq_valid1_r     <= {4{1'b0}};
    lsmq_pend00_r0   <= {4{1'b0}};
    lsmq_pend01_r0   <= {4{1'b0}};
    lsmq_pend10_r0   <= {4{1'b0}};
    lsmq_pend11_r0   <= {4{1'b0}};
    lsmq_pend00_r1   <= {4{1'b0}};
    lsmq_pend01_r1   <= {4{1'b0}};
    lsmq_pend10_r1   <= {4{1'b0}};
    lsmq_pend11_r1   <= {4{1'b0}};
    lsmq_pend00_r2   <= {4{1'b0}};
    lsmq_pend01_r2   <= {4{1'b0}};
    lsmq_pend10_r2   <= {4{1'b0}};
    lsmq_pend11_r2   <= {4{1'b0}};
    lsmq_pend00_r3   <= {4{1'b0}};
    lsmq_pend01_r3   <= {4{1'b0}};
    lsmq_pend10_r3   <= {4{1'b0}};
    lsmq_pend11_r3   <= {4{1'b0}};
    lsmq_load_r       <= {4{1'b0}};
    lsmq_store_r      <= {4{1'b0}};
    lsmq_part_err_r   <= 1'b0;
  end
  else
  begin
    lsmq_valid0_r     <= lsmq_valid0_nxt;
    lsmq_valid1_r     <= lsmq_valid1_nxt;
    lsmq_pend00_r0   <= lsmq_pend00_nxt0;
    lsmq_pend01_r0   <= lsmq_pend01_nxt0;
    lsmq_pend10_r0   <= lsmq_pend10_nxt0;
    lsmq_pend11_r0   <= lsmq_pend11_nxt0;
    lsmq_pend00_r1   <= lsmq_pend00_nxt1;
    lsmq_pend01_r1   <= lsmq_pend01_nxt1;
    lsmq_pend10_r1   <= lsmq_pend10_nxt1;
    lsmq_pend11_r1   <= lsmq_pend11_nxt1;
    lsmq_pend00_r2   <= lsmq_pend00_nxt2;
    lsmq_pend01_r2   <= lsmq_pend01_nxt2;
    lsmq_pend10_r2   <= lsmq_pend10_nxt2;
    lsmq_pend11_r2   <= lsmq_pend11_nxt2;
    lsmq_pend00_r3   <= lsmq_pend00_nxt3;
    lsmq_pend01_r3   <= lsmq_pend01_nxt3;
    lsmq_pend10_r3   <= lsmq_pend10_nxt3;
    lsmq_pend11_r3   <= lsmq_pend11_nxt3;
    lsmq_load_r       <= lsmq_load_nxt     ;
    lsmq_store_r      <= lsmq_store_nxt    ;
    lsmq_part_err_r   <= lsmq_part_err_nxt ;
  end
end

// spyglass disable_block ResetFlop-ML Ar_resetcross01
// SMD: Has neither asynchronous set/reset nor synchronous set/reset
// SJ:  Datapath items not reset
always @*
begin : lsmq_data_reg_fifo_PROC
    lsmq_mfifo0_r[0]  = lsmq_mfifo0_r0   ; 
    lsmq_mfifo1_r[0]  = lsmq_mfifo1_r0   ; 
    lsmq_gtag_r[0]    = lsmq_gtag_r0     ; 
    lsmq_size_r[0]    = lsmq_size_r0     ; 
    lsmq_addr0_r[0]   = lsmq_addr0_r0    ; 
    lsmq_addr1_r[0]   = lsmq_addr1_r0    ; 
    lsmq_data_r[0]    = lsmq_data_r0     ; 
    lsmq_mfifo0_r[1]  = lsmq_mfifo0_r1   ; 
    lsmq_mfifo1_r[1]  = lsmq_mfifo1_r1   ; 
    lsmq_gtag_r[1]    = lsmq_gtag_r1     ; 
    lsmq_size_r[1]    = lsmq_size_r1     ; 
    lsmq_addr0_r[1]   = lsmq_addr0_r1    ; 
    lsmq_addr1_r[1]   = lsmq_addr1_r1    ; 
    lsmq_data_r[1]    = lsmq_data_r1     ; 
    lsmq_mfifo0_r[2]  = lsmq_mfifo0_r2   ; 
    lsmq_mfifo1_r[2]  = lsmq_mfifo1_r2   ; 
    lsmq_gtag_r[2]    = lsmq_gtag_r2     ; 
    lsmq_size_r[2]    = lsmq_size_r2     ; 
    lsmq_addr0_r[2]   = lsmq_addr0_r2    ; 
    lsmq_addr1_r[2]   = lsmq_addr1_r2    ; 
    lsmq_data_r[2]    = lsmq_data_r2     ; 
    lsmq_mfifo0_r[3]  = lsmq_mfifo0_r3   ; 
    lsmq_mfifo1_r[3]  = lsmq_mfifo1_r3   ; 
    lsmq_gtag_r[3]    = lsmq_gtag_r3     ; 
    lsmq_size_r[3]    = lsmq_size_r3     ; 
    lsmq_addr0_r[3]   = lsmq_addr0_r3    ; 
    lsmq_addr1_r[3]   = lsmq_addr1_r3    ; 
    lsmq_data_r[3]    = lsmq_data_r3     ; 
end

always @*
begin : lsmq_data_comb_PROC
    lsmq_sex_nxt        = lsmq_sex_r;    
  // Separate writing of valid bit to lessen the load on ca_pass
  //
    lsmq_mfifo0_nxt0   = lsmq_mfifo0_r0  ; 
    lsmq_mfifo1_nxt0   = lsmq_mfifo1_r0  ; 
    lsmq_gtag_nxt0     = lsmq_gtag_r0    ; 
    lsmq_size_nxt0     = lsmq_size_r0    ; 
    lsmq_addr0_nxt0    = lsmq_addr0_r0   ; 
    lsmq_addr1_nxt0    = lsmq_addr1_r0   ; 
    lsmq_data_nxt0     = lsmq_data_r0    ; 
  if (lsmq_write & (wrentry == 0))
  begin
    lsmq_mfifo0_nxt0   = mq_entry0;    
    lsmq_mfifo1_nxt0    = mq_entry1;    
    lsmq_gtag_nxt0      = ca_grad_tag[2:0];  
  end
     
  if (lsmq_not_full && wrenable && (wrentry == 0))
  begin
    lsmq_size_nxt0     = ca_size_r[1:0];     
    lsmq_sex_nxt[0]    = ca_sex_r;    
    lsmq_addr0_nxt0    = ca_mem_addr0_r[39:0];    
    lsmq_addr1_nxt0    = ca_mem_addr1[39:0];    
    lsmq_data_nxt0     = dmp_lsmq_data[63:0];   
  end


  // Forwarding data for cross cache line load instruction
  //
  if (wr_lb_data & (pend_entry_r == 0))
  begin
    lsmq_data_nxt0       =  fwd_data_nxt;     
  end
    lsmq_mfifo0_nxt1   = lsmq_mfifo0_r1  ; 
    lsmq_mfifo1_nxt1   = lsmq_mfifo1_r1  ; 
    lsmq_gtag_nxt1     = lsmq_gtag_r1    ; 
    lsmq_size_nxt1     = lsmq_size_r1    ; 
    lsmq_addr0_nxt1    = lsmq_addr0_r1   ; 
    lsmq_addr1_nxt1    = lsmq_addr1_r1   ; 
    lsmq_data_nxt1     = lsmq_data_r1    ; 
  if (lsmq_write & (wrentry == 1))
  begin
    lsmq_mfifo0_nxt1   = mq_entry0;    
    lsmq_mfifo1_nxt1    = mq_entry1;    
    lsmq_gtag_nxt1      = ca_grad_tag[2:0];  
  end
     
  if (lsmq_not_full && wrenable && (wrentry == 1))
  begin
    lsmq_size_nxt1     = ca_size_r[1:0];     
    lsmq_sex_nxt[1]    = ca_sex_r;    
    lsmq_addr0_nxt1    = ca_mem_addr0_r[39:0];    
    lsmq_addr1_nxt1    = ca_mem_addr1[39:0];    
    lsmq_data_nxt1     = dmp_lsmq_data[63:0];   
  end


  // Forwarding data for cross cache line load instruction
  //
  if (wr_lb_data & (pend_entry_r == 1))
  begin
    lsmq_data_nxt1       =  fwd_data_nxt;     
  end
    lsmq_mfifo0_nxt2   = lsmq_mfifo0_r2  ; 
    lsmq_mfifo1_nxt2   = lsmq_mfifo1_r2  ; 
    lsmq_gtag_nxt2     = lsmq_gtag_r2    ; 
    lsmq_size_nxt2     = lsmq_size_r2    ; 
    lsmq_addr0_nxt2    = lsmq_addr0_r2   ; 
    lsmq_addr1_nxt2    = lsmq_addr1_r2   ; 
    lsmq_data_nxt2     = lsmq_data_r2    ; 
  if (lsmq_write & (wrentry == 2))
  begin
    lsmq_mfifo0_nxt2   = mq_entry0;    
    lsmq_mfifo1_nxt2    = mq_entry1;    
    lsmq_gtag_nxt2      = ca_grad_tag[2:0];  
  end
     
  if (lsmq_not_full && wrenable && (wrentry == 2))
  begin
    lsmq_size_nxt2     = ca_size_r[1:0];     
    lsmq_sex_nxt[2]    = ca_sex_r;    
    lsmq_addr0_nxt2    = ca_mem_addr0_r[39:0];    
    lsmq_addr1_nxt2    = ca_mem_addr1[39:0];    
    lsmq_data_nxt2     = dmp_lsmq_data[63:0];   
  end


  // Forwarding data for cross cache line load instruction
  //
  if (wr_lb_data & (pend_entry_r == 2))
  begin
    lsmq_data_nxt2       =  fwd_data_nxt;     
  end
    lsmq_mfifo0_nxt3   = lsmq_mfifo0_r3  ; 
    lsmq_mfifo1_nxt3   = lsmq_mfifo1_r3  ; 
    lsmq_gtag_nxt3     = lsmq_gtag_r3    ; 
    lsmq_size_nxt3     = lsmq_size_r3    ; 
    lsmq_addr0_nxt3    = lsmq_addr0_r3   ; 
    lsmq_addr1_nxt3    = lsmq_addr1_r3   ; 
    lsmq_data_nxt3     = lsmq_data_r3    ; 
  if (lsmq_write & (wrentry == 3))
  begin
    lsmq_mfifo0_nxt3   = mq_entry0;    
    lsmq_mfifo1_nxt3    = mq_entry1;    
    lsmq_gtag_nxt3      = ca_grad_tag[2:0];  
  end
     
  if (lsmq_not_full && wrenable && (wrentry == 3))
  begin
    lsmq_size_nxt3     = ca_size_r[1:0];     
    lsmq_sex_nxt[3]    = ca_sex_r;    
    lsmq_addr0_nxt3    = ca_mem_addr0_r[39:0];    
    lsmq_addr1_nxt3    = ca_mem_addr1[39:0];    
    lsmq_data_nxt3     = dmp_lsmq_data[63:0];   
  end


  // Forwarding data for cross cache line load instruction
  //
  if (wr_lb_data & (pend_entry_r == 3))
  begin
    lsmq_data_nxt3       =  fwd_data_nxt;     
  end
end
always @(posedge clk)
begin : lsmq_data_reg_PROC
    lsmq_mfifo0_r0  <= lsmq_mfifo0_nxt0   ; 
    lsmq_mfifo1_r0  <= lsmq_mfifo1_nxt0   ; 
    lsmq_gtag_r0    <= lsmq_gtag_nxt0     ; 
    lsmq_size_r0    <= lsmq_size_nxt0     ; 
    lsmq_addr0_r0   <= lsmq_addr0_nxt0    ; 
    lsmq_addr1_r0   <= lsmq_addr1_nxt0    ; 
    lsmq_data_r0    <= lsmq_data_nxt0     ; 
    lsmq_mfifo0_r1  <= lsmq_mfifo0_nxt1   ; 
    lsmq_mfifo1_r1  <= lsmq_mfifo1_nxt1   ; 
    lsmq_gtag_r1    <= lsmq_gtag_nxt1     ; 
    lsmq_size_r1    <= lsmq_size_nxt1     ; 
    lsmq_addr0_r1   <= lsmq_addr0_nxt1    ; 
    lsmq_addr1_r1   <= lsmq_addr1_nxt1    ; 
    lsmq_data_r1    <= lsmq_data_nxt1     ; 
    lsmq_mfifo0_r2  <= lsmq_mfifo0_nxt2   ; 
    lsmq_mfifo1_r2  <= lsmq_mfifo1_nxt2   ; 
    lsmq_gtag_r2    <= lsmq_gtag_nxt2     ; 
    lsmq_size_r2    <= lsmq_size_nxt2     ; 
    lsmq_addr0_r2   <= lsmq_addr0_nxt2    ; 
    lsmq_addr1_r2   <= lsmq_addr1_nxt2    ; 
    lsmq_data_r2    <= lsmq_data_nxt2     ; 
    lsmq_mfifo0_r3  <= lsmq_mfifo0_nxt3   ; 
    lsmq_mfifo1_r3  <= lsmq_mfifo1_nxt3   ; 
    lsmq_gtag_r3    <= lsmq_gtag_nxt3     ; 
    lsmq_size_r3    <= lsmq_size_nxt3     ; 
    lsmq_addr0_r3   <= lsmq_addr0_nxt3    ; 
    lsmq_addr1_r3   <= lsmq_addr1_nxt3    ; 
    lsmq_data_r3    <= lsmq_data_nxt3     ; 
    lsmq_sex_r       <= lsmq_sex_nxt        ; 
end
// spyglass enable_block ResetFlop-ML Ar_resetcross01

// leda NTL_RST03 on
// leda FM_1_7 on
// spyglass enable_block STARC05-2.2.3.3
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

//////////////////////////////////////////////////////////////////////////////
// Clock gate enable for write to FIFO: (1) Miss (2) Eviction (3) Flush
//
//////////////////////////////////////////////////////////////////////////////

  assign lsmq_valid = (lsmq_valid0_r | lsmq_valid1_r);
  assign lsmq_write = ca_pass && wrenable;

// Load data is for cross_line only, either hi or lo banks
//
  assign fwd_data_nxt = (fwd_addr_r[3] ?  
                         lbuf_fwd_data[32*4-1:32*2] :
                         lbuf_fwd_data[32*2-1:0]);

// Valid count from valid bit
//
always @*
begin : lsmq_valcnt_PROC
  valid_cnt[2] = 1'b0;
  valid_cnt[1:0] = {2{1'b0}};

// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  One bit incrementor

// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow
   if (lsmq_valid[0]) valid_cnt = valid_cnt + 1'b1;
   if (lsmq_valid[1]) valid_cnt = valid_cnt + 1'b1;
   if (lsmq_valid[2]) valid_cnt = valid_cnt + 1'b1;
   if (lsmq_valid[3]) valid_cnt = valid_cnt + 1'b1;
// leda W484 on
// leda BTTF_D002 on
// leda B_3200 on
end

  assign lsmq_empty = ~(| (lsmq_valid0_r | lsmq_valid1_r));
 
  // Two entry available
  // 
  assign lsmq_two_empty = (lsmq_valid == 4'b0011)
                        | (lsmq_valid == 4'b0101) 
                        | (lsmq_valid == 4'b0110)
                        | (lsmq_valid == 4'b1001)
                        | (lsmq_valid == 4'b1010)
                        | (lsmq_valid == 4'b1100); 

  // Generate full = 3 valid entries with 1 pending entry
  //
  // Valid count is 1 bit more than pointer range, i.e., 4-FIFO-->[2:0]
  // valid_cnt=3'b100=full, bit2=full, bit[1:0]=2'b11=1 entry left
  //
  assign lsmq_full = valid_cnt[2] |
                     ((& valid_cnt[1:0]) & (| dmp_lsmq_write));
  assign lsmq_not_full = ~valid_cnt[2]; 

  assign wrenable      = | dmp_lsmq_write;
  assign lsmq_wr_two   = & dmp_lsmq_write;
  assign mq_entry0     = mq_match0_val[2] ? 
                         mq_match0_val[1:0] : mq_wrptr0;

  assign mq_wr_two     = & dmp_mq_write;

// Select corresponding MQFIFO entry for Addr1 miss 
//
// It is possible that we have two writes in the MQ and a single
// write into the LSMQ.

always @*
begin : lsmq_mqentry_PROC
  casez ({mq_match1_val[2], 
          mq_match0_val[2], 
          lsmq_wr_two})
  // match w existing MQ entry
  //
  3'b1??:   mq_entry1 = mq_match1_val[1:0]; 
  // addr0 match w existing MQ entry, so addr1 uses new mq entry
  //
  3'b01?:   mq_entry1 = mq_wrptr0;          
  3'b001:   mq_entry1 = mq_wrptr1;    // 2 misses, needs 2 MQ entries
  3'b000:   mq_entry1 =   mq_wr_two
                        ? mq_wrptr1
                        : mq_wrptr0;  // 1 miss, needs 1 MQ entry
  default:  mq_entry1 = 2'b00;
  endcase  
end

// Select an empty entry to write
//
always @*
begin : lsmq_wrentry_PROC
  wrentry[1:0] = {2{1'b0}};
  wrentry_selected         = 1'b0;

  if (!lsmq_valid[0] && (!wrentry_selected))
  begin
    wrentry[1:0] = 2'd0;
    wrentry_selected         = 1'b1;
  end
  if (!lsmq_valid[1] && (!wrentry_selected))
  begin
    wrentry[1:0] = 2'd1;
    wrentry_selected         = 1'b1;
  end
  if (!lsmq_valid[2] && (!wrentry_selected))
  begin
    wrentry[1:0] = 2'd2;
    wrentry_selected         = 1'b1;
  end
  if (!lsmq_valid[3] && (!wrentry_selected))
  begin
    wrentry[1:0] = 2'd3;
    wrentry_selected         = 1'b1;
  end
end

////////////////////////////////////////////////////////////////////////////
// Asynchronous process for determining DC3 address matching
//   with previous load/store entries in LSMQ or CA stage. 
//   No forwarding from LSMQ
////////////////////////////////////////////////////////////////////////////

  // Valid load/store in dc3 that match with valid entry in FIFO
  //
  assign dc4_pend00_nxt[0] = (dmp_lsmq_write[0] & lsmq_valid0_r[0] & 
                               (lsmq_addr0_r[0][39:6]
                                == ca_mem_addr0_r[39:6]));
  assign dc4_pend01_nxt[0] = (dmp_lsmq_write[0] & lsmq_valid1_r[0] & 
                               (lsmq_addr1_r[0][39:6]
                                == ca_mem_addr0_r[39:6]));
  assign dc4_pend10_nxt[0] = (dmp_lsmq_write[1] & lsmq_valid0_r[0] & 
                               (lsmq_addr0_r[0][39:6]
                                == ca_mem_addr1[39:6]));
  assign dc4_pend11_nxt[0] = (dmp_lsmq_write[1] & lsmq_valid1_r[0] & 
                               (lsmq_addr1_r[0][39:6]
                                == ca_mem_addr1[39:6]));
  // Valid load/store in dc3 that match with valid entry in FIFO
  //
  assign dc4_pend00_nxt[1] = (dmp_lsmq_write[0] & lsmq_valid0_r[1] & 
                               (lsmq_addr0_r[1][39:6]
                                == ca_mem_addr0_r[39:6]));
  assign dc4_pend01_nxt[1] = (dmp_lsmq_write[0] & lsmq_valid1_r[1] & 
                               (lsmq_addr1_r[1][39:6]
                                == ca_mem_addr0_r[39:6]));
  assign dc4_pend10_nxt[1] = (dmp_lsmq_write[1] & lsmq_valid0_r[1] & 
                               (lsmq_addr0_r[1][39:6]
                                == ca_mem_addr1[39:6]));
  assign dc4_pend11_nxt[1] = (dmp_lsmq_write[1] & lsmq_valid1_r[1] & 
                               (lsmq_addr1_r[1][39:6]
                                == ca_mem_addr1[39:6]));
  // Valid load/store in dc3 that match with valid entry in FIFO
  //
  assign dc4_pend00_nxt[2] = (dmp_lsmq_write[0] & lsmq_valid0_r[2] & 
                               (lsmq_addr0_r[2][39:6]
                                == ca_mem_addr0_r[39:6]));
  assign dc4_pend01_nxt[2] = (dmp_lsmq_write[0] & lsmq_valid1_r[2] & 
                               (lsmq_addr1_r[2][39:6]
                                == ca_mem_addr0_r[39:6]));
  assign dc4_pend10_nxt[2] = (dmp_lsmq_write[1] & lsmq_valid0_r[2] & 
                               (lsmq_addr0_r[2][39:6]
                                == ca_mem_addr1[39:6]));
  assign dc4_pend11_nxt[2] = (dmp_lsmq_write[1] & lsmq_valid1_r[2] & 
                               (lsmq_addr1_r[2][39:6]
                                == ca_mem_addr1[39:6]));
  // Valid load/store in dc3 that match with valid entry in FIFO
  //
  assign dc4_pend00_nxt[3] = (dmp_lsmq_write[0] & lsmq_valid0_r[3] & 
                               (lsmq_addr0_r[3][39:6]
                                == ca_mem_addr0_r[39:6]));
  assign dc4_pend01_nxt[3] = (dmp_lsmq_write[0] & lsmq_valid1_r[3] & 
                               (lsmq_addr1_r[3][39:6]
                                == ca_mem_addr0_r[39:6]));
  assign dc4_pend10_nxt[3] = (dmp_lsmq_write[1] & lsmq_valid0_r[3] & 
                               (lsmq_addr0_r[3][39:6]
                                == ca_mem_addr1[39:6]));
  assign dc4_pend11_nxt[3] = (dmp_lsmq_write[1] & lsmq_valid1_r[3] & 
                               (lsmq_addr1_r[3][39:6]
                                == ca_mem_addr1[39:6]));
   
//////////////////////////////////////////////////////////////////////////////
// Asynchronous process for LSMQ to check line buffer
//
//////////////////////////////////////////////////////////////////////////////
   
// spyglass disable_block W553

  assign lsmq_pend0[0] = (| lsmq_pend00_r[0]) | (| lsmq_pend01_r[0]);
  assign lsmq_pend1[0] = (| lsmq_pend10_r[0]) | (| lsmq_pend11_r[0]);
   
  // Valid data in line buffer that match with valid entry in LSFIFO
  //
  assign match0_done[0] = (lsmq_valid0_r[0] & mq_valid &
                            (lsmq_mfifo0_r[0] == mq_rdptr));
  assign match1_done[0] = (lsmq_valid1_r[0] & mq_valid &
                            (lsmq_mfifo1_r[0] == mq_rdptr));

  assign match0[0] = (lsmq_valid0_r[0] & (~lsmq_pend0[0]) & mq_valid &
                       (lsmq_mfifo0_r[0] == mq_rdptr));
  assign match1[0] = (lsmq_valid1_r[0] & (~lsmq_pend1[0]) & mq_valid &
                       (lsmq_mfifo1_r[0] == mq_rdptr));
// Converting address into word valid for the load/store
//
always @*
begin : lsmq0_mask_PROC
  // Last 2 words of line buffer decoding
  //
  last_word[0] = (& lsmq_addr0_r[0][5:2]);
   
  case ({lsmq_size_r[0], lsmq_addr0_r[0][1:0]})
  4'b0000 : byte_mask[0] = 12'h001;
  4'b0001 : byte_mask[0] = 12'h002;
  4'b0010 : byte_mask[0] = 12'h004;
  4'b0011 : byte_mask[0] = 12'h008;
  4'b0100 : byte_mask[0] = 12'h003;
  4'b0101 : byte_mask[0] = 12'h006;
  4'b0110 : byte_mask[0] = 12'h00c;
  4'b0111 : byte_mask[0] = 12'h018;
  4'b1000 : byte_mask[0] = 12'h00f;
  4'b1001 : byte_mask[0] = 12'h01e;
  4'b1010 : byte_mask[0] = 12'h03c;
  4'b1011 : byte_mask[0] = 12'h078;
  4'b1100 : byte_mask[0] = 12'h0ff;
  4'b1101 : byte_mask[0] = 12'h1fe;
  4'b1110 : byte_mask[0] = 12'h3fc;
  4'b1111 : byte_mask[0] = 12'h7f8;
  default : byte_mask[0] = 12'h000;
  endcase  

  nxt_last_word[0] = (& lsmq_addr0_r[0][5:3]) 
                      & (~lsmq_addr0_r[0][2]);
  // Decode into line buffer write mask (8 bytes)
  //
  casez ({match0[0], last_word[0], nxt_last_word[0]})
  3'b100 : align_mask[0] = byte_mask[0];
  3'b101 : align_mask[0] = {4'h0,  byte_mask[0][7:0]};
  3'b110 : align_mask[0] = {8'h00, byte_mask[0][3:0]};
  3'b001 : align_mask[0] = {8'h00, byte_mask[0][11:8]};
  3'b010 : align_mask[0] = {4'h0,  byte_mask[0][11:4]};
  default: align_mask[0] = 12'h000;
  endcase  

   
  casez ({lsmq_size_r[0], lsmq_addr0_r[0][1:0]})
  4'b00?? : word_valid[0] = 3'b001;
  4'b010? : word_valid[0] = 3'b001;
  4'b0110 : word_valid[0] = 3'b001;
  4'b0111 : word_valid[0] = 3'b011;
  4'b1000 : word_valid[0] = 3'b001;
  4'b1001 : word_valid[0] = 3'b011;
  4'b101? : word_valid[0] = 3'b011;
  4'b1100 : word_valid[0] = 3'b011;
  4'b1101 : word_valid[0] = 3'b111;
  4'b111? : word_valid[0] = 3'b111;
  default : word_valid[0] = 3'b000;
  endcase  

  word0_mask[0] = {{15-2{1'b0}}, word_valid[0]};
  word1_mask[0] = {{15-1{1'b0}}, word_valid[0][2:1]};
  word2_mask[0] = {{15{1'b0}},   word_valid[0][2]};

// leda W244 off   
// LMD: Shift by non-constant
// LJ:  Shift by address is needed for proper functionality
  lsmq_wd0mask[0] = word0_mask[0] << lsmq_addr0_r[0][5:2];
// leda W244 on  
  lsmq_wd1mask[0] = lsmq_addr0_r[0][2] ? word1_mask[0] : word2_mask[0];
   
  // Byte   -> never crosses
  // Half   -> crosses when [(11111)]
  // Word   -> crosses when [(111, > 00)]
  // Double -> crosses when [(11,  > 000)]
  //
  casez (lsmq_size_r[0])
  2'b01  : lsmq_line_cross[0] =  (& lsmq_addr0_r[0][5:0]);
  2'b10  : lsmq_line_cross[0] = ((& lsmq_addr0_r[0][5:2])
                                & (| lsmq_addr0_r[0][1:0]));
  2'b11  : lsmq_line_cross[0] = ((& lsmq_addr0_r[0][5:3])
                                & (| lsmq_addr0_r[0][2:0]));
  default: lsmq_line_cross[0] = 1'b0;
  endcase  
  
  // [3:0] is bank select for data from line buffer, 32-bit banks
  // [7:4] is bank select for data from LSMQ, partial data from LSMQ
  //
  casez ({match0[0], match1[0], lsmq_line_cross[0]})
  3'b1?0 : fwd_bank[0] = 8'b00001111; 
  3'b1?1 : fwd_bank[0] = 8'b00111100;
  3'b01? : fwd_bank[0] = 8'b11000011;
  default: fwd_bank[0] = 8'b00000000;
  endcase  

  casez ({lsmq_ld_done, pend_req_r})
  2'b1?  : lsmq_drdy_nxt[0] = lsmq_drdy[0] & (~ptr_dec[0]); 
  2'b01  : lsmq_drdy_nxt[0] = ptr_dec[0]; 
  2'b00  : lsmq_drdy_nxt[0] = lsmq_drdy[0]; 
  default: lsmq_drdy_nxt[0] = 1'b0; 
  endcase  

end

  // Compare to valid words in line buffer
  // In case of lb_err_r, fake like all is valid
  //
  assign lsmq_dvalid0[0] = (((lsmq_wd0mask[0] & lb_valid_r)==lsmq_wd0mask[0])| lb_err_r);
  assign lsmq_dvalid1[0] = (((lsmq_wd1mask[0] & lb_valid_r)==lsmq_wd1mask[0])| lb_err_r);

  assign lsmq_drdy[0] = (  (match0[0] & lsmq_dvalid0[0]) 
                          | (match1[0] & lsmq_dvalid1[0]));
  
  assign st_nxt[0]    =   lsmq_drdy[0] 
                         & (~lsmq_load_r[0]) 
                         & lsmq_store_r[0];

  assign ld_nxt[0]    =    lsmq_drdy_nxt[0]
                         &  lsmq_load_r[0];


  assign lsmq_pend0[1] = (| lsmq_pend00_r[1]) | (| lsmq_pend01_r[1]);
  assign lsmq_pend1[1] = (| lsmq_pend10_r[1]) | (| lsmq_pend11_r[1]);
   
  // Valid data in line buffer that match with valid entry in LSFIFO
  //
  assign match0_done[1] = (lsmq_valid0_r[1] & mq_valid &
                            (lsmq_mfifo0_r[1] == mq_rdptr));
  assign match1_done[1] = (lsmq_valid1_r[1] & mq_valid &
                            (lsmq_mfifo1_r[1] == mq_rdptr));

  assign match0[1] = (lsmq_valid0_r[1] & (~lsmq_pend0[1]) & mq_valid &
                       (lsmq_mfifo0_r[1] == mq_rdptr));
  assign match1[1] = (lsmq_valid1_r[1] & (~lsmq_pend1[1]) & mq_valid &
                       (lsmq_mfifo1_r[1] == mq_rdptr));
// Converting address into word valid for the load/store
//
always @*
begin : lsmq1_mask_PROC
  // Last 2 words of line buffer decoding
  //
  last_word[1] = (& lsmq_addr0_r[1][5:2]);
   
  case ({lsmq_size_r[1], lsmq_addr0_r[1][1:0]})
  4'b0000 : byte_mask[1] = 12'h001;
  4'b0001 : byte_mask[1] = 12'h002;
  4'b0010 : byte_mask[1] = 12'h004;
  4'b0011 : byte_mask[1] = 12'h008;
  4'b0100 : byte_mask[1] = 12'h003;
  4'b0101 : byte_mask[1] = 12'h006;
  4'b0110 : byte_mask[1] = 12'h00c;
  4'b0111 : byte_mask[1] = 12'h018;
  4'b1000 : byte_mask[1] = 12'h00f;
  4'b1001 : byte_mask[1] = 12'h01e;
  4'b1010 : byte_mask[1] = 12'h03c;
  4'b1011 : byte_mask[1] = 12'h078;
  4'b1100 : byte_mask[1] = 12'h0ff;
  4'b1101 : byte_mask[1] = 12'h1fe;
  4'b1110 : byte_mask[1] = 12'h3fc;
  4'b1111 : byte_mask[1] = 12'h7f8;
  default : byte_mask[1] = 12'h000;
  endcase  

  nxt_last_word[1] = (& lsmq_addr0_r[1][5:3]) 
                      & (~lsmq_addr0_r[1][2]);
  // Decode into line buffer write mask (8 bytes)
  //
  casez ({match0[1], last_word[1], nxt_last_word[1]})
  3'b100 : align_mask[1] = byte_mask[1];
  3'b101 : align_mask[1] = {4'h0,  byte_mask[1][7:0]};
  3'b110 : align_mask[1] = {8'h00, byte_mask[1][3:0]};
  3'b001 : align_mask[1] = {8'h00, byte_mask[1][11:8]};
  3'b010 : align_mask[1] = {4'h0,  byte_mask[1][11:4]};
  default: align_mask[1] = 12'h000;
  endcase  

   
  casez ({lsmq_size_r[1], lsmq_addr0_r[1][1:0]})
  4'b00?? : word_valid[1] = 3'b001;
  4'b010? : word_valid[1] = 3'b001;
  4'b0110 : word_valid[1] = 3'b001;
  4'b0111 : word_valid[1] = 3'b011;
  4'b1000 : word_valid[1] = 3'b001;
  4'b1001 : word_valid[1] = 3'b011;
  4'b101? : word_valid[1] = 3'b011;
  4'b1100 : word_valid[1] = 3'b011;
  4'b1101 : word_valid[1] = 3'b111;
  4'b111? : word_valid[1] = 3'b111;
  default : word_valid[1] = 3'b000;
  endcase  

  word0_mask[1] = {{15-2{1'b0}}, word_valid[1]};
  word1_mask[1] = {{15-1{1'b0}}, word_valid[1][2:1]};
  word2_mask[1] = {{15{1'b0}},   word_valid[1][2]};

// leda W244 off   
// LMD: Shift by non-constant
// LJ:  Shift by address is needed for proper functionality
  lsmq_wd0mask[1] = word0_mask[1] << lsmq_addr0_r[1][5:2];
// leda W244 on  
  lsmq_wd1mask[1] = lsmq_addr0_r[1][2] ? word1_mask[1] : word2_mask[1];
   
  // Byte   -> never crosses
  // Half   -> crosses when [(11111)]
  // Word   -> crosses when [(111, > 00)]
  // Double -> crosses when [(11,  > 000)]
  //
  casez (lsmq_size_r[1])
  2'b01  : lsmq_line_cross[1] =  (& lsmq_addr0_r[1][5:0]);
  2'b10  : lsmq_line_cross[1] = ((& lsmq_addr0_r[1][5:2])
                                & (| lsmq_addr0_r[1][1:0]));
  2'b11  : lsmq_line_cross[1] = ((& lsmq_addr0_r[1][5:3])
                                & (| lsmq_addr0_r[1][2:0]));
  default: lsmq_line_cross[1] = 1'b0;
  endcase  
  
  // [3:0] is bank select for data from line buffer, 32-bit banks
  // [7:4] is bank select for data from LSMQ, partial data from LSMQ
  //
  casez ({match0[1], match1[1], lsmq_line_cross[1]})
  3'b1?0 : fwd_bank[1] = 8'b00001111; 
  3'b1?1 : fwd_bank[1] = 8'b00111100;
  3'b01? : fwd_bank[1] = 8'b11000011;
  default: fwd_bank[1] = 8'b00000000;
  endcase  

  casez ({lsmq_ld_done, pend_req_r})
  2'b1?  : lsmq_drdy_nxt[1] = lsmq_drdy[1] & (~ptr_dec[1]); 
  2'b01  : lsmq_drdy_nxt[1] = ptr_dec[1]; 
  2'b00  : lsmq_drdy_nxt[1] = lsmq_drdy[1]; 
  default: lsmq_drdy_nxt[1] = 1'b0; 
  endcase  

end

  // Compare to valid words in line buffer
  // In case of lb_err_r, fake like all is valid
  //
  assign lsmq_dvalid0[1] = (((lsmq_wd0mask[1] & lb_valid_r)==lsmq_wd0mask[1])| lb_err_r);
  assign lsmq_dvalid1[1] = (((lsmq_wd1mask[1] & lb_valid_r)==lsmq_wd1mask[1])| lb_err_r);

  assign lsmq_drdy[1] = (  (match0[1] & lsmq_dvalid0[1]) 
                          | (match1[1] & lsmq_dvalid1[1]));
  
  assign st_nxt[1]    =   lsmq_drdy[1] 
                         & (~lsmq_load_r[1]) 
                         & lsmq_store_r[1];

  assign ld_nxt[1]    =    lsmq_drdy_nxt[1]
                         &  lsmq_load_r[1];


  assign lsmq_pend0[2] = (| lsmq_pend00_r[2]) | (| lsmq_pend01_r[2]);
  assign lsmq_pend1[2] = (| lsmq_pend10_r[2]) | (| lsmq_pend11_r[2]);
   
  // Valid data in line buffer that match with valid entry in LSFIFO
  //
  assign match0_done[2] = (lsmq_valid0_r[2] & mq_valid &
                            (lsmq_mfifo0_r[2] == mq_rdptr));
  assign match1_done[2] = (lsmq_valid1_r[2] & mq_valid &
                            (lsmq_mfifo1_r[2] == mq_rdptr));

  assign match0[2] = (lsmq_valid0_r[2] & (~lsmq_pend0[2]) & mq_valid &
                       (lsmq_mfifo0_r[2] == mq_rdptr));
  assign match1[2] = (lsmq_valid1_r[2] & (~lsmq_pend1[2]) & mq_valid &
                       (lsmq_mfifo1_r[2] == mq_rdptr));
// Converting address into word valid for the load/store
//
always @*
begin : lsmq2_mask_PROC
  // Last 2 words of line buffer decoding
  //
  last_word[2] = (& lsmq_addr0_r[2][5:2]);
   
  case ({lsmq_size_r[2], lsmq_addr0_r[2][1:0]})
  4'b0000 : byte_mask[2] = 12'h001;
  4'b0001 : byte_mask[2] = 12'h002;
  4'b0010 : byte_mask[2] = 12'h004;
  4'b0011 : byte_mask[2] = 12'h008;
  4'b0100 : byte_mask[2] = 12'h003;
  4'b0101 : byte_mask[2] = 12'h006;
  4'b0110 : byte_mask[2] = 12'h00c;
  4'b0111 : byte_mask[2] = 12'h018;
  4'b1000 : byte_mask[2] = 12'h00f;
  4'b1001 : byte_mask[2] = 12'h01e;
  4'b1010 : byte_mask[2] = 12'h03c;
  4'b1011 : byte_mask[2] = 12'h078;
  4'b1100 : byte_mask[2] = 12'h0ff;
  4'b1101 : byte_mask[2] = 12'h1fe;
  4'b1110 : byte_mask[2] = 12'h3fc;
  4'b1111 : byte_mask[2] = 12'h7f8;
  default : byte_mask[2] = 12'h000;
  endcase  

  nxt_last_word[2] = (& lsmq_addr0_r[2][5:3]) 
                      & (~lsmq_addr0_r[2][2]);
  // Decode into line buffer write mask (8 bytes)
  //
  casez ({match0[2], last_word[2], nxt_last_word[2]})
  3'b100 : align_mask[2] = byte_mask[2];
  3'b101 : align_mask[2] = {4'h0,  byte_mask[2][7:0]};
  3'b110 : align_mask[2] = {8'h00, byte_mask[2][3:0]};
  3'b001 : align_mask[2] = {8'h00, byte_mask[2][11:8]};
  3'b010 : align_mask[2] = {4'h0,  byte_mask[2][11:4]};
  default: align_mask[2] = 12'h000;
  endcase  

   
  casez ({lsmq_size_r[2], lsmq_addr0_r[2][1:0]})
  4'b00?? : word_valid[2] = 3'b001;
  4'b010? : word_valid[2] = 3'b001;
  4'b0110 : word_valid[2] = 3'b001;
  4'b0111 : word_valid[2] = 3'b011;
  4'b1000 : word_valid[2] = 3'b001;
  4'b1001 : word_valid[2] = 3'b011;
  4'b101? : word_valid[2] = 3'b011;
  4'b1100 : word_valid[2] = 3'b011;
  4'b1101 : word_valid[2] = 3'b111;
  4'b111? : word_valid[2] = 3'b111;
  default : word_valid[2] = 3'b000;
  endcase  

  word0_mask[2] = {{15-2{1'b0}}, word_valid[2]};
  word1_mask[2] = {{15-1{1'b0}}, word_valid[2][2:1]};
  word2_mask[2] = {{15{1'b0}},   word_valid[2][2]};

// leda W244 off   
// LMD: Shift by non-constant
// LJ:  Shift by address is needed for proper functionality
  lsmq_wd0mask[2] = word0_mask[2] << lsmq_addr0_r[2][5:2];
// leda W244 on  
  lsmq_wd1mask[2] = lsmq_addr0_r[2][2] ? word1_mask[2] : word2_mask[2];
   
  // Byte   -> never crosses
  // Half   -> crosses when [(11111)]
  // Word   -> crosses when [(111, > 00)]
  // Double -> crosses when [(11,  > 000)]
  //
  casez (lsmq_size_r[2])
  2'b01  : lsmq_line_cross[2] =  (& lsmq_addr0_r[2][5:0]);
  2'b10  : lsmq_line_cross[2] = ((& lsmq_addr0_r[2][5:2])
                                & (| lsmq_addr0_r[2][1:0]));
  2'b11  : lsmq_line_cross[2] = ((& lsmq_addr0_r[2][5:3])
                                & (| lsmq_addr0_r[2][2:0]));
  default: lsmq_line_cross[2] = 1'b0;
  endcase  
  
  // [3:0] is bank select for data from line buffer, 32-bit banks
  // [7:4] is bank select for data from LSMQ, partial data from LSMQ
  //
  casez ({match0[2], match1[2], lsmq_line_cross[2]})
  3'b1?0 : fwd_bank[2] = 8'b00001111; 
  3'b1?1 : fwd_bank[2] = 8'b00111100;
  3'b01? : fwd_bank[2] = 8'b11000011;
  default: fwd_bank[2] = 8'b00000000;
  endcase  

  casez ({lsmq_ld_done, pend_req_r})
  2'b1?  : lsmq_drdy_nxt[2] = lsmq_drdy[2] & (~ptr_dec[2]); 
  2'b01  : lsmq_drdy_nxt[2] = ptr_dec[2]; 
  2'b00  : lsmq_drdy_nxt[2] = lsmq_drdy[2]; 
  default: lsmq_drdy_nxt[2] = 1'b0; 
  endcase  

end

  // Compare to valid words in line buffer
  // In case of lb_err_r, fake like all is valid
  //
  assign lsmq_dvalid0[2] = (((lsmq_wd0mask[2] & lb_valid_r)==lsmq_wd0mask[2])| lb_err_r);
  assign lsmq_dvalid1[2] = (((lsmq_wd1mask[2] & lb_valid_r)==lsmq_wd1mask[2])| lb_err_r);

  assign lsmq_drdy[2] = (  (match0[2] & lsmq_dvalid0[2]) 
                          | (match1[2] & lsmq_dvalid1[2]));
  
  assign st_nxt[2]    =   lsmq_drdy[2] 
                         & (~lsmq_load_r[2]) 
                         & lsmq_store_r[2];

  assign ld_nxt[2]    =    lsmq_drdy_nxt[2]
                         &  lsmq_load_r[2];


  assign lsmq_pend0[3] = (| lsmq_pend00_r[3]) | (| lsmq_pend01_r[3]);
  assign lsmq_pend1[3] = (| lsmq_pend10_r[3]) | (| lsmq_pend11_r[3]);
   
  // Valid data in line buffer that match with valid entry in LSFIFO
  //
  assign match0_done[3] = (lsmq_valid0_r[3] & mq_valid &
                            (lsmq_mfifo0_r[3] == mq_rdptr));
  assign match1_done[3] = (lsmq_valid1_r[3] & mq_valid &
                            (lsmq_mfifo1_r[3] == mq_rdptr));

  assign match0[3] = (lsmq_valid0_r[3] & (~lsmq_pend0[3]) & mq_valid &
                       (lsmq_mfifo0_r[3] == mq_rdptr));
  assign match1[3] = (lsmq_valid1_r[3] & (~lsmq_pend1[3]) & mq_valid &
                       (lsmq_mfifo1_r[3] == mq_rdptr));
// Converting address into word valid for the load/store
//
always @*
begin : lsmq3_mask_PROC
  // Last 2 words of line buffer decoding
  //
  last_word[3] = (& lsmq_addr0_r[3][5:2]);
   
  case ({lsmq_size_r[3], lsmq_addr0_r[3][1:0]})
  4'b0000 : byte_mask[3] = 12'h001;
  4'b0001 : byte_mask[3] = 12'h002;
  4'b0010 : byte_mask[3] = 12'h004;
  4'b0011 : byte_mask[3] = 12'h008;
  4'b0100 : byte_mask[3] = 12'h003;
  4'b0101 : byte_mask[3] = 12'h006;
  4'b0110 : byte_mask[3] = 12'h00c;
  4'b0111 : byte_mask[3] = 12'h018;
  4'b1000 : byte_mask[3] = 12'h00f;
  4'b1001 : byte_mask[3] = 12'h01e;
  4'b1010 : byte_mask[3] = 12'h03c;
  4'b1011 : byte_mask[3] = 12'h078;
  4'b1100 : byte_mask[3] = 12'h0ff;
  4'b1101 : byte_mask[3] = 12'h1fe;
  4'b1110 : byte_mask[3] = 12'h3fc;
  4'b1111 : byte_mask[3] = 12'h7f8;
  default : byte_mask[3] = 12'h000;
  endcase  

  nxt_last_word[3] = (& lsmq_addr0_r[3][5:3]) 
                      & (~lsmq_addr0_r[3][2]);
  // Decode into line buffer write mask (8 bytes)
  //
  casez ({match0[3], last_word[3], nxt_last_word[3]})
  3'b100 : align_mask[3] = byte_mask[3];
  3'b101 : align_mask[3] = {4'h0,  byte_mask[3][7:0]};
  3'b110 : align_mask[3] = {8'h00, byte_mask[3][3:0]};
  3'b001 : align_mask[3] = {8'h00, byte_mask[3][11:8]};
  3'b010 : align_mask[3] = {4'h0,  byte_mask[3][11:4]};
  default: align_mask[3] = 12'h000;
  endcase  

   
  casez ({lsmq_size_r[3], lsmq_addr0_r[3][1:0]})
  4'b00?? : word_valid[3] = 3'b001;
  4'b010? : word_valid[3] = 3'b001;
  4'b0110 : word_valid[3] = 3'b001;
  4'b0111 : word_valid[3] = 3'b011;
  4'b1000 : word_valid[3] = 3'b001;
  4'b1001 : word_valid[3] = 3'b011;
  4'b101? : word_valid[3] = 3'b011;
  4'b1100 : word_valid[3] = 3'b011;
  4'b1101 : word_valid[3] = 3'b111;
  4'b111? : word_valid[3] = 3'b111;
  default : word_valid[3] = 3'b000;
  endcase  

  word0_mask[3] = {{15-2{1'b0}}, word_valid[3]};
  word1_mask[3] = {{15-1{1'b0}}, word_valid[3][2:1]};
  word2_mask[3] = {{15{1'b0}},   word_valid[3][2]};

// leda W244 off   
// LMD: Shift by non-constant
// LJ:  Shift by address is needed for proper functionality
  lsmq_wd0mask[3] = word0_mask[3] << lsmq_addr0_r[3][5:2];
// leda W244 on  
  lsmq_wd1mask[3] = lsmq_addr0_r[3][2] ? word1_mask[3] : word2_mask[3];
   
  // Byte   -> never crosses
  // Half   -> crosses when [(11111)]
  // Word   -> crosses when [(111, > 00)]
  // Double -> crosses when [(11,  > 000)]
  //
  casez (lsmq_size_r[3])
  2'b01  : lsmq_line_cross[3] =  (& lsmq_addr0_r[3][5:0]);
  2'b10  : lsmq_line_cross[3] = ((& lsmq_addr0_r[3][5:2])
                                & (| lsmq_addr0_r[3][1:0]));
  2'b11  : lsmq_line_cross[3] = ((& lsmq_addr0_r[3][5:3])
                                & (| lsmq_addr0_r[3][2:0]));
  default: lsmq_line_cross[3] = 1'b0;
  endcase  
  
  // [3:0] is bank select for data from line buffer, 32-bit banks
  // [7:4] is bank select for data from LSMQ, partial data from LSMQ
  //
  casez ({match0[3], match1[3], lsmq_line_cross[3]})
  3'b1?0 : fwd_bank[3] = 8'b00001111; 
  3'b1?1 : fwd_bank[3] = 8'b00111100;
  3'b01? : fwd_bank[3] = 8'b11000011;
  default: fwd_bank[3] = 8'b00000000;
  endcase  

  casez ({lsmq_ld_done, pend_req_r})
  2'b1?  : lsmq_drdy_nxt[3] = lsmq_drdy[3] & (~ptr_dec[3]); 
  2'b01  : lsmq_drdy_nxt[3] = ptr_dec[3]; 
  2'b00  : lsmq_drdy_nxt[3] = lsmq_drdy[3]; 
  default: lsmq_drdy_nxt[3] = 1'b0; 
  endcase  

end

  // Compare to valid words in line buffer
  // In case of lb_err_r, fake like all is valid
  //
  assign lsmq_dvalid0[3] = (((lsmq_wd0mask[3] & lb_valid_r)==lsmq_wd0mask[3])| lb_err_r);
  assign lsmq_dvalid1[3] = (((lsmq_wd1mask[3] & lb_valid_r)==lsmq_wd1mask[3])| lb_err_r);

  assign lsmq_drdy[3] = (  (match0[3] & lsmq_dvalid0[3]) 
                          | (match1[3] & lsmq_dvalid1[3]));
  
  assign st_nxt[3]    =   lsmq_drdy[3] 
                         & (~lsmq_load_r[3]) 
                         & lsmq_store_r[3];

  assign ld_nxt[3]    =    lsmq_drdy_nxt[3]
                         &  lsmq_load_r[3];

// spyglass enable_block W553

// The first match will the content of LSMQ for request. Start with rdptr
// In-order retire of the entries.
//
always @*
begin : lsmq_rdptr_PROC
  ldentry[1:0] = {2{1'b0}};
  ldentry_selected         = 1'b0;
  stentry[1:0] = {2{1'b0}};
  stentry_selected         = 1'b0;

  if (ld_nxt[0] && (!ldentry_selected))
  begin
    ldentry[1:0] = 2'd0;
    ldentry_selected         = 1'b1;
  end
  if (st_nxt[0] && (!stentry_selected))
  begin
    stentry[1:0] = 2'd0;
    stentry_selected         = 1'b1;
  end
  if (ld_nxt[1] && (!ldentry_selected))
  begin
    ldentry[1:0] = 2'd1;
    ldentry_selected         = 1'b1;
  end
  if (st_nxt[1] && (!stentry_selected))
  begin
    stentry[1:0] = 2'd1;
    stentry_selected         = 1'b1;
  end
  if (ld_nxt[2] && (!ldentry_selected))
  begin
    ldentry[1:0] = 2'd2;
    ldentry_selected         = 1'b1;
  end
  if (st_nxt[2] && (!stentry_selected))
  begin
    stentry[1:0] = 2'd2;
    stentry_selected         = 1'b1;
  end
  if (ld_nxt[3] && (!ldentry_selected))
  begin
    ldentry[1:0] = 2'd3;
    ldentry_selected         = 1'b1;
  end
  if (st_nxt[3] && (!stentry_selected))
  begin
    stentry[1:0] = 2'd3;
    stentry_selected         = 1'b1;
  end
end

  // (1) The LSMQ is full, the top of the MQ is matching with the DC4 instruction,
  // there is no pending entries in the LSMQ, then replay the instruction in CA
  //
  // (2) The LSMQ is full, there is a set conflict between DC4 and DMU and no addr match.
  //     Hence the DC4 can be replayed.


  // lsmq_full_qual is set when lsmq is full or there is a line cross in DC4 and only one space left in LSMQ
  //
  wire   lsmq_full_qual;
  assign lsmq_full_qual = lsmq_full
                        | (  (&valid_cnt[1:0]) 
                           & dc4_dt_miss_r
                           & dc4_dt_line_cross_r);    

  assign dc4_lsmq_nomatch_replay =  (  dc4_mq_addr_match
                                     & lsmq_full_qual
                                     & (&lb_valid_r)
                                     & (~(lsmq_match0 | lsmq_match1))
                                    )                                           // (1)
                                 |  (  dc4_mq_set_match
//                                     & lsmq_full_qual
                                    );                                         // (2)

  // If no entry in LSMQ match with MQ, then the current line buffer
  // has no pending read/write, can be written to DC now.
  //
  assign mq_match0_top = (mq_match0_val[2] & dmp_lsmq_write[0] & 
                          (mq_match0_val[1:0]==mq_rdptr));
  assign mq_match1_top = (mq_match1_val[2] & dmp_lsmq_write[1] & 
                          (mq_match1_val[1:0]==mq_rdptr));
  
  // LSMQ done depends on the entries that are in the LSMQ
  // as we no longer support DC4 instructions updating the linebuffer; hence they do not depend on
  // ca_pass or ca_enable 
  // 
  assign lsmq_done = ~(  (| match0_done) 
                       | (| match1_done));

  // store is in the same cycle as match is detected while load is in
  // next cycle. In addition, store does not have graduation tag.
  //
  assign st_req_nxt = (| st_nxt) & (~pend_req_r); 
  assign lsmq_st_clr0 =   lsmq_match0 & st_req_nxt
                        ;
  assign lsmq_st_clr1 =  lsmq_match1 & st_req_nxt;  
  assign lsmq_st_addr = (lsmq_match0_r ? 
                         lsmq_addr0_r[st_entry_r][5:2] : 
                         {5-1{1'b0}});
  assign data_nxt   = lsmq_data_r[st_entry_r];
  // Load data is load as-is from data cache bank and will write
  // back to the same cache bank position before output align
  //   Seperate load from store data for speed path
  //
  assign lsmq_ld_data  = data_nxt;
  assign lsmq_data     = lsmq_match1_r ? data1_shf : data0_shf;
 
always @*
begin : lsmq_rddata_PROC
  // Store data shift left for byte position, 
  //
  case (lsmq_addr0_r[st_entry_r][1:0])
  2'b00  : data0_shf = {{32{1'b0}}, data_nxt};
  2'b01  : data0_shf = {{24{1'b0}}, data_nxt,  {8{1'b0}}};
  2'b10  : data0_shf = {{16{1'b0}}, data_nxt, {16{1'b0}}};
  2'b11  : data0_shf = { {8{1'b0}}, data_nxt, {24{1'b0}}};
  default: data0_shf = {{32{1'b0}}, data_nxt};
  endcase  

  // Then extracting the upper 32 or 64-bit if crossing line
  data1_shf = lsmq_addr0_r[st_entry_r][2] ? 
              {{32{1'b0}}, data0_shf[32*3-1:32]} :
              {{64{1'b0}}, data0_shf[32*3-1:32*2]};   
end
   
  // Convert pointer to 1-hot decode
  //
// leda W244 off   
// LMD: Shift by non-constant
// LJ:  1-hot decode function
  assign ptr_dec = {{4-1{1'b0}}, 1'b1} << pend_entry_r;
// leda W244 on   
  // If both banks are valid, then the data is read from line buffer
  // to LSMQ, and 1 valid bit is clear.
  //
  assign part_ld_nxt = (lsmq_valid0_r[rdentry] & 
                        lsmq_valid1_r[rdentry] & 
                       (| ld_nxt));               // 2 ld misses
  assign lsmq_ld_done = rb_ack_r | part_ld_r;
  assign lsmq_ld_req = (((| ld_nxt) & (~lsmq_st_req)) | 
                        (pend_req_r & (~(rb_ack_r | part_ld_r))));
  assign mq_rb_req    = lsmq_ld_req & (~part_ld_nxt);
  assign mq_rb_err    =   lsmq_ld_req 
                        & (~part_ld_nxt) 
                        & (lb_err_r | lsmq_part_err_r);
  
  assign lsmq_st_err  = lsmq_st_req & lb_err_r;
   
  assign lsmq_ld_clr0 = (lsmq_match0_r & pend_req_r & 
                        (rb_ack_r | part_ld_r));  // pend_entry_r
  assign lsmq_ld_clr1 = (lsmq_match1_r & pend_req_r &
                        (rb_ack_r | part_ld_r));  // pend_entry_r 
  assign wr_lb_data   = pend_req_r & part_ld_r;
   
  // Read out all control signals for load and store instruction.
  //
  assign rdentry = lsmq_ld_req ? ldentry : stentry;

  assign wr_mask_nxt  = align_mask[rdentry];

  assign lsmq_match0  = match0[rdentry];
  assign lsmq_match1  = match1[rdentry];
  assign lsmq_addr    = (lsmq_match0 ? 
                         lsmq_addr0_r[rdentry][5:2] : 
                         {5-1{1'b0}});
  assign mq_rb_addr   = lsmq_addr0_r[rdentry][39:0];
   
  assign mq_rb_tag     = lsmq_gtag_r[rdentry];
  assign mq_sex        = lsmq_sex_r[rdentry];
  assign mq_size       = lsmq_size_r[rdentry];
  assign lsmq_fwd_bank = fwd_bank[rdentry];
  assign lsmq_bank_lo_nxt  = (| lsmq_fwd_bank[5:4]);
  assign lsmq_bank_hi_nxt  = (| lsmq_fwd_bank[7:6]);

always @*
begin
    pend_req_next       = lsmq_ld_req | (pend_req_r & (~(rb_ack_r | part_ld_r)));
    pend_entry_next     = ((pend_req_r && (!(rb_ack_r || part_ld_r))) ? 
                           pend_entry_r : rdentry);
    lsmq_bank_hi_next   = ((pend_req_r && (!(rb_ack_r || part_ld_r))) ? 
                           lsmq_bank_hi : lsmq_bank_hi_nxt);
    lsmq_bank_lo_next   = ((pend_req_r && (!(rb_ack_r || part_ld_r))) ? 
                           lsmq_bank_lo : lsmq_bank_lo_nxt);
    rb_ack_next         = mq_rb_ack;
    part_ld_next        = part_ld_nxt;
    lsmq_match0_next    = lsmq_match0;
    lsmq_match1_next    = lsmq_match1;
    lsmq_st_req_next    = st_req_nxt;

    st_entry_next       = rdentry;
    lsmq_wr_mask_next   = wr_mask_nxt;
    fwd_addr_next       = lsmq_addr[3:2];

end

   // Keeping request until acknowledge by gradruate buffer
   //
always @(posedge clk or
         posedge rst_a)
begin: lsmqreq_sync_PROC
  if (rst_a == 1'b1)
  begin
    pend_req_r    <= 1'b0;
    pend_entry_r  <= {2{1'b0}};
    lsmq_bank_hi  <= 1'b0;
    lsmq_bank_lo  <= 1'b0;
    rb_ack_r      <= 1'b0;
    part_ld_r     <= 1'b0;
    lsmq_match0_r <= 1'b0;
    lsmq_match1_r <= 1'b0;
    lsmq_st_req   <= 1'b0;
    st_entry_r    <= {2{1'b0}};
    lsmq_wr_mask  <= {12{1'b0}};
    fwd_addr_r    <= 2'h0;
  end
  else
  begin
    pend_req_r    <= pend_req_next     ; 
    pend_entry_r  <= pend_entry_next   ; 
    lsmq_bank_hi  <= lsmq_bank_hi_next ; 
    lsmq_bank_lo  <= lsmq_bank_lo_next ; 
    rb_ack_r      <= rb_ack_next       ; 
    part_ld_r     <= part_ld_next      ; 
    lsmq_match0_r <= lsmq_match0_next  ; 
    lsmq_match1_r <= lsmq_match1_next  ; 
    lsmq_st_req   <= lsmq_st_req_next  ; 
    st_entry_r    <= st_entry_next     ; 
    lsmq_wr_mask  <= lsmq_wr_mask_next ; 
    fwd_addr_r    <= fwd_addr_next     ; 

  end
end
endmodule // alb_dmp_lsmq_fifo

