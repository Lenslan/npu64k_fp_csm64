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
//   ALB_DMP_LINE_BUF                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements the data cache line buffer.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_line_buf.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  rst: "rst_a", edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_dmp_line_buf (
// leda NTL_CON13C off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used
  ////////// General input signals ///////////////////////////////////////////
  //
  input                          clk,           // clock
  input                          rst_a,         // reset

  ////////// Refill Read Data Channel ///////////////////////////////////////
  //
  input                          rf_rd_valid,  // read data ready
  input                          rf_rd_last,   // read last packet
  input                          rf_err_rd,    // read bus error
  input [`npuarc_RF_CB_DATA_RANGE]      rf_rd_data,   // read data
  output wire                    rf_rd_accept, // read accept

 
  ////////// Line Buffer write to Data Cache ////////////////////////////////
  //
  input                          lbuf_initial,  // initialize LB entry
  input [`npuarc_DC_BLK_WRD_RANGE]      mq_addr,       // critical word to BIU
  input                          mq_pre_alloc,  // pre-alloc on top of mq
 
  input                          lbuf_rd_valid, // Lbuf --> Dc 
  input                          lbuf_rd_last,  // Lbuf --> Dc 
  input                          lbuf_rd_last_r,// Lbuf --> Dc 
  
  output wire [`npuarc_DC_DATA_RANGE]   lbuf_rd_data,  // read data --> DC  
  output wire [`npuarc_DC_DATA_RANGE]   lbuf_fwd_data, // read data --> load 
  output reg  [`npuarc_LBUF_FIFO_RANGE] lb_valid_r,    // Valid word in line buffer
  
  ////////// Request to read/write from LSMQ  //////////////////////////////
  //
  input                          lsmq_ld_req,   // load request to Lbuf 
  input                          lsmq_st_req,   // store request to Lbuf 
  input [`npuarc_LBWR_MASK_RANGE]       lsmq_wr_mask,  // write mask (64-bit)
  input [`npuarc_DC_BLK_WRD_RANGE]      lsmq_addr,     // Address of first word
  input [`npuarc_DC_BLK_WRD_RANGE]      lsmq_st_addr,  // St addr of first word
  input [`npuarc_LBWR_DATA_RANGE]       lsmq_data,     // write data from store
  
  ////////// Forward Request from MQ load hit on line buffer  /////////////
  //
  input [`npuarc_DC_BLK_WRD_RANGE]      mq_fwd_addr,   // Addr of 1st forward word
  input                          mq_lbfwd,      // Forward from Lbuf
  input [`npuarc_LBWR_MASK_RANGE]       mq_stmask,     // write mask (64-bit)
  input                          mq_lbstore,    // current store in x3
  input                          mq_addr0_hit,  // Hit for x3 addr0
  input                          x3_pass,       // valid inst
  input                          ca_enable,     // CA not stall
  input [2:0]                    ca_mem_addr0_r,
  input [`npuarc_DMP_DATA_RANGE]        ca_wr_data_r,  // write data from store

  ////////// Line buffer status //////////////////////////////////////////
  //
  output reg                     lb_err_r,        // Error in line buffer
  
  output wire                    lb_ready_to_dc,  // Ready to go to Cache
  output wire                    lb_empty      
  // leda NTL_CON13C on
);
   
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: some bits not used
reg  [`npuarc_WORD0_RANGE]             lb_data_nxt0;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_nxt0;
reg  [`npuarc_WORD0_RANGE]             lb_data_r0;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_r0;
reg  [`npuarc_WORD0_RANGE]             lb_data_nxt1;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_nxt1;
reg  [`npuarc_WORD0_RANGE]             lb_data_r1;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_r1;
reg  [`npuarc_WORD0_RANGE]             lb_data_nxt2;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_nxt2;
reg  [`npuarc_WORD0_RANGE]             lb_data_r2;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_r2;
reg  [`npuarc_WORD0_RANGE]             lb_data_nxt3;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_nxt3;
reg  [`npuarc_WORD0_RANGE]             lb_data_r3;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_r3;
reg  [`npuarc_WORD0_RANGE]             lb_data_nxt4;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_nxt4;
reg  [`npuarc_WORD0_RANGE]             lb_data_r4;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_r4;
reg  [`npuarc_WORD0_RANGE]             lb_data_nxt5;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_nxt5;
reg  [`npuarc_WORD0_RANGE]             lb_data_r5;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_r5;
reg  [`npuarc_WORD0_RANGE]             lb_data_nxt6;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_nxt6;
reg  [`npuarc_WORD0_RANGE]             lb_data_r6;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_r6;
reg  [`npuarc_WORD0_RANGE]             lb_data_nxt7;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_nxt7;
reg  [`npuarc_WORD0_RANGE]             lb_data_r7;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_r7;
reg  [`npuarc_WORD0_RANGE]             lb_data_nxt8;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_nxt8;
reg  [`npuarc_WORD0_RANGE]             lb_data_r8;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_r8;
reg  [`npuarc_WORD0_RANGE]             lb_data_nxt9;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_nxt9;
reg  [`npuarc_WORD0_RANGE]             lb_data_r9;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_r9;
reg  [`npuarc_WORD0_RANGE]             lb_data_nxt10;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_nxt10;
reg  [`npuarc_WORD0_RANGE]             lb_data_r10;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_r10;
reg  [`npuarc_WORD0_RANGE]             lb_data_nxt11;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_nxt11;
reg  [`npuarc_WORD0_RANGE]             lb_data_r11;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_r11;
reg  [`npuarc_WORD0_RANGE]             lb_data_nxt12;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_nxt12;
reg  [`npuarc_WORD0_RANGE]             lb_data_r12;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_r12;
reg  [`npuarc_WORD0_RANGE]             lb_data_nxt13;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_nxt13;
reg  [`npuarc_WORD0_RANGE]             lb_data_r13;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_r13;
reg  [`npuarc_WORD0_RANGE]             lb_data_nxt14;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_nxt14;
reg  [`npuarc_WORD0_RANGE]             lb_data_r14;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_r14;
reg  [`npuarc_WORD0_RANGE]             lb_data_nxt15;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_nxt15;
reg  [`npuarc_WORD0_RANGE]             lb_data_r15;
reg  [`npuarc_BMASK0_RANGE]            lb_mask_r15;
reg  [`npuarc_WORD0_RANGE]             lb_data_r[`npuarc_LBUF_FIFO_RANGE];    
reg  [`npuarc_BMASK0_RANGE]            lb_mask_r[`npuarc_LBUF_FIFO_RANGE];    
wire                            lb_full;
wire                            lb_wr_store;
// leda NTL_CON13A on

wire [`npuarc_LBUF_PTR_RANGE]          ptr0;
wire [`npuarc_LBUF_PTR_RANGE]          ptr1;
wire [`npuarc_LBUF_PTR_RANGE]          ptr2;
wire [`npuarc_LBUF_PTR_RANGE]          ptr3;
wire [`npuarc_LBUF_PTR_RANGE]          ptr4;
wire [`npuarc_LBUF_PTR_RANGE]          lsaddr0;
wire [`npuarc_LBUF_PTR_RANGE]          lsaddr1;
wire [`npuarc_LBUF_PTR_RANGE]          lsaddr2;
wire [`npuarc_LBUF_PTR_RANGE]          rdptr0;   
wire [`npuarc_LBUF_PTR_RANGE]          rdptr1;   
wire [`npuarc_LBUF_PTR_RANGE]          rdptr2;   
wire [`npuarc_LBUF_PTR_RANGE]          rdptr3;   

wire [`npuarc_DC_BLK_WRD_RANGE]        ld_addr;
wire [`npuarc_LBUF_PTR_RANGE]          ld_ptr0;
wire [`npuarc_LBUF_PTR_RANGE]          ld_ptr1;
wire [`npuarc_LBUF_PTR_RANGE]          ld_ptr2;
wire [`npuarc_LBUF_PTR_RANGE]          ld_ptr3;
reg  [`npuarc_LBUF_PTR_RANGE]          ld_ptr0_nxt;
reg  [`npuarc_LBUF_PTR_RANGE]          ld_ptr1_nxt;
reg  [`npuarc_LBUF_PTR_RANGE]          ld_ptr2_nxt;
reg  [`npuarc_LBUF_PTR_RANGE]          ld_ptr3_nxt;
reg  [`npuarc_LBUF_PTR_RANGE]          ld_ptr0_next;
reg  [`npuarc_LBUF_PTR_RANGE]          ld_ptr1_next;
reg  [`npuarc_LBUF_PTR_RANGE]          ld_ptr2_next;
reg  [`npuarc_LBUF_PTR_RANGE]          ld_ptr3_next;
reg  [`npuarc_LBUF_PTR_RANGE]          ld_ptr0_r;
reg  [`npuarc_LBUF_PTR_RANGE]          ld_ptr1_r;
reg  [`npuarc_LBUF_PTR_RANGE]          ld_ptr2_r;
reg  [`npuarc_LBUF_PTR_RANGE]          ld_ptr3_r;
wire                            ld_fwd;

wire                            rf_rd_en;
wire                            lb_err_en;
reg                             rf_pre_alloc_en;
reg                             rf_pre_alloc_last_r;
reg                             rf_pre_alloc_last_next;

reg [`npuarc_LBUF_PTR_RANGE]           ptr_r;
reg [`npuarc_LBUF_PTR_RANGE]           ptr_next;
reg [`npuarc_LBUF_PTR_RANGE]           ptr_nxt;
wire                            mq_lbstore_nxt   ;      
wire                            mq_addr0_hit_nxt ;    
wire                            mq_st_first_nxt  ;    
reg                             mq_lbstore_next   ;      
reg                             mq_addr0_hit_next ;    
reg                             mq_st_first_next  ;    

wire [`npuarc_LBWR_MASK_RANGE]         wr_mask;
wire [`npuarc_LBWR_DATA_RANGE]         wr_data;
reg                             mq_lbstore_r;
reg                             mq_addr0_hit_r;
reg  [`npuarc_LBWR_MASK_RANGE]         mq_stmask_r;
reg  [`npuarc_DC_BLK_WRD_RANGE]        mq_fwd_addr_r;
reg  [`npuarc_LBWR_DATA_RANGE]         st_wr_data_r;
wire [`npuarc_LBWR_DATA_RANGE]         dc4_wr_data;
reg  [`npuarc_LBWR_DATA_RANGE]         dc4_data0_shf;
wire [`npuarc_LBWR_DATA_RANGE]         dc4_data1_shf;
reg                             mq_st_first_r;
reg  [`npuarc_LBUF_FIFO_RANGE]         lb_valid_next;
reg                             lb_err_next;
wire                            lbuf_last_read;  


//////////////////////////////////////////////////////////////////////////////
// Pre-alloc enable
//////////////////////////////////////////////////////////////////////////////
always @*
begin : rf_pre_alloc_en_PROC
  rf_pre_alloc_en =  mq_pre_alloc
                   & lb_empty
                   & (~lbuf_rd_last_r);
end
//////////////////////////////////////////////////////////////////////////////
// Synchronous process for writing new information into the LBUF
// Organized as 32-bit entry FIFO, 32B cache line size = 8 entries
//////////////////////////////////////////////////////////////////////////////

// leda FM_1_7 off
// LMD: Signal assigned more than once in a single flow of control
// LJ:  register file with multiple write ports, conflict covered by assertions
//
// leda NTL_RST03 off
// LMD: A flipflop without reset
// LJ:  Valid is reset but Control, Address, Data should not be reset
//
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
//
// spyglass disable_block STARC05-2.2.3.3
// SMD: Flipflop value assigned more than once over same signal in always construct
// SJ:  Conflit covered by assertions
//
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01 STARC05-1.3.1.3
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @*
begin : lb_sync_comb_PROC
    lb_valid_next      = lb_valid_r      ;
    lb_err_next        = lb_err_r        ;
  begin
    casez ({rf_rd_en, rf_pre_alloc_en})
    2'b1?:
    begin
      lb_valid_next[ptr0]  =  1'b1;     
      lb_valid_next[ptr1]  =  1'b1;     
      lb_valid_next[ptr2]  =  1'b1;     
      lb_valid_next[ptr3]  =  1'b1;     
    end
   
    2'b01:
    begin
      lb_valid_next      = {`npuarc_LBUF_FIFO_DEPTH{1'b1}};
      lb_err_next        = 1'b0;
    end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept    
    default:
      ;
    endcase
// spyglass enable_block W193    
    if (lb_err_en)
    begin
      lb_err_next        = rf_err_rd;
    end
    
    if (lbuf_rd_last)
    begin
      lb_valid_next     = {`npuarc_LBUF_FIFO_DEPTH{1'b0}};
// spyglass disable_block W415a
// SMD: signal assigned multiple times in the same always block
// SJ:  done on purpose, last one has priority. 
      lb_err_next       = 1'b0;
// spyglass enable_block W415a 
    end
  end // else: !if(rst_a)
end
always @(posedge clk or posedge rst_a)
begin : lb_sync_PROC
  if (rst_a == 1'b1)
  begin
    lb_valid_r      <= {`npuarc_LBUF_FIFO_DEPTH{1'b0}};
    lb_err_r        <= 1'b0;
  end
  else
  begin
    lb_valid_r      <= lb_valid_next      ;
    lb_err_r        <= lb_err_next        ;
  end // else: !if(rst_a)
end
// spyglass enable_block STARC05-1.3.1.3

// spyglass disable_block Ac_conv01
// SMD: Convergence
// SJ:  two accessing path is independent path
//
// spyglass disable_block ResetFlop-ML
// SMD: Has neither asynchronous set/reset nor synchronous set/reset
// SJ:  Datapath items not reset
always @*
begin
    lb_data_r[0]     = lb_data_r0;
    lb_mask_r[0]     = lb_mask_r0;
    lb_data_r[1]     = lb_data_r1;
    lb_mask_r[1]     = lb_mask_r1;
    lb_data_r[2]     = lb_data_r2;
    lb_mask_r[2]     = lb_mask_r2;
    lb_data_r[3]     = lb_data_r3;
    lb_mask_r[3]     = lb_mask_r3;
    lb_data_r[4]     = lb_data_r4;
    lb_mask_r[4]     = lb_mask_r4;
    lb_data_r[5]     = lb_data_r5;
    lb_mask_r[5]     = lb_mask_r5;
    lb_data_r[6]     = lb_data_r6;
    lb_mask_r[6]     = lb_mask_r6;
    lb_data_r[7]     = lb_data_r7;
    lb_mask_r[7]     = lb_mask_r7;
    lb_data_r[8]     = lb_data_r8;
    lb_mask_r[8]     = lb_mask_r8;
    lb_data_r[9]     = lb_data_r9;
    lb_mask_r[9]     = lb_mask_r9;
    lb_data_r[10]     = lb_data_r10;
    lb_mask_r[10]     = lb_mask_r10;
    lb_data_r[11]     = lb_data_r11;
    lb_mask_r[11]     = lb_mask_r11;
    lb_data_r[12]     = lb_data_r12;
    lb_mask_r[12]     = lb_mask_r12;
    lb_data_r[13]     = lb_data_r13;
    lb_mask_r[13]     = lb_mask_r13;
    lb_data_r[14]     = lb_data_r14;
    lb_mask_r[14]     = lb_mask_r14;
    lb_data_r[15]     = lb_data_r15;
    lb_mask_r[15]     = lb_mask_r15;
end

always @*
begin : lb_data_comb_PROC
    lb_data_nxt0     = lb_data_r0;
    lb_mask_nxt0     = lb_mask_r0;
    lb_data_nxt1     = lb_data_r1;
    lb_mask_nxt1     = lb_mask_r1;
    lb_data_nxt2     = lb_data_r2;
    lb_mask_nxt2     = lb_mask_r2;
    lb_data_nxt3     = lb_data_r3;
    lb_mask_nxt3     = lb_mask_r3;
    lb_data_nxt4     = lb_data_r4;
    lb_mask_nxt4     = lb_mask_r4;
    lb_data_nxt5     = lb_data_r5;
    lb_mask_nxt5     = lb_mask_r5;
    lb_data_nxt6     = lb_data_r6;
    lb_mask_nxt6     = lb_mask_r6;
    lb_data_nxt7     = lb_data_r7;
    lb_mask_nxt7     = lb_mask_r7;
    lb_data_nxt8     = lb_data_r8;
    lb_mask_nxt8     = lb_mask_r8;
    lb_data_nxt9     = lb_data_r9;
    lb_mask_nxt9     = lb_mask_r9;
    lb_data_nxt10     = lb_data_r10;
    lb_mask_nxt10     = lb_mask_r10;
    lb_data_nxt11     = lb_data_r11;
    lb_mask_nxt11     = lb_mask_r11;
    lb_data_nxt12     = lb_data_r12;
    lb_mask_nxt12     = lb_mask_r12;
    lb_data_nxt13     = lb_data_r13;
    lb_mask_nxt13     = lb_mask_r13;
    lb_data_nxt14     = lb_data_r14;
    lb_mask_nxt14     = lb_mask_r14;
    lb_data_nxt15     = lb_data_r15;
    lb_mask_nxt15     = lb_mask_r15;
  casez ({rf_rd_en, rf_pre_alloc_en})
  2'b1?:
  begin
   if( ptr0 == 0 )
    lb_data_nxt0     = rf_rd_data[`npuarc_WORD0_RANGE];
   if( ptr1 == 0 )
    lb_data_nxt0     = rf_rd_data[`npuarc_WORD1_RANGE];
   if( ptr2 == 0 )
    lb_data_nxt0     = rf_rd_data[`npuarc_WORD2_RANGE];
   if( ptr3 == 0 )
    lb_data_nxt0     = rf_rd_data[`npuarc_WORD3_RANGE];
   if( ptr0 == 1 )
    lb_data_nxt1     = rf_rd_data[`npuarc_WORD0_RANGE];
   if( ptr1 == 1 )
    lb_data_nxt1     = rf_rd_data[`npuarc_WORD1_RANGE];
   if( ptr2 == 1 )
    lb_data_nxt1     = rf_rd_data[`npuarc_WORD2_RANGE];
   if( ptr3 == 1 )
    lb_data_nxt1     = rf_rd_data[`npuarc_WORD3_RANGE];
   if( ptr0 == 2 )
    lb_data_nxt2     = rf_rd_data[`npuarc_WORD0_RANGE];
   if( ptr1 == 2 )
    lb_data_nxt2     = rf_rd_data[`npuarc_WORD1_RANGE];
   if( ptr2 == 2 )
    lb_data_nxt2     = rf_rd_data[`npuarc_WORD2_RANGE];
   if( ptr3 == 2 )
    lb_data_nxt2     = rf_rd_data[`npuarc_WORD3_RANGE];
   if( ptr0 == 3 )
    lb_data_nxt3     = rf_rd_data[`npuarc_WORD0_RANGE];
   if( ptr1 == 3 )
    lb_data_nxt3     = rf_rd_data[`npuarc_WORD1_RANGE];
   if( ptr2 == 3 )
    lb_data_nxt3     = rf_rd_data[`npuarc_WORD2_RANGE];
   if( ptr3 == 3 )
    lb_data_nxt3     = rf_rd_data[`npuarc_WORD3_RANGE];
   if( ptr0 == 4 )
    lb_data_nxt4     = rf_rd_data[`npuarc_WORD0_RANGE];
   if( ptr1 == 4 )
    lb_data_nxt4     = rf_rd_data[`npuarc_WORD1_RANGE];
   if( ptr2 == 4 )
    lb_data_nxt4     = rf_rd_data[`npuarc_WORD2_RANGE];
   if( ptr3 == 4 )
    lb_data_nxt4     = rf_rd_data[`npuarc_WORD3_RANGE];
   if( ptr0 == 5 )
    lb_data_nxt5     = rf_rd_data[`npuarc_WORD0_RANGE];
   if( ptr1 == 5 )
    lb_data_nxt5     = rf_rd_data[`npuarc_WORD1_RANGE];
   if( ptr2 == 5 )
    lb_data_nxt5     = rf_rd_data[`npuarc_WORD2_RANGE];
   if( ptr3 == 5 )
    lb_data_nxt5     = rf_rd_data[`npuarc_WORD3_RANGE];
   if( ptr0 == 6 )
    lb_data_nxt6     = rf_rd_data[`npuarc_WORD0_RANGE];
   if( ptr1 == 6 )
    lb_data_nxt6     = rf_rd_data[`npuarc_WORD1_RANGE];
   if( ptr2 == 6 )
    lb_data_nxt6     = rf_rd_data[`npuarc_WORD2_RANGE];
   if( ptr3 == 6 )
    lb_data_nxt6     = rf_rd_data[`npuarc_WORD3_RANGE];
   if( ptr0 == 7 )
    lb_data_nxt7     = rf_rd_data[`npuarc_WORD0_RANGE];
   if( ptr1 == 7 )
    lb_data_nxt7     = rf_rd_data[`npuarc_WORD1_RANGE];
   if( ptr2 == 7 )
    lb_data_nxt7     = rf_rd_data[`npuarc_WORD2_RANGE];
   if( ptr3 == 7 )
    lb_data_nxt7     = rf_rd_data[`npuarc_WORD3_RANGE];
   if( ptr0 == 8 )
    lb_data_nxt8     = rf_rd_data[`npuarc_WORD0_RANGE];
   if( ptr1 == 8 )
    lb_data_nxt8     = rf_rd_data[`npuarc_WORD1_RANGE];
   if( ptr2 == 8 )
    lb_data_nxt8     = rf_rd_data[`npuarc_WORD2_RANGE];
   if( ptr3 == 8 )
    lb_data_nxt8     = rf_rd_data[`npuarc_WORD3_RANGE];
   if( ptr0 == 9 )
    lb_data_nxt9     = rf_rd_data[`npuarc_WORD0_RANGE];
   if( ptr1 == 9 )
    lb_data_nxt9     = rf_rd_data[`npuarc_WORD1_RANGE];
   if( ptr2 == 9 )
    lb_data_nxt9     = rf_rd_data[`npuarc_WORD2_RANGE];
   if( ptr3 == 9 )
    lb_data_nxt9     = rf_rd_data[`npuarc_WORD3_RANGE];
   if( ptr0 == 10 )
    lb_data_nxt10     = rf_rd_data[`npuarc_WORD0_RANGE];
   if( ptr1 == 10 )
    lb_data_nxt10     = rf_rd_data[`npuarc_WORD1_RANGE];
   if( ptr2 == 10 )
    lb_data_nxt10     = rf_rd_data[`npuarc_WORD2_RANGE];
   if( ptr3 == 10 )
    lb_data_nxt10     = rf_rd_data[`npuarc_WORD3_RANGE];
   if( ptr0 == 11 )
    lb_data_nxt11     = rf_rd_data[`npuarc_WORD0_RANGE];
   if( ptr1 == 11 )
    lb_data_nxt11     = rf_rd_data[`npuarc_WORD1_RANGE];
   if( ptr2 == 11 )
    lb_data_nxt11     = rf_rd_data[`npuarc_WORD2_RANGE];
   if( ptr3 == 11 )
    lb_data_nxt11     = rf_rd_data[`npuarc_WORD3_RANGE];
   if( ptr0 == 12 )
    lb_data_nxt12     = rf_rd_data[`npuarc_WORD0_RANGE];
   if( ptr1 == 12 )
    lb_data_nxt12     = rf_rd_data[`npuarc_WORD1_RANGE];
   if( ptr2 == 12 )
    lb_data_nxt12     = rf_rd_data[`npuarc_WORD2_RANGE];
   if( ptr3 == 12 )
    lb_data_nxt12     = rf_rd_data[`npuarc_WORD3_RANGE];
   if( ptr0 == 13 )
    lb_data_nxt13     = rf_rd_data[`npuarc_WORD0_RANGE];
   if( ptr1 == 13 )
    lb_data_nxt13     = rf_rd_data[`npuarc_WORD1_RANGE];
   if( ptr2 == 13 )
    lb_data_nxt13     = rf_rd_data[`npuarc_WORD2_RANGE];
   if( ptr3 == 13 )
    lb_data_nxt13     = rf_rd_data[`npuarc_WORD3_RANGE];
   if( ptr0 == 14 )
    lb_data_nxt14     = rf_rd_data[`npuarc_WORD0_RANGE];
   if( ptr1 == 14 )
    lb_data_nxt14     = rf_rd_data[`npuarc_WORD1_RANGE];
   if( ptr2 == 14 )
    lb_data_nxt14     = rf_rd_data[`npuarc_WORD2_RANGE];
   if( ptr3 == 14 )
    lb_data_nxt14     = rf_rd_data[`npuarc_WORD3_RANGE];
   if( ptr0 == 15 )
    lb_data_nxt15     = rf_rd_data[`npuarc_WORD0_RANGE];
   if( ptr1 == 15 )
    lb_data_nxt15     = rf_rd_data[`npuarc_WORD1_RANGE];
   if( ptr2 == 15 )
    lb_data_nxt15     = rf_rd_data[`npuarc_WORD2_RANGE];
   if( ptr3 == 15 )
    lb_data_nxt15     = rf_rd_data[`npuarc_WORD3_RANGE];
  end
   
  2'b01:
  begin
    lb_data_nxt0   = {`npuarc_WORD_SIZE{1'b0}};
    lb_mask_nxt0   = {`npuarc_BMASK_SIZE{1'b1}};
    lb_data_nxt1   = {`npuarc_WORD_SIZE{1'b0}};
    lb_mask_nxt1   = {`npuarc_BMASK_SIZE{1'b1}};
    lb_data_nxt2   = {`npuarc_WORD_SIZE{1'b0}};
    lb_mask_nxt2   = {`npuarc_BMASK_SIZE{1'b1}};
    lb_data_nxt3   = {`npuarc_WORD_SIZE{1'b0}};
    lb_mask_nxt3   = {`npuarc_BMASK_SIZE{1'b1}};
    lb_data_nxt4   = {`npuarc_WORD_SIZE{1'b0}};
    lb_mask_nxt4   = {`npuarc_BMASK_SIZE{1'b1}};
    lb_data_nxt5   = {`npuarc_WORD_SIZE{1'b0}};
    lb_mask_nxt5   = {`npuarc_BMASK_SIZE{1'b1}};
    lb_data_nxt6   = {`npuarc_WORD_SIZE{1'b0}};
    lb_mask_nxt6   = {`npuarc_BMASK_SIZE{1'b1}};
    lb_data_nxt7   = {`npuarc_WORD_SIZE{1'b0}};
    lb_mask_nxt7   = {`npuarc_BMASK_SIZE{1'b1}};
    lb_data_nxt8   = {`npuarc_WORD_SIZE{1'b0}};
    lb_mask_nxt8   = {`npuarc_BMASK_SIZE{1'b1}};
    lb_data_nxt9   = {`npuarc_WORD_SIZE{1'b0}};
    lb_mask_nxt9   = {`npuarc_BMASK_SIZE{1'b1}};
    lb_data_nxt10   = {`npuarc_WORD_SIZE{1'b0}};
    lb_mask_nxt10   = {`npuarc_BMASK_SIZE{1'b1}};
    lb_data_nxt11   = {`npuarc_WORD_SIZE{1'b0}};
    lb_mask_nxt11   = {`npuarc_BMASK_SIZE{1'b1}};
    lb_data_nxt12   = {`npuarc_WORD_SIZE{1'b0}};
    lb_mask_nxt12   = {`npuarc_BMASK_SIZE{1'b1}};
    lb_data_nxt13   = {`npuarc_WORD_SIZE{1'b0}};
    lb_mask_nxt13   = {`npuarc_BMASK_SIZE{1'b1}};
    lb_data_nxt14   = {`npuarc_WORD_SIZE{1'b0}};
    lb_mask_nxt14   = {`npuarc_BMASK_SIZE{1'b1}};
    lb_data_nxt15   = {`npuarc_WORD_SIZE{1'b0}};
    lb_mask_nxt15   = {`npuarc_BMASK_SIZE{1'b1}};
  end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept    
  default:
    ;
  endcase
// spyglass enable_block W193    
    // Write data from LSMQ or STORE to LBUF, 64-bit store miss data  
    // 
  if (lb_wr_store)
  begin
   if( lsaddr0 == 0 )
   begin
    lb_mask_nxt0  =  wr_mask[`npuarc_BMASK0_RANGE];  
    if (wr_mask[3])   
      lb_data_nxt0[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE3_RANGE]; 
    if (wr_mask[2])   
      lb_data_nxt0[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE2_RANGE]; 
    if (wr_mask[1])   
      lb_data_nxt0[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE1_RANGE]; 
    if (wr_mask[0])   
      lb_data_nxt0[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE0_RANGE]; 
   end

   if( lsaddr1 == 0 )
   begin
    lb_mask_nxt0   =  wr_mask[`npuarc_BMASK1_RANGE];     
    if (wr_mask[7])   
      lb_data_nxt0[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE7_RANGE]; 
    if (wr_mask[6])   
      lb_data_nxt0[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE6_RANGE]; 
    if (wr_mask[5])   
      lb_data_nxt0[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE5_RANGE]; 
    if (wr_mask[4])   
      lb_data_nxt0[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE4_RANGE]; 
   end

   if( lsaddr2 == 0 )
   begin
    lb_mask_nxt0   =  wr_mask[`npuarc_BMASK2_RANGE];     
    if (wr_mask[11])   
      lb_data_nxt0[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE11_RANGE]; 
    if (wr_mask[10])   
      lb_data_nxt0[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE10_RANGE]; 
    if (wr_mask[9])   
      lb_data_nxt0[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE9_RANGE]; 
    if (wr_mask[8])   
      lb_data_nxt0[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE8_RANGE]; 
   end
   if( lsaddr0 == 1 )
   begin
    lb_mask_nxt1  =  wr_mask[`npuarc_BMASK0_RANGE];  
    if (wr_mask[3])   
      lb_data_nxt1[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE3_RANGE]; 
    if (wr_mask[2])   
      lb_data_nxt1[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE2_RANGE]; 
    if (wr_mask[1])   
      lb_data_nxt1[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE1_RANGE]; 
    if (wr_mask[0])   
      lb_data_nxt1[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE0_RANGE]; 
   end

   if( lsaddr1 == 1 )
   begin
    lb_mask_nxt1   =  wr_mask[`npuarc_BMASK1_RANGE];     
    if (wr_mask[7])   
      lb_data_nxt1[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE7_RANGE]; 
    if (wr_mask[6])   
      lb_data_nxt1[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE6_RANGE]; 
    if (wr_mask[5])   
      lb_data_nxt1[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE5_RANGE]; 
    if (wr_mask[4])   
      lb_data_nxt1[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE4_RANGE]; 
   end

   if( lsaddr2 == 1 )
   begin
    lb_mask_nxt1   =  wr_mask[`npuarc_BMASK2_RANGE];     
    if (wr_mask[11])   
      lb_data_nxt1[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE11_RANGE]; 
    if (wr_mask[10])   
      lb_data_nxt1[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE10_RANGE]; 
    if (wr_mask[9])   
      lb_data_nxt1[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE9_RANGE]; 
    if (wr_mask[8])   
      lb_data_nxt1[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE8_RANGE]; 
   end
   if( lsaddr0 == 2 )
   begin
    lb_mask_nxt2  =  wr_mask[`npuarc_BMASK0_RANGE];  
    if (wr_mask[3])   
      lb_data_nxt2[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE3_RANGE]; 
    if (wr_mask[2])   
      lb_data_nxt2[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE2_RANGE]; 
    if (wr_mask[1])   
      lb_data_nxt2[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE1_RANGE]; 
    if (wr_mask[0])   
      lb_data_nxt2[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE0_RANGE]; 
   end

   if( lsaddr1 == 2 )
   begin
    lb_mask_nxt2   =  wr_mask[`npuarc_BMASK1_RANGE];     
    if (wr_mask[7])   
      lb_data_nxt2[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE7_RANGE]; 
    if (wr_mask[6])   
      lb_data_nxt2[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE6_RANGE]; 
    if (wr_mask[5])   
      lb_data_nxt2[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE5_RANGE]; 
    if (wr_mask[4])   
      lb_data_nxt2[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE4_RANGE]; 
   end

   if( lsaddr2 == 2 )
   begin
    lb_mask_nxt2   =  wr_mask[`npuarc_BMASK2_RANGE];     
    if (wr_mask[11])   
      lb_data_nxt2[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE11_RANGE]; 
    if (wr_mask[10])   
      lb_data_nxt2[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE10_RANGE]; 
    if (wr_mask[9])   
      lb_data_nxt2[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE9_RANGE]; 
    if (wr_mask[8])   
      lb_data_nxt2[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE8_RANGE]; 
   end
   if( lsaddr0 == 3 )
   begin
    lb_mask_nxt3  =  wr_mask[`npuarc_BMASK0_RANGE];  
    if (wr_mask[3])   
      lb_data_nxt3[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE3_RANGE]; 
    if (wr_mask[2])   
      lb_data_nxt3[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE2_RANGE]; 
    if (wr_mask[1])   
      lb_data_nxt3[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE1_RANGE]; 
    if (wr_mask[0])   
      lb_data_nxt3[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE0_RANGE]; 
   end

   if( lsaddr1 == 3 )
   begin
    lb_mask_nxt3   =  wr_mask[`npuarc_BMASK1_RANGE];     
    if (wr_mask[7])   
      lb_data_nxt3[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE7_RANGE]; 
    if (wr_mask[6])   
      lb_data_nxt3[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE6_RANGE]; 
    if (wr_mask[5])   
      lb_data_nxt3[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE5_RANGE]; 
    if (wr_mask[4])   
      lb_data_nxt3[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE4_RANGE]; 
   end

   if( lsaddr2 == 3 )
   begin
    lb_mask_nxt3   =  wr_mask[`npuarc_BMASK2_RANGE];     
    if (wr_mask[11])   
      lb_data_nxt3[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE11_RANGE]; 
    if (wr_mask[10])   
      lb_data_nxt3[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE10_RANGE]; 
    if (wr_mask[9])   
      lb_data_nxt3[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE9_RANGE]; 
    if (wr_mask[8])   
      lb_data_nxt3[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE8_RANGE]; 
   end
   if( lsaddr0 == 4 )
   begin
    lb_mask_nxt4  =  wr_mask[`npuarc_BMASK0_RANGE];  
    if (wr_mask[3])   
      lb_data_nxt4[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE3_RANGE]; 
    if (wr_mask[2])   
      lb_data_nxt4[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE2_RANGE]; 
    if (wr_mask[1])   
      lb_data_nxt4[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE1_RANGE]; 
    if (wr_mask[0])   
      lb_data_nxt4[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE0_RANGE]; 
   end

   if( lsaddr1 == 4 )
   begin
    lb_mask_nxt4   =  wr_mask[`npuarc_BMASK1_RANGE];     
    if (wr_mask[7])   
      lb_data_nxt4[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE7_RANGE]; 
    if (wr_mask[6])   
      lb_data_nxt4[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE6_RANGE]; 
    if (wr_mask[5])   
      lb_data_nxt4[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE5_RANGE]; 
    if (wr_mask[4])   
      lb_data_nxt4[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE4_RANGE]; 
   end

   if( lsaddr2 == 4 )
   begin
    lb_mask_nxt4   =  wr_mask[`npuarc_BMASK2_RANGE];     
    if (wr_mask[11])   
      lb_data_nxt4[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE11_RANGE]; 
    if (wr_mask[10])   
      lb_data_nxt4[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE10_RANGE]; 
    if (wr_mask[9])   
      lb_data_nxt4[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE9_RANGE]; 
    if (wr_mask[8])   
      lb_data_nxt4[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE8_RANGE]; 
   end
   if( lsaddr0 == 5 )
   begin
    lb_mask_nxt5  =  wr_mask[`npuarc_BMASK0_RANGE];  
    if (wr_mask[3])   
      lb_data_nxt5[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE3_RANGE]; 
    if (wr_mask[2])   
      lb_data_nxt5[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE2_RANGE]; 
    if (wr_mask[1])   
      lb_data_nxt5[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE1_RANGE]; 
    if (wr_mask[0])   
      lb_data_nxt5[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE0_RANGE]; 
   end

   if( lsaddr1 == 5 )
   begin
    lb_mask_nxt5   =  wr_mask[`npuarc_BMASK1_RANGE];     
    if (wr_mask[7])   
      lb_data_nxt5[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE7_RANGE]; 
    if (wr_mask[6])   
      lb_data_nxt5[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE6_RANGE]; 
    if (wr_mask[5])   
      lb_data_nxt5[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE5_RANGE]; 
    if (wr_mask[4])   
      lb_data_nxt5[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE4_RANGE]; 
   end

   if( lsaddr2 == 5 )
   begin
    lb_mask_nxt5   =  wr_mask[`npuarc_BMASK2_RANGE];     
    if (wr_mask[11])   
      lb_data_nxt5[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE11_RANGE]; 
    if (wr_mask[10])   
      lb_data_nxt5[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE10_RANGE]; 
    if (wr_mask[9])   
      lb_data_nxt5[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE9_RANGE]; 
    if (wr_mask[8])   
      lb_data_nxt5[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE8_RANGE]; 
   end
   if( lsaddr0 == 6 )
   begin
    lb_mask_nxt6  =  wr_mask[`npuarc_BMASK0_RANGE];  
    if (wr_mask[3])   
      lb_data_nxt6[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE3_RANGE]; 
    if (wr_mask[2])   
      lb_data_nxt6[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE2_RANGE]; 
    if (wr_mask[1])   
      lb_data_nxt6[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE1_RANGE]; 
    if (wr_mask[0])   
      lb_data_nxt6[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE0_RANGE]; 
   end

   if( lsaddr1 == 6 )
   begin
    lb_mask_nxt6   =  wr_mask[`npuarc_BMASK1_RANGE];     
    if (wr_mask[7])   
      lb_data_nxt6[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE7_RANGE]; 
    if (wr_mask[6])   
      lb_data_nxt6[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE6_RANGE]; 
    if (wr_mask[5])   
      lb_data_nxt6[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE5_RANGE]; 
    if (wr_mask[4])   
      lb_data_nxt6[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE4_RANGE]; 
   end

   if( lsaddr2 == 6 )
   begin
    lb_mask_nxt6   =  wr_mask[`npuarc_BMASK2_RANGE];     
    if (wr_mask[11])   
      lb_data_nxt6[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE11_RANGE]; 
    if (wr_mask[10])   
      lb_data_nxt6[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE10_RANGE]; 
    if (wr_mask[9])   
      lb_data_nxt6[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE9_RANGE]; 
    if (wr_mask[8])   
      lb_data_nxt6[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE8_RANGE]; 
   end
   if( lsaddr0 == 7 )
   begin
    lb_mask_nxt7  =  wr_mask[`npuarc_BMASK0_RANGE];  
    if (wr_mask[3])   
      lb_data_nxt7[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE3_RANGE]; 
    if (wr_mask[2])   
      lb_data_nxt7[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE2_RANGE]; 
    if (wr_mask[1])   
      lb_data_nxt7[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE1_RANGE]; 
    if (wr_mask[0])   
      lb_data_nxt7[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE0_RANGE]; 
   end

   if( lsaddr1 == 7 )
   begin
    lb_mask_nxt7   =  wr_mask[`npuarc_BMASK1_RANGE];     
    if (wr_mask[7])   
      lb_data_nxt7[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE7_RANGE]; 
    if (wr_mask[6])   
      lb_data_nxt7[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE6_RANGE]; 
    if (wr_mask[5])   
      lb_data_nxt7[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE5_RANGE]; 
    if (wr_mask[4])   
      lb_data_nxt7[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE4_RANGE]; 
   end

   if( lsaddr2 == 7 )
   begin
    lb_mask_nxt7   =  wr_mask[`npuarc_BMASK2_RANGE];     
    if (wr_mask[11])   
      lb_data_nxt7[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE11_RANGE]; 
    if (wr_mask[10])   
      lb_data_nxt7[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE10_RANGE]; 
    if (wr_mask[9])   
      lb_data_nxt7[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE9_RANGE]; 
    if (wr_mask[8])   
      lb_data_nxt7[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE8_RANGE]; 
   end
   if( lsaddr0 == 8 )
   begin
    lb_mask_nxt8  =  wr_mask[`npuarc_BMASK0_RANGE];  
    if (wr_mask[3])   
      lb_data_nxt8[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE3_RANGE]; 
    if (wr_mask[2])   
      lb_data_nxt8[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE2_RANGE]; 
    if (wr_mask[1])   
      lb_data_nxt8[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE1_RANGE]; 
    if (wr_mask[0])   
      lb_data_nxt8[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE0_RANGE]; 
   end

   if( lsaddr1 == 8 )
   begin
    lb_mask_nxt8   =  wr_mask[`npuarc_BMASK1_RANGE];     
    if (wr_mask[7])   
      lb_data_nxt8[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE7_RANGE]; 
    if (wr_mask[6])   
      lb_data_nxt8[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE6_RANGE]; 
    if (wr_mask[5])   
      lb_data_nxt8[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE5_RANGE]; 
    if (wr_mask[4])   
      lb_data_nxt8[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE4_RANGE]; 
   end

   if( lsaddr2 == 8 )
   begin
    lb_mask_nxt8   =  wr_mask[`npuarc_BMASK2_RANGE];     
    if (wr_mask[11])   
      lb_data_nxt8[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE11_RANGE]; 
    if (wr_mask[10])   
      lb_data_nxt8[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE10_RANGE]; 
    if (wr_mask[9])   
      lb_data_nxt8[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE9_RANGE]; 
    if (wr_mask[8])   
      lb_data_nxt8[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE8_RANGE]; 
   end
   if( lsaddr0 == 9 )
   begin
    lb_mask_nxt9  =  wr_mask[`npuarc_BMASK0_RANGE];  
    if (wr_mask[3])   
      lb_data_nxt9[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE3_RANGE]; 
    if (wr_mask[2])   
      lb_data_nxt9[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE2_RANGE]; 
    if (wr_mask[1])   
      lb_data_nxt9[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE1_RANGE]; 
    if (wr_mask[0])   
      lb_data_nxt9[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE0_RANGE]; 
   end

   if( lsaddr1 == 9 )
   begin
    lb_mask_nxt9   =  wr_mask[`npuarc_BMASK1_RANGE];     
    if (wr_mask[7])   
      lb_data_nxt9[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE7_RANGE]; 
    if (wr_mask[6])   
      lb_data_nxt9[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE6_RANGE]; 
    if (wr_mask[5])   
      lb_data_nxt9[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE5_RANGE]; 
    if (wr_mask[4])   
      lb_data_nxt9[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE4_RANGE]; 
   end

   if( lsaddr2 == 9 )
   begin
    lb_mask_nxt9   =  wr_mask[`npuarc_BMASK2_RANGE];     
    if (wr_mask[11])   
      lb_data_nxt9[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE11_RANGE]; 
    if (wr_mask[10])   
      lb_data_nxt9[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE10_RANGE]; 
    if (wr_mask[9])   
      lb_data_nxt9[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE9_RANGE]; 
    if (wr_mask[8])   
      lb_data_nxt9[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE8_RANGE]; 
   end
   if( lsaddr0 == 10 )
   begin
    lb_mask_nxt10  =  wr_mask[`npuarc_BMASK0_RANGE];  
    if (wr_mask[3])   
      lb_data_nxt10[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE3_RANGE]; 
    if (wr_mask[2])   
      lb_data_nxt10[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE2_RANGE]; 
    if (wr_mask[1])   
      lb_data_nxt10[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE1_RANGE]; 
    if (wr_mask[0])   
      lb_data_nxt10[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE0_RANGE]; 
   end

   if( lsaddr1 == 10 )
   begin
    lb_mask_nxt10   =  wr_mask[`npuarc_BMASK1_RANGE];     
    if (wr_mask[7])   
      lb_data_nxt10[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE7_RANGE]; 
    if (wr_mask[6])   
      lb_data_nxt10[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE6_RANGE]; 
    if (wr_mask[5])   
      lb_data_nxt10[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE5_RANGE]; 
    if (wr_mask[4])   
      lb_data_nxt10[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE4_RANGE]; 
   end

   if( lsaddr2 == 10 )
   begin
    lb_mask_nxt10   =  wr_mask[`npuarc_BMASK2_RANGE];     
    if (wr_mask[11])   
      lb_data_nxt10[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE11_RANGE]; 
    if (wr_mask[10])   
      lb_data_nxt10[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE10_RANGE]; 
    if (wr_mask[9])   
      lb_data_nxt10[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE9_RANGE]; 
    if (wr_mask[8])   
      lb_data_nxt10[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE8_RANGE]; 
   end
   if( lsaddr0 == 11 )
   begin
    lb_mask_nxt11  =  wr_mask[`npuarc_BMASK0_RANGE];  
    if (wr_mask[3])   
      lb_data_nxt11[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE3_RANGE]; 
    if (wr_mask[2])   
      lb_data_nxt11[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE2_RANGE]; 
    if (wr_mask[1])   
      lb_data_nxt11[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE1_RANGE]; 
    if (wr_mask[0])   
      lb_data_nxt11[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE0_RANGE]; 
   end

   if( lsaddr1 == 11 )
   begin
    lb_mask_nxt11   =  wr_mask[`npuarc_BMASK1_RANGE];     
    if (wr_mask[7])   
      lb_data_nxt11[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE7_RANGE]; 
    if (wr_mask[6])   
      lb_data_nxt11[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE6_RANGE]; 
    if (wr_mask[5])   
      lb_data_nxt11[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE5_RANGE]; 
    if (wr_mask[4])   
      lb_data_nxt11[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE4_RANGE]; 
   end

   if( lsaddr2 == 11 )
   begin
    lb_mask_nxt11   =  wr_mask[`npuarc_BMASK2_RANGE];     
    if (wr_mask[11])   
      lb_data_nxt11[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE11_RANGE]; 
    if (wr_mask[10])   
      lb_data_nxt11[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE10_RANGE]; 
    if (wr_mask[9])   
      lb_data_nxt11[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE9_RANGE]; 
    if (wr_mask[8])   
      lb_data_nxt11[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE8_RANGE]; 
   end
   if( lsaddr0 == 12 )
   begin
    lb_mask_nxt12  =  wr_mask[`npuarc_BMASK0_RANGE];  
    if (wr_mask[3])   
      lb_data_nxt12[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE3_RANGE]; 
    if (wr_mask[2])   
      lb_data_nxt12[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE2_RANGE]; 
    if (wr_mask[1])   
      lb_data_nxt12[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE1_RANGE]; 
    if (wr_mask[0])   
      lb_data_nxt12[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE0_RANGE]; 
   end

   if( lsaddr1 == 12 )
   begin
    lb_mask_nxt12   =  wr_mask[`npuarc_BMASK1_RANGE];     
    if (wr_mask[7])   
      lb_data_nxt12[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE7_RANGE]; 
    if (wr_mask[6])   
      lb_data_nxt12[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE6_RANGE]; 
    if (wr_mask[5])   
      lb_data_nxt12[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE5_RANGE]; 
    if (wr_mask[4])   
      lb_data_nxt12[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE4_RANGE]; 
   end

   if( lsaddr2 == 12 )
   begin
    lb_mask_nxt12   =  wr_mask[`npuarc_BMASK2_RANGE];     
    if (wr_mask[11])   
      lb_data_nxt12[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE11_RANGE]; 
    if (wr_mask[10])   
      lb_data_nxt12[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE10_RANGE]; 
    if (wr_mask[9])   
      lb_data_nxt12[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE9_RANGE]; 
    if (wr_mask[8])   
      lb_data_nxt12[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE8_RANGE]; 
   end
   if( lsaddr0 == 13 )
   begin
    lb_mask_nxt13  =  wr_mask[`npuarc_BMASK0_RANGE];  
    if (wr_mask[3])   
      lb_data_nxt13[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE3_RANGE]; 
    if (wr_mask[2])   
      lb_data_nxt13[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE2_RANGE]; 
    if (wr_mask[1])   
      lb_data_nxt13[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE1_RANGE]; 
    if (wr_mask[0])   
      lb_data_nxt13[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE0_RANGE]; 
   end

   if( lsaddr1 == 13 )
   begin
    lb_mask_nxt13   =  wr_mask[`npuarc_BMASK1_RANGE];     
    if (wr_mask[7])   
      lb_data_nxt13[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE7_RANGE]; 
    if (wr_mask[6])   
      lb_data_nxt13[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE6_RANGE]; 
    if (wr_mask[5])   
      lb_data_nxt13[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE5_RANGE]; 
    if (wr_mask[4])   
      lb_data_nxt13[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE4_RANGE]; 
   end

   if( lsaddr2 == 13 )
   begin
    lb_mask_nxt13   =  wr_mask[`npuarc_BMASK2_RANGE];     
    if (wr_mask[11])   
      lb_data_nxt13[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE11_RANGE]; 
    if (wr_mask[10])   
      lb_data_nxt13[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE10_RANGE]; 
    if (wr_mask[9])   
      lb_data_nxt13[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE9_RANGE]; 
    if (wr_mask[8])   
      lb_data_nxt13[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE8_RANGE]; 
   end
   if( lsaddr0 == 14 )
   begin
    lb_mask_nxt14  =  wr_mask[`npuarc_BMASK0_RANGE];  
    if (wr_mask[3])   
      lb_data_nxt14[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE3_RANGE]; 
    if (wr_mask[2])   
      lb_data_nxt14[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE2_RANGE]; 
    if (wr_mask[1])   
      lb_data_nxt14[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE1_RANGE]; 
    if (wr_mask[0])   
      lb_data_nxt14[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE0_RANGE]; 
   end

   if( lsaddr1 == 14 )
   begin
    lb_mask_nxt14   =  wr_mask[`npuarc_BMASK1_RANGE];     
    if (wr_mask[7])   
      lb_data_nxt14[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE7_RANGE]; 
    if (wr_mask[6])   
      lb_data_nxt14[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE6_RANGE]; 
    if (wr_mask[5])   
      lb_data_nxt14[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE5_RANGE]; 
    if (wr_mask[4])   
      lb_data_nxt14[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE4_RANGE]; 
   end

   if( lsaddr2 == 14 )
   begin
    lb_mask_nxt14   =  wr_mask[`npuarc_BMASK2_RANGE];     
    if (wr_mask[11])   
      lb_data_nxt14[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE11_RANGE]; 
    if (wr_mask[10])   
      lb_data_nxt14[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE10_RANGE]; 
    if (wr_mask[9])   
      lb_data_nxt14[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE9_RANGE]; 
    if (wr_mask[8])   
      lb_data_nxt14[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE8_RANGE]; 
   end
   if( lsaddr0 == 15 )
   begin
    lb_mask_nxt15  =  wr_mask[`npuarc_BMASK0_RANGE];  
    if (wr_mask[3])   
      lb_data_nxt15[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE3_RANGE]; 
    if (wr_mask[2])   
      lb_data_nxt15[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE2_RANGE]; 
    if (wr_mask[1])   
      lb_data_nxt15[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE1_RANGE]; 
    if (wr_mask[0])   
      lb_data_nxt15[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE0_RANGE]; 
   end

   if( lsaddr1 == 15 )
   begin
    lb_mask_nxt15   =  wr_mask[`npuarc_BMASK1_RANGE];     
    if (wr_mask[7])   
      lb_data_nxt15[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE7_RANGE]; 
    if (wr_mask[6])   
      lb_data_nxt15[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE6_RANGE]; 
    if (wr_mask[5])   
      lb_data_nxt15[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE5_RANGE]; 
    if (wr_mask[4])   
      lb_data_nxt15[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE4_RANGE]; 
   end

   if( lsaddr2 == 15 )
   begin
    lb_mask_nxt15   =  wr_mask[`npuarc_BMASK2_RANGE];     
    if (wr_mask[11])   
      lb_data_nxt15[`npuarc_BYTE3_RANGE] =  wr_data[`npuarc_BYTE11_RANGE]; 
    if (wr_mask[10])   
      lb_data_nxt15[`npuarc_BYTE2_RANGE] =  wr_data[`npuarc_BYTE10_RANGE]; 
    if (wr_mask[9])   
      lb_data_nxt15[`npuarc_BYTE1_RANGE] =  wr_data[`npuarc_BYTE9_RANGE]; 
    if (wr_mask[8])   
      lb_data_nxt15[`npuarc_BYTE0_RANGE] =  wr_data[`npuarc_BYTE8_RANGE]; 
   end
  end
end
always @(posedge clk)
begin : lb_data_reg_PROC
    lb_data_r0   <= lb_data_nxt0;
    lb_mask_r0   <= lb_mask_nxt0;
    lb_data_r1   <= lb_data_nxt1;
    lb_mask_r1   <= lb_mask_nxt1;
    lb_data_r2   <= lb_data_nxt2;
    lb_mask_r2   <= lb_mask_nxt2;
    lb_data_r3   <= lb_data_nxt3;
    lb_mask_r3   <= lb_mask_nxt3;
    lb_data_r4   <= lb_data_nxt4;
    lb_mask_r4   <= lb_mask_nxt4;
    lb_data_r5   <= lb_data_nxt5;
    lb_mask_r5   <= lb_mask_nxt5;
    lb_data_r6   <= lb_data_nxt6;
    lb_mask_r6   <= lb_mask_nxt6;
    lb_data_r7   <= lb_data_nxt7;
    lb_mask_r7   <= lb_mask_nxt7;
    lb_data_r8   <= lb_data_nxt8;
    lb_mask_r8   <= lb_mask_nxt8;
    lb_data_r9   <= lb_data_nxt9;
    lb_mask_r9   <= lb_mask_nxt9;
    lb_data_r10   <= lb_data_nxt10;
    lb_mask_r10   <= lb_mask_nxt10;
    lb_data_r11   <= lb_data_nxt11;
    lb_mask_r11   <= lb_mask_nxt11;
    lb_data_r12   <= lb_data_nxt12;
    lb_mask_r12   <= lb_mask_nxt12;
    lb_data_r13   <= lb_data_nxt13;
    lb_mask_r13   <= lb_mask_nxt13;
    lb_data_r14   <= lb_data_nxt14;
    lb_mask_r14   <= lb_mask_nxt14;
    lb_data_r15   <= lb_data_nxt15;
    lb_mask_r15   <= lb_mask_nxt15;
// spyglass enable_block Ac_conv01
end
// leda NTL_CON32 on
// leda NTL_RST03 on
// leda FM_1_7 on
// spyglass enable_block STARC05-2.2.3.3
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01
// spyglass enable_block ResetFlop-ML

//////////////////////////////////////////////////////////////////////////////
// Clock gate enable for write to LBUF: (1) Miss (2) Eviction (3) Flush
//
//////////////////////////////////////////////////////////////////////////////

  // CA store data must be shifted to the correct position to write to
  // line buffer for Addr0 and extracted the upper data for Addr1
  //
always @*
begin : byte_shift_PROC
  case (ca_mem_addr0_r[1:0])
  // Store data shift left for byte position, 
  //
  2'b00  : dc4_data0_shf = {{32{1'b0}}, ca_wr_data_r};
  2'b01  : dc4_data0_shf = {{24{1'b0}}, ca_wr_data_r,  {8{1'b0}}};
  2'b10  : dc4_data0_shf = {{16{1'b0}}, ca_wr_data_r, {16{1'b0}}};
  2'b11  : dc4_data0_shf = { {8{1'b0}}, ca_wr_data_r, {24{1'b0}}};
  default: dc4_data0_shf = {{32{1'b0}}, ca_wr_data_r};
  endcase  
end


  assign dc4_data1_shf = ca_mem_addr0_r[2] ? 
                         {{32{1'b0}}, dc4_data0_shf[`npuarc_DWORD1_RANGE]} :
                         {{64{1'b0}}, dc4_data0_shf[`npuarc_WORD2_RANGE]};   
   
  assign dc4_wr_data = mq_addr0_hit_r ? dc4_data0_shf : dc4_data1_shf;

  assign lb_wr_store = lsmq_st_req ;//| (mq_lbstore_r & ca_store_r & ca_pass);
   
  assign lsaddr0 = lsmq_st_req ? lsmq_st_addr : mq_fwd_addr_r;
// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  One/two bits incrementor

// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow
  assign lsaddr1 = lsaddr0 + 2'b01;
  assign lsaddr2 = lsaddr0 + 2'b10;
// leda W484 on
// leda BTTF_D002 on
// leda B_3200 on

  assign wr_mask = lsmq_st_req ? lsmq_wr_mask : mq_stmask_r;
  assign wr_data = lsmq_st_req ? lsmq_data : 
                   (mq_st_first_r ? dc4_wr_data : st_wr_data_r);

//////////////////////////////////////////////////////////////////////////////
// Mux logic to select the next entry for line buffer request 
//
//////////////////////////////////////////////////////////////////////////////

  // (1) MQ forward request for load hit in line buffer
  // (2) LSMQ read request for load miss instruction
  //
  assign ld_addr = (mq_lbfwd & x3_pass) ? mq_fwd_addr : lsmq_addr;
  assign ld_fwd  = (mq_lbfwd & x3_pass) | lsmq_ld_req;
 
  assign ld_ptr0 = ld_addr;
// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  One/two bits incrementor

// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow
  assign ld_ptr1 = ld_addr + 2'b01;
  assign ld_ptr2 = ld_addr + 2'b10;
  assign ld_ptr3 = ld_addr + 2'b11;
// leda W484 on
// leda BTTF_D002 on
// leda B_3200 on

always @*
begin : rdptr_sel_PROC
  casez (ld_addr[3:2])
  2'b00  : {ld_ptr3_nxt, ld_ptr2_nxt, ld_ptr1_nxt, ld_ptr0_nxt} = 
                           {ld_ptr3, ld_ptr2, ld_ptr1, ld_ptr0};
  2'b01  : {ld_ptr3_nxt, ld_ptr2_nxt, ld_ptr1_nxt, ld_ptr0_nxt} = 
                           {ld_ptr2, ld_ptr1, ld_ptr0, ld_ptr3};
  2'b10  : {ld_ptr3_nxt, ld_ptr2_nxt, ld_ptr1_nxt, ld_ptr0_nxt} = 
                           {ld_ptr1, ld_ptr0, ld_ptr3, ld_ptr2};
  2'b11  : {ld_ptr3_nxt, ld_ptr2_nxt, ld_ptr1_nxt, ld_ptr0_nxt} = 
                           {ld_ptr0, ld_ptr3, ld_ptr2, ld_ptr1};
  default: {ld_ptr3_nxt, ld_ptr2_nxt, ld_ptr1_nxt, ld_ptr0_nxt} = 
                           {ld_ptr3, ld_ptr2, ld_ptr1, ld_ptr0};
  endcase  
end

  assign rdptr0 = ld_ptr0_r;
  assign rdptr1 = ld_ptr1_r;
  assign rdptr2 = ld_ptr2_r;
  assign rdptr3 = ld_ptr3_r;

  assign lbuf_rd_data  = {lb_data_r[ptr3], lb_data_r[ptr2], 
                          lb_data_r[ptr1], lb_data_r[ptr0]};
  assign lbuf_fwd_data = {lb_data_r[rdptr3], lb_data_r[rdptr2], 
                          lb_data_r[rdptr1], lb_data_r[rdptr0]};

//////////////////////////////////////////////////////////////////////////////
// BIU interface and Counter logic
//
//////////////////////////////////////////////////////////////////////////////
  // Assuming data from BIU is 64-bit, ptr is incremented by 2
  //   rf_rd_en can start from any position
  //
  assign rf_rd_accept    =  (~lb_full)
                          & (~lbuf_rd_last_r)
                          ;
  assign rf_rd_en        =  (rf_rd_valid | rf_err_rd)                 
                          & rf_rd_accept
                          & (~mq_pre_alloc)
                          ; 

  assign lb_err_en       =  rf_rd_en
                          & (~lb_err_r)
                          ;
    
  //   - Read accept on not full
  //
  assign last_read      =  (rf_rd_valid | rf_err_rd) 
                          & rf_rd_last 
                          & rf_rd_accept;
 
  assign lbuf_last_read = last_read | rf_pre_alloc_last_r;
  
  assign lb_full        =  (& lb_valid_r);
  assign lb_empty       = ~(| lb_valid_r);
  assign lb_ready_to_dc =  lb_full
                         ;
                            
//////////////////////////////////////////////////////////////////////////////
// Pointers
//
//////////////////////////////////////////////////////////////////////////////
  assign ptr0 = ptr_r;
// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  One/two bits incrementor

// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow
  assign ptr1 = ptr_r + 2'b01;
  assign ptr2 = ptr_r + 2'b10;
  assign ptr3 = ptr_r + 2'b11;
  assign ptr4 = ptr_r + 3'b100;
// leda W484 on
// leda BTTF_D002 on
 // leda B_3200 on

always @*
begin : ptr_nxt_PROC
  // Ptr is initialized to the critical word
  //
  ptr_nxt = ptr_r;

  casez ({lbuf_last_read, 
          lbuf_initial, 
          rf_rd_en, 
          lbuf_rd_valid})
  4'b1???: 
    // last read: reset pointer
    //
    ptr_nxt = {`npuarc_LBUF_PTR_DEPTH{1'b0}};             
 
  4'b01??: 
    // initial setup
    //
    ptr_nxt = {mq_addr [`npuarc_DC_BLK_MSB:4], 2'b00};
  
  4'b001?: 
    // BIU->LBUF, increment pointer
    //
    ptr_nxt = ptr4;

  4'b0001: 
    // LBUF->DC, increment pointer
    //
    ptr_nxt = ptr4;

// spyglass disable_block W193
// SMD: Empty statement
// SJ:  Empty default statements kept

  default: ;
  endcase
// spyglass enable_block W193
end

  assign mq_lbstore_nxt   = ((mq_lbstore & x3_pass) | 
                             ((lsmq_st_req | (~ca_enable)) & mq_lbstore_r));
  assign mq_addr0_hit_nxt = ((mq_addr0_hit & x3_pass) | 
                             ((lsmq_st_req | (~ca_enable)) & mq_addr0_hit_r));
  assign mq_st_first_nxt = ((mq_lbstore & x3_pass) | 
                            (~ca_enable & mq_st_first_r));
  assign st_first_sel    = ca_enable & mq_st_first_r;
   
//////////////////////////////////////////////////////////////////////////////
// Synchronous process for the pointer manipulation logic
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin
    ptr_next              = ptr_nxt; 
    mq_lbstore_next       = mq_lbstore_nxt;
    mq_addr0_hit_next     = mq_addr0_hit_nxt;
    mq_st_first_next      = mq_st_first_nxt;
    ld_ptr0_next          = ld_fwd ? ld_ptr0_nxt : ld_ptr0_r;
    ld_ptr1_next          = ld_fwd ? ld_ptr1_nxt : ld_ptr1_r;
    ld_ptr2_next          = ld_fwd ? ld_ptr2_nxt : ld_ptr2_r;
    ld_ptr3_next          = ld_fwd ? ld_ptr3_nxt : ld_ptr3_r;
    rf_pre_alloc_last_next= rf_pre_alloc_en;
end

always @(posedge clk or posedge rst_a)
begin: lbptr_sync_PROC
  if (rst_a == 1'b1)
  begin
    ptr_r                <= {`npuarc_LBUF_PTR_DEPTH{1'b0}};
    ld_ptr0_r            <= {`npuarc_LBUF_PTR_DEPTH{1'b0}};
    ld_ptr1_r            <= {`npuarc_LBUF_PTR_DEPTH{1'b0}};
    ld_ptr2_r            <= {`npuarc_LBUF_PTR_DEPTH{1'b0}};
    ld_ptr3_r            <= {`npuarc_LBUF_PTR_DEPTH{1'b0}};
    mq_lbstore_r         <= 1'b0;
    mq_addr0_hit_r       <= 1'b0;
    mq_st_first_r        <= 1'b0;
    rf_pre_alloc_last_r  <= 1'b0;
  end
  else
  begin
    ptr_r                <= ptr_next; 

    // Cannot write data if conflict with lsmq write or CA stall (no data)
    //
    mq_lbstore_r         <= mq_lbstore_next;
    mq_addr0_hit_r       <= mq_addr0_hit_next;

    // mq_st_first_r = latch data from dc4_wr_data to use in next cycle if
    // conflict with lsmq write
    //
    mq_st_first_r       <= mq_st_first_next;

// leda NTL_RST03 off
// LMD: A flipflop without reset
// LJ:  Valid is reset but Control, Address, Data should not be reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
   //
    ld_ptr0_r          <= ld_ptr0_next ;
    ld_ptr1_r          <= ld_ptr1_next ;
    ld_ptr2_r          <= ld_ptr2_next ;
    ld_ptr3_r          <= ld_ptr3_next ;

    // Fake a rd_last for prealloc
    //
    rf_pre_alloc_last_r <= rf_pre_alloc_last_next;
// leda NTL_RST03 on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01
  end
end

// leda NTL_RST03 off
// LMD: A flipflop without reset
// LJ:  Valid is reset but Control, Address, Data should not be reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
//
// spyglass disable_block ResetFlop-ML
// SMD: Has neither asynchronous set/reset nor synchronous set/reset
// SJ:  Datapath items not reset
always @(posedge clk)
begin: lb_mask_reg_PROC
  // Note that: NO stall for load/store in CA
  mq_stmask_r        <= (mq_lbstore & x3_pass) ? mq_stmask   : mq_stmask_r;
  mq_fwd_addr_r      <= (mq_lbstore & x3_pass) ? mq_fwd_addr : mq_fwd_addr_r;
  st_wr_data_r       <= st_first_sel ? dc4_wr_data : st_wr_data_r;
end
// leda NTL_RST03 on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01
// spyglass enable_block ResetFlop-ML

endmodule // alb_dmp_line_buf

