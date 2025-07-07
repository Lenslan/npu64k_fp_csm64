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
//   ALB_DMP_CB                 
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements the Copy Back unit of the Data Cache
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_cb.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  rst: "rst_a", edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }
//D: error_signal { name: "alb_dmp_cb_hazard_fifo_err" }

module npuarc_alb_dmp_cb (
// leda NTL_CON37 off
// leda NTL_CON13C off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used
  ////////// General input signals ///////////////////////////////////////////
  //
  input                            clk,              // clock
  input                            rst_a,            // reset
  input                            ecc_dmp_disable, 
  
  input                            dc_pipe_busy,    // valid ld/st at dc2
  
  ////////// Interface with X3 for conflict detection /////////////////////
  //
  input                            x3_load_r,       // X3 load  
  input                            x3_store_r,      // X3 load  
  input [`npuarc_PADDR_RANGE]             x3_mem_addr0_r,  // X3 memory address
  input                            dc3_dc_target,   // X3 memory target
  input [`npuarc_PADDR_RANGE]             dc3_mem_addr1_r, // X3 memory address
  input                            dc3_dt_line_cross_r,  // addr1 is valid
 
  ////////// Interface to the Miss queue ////////////////////////////////////
  //
  input                            mq_valid,             // top of mq is valid
  input [`npuarc_PADDR_RANGE]             mq_addr,              // miss address
  input                            mq_cb_complete,       // cb status for top entry
  input                            mq_cache_flush,       // cache maintenance
  input                            mq_cache_purge,       // cache maintenance
  input                            mq_cache_lock,        // cache maintenance
  input                            mq_cache_cb_complete, // cache maintenance
  input                            mq_cache_way,         // cache maintenance
  
  output reg                       cb_cache_complete,  // cache maintenance complete
  output reg                       cb_complete,        // copy back is done
  output reg                       cb_way_select_r,    // LRU way for refill
  output reg                       cb_way_valid,       // not valid if all locked
  
  ////////// Interface to the DMU ////////////////////////////////////
  //
  input                            cb_ack_ok,         // cb can proceed
  
  output reg                       cb_dc_start,       // starting a cb
  output reg                       cb_dc_done,        // cb is done

  output                           cb_empty,          // no copy back pending
  output                           cb_full,           // two outstanding cb
  output                           cb_buf_busy_r,     // eviction buf busy
  output reg                       cb_dc_idle,        // not accessing the cache
  input                            cb_evict_error_r,  // ecc 2 bit error
  output                           cb_evict_hit,      // hit in the eviction bf

  output [`npuarc_DC_LBUF_RANGE]          cb_flush_err_addr, // flush error address
  output                           cb_flush_err_req,  // req flush error to EXU 
  input                            cb_flush_err_ack,  // flush err ack      


  ////////// IBP write interface ////////////////////////////////////////
  //   
  output reg                       cb_cmd_valid,
  input                            cb_cmd_accept,
  output reg                       cb_cmd_read, 
  output reg [`npuarc_PADDR_RANGE]        cb_cmd_addr, 
  output reg                       cb_cmd_prot, 
  output reg                       cb_cmd_wrap, 
  output reg [3:0]                 cb_cmd_burst_size, 

  output reg                       cb_wr_valid,
  input                            cb_wr_accept,
  output reg                       cb_wr_last,
  output reg [`npuarc_RF_CB_DATA_RANGE]   cb_wr_data,
  output reg [`npuarc_RF_CB_MASK_RANGE]   cb_wr_mask,
  
  input                            cb_wr_done,
  input                            cb_err_wr,
  
  ////////// Interface to the  Data Cache Arrays /////////////////////////
  //
  output reg                       cb_req_dt_even, // Request even tag array
  output reg                       cb_req_dt_odd,  // Request odd tag array
  output reg                       cb_dt_odd_sel,  // Request odd tag array
  output reg [`npuarc_DC_WAY_RANGE]       cb_dt_way_hot,  // Selected way to write
  output reg                       cb_dt_we,       // Write enable, 0=read
  output reg [2:0]                 cb_dt_wem,      // Mask=write enable
  output reg [`npuarc_DC_IDX_RANGE]       cb_dt_addr,     // Address from MQ
  output reg                       cb_dt_valid,    // Valid bit
  output reg [`npuarc_DC_TAG_RANGE]       cb_dt_tag,      // Data tag
  
  output reg                       cb_req_dd,       // DC1 Request to data array
  output reg                       cb_evict_rd,     // mux control to read data
  output reg [`npuarc_DC_WAY_RANGE]       cb_dd_way_hot,   // Selected way to write
  output reg                       cb_dd_we,        // Write enable, 0=read
  output reg [`npuarc_DC_ADR_RANGE]       cb_dd_addr,      // DC2 Address from MQ
  
  output reg                       cb_req_ds,       // request status flops
  output reg                       cb_ds_odd_sel,   // even, odd set
  output reg                       cb_ds_we,        // write enable
  output reg                       cb_ds_lru,       // LRU way
  output reg [2:0]                 cb_ds_wem,       // lock, dirty, lru
  output reg [`npuarc_DC_WAY_RANGE]       cb_ds_way_hot,   // selected way to write
  output reg [`npuarc_DC_IDX_RANGE]       cb_ds_addr,
  
  output reg [`npuarc_DC_LBUF_RANGE]      cb_line_addr_r,   // line address
  
  input [`npuarc_DC_TAG_RANGE]            dc3_dt_tag,     // Dirty tag of replacement way
  input                            dc3_dt_val,     // Valid bit of replacement way
  input [`npuarc_DC_TAG_TAG_DATA_RANGE]   dc4_dt_ecc_corrected,
  input                            dc3_status_lru,   // Read LRU for replacement
  input [`npuarc_DC_WAY_RANGE]            dc3_status_lock,  // Read lock bits
  input [`npuarc_DC_WAY_RANGE]            dc3_status_dirty, // Read dirty bits
  
  input [`npuarc_DC_DATA_RANGE]           dc4_dd_data       // DC4 pipeline data
// leda NTL_CON13C on
// leda NTL_CON37 on
);
// leda W175 off
// LMD: A parameter has been defined but is not used.
// LJ:  Code more readable; 

// Local Declarations
//
wire  [3:0]                cb_dc_state_next;
wire                       cb_dc_counter_done_next;
wire			               cb_way_select_next;
wire 			               cb_data_valid_next;
wire 			               cb_status_ready_next;
wire 			               cb_ack_ok_next;

wire                       cb_read_state_next;
wire                       cb_buf_write_next;
wire                       cb_buf_write_valid_next;
wire                       cb_buf_write_cnt_done_next;


reg  [3:0]                cb_dc_state_r;
reg  [3:0]                cb_dc_state_nxt;
reg  [2-1:0]             cb_dc_counter_r;
reg  [2-1:0]             cb_dc_counter_nxt;
wire  [2-1:0]            cb_dc_counter_next;
wire [2-1:0]             cb_dc_counter_incr;

wire                      cb_dc_counter_done_nxt;
reg                       cb_dc_counter_done_r;
wire                      cb_dc_counter_zero;

reg                       cb_way_select;
reg                       cb_way_select_nxt;

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: some variabled are not used in certain configurations
reg                       cb_cache_op_r;
reg                       cb_cache_op_nxt;
reg                       cb_cache_op_next;
reg                       cb_cache_op_cg0;
// leda NTL_CON13A on

reg                       lru_way_dirty;

reg                       cb_data_valid_r;
reg                       cb_data_valid_nxt;
reg                       cb_tag_valid;

reg                       cb_status_ready_r;
reg                       cb_status_ready_nxt;
reg                       cb_ack_ok_r;

// DC to buffer FSM
//
reg                       cb_buf_wr_addr;
reg                       cb_buf_write_r;
reg                       cb_buf_write_nxt;
reg                       cb_buf_write_valid_r;
reg                       cb_buf_write_valid_nxt;
reg [2-1:0]              cb_buf_write_cnt_r;
reg [2-1:0]              cb_buf_write_cnt_nxt;
wire [2-1:0]             cb_buf_write_cnt_next;
wire [2-1:0]             cb_buf_write_cnt_incr;
wire                      cb_buf_write_cnt_done_nxt;
reg                       cb_buf_write_cnt_done_r;
wire                      cb_evict_valid;

wire                      cb_buf_write_complete;
reg                       cb_read_state_r;
reg                       cb_read_state_nxt;

// CB buffer
//
reg [`npuarc_CB_NR_BUF-1:0]      cb_buf_channel_r;    // 0: wr ch, 1: snp ch
reg                       cb_buf_channel_nxt;  // 0: wr ch, 1: snp ch
wire                      cb_buf_channel;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg  [`npuarc_PADDR_RANGE]       cb_buf_addr_r;
wire  [`npuarc_PADDR_RANGE]      cb_buf_addr;
reg  [`npuarc_PADDR_RANGE]       cb_buf_addr_nxt;
reg                       cb_buf_addr_cg0;

reg  [`npuarc_WORD0_RANGE]       cb_buf_data_r0;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_nxt0;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_r1;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_nxt1;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_r2;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_nxt2;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_r3;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_nxt3;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_r4;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_nxt4;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_r5;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_nxt5;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_r6;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_nxt6;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_r7;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_nxt7;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_r8;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_nxt8;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_r9;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_nxt9;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_r10;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_nxt10;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_r11;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_nxt11;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_r12;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_nxt12;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_r13;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_nxt13;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_r14;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_nxt14;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_r15;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_nxt15;   
reg  [`npuarc_WORD0_RANGE]       cb_buf_data_r[`npuarc_CB_FIFO_RANGE];
reg  [`npuarc_CB_NR_BUF_RANGE]   cb_buf_aux_flush_r;
wire                      cb_buf_aux_flush;
wire                      cb_aux_flush;
// leda NTL_CON32 on

reg  [`npuarc_CB_FIFO_RANGE]     cb_buf_valid_r;    
reg  [`npuarc_CB_FIFO_RANGE]     cb_buf_valid_nxt;    
reg  [`npuarc_CB_NR_BUF_RANGE]   cb_buf_used_r;
wire  [`npuarc_CB_NR_BUF_RANGE]  cb_buf_used_incr;
wire  [`npuarc_CB_NR_BUF_RANGE]  cb_buf_used_decr;
wire                      cb_buf_used_max;
reg  [`npuarc_CB_NR_BUF_RANGE]   cb_buf_wr_id_r;   // id of the copy back 
wire  [`npuarc_CB_NR_BUF_RANGE]  cb_buf_wr_id_incr;
reg  [`npuarc_CB_NR_BUF_RANGE]   cb_buf_rd_id_r;   // id of the copy back 
wire  [`npuarc_CB_NR_BUF_RANGE]  cb_buf_rd_id_incr;

reg  [`npuarc_CB_FIFO_RANGE]     cb_buf_err_r;    
reg  [`npuarc_CB_FIFO_RANGE]     cb_buf_err_nxt;    
wire                      cb_pending;

reg                       cb_buf_ctrl_cg0;
reg  [`npuarc_CB_NR_BUF_RANGE]   cb_buf_used_next;     
reg  [`npuarc_CB_NR_BUF_RANGE]   cb_buf_wr_id_next;     
reg  [`npuarc_CB_NR_BUF_RANGE]   cb_buf_rd_id_next;     
reg  [`npuarc_CB_NR_BUF_RANGE]   cb_buf_aux_flush_next; 
reg  [`npuarc_CB_NR_BUF_RANGE]   cb_buf_used_nxt;     
reg  [`npuarc_CB_NR_BUF_RANGE]   cb_buf_wr_id_nxt;     
reg  [`npuarc_CB_NR_BUF_RANGE]   cb_buf_rd_id_nxt;     
reg  [`npuarc_CB_NR_BUF_RANGE]   cb_buf_aux_flush_nxt; 
wire  [`npuarc_CB_NR_BUF_RANGE]  cb_buf_aux_flush_incr; 

reg                       cb_buf_wr_ptr_cg0;
reg  [`npuarc_CB_PTR_RANGE]      cb_buf_wr_ptr_r;
reg  [`npuarc_CB_PTR_RANGE]      cb_buf_wr_ptr_nxt;
wire [`npuarc_CB_PTR_RANGE]      cb_buf_wr_ptr_next;
wire [`npuarc_CB_PTR_RANGE]      cb_buf_rd_ptr_next;

wire [`npuarc_CB_PTR_RANGE]      wr_ptr0;
wire [`npuarc_CB_PTR_RANGE]      wr_ptr1;
wire [`npuarc_CB_PTR_RANGE]      wr_ptr2;
wire [`npuarc_CB_PTR_RANGE]      wr_ptr3;
wire [`npuarc_CB_PTR_RANGE]      wr_ptr4;

reg  [`npuarc_CB_PTR_RANGE]      cb_buf_rd_ptr_r;
reg  [`npuarc_CB_PTR_RANGE]      cb_buf_rd_ptr_nxt;
wire  [`npuarc_CB_PTR_RANGE]     cb_buf_rd_ptr_start;
wire [`npuarc_CB_PTR_RANGE]      rd_ptr0;
wire [`npuarc_CB_PTR_RANGE]      rd_ptr1;
wire [`npuarc_CB_PTR_RANGE]      rd_ptr2;
wire [`npuarc_CB_PTR_RANGE]      rd_ptr3;
wire [`npuarc_CB_PTR_RANGE]      rd_ptr4;
// Buffer to BIU FSM
// 
reg                       cb_biu_push;
reg                       cb_buf_pop; 

reg [1:0]                 cb_biu_state_r;
reg [1:0]                 cb_biu_state_nxt;
wire [1:0]                cb_biu_state_next;

reg [2-1:0]              cb_biu_wr_cnt_r;
reg [2-1:0]              cb_biu_wr_cnt_nxt;
wire [2-1:0]             cb_biu_wr_cnt_next;
wire [2-1:0]             cb_biu_wr_cnt_incr;
reg                       cb_biu_idle;

reg                       cb_line_addr_cg0;
reg [`npuarc_DC_LBUF_RANGE]      cb_line_addr_nxt;



reg [`npuarc_DC_TAG_TAG_DATA_RANGE]   dc4_dt_ecc_corrected_r;
reg [`npuarc_DC_TAG_TAG_DATA_RANGE]   dc4_dt_ecc_corrected_nxt;
//////////////////////////////////////////////////////////////////////////
//                                                                        
// Asynchronous process to find out the LRU way of the set      
//                                                                        
//////////////////////////////////////////////////////////////////////////
always @*
begin : lru_way_PROC
  
  casez (dc3_status_lock)                    
  2'b00:   cb_way_select = dc3_status_lru;      
  2'b01:   cb_way_select = 1'b1;            
  2'b10:   cb_way_select = 1'b0;            
  default: cb_way_select = cb_way_select_r;    
  endcase                                
end

//////////////////////////////////////////////////////////////////////////
//                                                                        
// Asynchronous process to determine whether an eviction is needed      
//                                                                        
//////////////////////////////////////////////////////////////////////////
always @*
begin : evict_PROC
  // If dirty, then write the cache line back to memory
  //
  lru_way_dirty = (cb_way_select ? dc3_status_dirty[1] : dc3_status_dirty[0]);
end


//////////////////////////////////////////////////////////////////////////
//                                                                        
// Handy variables     
//                                                                        
//////////////////////////////////////////////////////////////////////////

// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  One bit incrementor. Never overflows

// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow
//
// cb_dc_counter_done always comes form the flop, we compute the cb_dc_counter_done_nxt
// one cycle early and use the registered version
//
assign cb_dc_counter_done_nxt = cb_dc_counter_nxt == {2{1'b1}};
assign cb_dc_counter_zero     = cb_dc_counter_r == {2{1'b0}};
assign cb_dc_counter_incr     = cb_dc_counter_r + 2'h1;
// leda W484 on
// leda BTTF_D002 on
// leda B_3200 on

//////////////////////////////////////////////////////////////////////////
//                                                                        
// CB FSM       
//                                                                        
//////////////////////////////////////////////////////////////////////////
parameter CB_IDLE               = 4'b0000;
parameter CB_READ_STATUS0       = 4'b0001;
parameter CB_READ_STATUS1       = 4'b0010;
parameter CB_BUF_UNAVAILABLE    = 4'b0011;
parameter CB_INVALIDATE         = 4'b0100;
parameter CB_READ_DATA0         = 4'b0101;
parameter CB_READ_DATA1         = 4'b0110;
parameter CB_WAIT_BUF           = 4'b0111;
parameter CB_WAIT_DONE          = 4'b1000;

////////////////////////////////////////////////////////////////////////////
//
//
//          |     DC1     |    DC2     |   DC3      |    DC4     |
//          |             |            |            |            |
//          |      _______|____________|____________|____        |
//          |     |       |            |            |    |       |
//          |     |       |            |            |_   |       |
//          |     |(Wr)  _|      ______|_____       | |          |
//          | DS  ----->| |     |      |     |      |_| DIRTY    |
//          | REQ ----->|_|     | DS   |     |      |            |
//          |      (Rd)   |     | MEM  |     |      |_           |
//          |             |     |      |     |      | | LRU      |
//          |             |     |______|_____|      |_|          |
//          |             |_           |            |            |
//          |             | | DS_ACK   |            |            |
//          |             |_|          |            |            |
//          |             |            |            |            |
//          |             |            |            |            |
//
////////////////////////////////////////////////////////////////////////////

always @*
begin : dmu_cb_fsm_PROC
  // Data tag
  //
  cb_req_dt_even            = 1'b0;
  cb_req_dt_odd             = 1'b0; 
  cb_dt_odd_sel             = mq_addr[`npuarc_DC_TAG_BANK_ID];
  cb_dt_way_hot             = {cb_way_select_r, ~cb_way_select_r};
  cb_dt_wem                 = 3'b010;  // Exclusive, Valid, Tag;     
  cb_dt_we                  = 1'b0;      
  cb_dt_addr                = mq_addr[`npuarc_DC_IDX_RANGE]; 
  cb_dt_valid               = 1'b0;
  cb_dt_tag                 = `npuarc_DC_TAG_BITS'b0;
  
  // Data Data
  //
  cb_req_dd                 = 1'b0;
  cb_evict_rd               = 1'b0;
  cb_dd_way_hot             = {cb_way_select_r, ~cb_way_select_r};
  cb_dd_we                  = 1'b0;
  cb_dd_addr                = {mq_addr[`npuarc_DC_DADR_RANGE], cb_dc_counter_r};

  // Status (dirty, lock, lru)
  //
  cb_req_ds                 = 1'b0;  
  cb_ds_odd_sel             = mq_addr[`npuarc_DC_TAG_BANK_ID];
  cb_ds_we                  = 1'b0; 
  cb_ds_lru                 = cb_way_select_r;
  cb_ds_wem                 = 3'b000;  
  cb_ds_way_hot             = {cb_way_select_r, ~cb_way_select_r};
  cb_ds_addr                = mq_addr[`npuarc_DC_IDX_RANGE];    
  
  // Line address being worked on
  //
  cb_line_addr_cg0          = 1'b0;
  cb_line_addr_nxt          = cb_line_addr_r;
  
  // The copy back unit only clears the excl and valid bits. Therefore
  // it is implicit that cb_dt_valid = 1'b0 and cb_dt_excl = 1'b0; The 
  // clearing exclusive and valid are controlled by  cb_dt_wem
  // 
  
  // Control signals for the copy back buffer
  //
  cb_data_valid_nxt        = cb_data_valid_r;
  cb_status_ready_nxt      = cb_status_ready_r;
  cb_tag_valid             = 1'b0;
  
  cb_dc_start              = 1'b0;
  cb_dc_done               = 1'b0;
    
  cb_cache_complete        = 1'b0;
  cb_complete              = 1'b0;
    
  cb_way_valid             = 1'b1;
  cb_way_select_nxt        = cb_way_select_r;
  
  cb_dc_counter_nxt        = cb_dc_counter_r;
  
   
  cb_cache_op_cg0          = 1'b0;
  cb_cache_op_nxt          = cb_cache_op_r;
  
  // FSM state
  //
  cb_dc_idle               = 1'b0;
  cb_dc_state_nxt          = cb_dc_state_r;
  
  case (cb_dc_state_r)
  CB_IDLE:
  begin
    // Get hold of cache for cache maintenance flushes
    //
    cb_dc_idle  = 1'b1;
    cb_dc_start = (mq_cache_flush & (~mq_cache_cb_complete))
                | (mq_cache_lock  & (~mq_cb_complete));

    if (mq_valid)
    begin
      // Figure out what I need to process: cache maintenance or regular miss
      //
      if (  (mq_cache_flush | mq_cache_purge)
          & (~mq_cache_cb_complete))
      begin
        // Cache maintenance: flush or purge
        // I already have the way and the address 
        // information (from aux).The pipline is guaranteed to be empty, so 
        // I dont need  to ask permission for star the  process
        //
        cb_cache_op_cg0   = 1'b1;
        cb_cache_op_nxt   = 1'b1;
        
        cb_data_valid_nxt = 1'b0;
        cb_dc_counter_nxt = {2{1'b0}};
       
        if (mq_cache_flush)
        begin
          // Need to flush the line. Check if the buffer is available
          //
          cb_dc_state_nxt   =  cb_buf_used_max ? CB_BUF_UNAVAILABLE : CB_READ_DATA0; 
        end
        else
        begin
          // Just need to invalidate the line
          //
          cb_dc_state_nxt   = CB_INVALIDATE;
        end
      end
      else if (~mq_cb_complete)
      begin
        // We have a valid mq entry that has not been processed yet.
        //
        cb_cache_op_cg0      = 1'b1;
        cb_cache_op_nxt      = 1'b0;

        cb_line_addr_cg0     = 1'b1;
        cb_line_addr_nxt     = mq_addr[`npuarc_DC_LBUF_RANGE];
        
        if (mq_cache_lock)
        begin
          // Copy back way0. We already know way0 is dirty
          //
          // This stalls DMP pipe in DC2
          //
//          cb_dc_start          = ~cb_ack_ok_r;

          cb_way_select_nxt    = 1'b0;

          cb_data_valid_nxt    = 1'b0;
          cb_dc_counter_nxt    = {2{1'b0}};
       
          cb_dc_state_nxt      =  cb_buf_used_max 
                                ? CB_BUF_UNAVAILABLE 
                                : CB_READ_DATA0;
        end
        else
        begin
          // Regular copy-back processing
          //
          cb_status_ready_nxt  = 1'b0;

          
          if (~dc_pipe_busy)
          begin
            // Copy back only intervenes when there is no valid ld/st in DC2
            // that have not been stalled
            //
            cb_dc_state_nxt      = CB_READ_STATUS0;
          end  
        end
      end
    end  
  end
  
  
  CB_READ_STATUS0:
  begin
    // We have a valid mq entry that has not been processed yet. Let's start
    // by reading the status memory. This stalls DMP pipe in DC2
    //
    cb_req_ds           = ~cb_status_ready_r;
    
    // This stalls DMP pipe in DC2
    //
    cb_dc_start          = ~cb_ack_ok_r;
    
    // The status information is available in DC3 
    //
    cb_status_ready_nxt = cb_ack_ok | cb_status_ready_r; 
    
    // Check if there is any set conflict with instructions in the DMP pipe or
    // in the WQ
    //
    if (  cb_ack_ok_r
        & cb_status_ready_r)
    begin
      // No conflict. Let's proceed
      //
      cb_dc_counter_nxt = {2{1'b0}};
      cb_dc_state_nxt   = CB_READ_STATUS1;
    end
  end
  
  CB_READ_STATUS1:
  begin
    // Remember the replacement way
    //
    cb_way_select_nxt    = cb_way_select;
    
    if (& dc3_status_lock)
    begin
      // Both ways are "locked". 
      cb_way_select_nxt    = 1'b0;
      
      if (dc3_status_dirty[0])
      begin
        // way0 needs to be evicted
        //
        cb_data_valid_nxt = 1'b0;
        cb_dc_state_nxt   =  (cb_buf_busy_r | cb_full) 
                            ?  CB_BUF_UNAVAILABLE
                            :  CB_READ_DATA0;
      end
      else
      begin
        // No need to do an eviction. Lets just invalidate the tag
        //
        cb_dc_state_nxt = CB_INVALIDATE;
      end
    end
    else if (lru_way_dirty)
    begin
      // LRU needs to be evicted
      //
      cb_data_valid_nxt = 1'b0;
      cb_dc_state_nxt   =  (cb_buf_busy_r | cb_full) 
                          ?  CB_BUF_UNAVAILABLE
                          :  CB_READ_DATA0;
    end
    else
    begin
      // No need to do an eviction. Lets just invalidate the tag
      //
      cb_dc_state_nxt = CB_INVALIDATE;
    end
  end
  
  CB_BUF_UNAVAILABLE:
  begin
    // Wait until the eviction buffer is available
    //
    if (  (cb_buf_busy_r == 1'b0)
        & (cb_full       == 1'b0))
    begin
      cb_dc_state_nxt   = CB_READ_DATA0;
    end
  end
  
  CB_READ_DATA0:
  begin
    // DD memory (read)
    //
    cb_req_dd             = 1'b1;
    cb_dd_we              = 1'b0;
    cb_dd_addr            = {mq_addr[`npuarc_DC_DADR_RANGE], cb_dc_counter_r}; 
    cb_dd_way_hot         =  cb_cache_op_r 
                           ? {mq_cache_way, ~mq_cache_way}
                           : {cb_way_select_r, ~cb_way_select_r};
    
    // DT memory (read) to find out the evicted address
    //
    // (1) in case of cache_op that does only eviction without invalidation
    //     read the tags here
    //
    cb_req_dt_even        =    cb_dc_counter_zero
                            & (~(cb_cache_op_r & mq_cache_purge))  // (1)
                            & (~mq_addr[`npuarc_DC_TAG_BANK_ID]);
    cb_req_dt_odd         =   cb_dc_counter_zero 
                            & (~(cb_cache_op_r & mq_cache_purge))  // (1)
                            & mq_addr[`npuarc_DC_TAG_BANK_ID];

    cb_dt_way_hot         =  cb_cache_op_r
                          ? {mq_cache_way, ~mq_cache_way}
                          : {cb_way_select_r, ~cb_way_select_r};

    cb_dt_we              = 1'b0;
    
    cb_evict_rd           = 1'b1;
    
    cb_tag_valid          =  dc3_dt_val
                           | cb_cache_op_r
                           | 1'b1
                           ;

    cb_dc_state_nxt       = CB_READ_DATA1;
  end
  
  CB_READ_DATA1:
  begin
    // No access to DD this cycle
    //
    cb_evict_rd           = 1'b1;
   

    if (cb_dc_counter_zero)
    begin
      
      // Lets clear the valid and dirty bits of the evicted way.
      //
      // (1) in case of cache_op that does invalidation do the invalidation here
      //
      cb_req_dt_even        = ~mq_addr[`npuarc_DC_TAG_BANK_ID]
                            & (~cb_cache_op_r | (cb_cache_op_r & mq_cache_purge)); // (1)
  
      cb_req_dt_odd         = mq_addr[`npuarc_DC_TAG_BANK_ID]
                            & (~cb_cache_op_r | (cb_cache_op_r & mq_cache_purge)); // (1)  

      cb_dt_we              = (mq_cache_purge | (~cb_cache_op_r)); 

      cb_dt_way_hot         =  cb_cache_op_r 
                             ? {mq_cache_way, ~mq_cache_way}
                             : {cb_way_select_r, ~cb_way_select_r};

      cb_dt_wem             = { 1'b0,                               // excl
                               (mq_cache_purge | (~cb_cache_op_r)), // valid
                               1'b0};                               // tag
      
      // Status (dirty, lock, lru)
      //
      cb_req_ds             = 1'b1;
      cb_ds_we              = 1'b1;
      cb_ds_way_hot         =   cb_cache_op_r 
                              ? {mq_cache_way, ~mq_cache_way}
                              : {cb_way_select_r, ~cb_way_select_r};
      cb_ds_wem             =   {(mq_cache_purge & cb_cache_op_r),  // lock
                                 1'b1,                              // dirty
                                 1'b0};                             //lru
    end
    
    if (cb_dc_counter_zero)
    begin
      cb_data_valid_nxt     = 1'b1;
    end
    
    if (cb_dc_counter_done_r)
    begin
      cb_dc_done            = 1'b1;
      cb_dc_state_nxt       = CB_WAIT_BUF;
    end
    else
    begin
      // Lets start another eviction cycle by reading the Data memories
      //
      cb_dc_counter_nxt     = cb_dc_counter_incr;
      cb_dc_state_nxt       = CB_READ_DATA0; 
    end
  end
  
  CB_WAIT_BUF:
  begin
    // This state waits until all the cache contents have been written into
    // the copy back buffer
    //
    cb_evict_rd             = 1'b1;
    cb_dd_way_hot           =  cb_cache_op_r
                             ? {mq_cache_way, ~mq_cache_way}
                                : {cb_way_select_r, ~cb_way_select_r};
    
    
    if (cb_buf_write_complete)
    begin
      cb_evict_rd         = 1'b0;
      cb_complete         = ~cb_cache_op_r; 
      cb_status_ready_nxt = 1'b0;
    
      cb_cache_complete   = cb_cache_op_r;
      cb_cache_op_cg0     = 1'b1;
      cb_cache_op_nxt     = 1'b0;

      cb_dc_state_nxt     = CB_IDLE;
    end
  end

  
  CB_INVALIDATE:
  begin
    // Invalidate the tag to prevent further accesses to it until the refill
    // unit makes it valid. 
    //
    // Data tag
    //
    cb_req_dt_even      = ~mq_addr[`npuarc_DC_TAG_BANK_ID];
    cb_req_dt_odd       =  mq_addr[`npuarc_DC_TAG_BANK_ID];
    cb_dt_we            = 1'b1;
    cb_dt_way_hot       =  cb_cache_op_r 
                         ? {mq_cache_way, ~mq_cache_way}
                         : {cb_way_select_r, ~cb_way_select_r};
    cb_dt_wem           = { 1'b0,                                    // excl
                           (mq_cache_purge | (~cb_cache_op_r)),      // valid
                           1'b0};                                    // tag
    
    // Status (dirty, lock, lru)
    //
    cb_req_ds           = 1'b1;
    cb_ds_we            = 1'b1;
    cb_ds_wem           = {(mq_cache_purge & cb_cache_op_r), 
                           1'b1, 
                           1'b1}; // lock, dirty, lru;
    cb_ds_way_hot       =  cb_cache_op_r 
                         ? {mq_cache_way, ~mq_cache_way}
                         : {cb_way_select_r, ~cb_way_select_r};

    // Make the way that CB is invalidating as LRU
    //
    cb_ds_lru           =  cb_cache_op_r
                         ? mq_cache_way
                         : cb_way_select_r; 
      
    cb_cache_complete   = cb_cache_op_r;
    cb_complete         = ~cb_cache_op_r; 
    cb_dc_done          = ~cb_cache_op_r; 
    cb_status_ready_nxt = 1'b0;
    cb_cache_op_cg0     = 1'b1;
    cb_cache_op_nxt     = 1'b0;
    cb_dc_state_nxt     = CB_IDLE;
  end
  
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept  
  default:
    ;
  endcase  
end
// spyglass enable_block W193
// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ: Pointer arithmetic: incremented value will not overflow

// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow
assign cb_buf_write_cnt_incr = cb_buf_write_cnt_r + 2'h1;

//
// cb_buf_write_cnt_done always comes form the flop, we compute the cb_buf_write_cnt_done_nxt
// one cycle early and use the registered version
//
assign cb_buf_write_cnt_done_nxt = (& cb_buf_write_cnt_nxt);
assign cb_evict_valid        =    mq_cache_lock
                                | cb_tag_valid
                                ;
// leda W484 on
// leda BTTF_D002 on
// leda B_3200 on
//////////////////////////////////////////////////////////////////////////
//                                                                        
// This is a small FSM that controls the reading of the two-cycle DD memory
// and the write into the copy back buffer     
//                                                                        
//////////////////////////////////////////////////////////////////////////


parameter CB_READ_DC_IDLE    = 1'b0;
parameter CB_READ_DC_TO_BUF  = 1'b1;

always @*
begin : cb_buf_fsm_PROC
  // The evict address, computed by reading the tags is written into the
  // copy back buffer when cb_buf_wr_addr is asserted 
  //
  cb_buf_wr_addr         = 1'b0;
  cb_buf_write_nxt       = 1'b0; 
  cb_buf_write_valid_nxt = cb_buf_write_valid_r;
  cb_buf_write_cnt_nxt   = cb_buf_write_cnt_r;
  
  cb_read_state_nxt      = cb_read_state_r;
  
  case (cb_read_state_r)
  CB_READ_DC_IDLE:
  begin
    if (  cb_evict_rd
        & cb_data_valid_r)
    begin
      // The read flow is in "DC3". We capture the address at this cycle. The 
      // memory data is being written into the DC4 dd flops
      //
      cb_buf_wr_addr         = cb_evict_valid;
      cb_buf_write_nxt       = cb_evict_valid;
      // This is valid only when the tags are valid or this is a snoop flush
      //
      cb_buf_write_valid_nxt = cb_evict_valid;
      
      cb_buf_write_cnt_nxt   = 2'b0;
      cb_read_state_nxt      = CB_READ_DC_TO_BUF;
    end
  end
  
  CB_READ_DC_TO_BUF:
  begin
    // The data from the cache is coming every other cycle
    //
    cb_buf_write_nxt = !cb_buf_write_r;
    
    if (cb_buf_write_r)
    begin
      cb_buf_write_cnt_nxt = cb_buf_write_cnt_incr[2-1:0];
      
      if (cb_buf_write_cnt_done_r)
      begin
        // This is the last write from the cache into the copy back buffer
        //
        cb_buf_write_nxt      = 1'b0;
        cb_read_state_nxt     = CB_READ_DC_IDLE;
      end
    end
  end
// spyglass disable_block W193
// SMD: empty statements
// SJ:  empty default statements kept
  default:
   ;
// spyglass enable_block W193
  endcase
end

assign cb_buf_write_complete  = cb_buf_write_r  & cb_buf_write_cnt_done_r;

// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  One bit incrementor. Never overflows

// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow
assign cb_biu_wr_cnt_incr = cb_biu_wr_cnt_r + 2'h1;

assign cb_buf_used_incr   = cb_buf_used_r + 1'b1;
assign cb_buf_used_decr   = cb_buf_used_r - 1'b1;

//`if (`CB_NR_BUF == 1) // {
assign cb_buf_wr_id_incr = cb_buf_wr_id_r + 1'b1;
assign cb_buf_rd_id_incr = cb_buf_rd_id_r + 1'b1;
//`endif // }

// leda W484 on
// leda BTTF_D002 on
// leda B_3200 on

assign cb_buf_used_max        = cb_buf_used_r == `npuarc_CB_NR_BUF;

//////////////////////////////////////////////////////////////////////////////
// Copy Back Buffer BIU FSM
// 
//////////////////////////////////////////////////////////////////////////////
parameter CB_BIU_IDLE           = 2'b00;
parameter CB_BIU_WAIT_ACCEPT    = 2'b01;
parameter CB_BIU_WR_DATA        = 2'b10;

// leda NTL_CON16 off
// LMD: Nets or cell pins should not be tied to logic 0 / logic 1
// LJ:  Copy back address is always cache line aligned

reg  [`npuarc_PADDR_RANGE]       cb_buf_addr_qual;

reg                       cb_cmd_addr_saved_cg0;
reg  [`npuarc_PADDR_RANGE]       cb_cmd_addr_saved_nxt;
reg  [`npuarc_PADDR_RANGE]       cb_cmd_addr_saved_r;

always @*
begin
  //
  //
  // The corrected address comes form DC4
  //
  cb_buf_addr_qual                = cb_buf_addr;
  cb_buf_addr_qual[`npuarc_DC_TAG_RANGE] = (
                                       1'b0 
                                     | cb_cache_op_r | ecc_dmp_disable)
                           
                                  ? cb_buf_addr[`npuarc_DC_TAG_RANGE]
                                  : (cb_evict_rd ? dc4_dt_ecc_corrected[`npuarc_DC_TAG_TAG_RANGE] : dc4_dt_ecc_corrected_r[`npuarc_DC_TAG_TAG_RANGE]);
end

always @*
begin : cb_biu_fsm_PROC
  cb_cmd_valid         = 1'b0;
  cb_cmd_read          = 1'b0;
  cb_cmd_addr          = {cb_buf_addr_qual[`npuarc_DC_LBUF_RANGE], {`npuarc_DC_BLOCK_BITS{1'b0}}}; 
  cb_cmd_prot          = 1'b1;
  cb_cmd_wrap          = 1'b0;
  cb_cmd_burst_size    = 4'b0011;

  cb_wr_valid           = 1'b0;
  cb_wr_data            = {cb_buf_data_r[rd_ptr3], cb_buf_data_r[rd_ptr2],
                           cb_buf_data_r[rd_ptr1], cb_buf_data_r[rd_ptr0]};
  cb_wr_last            = 1'b0;
  cb_wr_mask            = {`npuarc_RF_CB_MASK_SIZE{1'b1}};

  cb_cmd_addr_saved_cg0 = 1'b0;
  cb_cmd_addr_saved_nxt = cb_cmd_addr_saved_r;

  
  cb_biu_push       = 1'b0;
  cb_buf_pop        = 1'b0; 

  cb_buf_rd_ptr_nxt = cb_buf_rd_ptr_r;
  cb_biu_wr_cnt_nxt = cb_biu_wr_cnt_r;
  
  // FSM state
  //
  cb_biu_idle       = 1'b0;
  cb_biu_state_nxt  = cb_biu_state_r;
  
  case (cb_biu_state_r)
  CB_BIU_IDLE:
  begin
    cb_biu_idle     = 1'b1;
    
    if (cb_buf_busy_r)
    begin
      // The copy back buffer is receiving data from the cache
      //
      if (  (cb_buf_channel == 1'b0)
          // @@@ these should be from the output of the copy-back buffer
          //
          & (  dc4_dt_ecc_corrected[`npuarc_DC_TAG_VALID_BIT]
             | cb_evict_error_r 
             | cb_cache_op_r     
            )  
         )
      begin
        // Check for max number of outstanding transactions
        //
        if (cb_full == 1'b0)
        begin
          // We have the copy back address information
          //
          cb_cmd_valid = 1'b1;
          cb_biu_push  = 1'b1;

          if (cb_cmd_accept)
          begin
            cb_biu_wr_cnt_nxt = {2{1'b0}};
            cb_buf_rd_ptr_nxt = cb_buf_rd_ptr_start;
            cb_biu_state_nxt  = CB_BIU_WR_DATA;
          end
          else
          begin
            cb_cmd_addr_saved_cg0 = 1'b1;
            cb_cmd_addr_saved_nxt = {cb_buf_addr_qual[`npuarc_DC_LBUF_RANGE], {`npuarc_DC_BLOCK_BITS{1'b0}}};
            cb_biu_state_nxt      = CB_BIU_WAIT_ACCEPT;
          end
        end
      end
      else if (  (cb_buf_channel == 1'b0)
               & (~ (  dc4_dt_ecc_corrected[`npuarc_DC_TAG_VALID_BIT]
                     | cb_evict_error_r       
                     | cb_cache_op_r     
                 )  )
              & (&cb_buf_valid_r))
    begin
      cb_buf_pop       = 1'b1;
      cb_biu_state_nxt = CB_BIU_IDLE;
    end    
      
    end
  end
  
  CB_BIU_WAIT_ACCEPT:
  begin
    cb_cmd_valid = 1'b1;

    cb_cmd_addr  = cb_cmd_addr_saved_r;

    if (cb_cmd_accept)
    begin
      cb_biu_wr_cnt_nxt  = {2{1'b0}};
      cb_buf_rd_ptr_nxt  = cb_buf_rd_ptr_start;
      cb_biu_state_nxt   = CB_BIU_WR_DATA;
    end
  end
  
  CB_BIU_WR_DATA:
  begin
    cb_wr_valid =   cb_buf_valid_r[rd_ptr0] 
                  & cb_buf_valid_r[rd_ptr1]
                  & cb_buf_valid_r[rd_ptr2]
                  & cb_buf_valid_r[rd_ptr3];
    if (  cb_buf_err_r[rd_ptr0] 
        | cb_buf_err_r[rd_ptr1]
        | cb_buf_err_r[rd_ptr2]
        | cb_buf_err_r[rd_ptr3]
       )
      cb_wr_mask  = {`npuarc_RF_CB_MASK_SIZE{1'b0}};
    else
      cb_wr_mask  = {`npuarc_RF_CB_MASK_SIZE{1'b1}};
// leda W563 off
// LMD: reduction of single bit expression is redundant
// LJ:  configurable field may be a single bit
    cb_wr_last  = & cb_biu_wr_cnt_r;
    
    if (cb_wr_valid & cb_wr_accept)
    begin
      // Increment the read pointer by 4 (128-bit interface)
      //
     cb_buf_rd_ptr_nxt = rd_ptr4;
     
      if (& cb_biu_wr_cnt_r)
      begin
        cb_buf_pop       = 1'b1;
        cb_biu_state_nxt = CB_BIU_IDLE;
      end
      else
      begin
        cb_biu_wr_cnt_nxt = cb_biu_wr_cnt_incr;
      end
    end
  end

// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept 
  default:
    ;
  endcase
end
// spyglass enable_block W193
// leda NTL_CON16 on

// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  One bit incrementor. Never overflows

// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow
// Helpers
//
assign wr_ptr0 = cb_buf_wr_ptr_r;
assign wr_ptr1 = cb_buf_wr_ptr_r + `npuarc_CB_PTR_DEPTH'h1;
assign wr_ptr2 = cb_buf_wr_ptr_r + `npuarc_CB_PTR_DEPTH'h2;
assign wr_ptr3 = cb_buf_wr_ptr_r + `npuarc_CB_PTR_DEPTH'h3;
assign wr_ptr4 = cb_buf_wr_ptr_r + `npuarc_CB_PTR_DEPTH'h4;

// Helpers
//
assign rd_ptr0 = cb_buf_rd_ptr_r;
assign rd_ptr1 = cb_buf_rd_ptr_r + `npuarc_CB_PTR_DEPTH'h1;
assign rd_ptr2 = cb_buf_rd_ptr_r + `npuarc_CB_PTR_DEPTH'h2;
assign rd_ptr3 = cb_buf_rd_ptr_r + `npuarc_CB_PTR_DEPTH'h3;
assign rd_ptr4 = cb_buf_rd_ptr_r + `npuarc_CB_PTR_DEPTH'h4;

// leda W484 on
// leda BTTF_D002 on
// leda B_3200 on

//////////////////////////////////////////////////////////////////////////////
// Write Pointer manipulation: the wr_ptr is incremented by 4 on every write
// from the Data Cache.
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : cb_buf_wr_ptr_PROC
  // Clock gate enable
  //
  cb_buf_wr_ptr_cg0 = cb_buf_write_complete | cb_buf_write_r;
  
  casez ({cb_buf_write_complete, cb_buf_write_r})
  2'b1?:
  begin
    cb_buf_wr_ptr_nxt = {`npuarc_CB_PTR_DEPTH{1'b0}};
  end
  
  2'b01:
  begin
    // Increment the write pointer by 4 (4*32 bits chunk of data has been written)
    //
    cb_buf_wr_ptr_nxt = wr_ptr4;
  end
  
  default:
  begin
    cb_buf_wr_ptr_nxt = cb_buf_wr_ptr_r;
  end  
  endcase
end

assign cb_buf_rd_ptr_start = {`npuarc_CB_PTR_DEPTH{1'b0}};

assign cb_buf_addr         = cb_buf_addr_r;
assign cb_buf_channel      = cb_buf_channel_r;

//////////////////////////////////////////////////////////////////////////////
// Process to compute the _nxt buf state variables 
// 
//
//////////////////////////////////////////////////////////////////////////////

assign cb_aux_flush          = mq_cache_flush & (~mq_cache_purge);
assign cb_buf_aux_flush      =  cb_buf_aux_flush_r;
assign cb_buf_busy_r         = | cb_buf_used_r; // @@@ naming

assign cb_buf_aux_flush_incr = cb_buf_aux_flush_r + 1'b1;

// spyglass disable_block W484 
// SMD: Possible loss of carry/borrow in addition/subtraction LHS
// SJ: Pointer arithmetic: incremented value will not overflow
//
// spyglass disable_block W164a
// SMD: LHS width < RHS in assignment
// SJ:  correct width will be used

always @*
begin : cb_buf_ctrl_PROC
  // Clock gate
  //
  cb_buf_ctrl_cg0 = cb_buf_wr_addr | cb_buf_pop;
  
  casez ({cb_buf_wr_addr, cb_buf_pop})
  2'b10:
  begin
    // Pushing...
    //
    cb_buf_used_nxt      = cb_buf_used_incr;
    cb_buf_wr_id_nxt     = cb_buf_wr_id_incr;
    cb_buf_rd_id_nxt     = cb_buf_rd_id_r;
    cb_buf_aux_flush_nxt = cb_buf_aux_flush_r + cb_aux_flush;
  end

  2'b01:
  begin
    // Popping...
    //
    cb_buf_used_nxt      = cb_buf_used_decr;
    cb_buf_wr_id_nxt     = cb_buf_wr_id_r;
    cb_buf_rd_id_nxt     = cb_buf_rd_id_incr;
    cb_buf_aux_flush_nxt =  (| cb_buf_aux_flush_r) 
                         ? cb_buf_aux_flush_r - 1'b1
                         : cb_buf_aux_flush_r;
  end

  2'b11:
  begin
    // Pushing and popping
    //
    cb_buf_used_nxt      = cb_buf_used_r; 
    cb_buf_wr_id_nxt     = cb_buf_wr_id_incr;//cb_buf_wr_id_r;
    cb_buf_rd_id_nxt     = cb_buf_rd_id_incr;//cb_buf_rd_id_r;
    cb_buf_aux_flush_nxt = cb_buf_aux_flush_r 
                         + cb_buf_aux_flush_incr 
                         - (| cb_buf_aux_flush_r)
                         ;
  end
  
  default: // 2'b00
  begin
    // No change
    //
    cb_buf_used_nxt      = cb_buf_used_r; 
    cb_buf_wr_id_nxt     = cb_buf_wr_id_r;
    cb_buf_rd_id_nxt     = cb_buf_rd_id_r;
    cb_buf_aux_flush_nxt = cb_buf_aux_flush_r;
  end
  endcase
end    
// spyglass enable_block W164a
// spyglass enable_block W484

always @*
begin : cb_buf_addr_PROC
  // Clock gate enable
  //
  cb_buf_addr_cg0 = cb_buf_wr_addr;
  
  case (1'b1)

  cb_cache_op_r:
  begin
    cb_buf_channel_nxt = 1'b0;
    cb_buf_addr_nxt    = mq_addr;
  end
  
    
  default:
  begin
    cb_buf_channel_nxt = 1'b0;
    cb_buf_addr_nxt    = { dc3_dt_tag, 
                           mq_addr[`npuarc_DC_IDX_RANGE], mq_addr[`npuarc_DC_TAG_BANK_ID],
                           {`npuarc_DC_BLOCK_BITS{1'b0}}
                         };
    
    
  end
  endcase
end




//////////////////////////////////////////////////////////////////////////
//                                                                        
// Module instantiation
//                                                                        
//////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_cb_hazard_fifo  u_alb_dmp_cb_hazard_fifo (
  
  .clk                 (clk               ),       
  .rst_a               (rst_a             ),       




  .cb_wr_push          (cb_biu_push       ), 
  .cb_wr_addr          (cb_cmd_addr       ),       
  .cb_evict_error_r    (cb_evict_error_r  ),

  .cb_wr_done          (cb_wr_done         ),
  .cb_err_wr           (cb_err_wr          ),

  .x3_load_r           (x3_load_r          ),       
  .x3_store_r          (x3_store_r         ),      
  .x3_mem_addr0_r      (x3_mem_addr0_r     ),  
  .x3_mem_addr1_r      (dc3_mem_addr1_r    ), 
  .dc3_dc_target       (dc3_dc_target      ),   
  .dc3_dt_line_cross_r (dc3_dt_line_cross_r), 

  .cbh_pending         (cb_pending         ),
  .cbh_hit             (cb_evict_hit       ),          
  .cbh_full            (cb_full            ),

  .cbh_err_addr        (cb_flush_err_addr  ),         
  .cbh_err_req_r       (cb_flush_err_req   ),    
  .cbh_err_ack         (cb_flush_err_ack   )  
);


//////////////////////////////////////////////////////////////////////////
//                                                                        
// Asynchronous output state  
//                                                                        
//////////////////////////////////////////////////////////////////////////
assign cb_empty =   cb_dc_idle
                  & cb_biu_idle
                  & (~cb_pending)
                  ;


//////////////////////////////////////////////////////////////////////////
//                                                                        
// Synchronous processes   
//                                                                        
//////////////////////////////////////////////////////////////////////////
assign cb_dc_state_next        = 
			cb_dc_state_nxt; 
assign    cb_dc_counter_next     = 
			cb_dc_counter_nxt;
assign    cb_dc_counter_done_next = 
			cb_dc_counter_done_nxt;  
assign    cb_way_select_next     = 
			 cb_way_select_nxt;
assign    cb_data_valid_next     = 
			cb_data_valid_nxt;
assign    cb_status_ready_next  = 
			cb_status_ready_nxt;
assign    cb_ack_ok_next         = 
			cb_dc_start & cb_ack_ok;


always @(posedge clk or posedge rst_a)
begin : cb_dc_state_sync_PROC
  if (rst_a == 1'b1)
  begin
    cb_dc_state_r        <= CB_IDLE;
    cb_dc_counter_r      <= {2{1'b0}};
    cb_way_select_r      <= 1'b0;
    cb_data_valid_r      <= 1'b0;
    cb_status_ready_r    <= 1'b0;
    cb_ack_ok_r          <= 1'b0;
    cb_dc_counter_done_r <= 1'b0;
  end
  else
  begin
    cb_dc_state_r        <= cb_dc_state_next;
    cb_dc_counter_r      <= cb_dc_counter_next;
    cb_dc_counter_done_r <= cb_dc_counter_done_next;  
    cb_way_select_r      <= cb_way_select_next;
    cb_data_valid_r      <= cb_data_valid_next;
    cb_status_ready_r    <= cb_status_ready_next;
    cb_ack_ok_r          <= cb_ack_ok_next;
  end
end

// leda TEST_975 off
// LMD: Latch enabled by a clock affects data input of flipflops clocked by the trailing edge of the same clock
// LJ:
//
// CB->buffer 
//
assign cb_read_state_next         = 
			cb_read_state_nxt;
assign cb_buf_write_next          = 
			cb_buf_write_nxt;
assign cb_buf_write_valid_next    = 
			cb_buf_write_valid_nxt;
assign cb_buf_write_cnt_next      = 
			cb_buf_write_cnt_nxt;
assign cb_buf_write_cnt_done_next = 
			cb_buf_write_cnt_done_nxt;

always @(posedge clk or posedge rst_a)
begin: cb_dc_read_sync_PROC
  if (rst_a == 1'b1)
  begin
    cb_read_state_r         <= CB_READ_DC_IDLE;
    cb_buf_write_r          <= 1'b0;
    cb_buf_write_valid_r    <= 1'b0;
    cb_buf_write_cnt_r      <= {2{1'b0}};
    cb_buf_write_cnt_done_r <= 1'b0;
  end
  else
  begin
    cb_read_state_r         <= cb_read_state_next;
    cb_buf_write_r          <= cb_buf_write_next;
    cb_buf_write_valid_r    <= cb_buf_write_valid_next;
    cb_buf_write_cnt_r      <= cb_buf_write_cnt_next;
    cb_buf_write_cnt_done_r <= cb_buf_write_cnt_done_next;
  end
end
// leda TEST_975 on
// Buffer->BIU 
//
assign cb_biu_state_next   = 
				cb_biu_state_nxt;
assign cb_biu_wr_cnt_next   = 
				cb_biu_wr_cnt_nxt;

always @(posedge clk or posedge rst_a)
begin: cb_biu_sync_PROC
  if (rst_a == 1'b1)
  begin
    cb_biu_state_r    <= CB_BIU_IDLE;
    cb_biu_wr_cnt_r   <= {2{1'b0}};
  end
  else
  begin
    cb_biu_state_r    <= cb_biu_state_next;
    cb_biu_wr_cnt_r   <= cb_biu_wr_cnt_next;
  end
end

// leda FM_1_7 off
// LMD: Signal assigned more than once in a single flow of control
// LJ:  Conflict covered by assertions
//
// spyglass disable_block STARC05-2.2.3.3
// SMD: Flipflop value assigned more than once over same signal in always construct
// SJ:  Conflit covered by assertions
always @*
begin : dc4_dt_ecc_corrected_comb_PROC
  dc4_dt_ecc_corrected_nxt = dc4_dt_ecc_corrected_r;
    if (cb_evict_rd & cb_cmd_valid)
    begin
      dc4_dt_ecc_corrected_nxt   = dc4_dt_ecc_corrected;
    end
end  
always @(posedge clk or posedge rst_a)
begin : dc4_dt_ecc_corrected_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_dt_ecc_corrected_r      <= 27'd0;
  end
  else
  begin
    dc4_dt_ecc_corrected_r    <= dc4_dt_ecc_corrected_nxt;
  end
end  

always @*
begin : cb_buf_valid_comb_PROC
    cb_buf_valid_nxt = cb_buf_valid_r ;
    cb_buf_err_nxt   = cb_buf_err_r   ;
  begin
    if (cb_buf_write_r)
    begin
      cb_buf_valid_nxt[wr_ptr0]            = cb_buf_write_valid_r; 
      cb_buf_valid_nxt[wr_ptr1]            = cb_buf_write_valid_r;  
      cb_buf_valid_nxt[wr_ptr2]            = cb_buf_write_valid_r;  
      cb_buf_valid_nxt[wr_ptr3]            = cb_buf_write_valid_r; 
      // ECC double bit error
      //
      cb_buf_err_nxt[wr_ptr0]              = cb_evict_error_r;  
      cb_buf_err_nxt[wr_ptr1]              = cb_evict_error_r;    
      cb_buf_err_nxt[wr_ptr2]              = cb_evict_error_r;   
      cb_buf_err_nxt[wr_ptr3]              = cb_evict_error_r;  
    end    
    if (cb_buf_pop)
    begin
      cb_buf_valid_nxt                       = {`npuarc_CB_FIFO_DEPTH{1'b0}};
      cb_buf_err_nxt                         = {`npuarc_CB_FIFO_DEPTH{1'b0}};
    end
  end
end
always @(posedge clk or posedge rst_a)
begin : cb_buf_valid_PROC
  if (rst_a == 1'b1)
  begin
    cb_buf_valid_r <= {`npuarc_CB_FIFO_DEPTH{1'b0}};
    cb_buf_err_r   <= {`npuarc_CB_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    cb_buf_valid_r <= cb_buf_valid_nxt;
    cb_buf_err_r   <= cb_buf_err_nxt;
  end
end
// leda FM_1_7 on
// spyglass enable_block STARC05-2.2.3.3

always @(posedge clk or posedge rst_a)
begin : cb_cmd_addr_reg_PROC
  if (rst_a == 1'b1)
  begin
    cb_cmd_addr_saved_r <= {`npuarc_PADDR_SIZE{1'b0}};
  end
  else if (cb_cmd_addr_saved_cg0 == 1'b1)
  begin
    cb_cmd_addr_saved_r <= cb_cmd_addr_saved_nxt;
  end
end


// leda TEST_975 off
// LMD: Latch enabled by a clock affects data input of flipflops clocked by the trailing edge of the same clock
// LJ:

// KS: Conditional reset datapath when safety enabled
always @(posedge clk or posedge rst_a)
begin : cb_buf_channel_PROC
  if (rst_a == 1'b1)
  begin
    cb_buf_channel_r <= 1'b0;
  end
  else if (cb_buf_addr_cg0 == 1'b1)
  begin
    cb_buf_channel_r                 <= cb_buf_channel_nxt;  
  end
end

// Flops that dont need a reset
//
// leda NTL_RST03 off
// LMD: A flipflop without reset
// LJ:  Data path signals that dont require a reset

// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk)
begin : cb_buf_data_reg_PROC
  if (cb_buf_write_r == 1'b1)
  begin
    // Data
    //
    cb_buf_data_r[wr_ptr0]  <= dc4_dd_data[`npuarc_WORD0_RANGE];   
    cb_buf_data_r[wr_ptr1]  <= dc4_dd_data[`npuarc_WORD1_RANGE];   
    cb_buf_data_r[wr_ptr2]  <= dc4_dd_data[`npuarc_WORD2_RANGE];   
    cb_buf_data_r[wr_ptr3]  <= dc4_dd_data[`npuarc_WORD3_RANGE]; 
  end
end

always @(posedge clk)
begin : cb_buf_addr_reg_PROC
  if (cb_buf_addr_cg0 == 1'b1)
  begin
    cb_buf_addr_r                 <= cb_buf_addr_nxt;
  end
end
// leda TEST_975 on
// leda NTL_RST03 on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

always @*
begin : cb_buf_state_comb_PROC
    cb_buf_used_next     = cb_buf_used_r      ;
    cb_buf_wr_id_next    = cb_buf_wr_id_r     ;
    cb_buf_rd_id_next    = cb_buf_rd_id_r     ;
    cb_buf_aux_flush_next= cb_buf_aux_flush_r ;
  if (cb_buf_ctrl_cg0 == 1)
  begin
    cb_buf_used_next      = cb_buf_used_nxt;
    cb_buf_wr_id_next     = cb_buf_wr_id_nxt;
    cb_buf_rd_id_next     = cb_buf_rd_id_nxt;
    cb_buf_aux_flush_next = cb_buf_aux_flush_nxt;
  end
end  
always @(posedge clk or posedge rst_a)
begin : cb_buf_state_reg_PROC
  if (rst_a == 1'b1)
  begin
    cb_buf_used_r      <= {`npuarc_CB_NR_BUF_BITS{1'b0}};
    cb_buf_wr_id_r     <= {`npuarc_CB_NR_BUF_BITS{1'b0}};
    cb_buf_rd_id_r     <= {`npuarc_CB_NR_BUF_BITS{1'b0}};
    cb_buf_aux_flush_r <= {`npuarc_CB_NR_BUF_BITS{1'b0}};
  end
  else
  begin
    cb_buf_used_r      <= cb_buf_used_next;
    cb_buf_wr_id_r     <= cb_buf_wr_id_next;
    cb_buf_rd_id_r     <= cb_buf_rd_id_next;
    cb_buf_aux_flush_r <= cb_buf_aux_flush_next;
  end
end  
assign cb_buf_wr_ptr_next = 
			 cb_buf_wr_ptr_nxt;
assign cb_buf_rd_ptr_next = 
			cb_buf_rd_ptr_nxt;

always @(posedge clk or posedge rst_a)
begin : cb_buf_ptr_PROC
  if (rst_a == 1'b1)
  begin
    cb_buf_wr_ptr_r <= {`npuarc_CB_PTR_DEPTH{1'b0}};
    cb_buf_rd_ptr_r <= {`npuarc_CB_PTR_DEPTH{1'b0}};
  end
  else
  begin
    cb_buf_wr_ptr_r <= cb_buf_wr_ptr_next;
    cb_buf_rd_ptr_r <= cb_buf_rd_ptr_next;
  end
end
always @*
begin : cb_cache_op_comb_PROC
  cb_cache_op_next = cb_cache_op_r;
  if (cb_cache_op_cg0 == 1'b1)
  begin
    cb_cache_op_next = cb_cache_op_nxt;
  end
end
always @(posedge clk or posedge rst_a)
begin : cb_cache_op_PROC
  if (rst_a == 1'b1)
  begin
    cb_cache_op_r     <= 1'b0;
  end
  else
  begin
    cb_cache_op_r  <= cb_cache_op_next;
  end
end

// leda NTL_RST03 off
// leda S_1C_R off
// LMD: A flipflop without reset
// LJ:  Data path signals that dont require a reset

// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
// KS: Conditional reset datapath when safety enabled
always @(posedge clk)
begin : cb_line_addr_PROC
  if (cb_line_addr_cg0 == 1'b1)
  begin
    cb_line_addr_r <= cb_line_addr_nxt;
  end  
end  


// leda S_1C_R on
// leda NTL_RST03 on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01
// leda W175 on
endmodule // alb_dmp_cb

