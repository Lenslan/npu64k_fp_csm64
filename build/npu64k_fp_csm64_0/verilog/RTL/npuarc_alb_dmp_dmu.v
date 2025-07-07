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
//   ALB_DMP_DMU                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements the Data cache Miss Unit. This module acts as an
//  interface between the BIU and the data cache, that is responsible for cache 
//  refill and cache evictions.
//  
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_dmu.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"



//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

//D: error_signal { name: "alb_dmp_lsmq_fifo_edc_err" }
//D: error_signal { name: "alb_dmp_mq_fifo_edc_err" }
//D: error_signal { name: "alb_dmp_cb_edc_err" }
//D: error_signal { name: "alb_dmp_rf_edc_err" }
//D: error_signal { name: "alb_dmp_line_buf_edc_err" }

module npuarc_alb_dmp_dmu (
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used
  ////////// General input signals ///////////////////////////////////////////
  //
  input                        clk,              // clock
  input                        rst_a,            // reset

  input                        ecc_dmp_disable,
  ////////// Interface to the X3 //////////////////////////////////////////
  //

  input                        dc3_dt_line_cross_r,  // addr1 is valid
  input                        dc4_dt_line_cross_r,  // addr1 is valid

  input [`npuarc_DMP_TARGET_RANGE]    dc3_target_r,
  input [`npuarc_DMP_TARGET_RANGE]    dc4_target_r,

  ////////// Interface to the X3 //////////////////////////////////////////
  //
  input                        x3_valid_r,      // X3 has valid instruction 
  input                        x3_pass,         // X3 No stall 
  input                        x3_load_r,       // X3 load  
  input                        x3_store_r,      // X3 load  
  input [1:0]                  x3_size_r,       // 00-b, 01-h, 10-w, 11-dw
  input [`npuarc_PADDR_RANGE]         x3_mem_addr0_r,  // X3 memory address
  input [`npuarc_PADDR_RANGE]         dc3_mem_addr1_r, // X3 memory address
  
  output                       mq_addr_even_hit, // Address 0 hit with Lbuf
  output                       mq_addr_odd_hit,  // Address 1 hit with Lbuf
  output                       dmu_evict_hit,

  ////////// Interface to the DC4 (commit stage) ////////////////////////////
  //
  input                        ca_valid_r,      // CA has valid instruction 
  input                        ca_pass,         // CA no stall
  input                        ca_enable,       // CA not stalling
  input                        ca_load_r,       // CA load  
  input                        ca_pref_r,       // CA pref  
  input                        ca_pref_l2_r,    // CA pref l2 
  input                        ca_prefw_r,      // CA prefw  
  input                        ca_pre_alloc_r,  // CA pre_alloc  
  input                        dc4_pref_bad_r,  
  input                        ca_store_r,      // CA store  
  input                        ca_locked_r,     // CA locked
  input                        ca_sex_r,        // Ca sign extension
  input                        ca_userm_r,      // Ca user mode
  input [1:0]                  ca_size_r,       // 00-b, 01-h, 10-w, 11-dw
  input [`npuarc_PADDR_RANGE]         ca_mem_addr0_r,  // CA memory address
  input [`npuarc_PADDR_RANGE]         dc4_mem_addr1_r, // CA memory address1
  input [`npuarc_DMP_DATA_RANGE]      ca_wr_data_r,    // CA write data
  input [`npuarc_DC_WAY_RANGE]        dc4_hit_even_way_hot_r,     // CA hit even 
  input [`npuarc_DC_WAY_RANGE]        dc4_hit_odd_way_hot_r,      // CA hit odd
  input                        dc4_dt_miss_even_r, 
  input                        dc4_dt_miss_odd_r,
  input                        dc4_dt_miss_r,

  input                        dc4_scond_go,      //
  input                        wq_scond_entry,    // SCOND pending in the WQ

  
  ////////// DMU status /////////////////////////////////////////////////////
  //
  output                       dmu_empty,            // MQ and LB empty
  output                       dmu_dc_idle,          // CB not accesing cache
  output                       dmu_poison_stuck,     // Poison dc3 stuck
  output                       dmu_mq_full,          // mq full
  output                       dmu_lsmq_full,        // lsmq full
  output                       lsmq_two_empty,       // LSMQ has two spaces     
  output reg [1:0]             dc4_lsmq_write,
  output                       dc4_lsmq_nomatch_replay,
  output                       lsmq_match0,
  output                       lsmq_match1,
  output                       dmu_wr_pending,       // pending store miss
 
  input                        dd_busy_nxt,      //
  input                        dc_pipe_busy,     // 
  
  ////////// Interface to the  Data Cache Arrays /////////////////////////
  //
  output reg                   dmu_req_dt_even, // Request even tag array
  output reg                   dmu_req_dt_odd,  // Request odd tag array
  output reg                   dmu_dt_odd_sel,  // Request odd tag array
  output reg [`npuarc_DC_WAY_RANGE]   dmu_dt_way_hot,  // Selected way to write
  output reg                   dmu_dt_we,       // Write enable, 0=read
  output reg [2:0]             dmu_dt_wem,      // e,v,tag
  output reg [`npuarc_DC_IDX_RANGE]   dmu_dt_addr,     // Address from MQ
  output reg                   dmu_dt_valid,    // Valid bit
  output reg [`npuarc_DC_TAG_RANGE]   dmu_dt_tag,      // Address from MQ
  
  output reg                   dmu_req_ds,      // Request to status array
  output reg                   dmu_ds_odd_sel,  // which half data to write
  output reg                   dmu_ds_we,       // Write enable, 0=read
  output reg [2:0]             dmu_ds_wem,      // lock, dirty, lru
  output reg [`npuarc_DC_WAY_RANGE]   dmu_ds_way_hot,  // Selected way to write
  output reg                   dmu_ds_dirty,    // drity bit
  output reg                   dmu_ds_lock,     // lock bit
  output reg                   dmu_ds_lru,      // lru bit
  output reg [`npuarc_DC_IDX_RANGE]   dmu_ds_addr,     // Address 
  
  input                        dc3_ds_lru,       // Read LRU for replacement
  input [`npuarc_DC_WAY_RANGE]        dc3_ds_lock,      // Read lock bits
  input [`npuarc_DC_WAY_RANGE]        dc3_ds_dirty,     // Read dirty bits
  
  output reg                   dmu_req_dd,      // DC1 Request to data array
  output reg                   dmu_evict_rd,    // mux control to read data
  output reg [`npuarc_DC_WAY_RANGE]   dmu_dd_way_hot,  // Selected way to write
  output reg                   dmu_dd_we,       // Write enable, 0=read
  output reg [`npuarc_DC_ADR_RANGE]   dmu_dd_addr,     // DC2 Address from MQ
  
  input [`npuarc_DC_TAG_RANGE]        dc3_dt_tag,    // Dirty tag of replacement way
  input                        dc3_dt_val,    // Valid bit of replacement way
  input [`npuarc_DC_TAG_TAG_DATA_RANGE] dc4_dt_ecc_corrected,
  input                        dc4_dc_dt_ecc_db_error, // error during eviction
  input                        dc4_dc_dd_ecc_db_error, // error during eviction
  input [`npuarc_DC_DATA_RANGE]       dc4_dd_data,   // DC4 data evict/flush
 
  input                        dc3_mq_addr_match, 
  input                        dc4_mq_addr_match, 
  input                        dc4_mq_set_match, 
  output [`npuarc_DC_DATA_RANGE]      lbuf_rd_data,  // Lbuf --> DC data
  output reg                   dmu_dc_start,  // DMU wants to start
  output reg                   dmu_dc_ready,  // DMU/RF ready to dump line buff
  output     [`npuarc_PADDR_RANGE]    mq_addr,        
  output                       mq_valid,        
  output reg [`npuarc_DC_LBUF_RANGE]  dmu_line_addr, // DMU line addr
  output reg                   dmu_dc_read,   // Read from cache
  output reg                   dmu_dc_done,   // DMU is done with DC
  
  input                        dmu_ack_ok,    // Ack to DS request, single
  ////////// CB IBP interface ///////////////////////////////////////////
  //
  output                       cb_cmd_valid,     
  input                        cb_cmd_accept,    
  output                       cb_cmd_read,      
  output  [`npuarc_PADDR_RANGE]       cb_cmd_addr,      
  output                       cb_cmd_prot,      
  output                       cb_cmd_wrap,      
  output  [3:0]                cb_cmd_burst_size,

  output                       cb_wr_valid,      
  input                        cb_wr_accept,     
  output                       cb_wr_last,       
  output  [`npuarc_RF_CB_DATA_RANGE]  cb_wr_data,       
  output  [`npuarc_RF_CB_MASK_RANGE]  cb_wr_mask,       
  input                        cb_wr_done,       
  input                        cb_err_wr,        
  
  ////////// RF IBP interface ///////////////////////////////////////////
  //
  output                       rf_cmd_valid,   
  output                       rf_cmd_excl,  
  input                        rf_cmd_accept,    
  output                       rf_cmd_read,      
  output  [`npuarc_PADDR_RANGE]       rf_cmd_addr,      
  output                       rf_cmd_prot,      
  output                       rf_cmd_wrap,      
  output  [3:0]                rf_cmd_burst_size,

  input                        rf_rd_valid,  
  input                        rf_rd_last,   
  input                        rf_err_rd,    
  input [`npuarc_RF_CB_DATA_RANGE]    rf_rd_data,   
  output                       rf_rd_accept, 

  ////////// Performance counters interface  ////////////////////////////////
  //
  output reg                   dc_pct_dcm,   // Data Cache miss         
  output reg                   dc_pct_dclm,  // Data Cache load miss    
  output reg                   dc_pct_dcsm,  // Data Cache store miss   


  ////////// Interface to the post-commit stage (dc miss queue) ///////////////
  //
  output                       mq_rb_req,      // Result bus request
  output                       mq_rb_err,      // load miss bus error  
  input [`npuarc_GRAD_TAG_RANGE]      ca_grad_tag,
  input                        mq_rb_ack,
  
  output [3:0]                 mq_bank_sel,       // Bank Select from LSMQ
  output [`npuarc_GRAD_TAG_RANGE]     mq_rb_tag,         // Load grad tag
  output [`npuarc_PADDR_RANGE]        mq_rb_addr,        // Address of load data
  output                       mq_sex,            // signed extension
  output [1:0]                 mq_size,           // load size
  output                       mq_userm,          // User mode 
  output reg [`npuarc_DC_DATA_RANGE]  mq_rb_data,        // Lbuf --> DC data
  output                       mq_wr_err,         // store miss bus error
  
  output                       mq_flush_err_req,  // flush error exxpn req
  output [`npuarc_DC_LBUF_RANGE]      mq_flush_err_addr, // flush error addr
  input                        mq_flush_err_ack,  // flush error ack
  
  output                       rf_err_req,        // refill delayed bus err
  output [`npuarc_DC_LBUF_RANGE]      rf_err_addr,       // refill err addr
  

  ////////// AUX interface //////////////////////////////////////
  //
  input                        aux_mq_write,
  input                        aux_mq_flush,
  input                        aux_mq_purge,
  input                        aux_mq_refill,
  input                        aux_mq_way,
  input [`npuarc_DC_LBUF_RANGE]       aux_mq_addr,
  input                        aux_mq_lru_dirty,
  output                       lb_err_r,
  output                       mq_empty,
  output                       mq_one_or_less_entry,
  output                       cb_full
// leda NTL_CON37 on    
// leda NTL_CON13C on    
);

// leda W175 off
// LMD: A parameter has been defined but is not used.
// LJ:  Code more readable; 

// Local Declarations
//

/////////////////////////////////////////////////////////////////////////////  
// Block Interface Wire Connections declarations 
//
/////////////////////////////////////////////////////////////////////////////  
wire                       dc3_dc_target;    // load/store is for DCache
wire [1:0]                 dc3_ls_valid;     // Valid load/store for mq

reg  [`npuarc_DMP_DATA_RANGE]     dmp_lsmq_data;    // Store data from EXU
//reg                        dmp_evict_error_cg0;
reg                        dmp_evict_error;
  
   
// Directly from LSMQ to Lbuf, no other control logic
wire [`npuarc_DC_BLK_WRD_RANGE]  lsmq_addr;      
wire [`npuarc_DC_BLK_WRD_RANGE]  lsmq_st_addr;      
wire [`npuarc_LBWR_DATA_RANGE]   lsmq_data;      
wire [`npuarc_DMP_DATA_RANGE]    lsmq_ld_data;    // Load data to result bus
wire                      lsmq_ld_req;    
wire                      lsmq_st_req;   
wire [`npuarc_LBWR_MASK_RANGE]   lsmq_wr_mask;   
wire [3:0]                mq_fwd_bank;    // Current load or missed load
wire [7:0]                lsmq_fwd_bank;  // Bank Select from LSMQ
wire                      lsmq_bank_lo;   
wire                      lsmq_bank_hi;   

// Directly from MQ to Lbuf, no other control logic
//
wire [`npuarc_LBUF_PTR_RANGE]    mq_fwd_addr;   
wire                      mq_lbfwd;      
wire [`npuarc_DC_DATA_RANGE]     lbuf_fwd_data; // Lbuf --> load
wire [`npuarc_LBWR_MASK_RANGE]   mq_stmask;     // write mask (64-bit)
wire                      mq_lbstore;    // current store in x3
reg                       mq_addr0_hit_r; // Addr0 hit
reg                       mq_addr1_hit_r; // Addr1 hit

// Condition to pop MQ entry or make req to BIU/DC
//
wire                      lb_empty;  
wire                      lb_ready_to_dc;
wire                      lsmq_done;      
wire                      lsmq_full; 
wire                      lsmq_empty; 

// When an entry is popped the next valid entry will initialize Lbuf with
// Critical word
wire                      mq_full;
wire                      mq_entry_full;


// From MQ to LSMQ to set up nfifo in LSMQ
wire [`npuarc_MQ_PTR_RANGE]      mq_wrptr0;  
wire [`npuarc_MQ_PTR_RANGE]      mq_wrptr1;      
wire [`npuarc_MQ_VPTR_RANGE]     mq_match0_val;    
wire [`npuarc_MQ_VPTR_RANGE]     mq_match1_val;    
wire [`npuarc_LBUF_FIFO_RANGE]   lb_valid_r;    


wire [`npuarc_DC_WAY_RANGE]      dc4_dt_bank_sel;

wire                      mq_addr0_hit;    // Address 0 hit with Lbuf
wire                      mq_addr1_hit;    // Address 1 hit with Lbuf
wire [1:0]                dc4_miss;
wire                      dc4_pref;
wire [`npuarc_PADDR_RANGE]       ca_mem_addr1;    // CA memory address1

reg                       rf_ack_dd;

// MQ outputs
//
//wire                      mq_valid;
wire                      mq_dirty;
wire                      mq_bus_err_r;
wire                      mq_cb_complete;
wire                      mq_cache_flush;
wire                      mq_cache_purge;
wire                      mq_cache_lock;
wire                      mq_cache_cb_complete;
wire                      mq_replacement_way;
wire                      mq_replacement_valid;
wire                      mq_pre_alloc;
wire                      mq_pref;
wire                      mq_scond;
//wire [`PADDR_RANGE]       mq_addr;   
wire [`npuarc_MQ_PTR_RANGE]      mq_rdptr;

wire                      mq_cmd_valid;
wire                      mq_cmd_pre_alloc;
wire                      mq_cmd_cache_op;
wire                      mq_cmd_cache_rf; 
wire                      mq_cmd_userm;
wire [`npuarc_PADDR_RANGE]       mq_cmd_addr;   
wire  [`npuarc_MQ_PTR_RANGE]     rf_cmd_rptr_r;

// CB outputs
//
wire                      cb_complete;
wire                      cb_cache_complete;
wire                      cb_way_select_r;
wire                      cb_way_valid;
wire                      cb_dc_start;  
wire                      cb_dc_done; 

wire                      cb_req_dt_even;  
wire                      cb_req_dt_odd;   
wire                      cb_dt_odd_sel;   
wire  [`npuarc_DC_WAY_RANGE]     cb_dt_way_hot;   
wire                      cb_dt_we;        
wire  [2:0]               cb_dt_wem;       
wire  [`npuarc_DC_IDX_RANGE]     cb_dt_addr;      
wire                      cb_dt_valid;     
wire  [`npuarc_DC_TAG_RANGE]     cb_dt_tag;       

wire                      cb_req_dd;       
wire                      cb_evict_rd;     
wire  [`npuarc_DC_WAY_RANGE]     cb_dd_way_hot;   
wire                      cb_dd_we;        
wire  [`npuarc_DC_ADR_RANGE]     cb_dd_addr;      

wire                      cb_req_ds;       
wire                      cb_ds_odd_sel;   
wire                      cb_ds_we;        
wire                      cb_ds_lru;
wire  [2:0]               cb_ds_wem;       
wire  [`npuarc_DC_WAY_RANGE]     cb_ds_way_hot;   
wire  [`npuarc_DC_IDX_RANGE]     cb_ds_addr;

wire  [`npuarc_DC_LBUF_RANGE]    cb_line_addr_r;

wire                      cb_empty;
wire                      cb_buf_busy_r;   
wire                      cb_dc_idle;       
// RF outputs
//
wire                      lbuf_initial; 
wire                      lbuf_rd_valid;
wire                      lbuf_rd_last;
wire                      lbuf_rd_last_r;

wire                      rf_req_dt_even;  
wire                      rf_req_dt_odd;   
wire                      rf_dt_odd_sel;   
wire [`npuarc_DC_WAY_RANGE]      rf_dt_way_hot;  
wire                      rf_dt_we;        
wire [2:0]                rf_dt_wem;       
wire [`npuarc_DC_IDX_RANGE]      rf_dt_addr;      
wire                      rf_dt_valid;     
wire [`npuarc_DC_TAG_RANGE]      rf_dt_tag;       
wire                      rf_req_dd;       
wire [`npuarc_DC_WAY_RANGE]      rf_dd_way_hot;   
wire                      rf_dd_we;        
wire [`npuarc_DC_ADR_RANGE]      rf_dd_addr;      

wire                      rf_req_ds;       
wire                      rf_ds_odd_sel;  
wire                      rf_ds_we;        
wire [2:0]                rf_ds_wem;       
wire [`npuarc_DC_WAY_RANGE]      rf_ds_way_hot;   
wire [`npuarc_DC_IDX_RANGE]      rf_ds_addr;      
wire                      rf_ds_lock;      
wire                      rf_ds_dirty;     
wire                      rf_ds_lru; 

wire                      rf_dc_start;  
wire                      rf_dc_ready;  
wire                      rf_dc_done; 





//////////////////////////////////////////////////////////////////////////////
// Translating the even/odd (use in Dcache) to addr0/1 (use in DMU)
// 
//////////////////////////////////////////////////////////////////////////////
// Number of selected banks
//
assign dc3_bank_flip    = x3_mem_addr0_r[`npuarc_DC_TAG_BANK_ID];
assign mq_addr_even_hit = dc3_bank_flip ? mq_addr1_hit : mq_addr0_hit;
assign mq_addr_odd_hit  = dc3_bank_flip ? mq_addr0_hit : mq_addr1_hit;

//////////////////////////////////////////////////////////////////////////////
// Local generate interface signals in DC3 stage to LSMQ & MQ
// 
//////////////////////////////////////////////////////////////////////////////

assign dc3_dc_target = dc3_target_r==`npuarc_DMP_TARGET_DC;
assign dc3_ls_valid[1] = (x3_valid_r & dc3_dc_target & 
                          (x3_load_r | x3_store_r) & 
                          dc3_dt_line_cross_r);            // Valid load/store
assign dc3_ls_valid[0] = (x3_valid_r & dc3_dc_target & 
                          (x3_load_r | x3_store_r));      // Valid load/store

// Number of selected banks
//
assign dc4_dt_bank_sel[0] = ca_valid_r & (ca_load_r | ca_store_r);
assign dc4_dt_bank_sel[1] = dc4_dt_bank_sel[0] & dc4_dt_line_cross_r;
assign dc4_bank_flip = ca_mem_addr0_r[`npuarc_DC_TAG_BANK_ID];


reg [1:0] dc4_rd_miss;
reg [1:0] dc4_wr_miss;
reg       dc4_hit0_way;
wire      dc4_target_dc;
wire      dc4_load;
wire      dc4_store;
wire      dc4_store_qual;

assign dc4_target_dc  = (dc4_target_r == `npuarc_DMP_TARGET_DC);
assign dc4_load       =    ca_load_r 
                        & (~ca_store_r)
                        & (~dc4_pref_bad_r)
                        ;
assign dc4_store_qual =  ca_store_r
                       & (~dc4_pref_bad_r)
                       ;

assign dc4_store      = ca_locked_r   ? dc4_scond_go : dc4_store_qual;

//////////////////////////////////////////////////////////////////////////////
// Asynchronous process qualifying misses 
// 
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_rd_wr_miss_PROC
  if (dc4_bank_flip)
  begin
    dc4_rd_miss[0]       = dc4_load  & dc4_target_dc & dc4_dt_miss_odd_r;
    dc4_rd_miss[1]       = dc4_load  & dc4_target_dc & dc4_dt_miss_even_r;
    dc4_wr_miss[0]       = dc4_store & dc4_target_dc & dc4_dt_miss_odd_r;
    dc4_wr_miss[1]       = dc4_store & dc4_target_dc & dc4_dt_miss_even_r;
    dc4_hit0_way         = dc4_hit_odd_way_hot_r[1];
  end
  else
  begin
    dc4_rd_miss[0]       = dc4_load  & dc4_target_dc & dc4_dt_miss_even_r;
    dc4_rd_miss[1]       = dc4_load  & dc4_target_dc & dc4_dt_miss_odd_r;
    dc4_wr_miss[0]       = dc4_store & dc4_target_dc & dc4_dt_miss_even_r;
    dc4_wr_miss[1]       = dc4_store & dc4_target_dc & dc4_dt_miss_odd_r;
    dc4_hit0_way         = dc4_hit_even_way_hot_r[1];
  end
end

assign dc4_miss[0] = dc4_rd_miss[0] | dc4_wr_miss[0];
assign dc4_miss[1] = dc4_rd_miss[1] | dc4_wr_miss[1];
assign dc4_pref    = ca_pref_r | ca_pref_l2_r | ca_prefw_r | ca_pre_alloc_r;

//////////////////////////////////////////////////////////////////////////////
// Local generate interface signals in DC4 stage to LSMQ & MQ 
// 
//////////////////////////////////////////////////////////////////////////////
reg [1:0] dc4_mq_write;
//reg [1:0] dc4_lsmq_write;

parameter SNP_NO_SNP  = 4'b0000;
parameter SNP_RD_SHD  = 4'b1000;
parameter SNP_RD_UNQ  = 4'b1001;
parameter SNP_CL_SHD  = 4'b1010;
parameter SNP_CL_UNQ  = 4'b1011;
parameter SNP_MK_UNQ  = 4'b1101;

// spyglass disable_block W553
always @*
begin : dc4_mq_write0_PROC
  case (1'b1)
  dc4_rd_miss[0]:
  begin
    // In case of mq_addr0_hit_r, check for dc4_dt_miss_r, if this is set it indicates
    // the entry needs to go to LSMQ and then retire.
    //
    dc4_mq_write[0]    = ca_enable & (~mq_entry_full) & (~mq_addr0_hit_r);
    dc4_lsmq_write[0]  = ca_enable & (~dc4_pref)      & ((~mq_addr0_hit_r) | dc4_dt_miss_r);
  end
  
  dc4_wr_miss[0]:
  begin
    dc4_mq_write[0]    = ca_enable & (~mq_addr0_hit_r);
    dc4_lsmq_write[0]  = ca_enable ;//& (~mq_addr0_hit_r);
  end
  
  
  default:
  begin
    dc4_mq_write[0]    = 1'b0;
    dc4_lsmq_write[0]  = 1'b0;
  end
  endcase
end

always @*
begin : dc4_mq_write1_PROC
  case (1'b1)
  dc4_rd_miss[1]:
  begin
    // In case of mq_addr0_hit_r, check for dc4_dt_miss_r, if this is set it indicates 
    // the entry needs to go to LSMQ and then retire.
    // 
    dc4_mq_write[1]    = ca_enable & (~dc4_pref) & dc4_dt_line_cross_r & (~mq_addr1_hit_r);
    dc4_lsmq_write[1]  = ca_enable & (~dc4_pref) & dc4_dt_line_cross_r & ((~mq_addr1_hit_r) | dc4_dt_miss_r);
  end
  
  dc4_wr_miss[1]:
  begin  
    dc4_mq_write[1]    = ca_enable & dc4_dt_line_cross_r & (~mq_addr1_hit_r);
    dc4_lsmq_write[1]  = ca_enable & dc4_dt_line_cross_r ;//& (~mq_addr1_hit_r);
  end
  
   
  default:
  begin
    dc4_mq_write[1]    = 1'b0;
    dc4_lsmq_write[1]  = 1'b0;
  end    
  endcase
end
// spyglass enable_block W553

//////////////////////////////////////////////////////////////////////////////
// Performance counters
// 
/////////////////////////////////////////////////////////////////////////////
always @*
begin : dc_pct_PROC
  // Data Cache miss 
  //
  dc_pct_dcm  =   (dc4_mq_write[0] | dc4_lsmq_write[0])
                & (~dc4_pref)
                & ca_pass;
  
  // Data Cache load miss 
  //
  dc_pct_dclm =  (dc4_mq_write[0] | dc4_lsmq_write[0])
               & ca_load_r  
               & (~dc4_pref) 
               & ca_pass;
  
  // Data Cache store miss 
  //
  dc_pct_dcsm = (dc4_mq_write[0] | dc4_lsmq_write[0])
               & ca_store_r  
               & (~dc4_pref) 
               & ca_pass;
end


// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  One bit incrementor
assign ca_mem_addr1 = dc4_mem_addr1_r; //{(ca_mem_addr0_r[`PADDR_MSB:3] + 1'b1), 3'b000}; 
// leda BTTF_D002 on                                           
// leda B_3200 on                                           

//////////////////////////////////////////////////////////////////////////////
// Status
// 
//////////////////////////////////////////////////////////////////////////////
  
assign dmu_mq_full      = mq_full;
assign dmu_lsmq_full    = lsmq_full;
assign dmu_empty        = lb_empty  & mq_empty & cb_empty;
assign dmu_dc_idle      = cb_dc_idle;


// Poison dc3 stuck store when it may depend on an entry that is not the top
// of the MQ
//
assign dmu_poison_stuck =  (lsmq_done      & (~lsmq_empty))
                         ;
                           

//////////////////////////////////////////////////////////////////////////////
// 
// 
//////////////////////////////////////////////////////////////////////////////
reg dc4_ex_hit_non_e;

always @*
begin : lsmq_data_PROC
  dc4_ex_hit_non_e = 1'b0
                   ;
                      
  // Load data is used only on line crossing, the upper 32-bit of
  // even/odd for addr0 and the lower 32-bit of even/odd for addr1
  //
  casez({ca_store_r, dc4_ex_hit_non_e, dc4_dt_bank_sel, dc4_miss})
  6'b10_??_?? : dmp_lsmq_data = ca_wr_data_r; 
  6'b0?_1?_1? : dmp_lsmq_data = dc4_dd_data[`npuarc_DWORD2_RANGE];  // Addr0 hit
  6'b0?_11_01 : dmp_lsmq_data = dc4_dd_data[`npuarc_DWORD0_RANGE];  // Addr1 hit
  default     : dmp_lsmq_data = ca_wr_data_r; 
  endcase  
end

//////////////////////////////////////////////////////////////////////////////
// Control signals to output aligner and DC4 stage, result bus
//   - Partial load data and store-to-load forwarding data are both
//     on the same bus, lsmq_data
//////////////////////////////////////////////////////////////////////////////
assign mq_fwd_en   = (| mq_fwd_bank);

assign mq_bank_sel = (  mq_rb_ack 
                      ? (lsmq_fwd_bank[3:0] | lsmq_fwd_bank[7:4]) 
                      : (   (mq_fwd_en & x3_pass & x3_load_r) 
                          ? mq_fwd_bank
                          : 4'b0000));

//assign bank_lo_sel = lsmq_bank_lo & (~mq_fwd_en);
//assign bank_hi_sel = lsmq_bank_hi & (~mq_fwd_en);

always @*
begin : rb_data_PROC
  casez ({lsmq_bank_lo, lsmq_bank_hi})
  2'b1?   : mq_rb_data = {lbuf_fwd_data[`npuarc_DWORD2_RANGE], lsmq_ld_data};
  2'b01   : mq_rb_data = {lsmq_ld_data, lbuf_fwd_data[`npuarc_DWORD0_RANGE]};
  default : mq_rb_data = lbuf_fwd_data;
  endcase  
end

/*
new stuff...
*/
wire   cb_req_dt;
wire   rf_req_dt;

//////////////////////////////////////////////////////////////////////////
//                                                                        
// Handy variables     
//                                                                        
//////////////////////////////////////////////////////////////////////////
assign  cb_req_dt = cb_req_dt_even | cb_req_dt_odd;
assign  rf_req_dt = rf_req_dt_even | rf_req_dt_odd;

always @*
begin : dmu_cache_arbiter_PROC
  //
  //
  dmu_dc_start        = rf_dc_start
                      | cb_dc_start;
  dmu_dc_ready        = rf_dc_ready;
  dmu_dc_done         = cb_dc_done  | rf_dc_done;
  dmu_dc_read         = cb_dc_start;
  dmu_line_addr       = cb_line_addr_r;
  
  // Data tag
  //
  casez ({cb_req_dt, rf_req_dt})
  2'b1?:
  begin
    // Copy back
    //
    dmu_req_dt_even   = cb_req_dt_even; 
    dmu_req_dt_odd    = cb_req_dt_odd;  
    dmu_dt_odd_sel    = cb_dt_odd_sel;  
    dmu_dt_way_hot    = cb_dt_way_hot;  
    dmu_dt_we         = cb_dt_we;       
    dmu_dt_wem        = cb_dt_wem;      
    dmu_dt_addr       = cb_dt_addr;     
    dmu_dt_valid      = cb_dt_valid;    
    dmu_dt_tag        = cb_dt_tag;      
     
  end
  
  2'b01:
  begin
    // Refill 
    //
    dmu_req_dt_even   = rf_req_dt_even; 
    dmu_req_dt_odd    = rf_req_dt_odd;  
    dmu_dt_odd_sel    = rf_dt_odd_sel;  
    dmu_dt_way_hot    = rf_dt_way_hot;  
    dmu_dt_we         = rf_dt_we;       
    dmu_dt_wem        = rf_dt_wem;      
    dmu_dt_addr       = rf_dt_addr;     
    dmu_dt_valid      = rf_dt_valid;    
    dmu_dt_tag        = rf_dt_tag;      
    
  end
  
  default:
  begin
    // Default to the Copy back credentials
    //
    dmu_req_dt_even   = 1'b0; 
    dmu_req_dt_odd    = 1'b0;  
    dmu_dt_odd_sel    = cb_dt_odd_sel;  
    dmu_dt_way_hot    = cb_dt_way_hot;  
    dmu_dt_we         = 1'b0;       
    dmu_dt_wem        = 3'b000;      
    dmu_dt_addr       = cb_dt_addr;     
    dmu_dt_valid      = 1'b0;    
    dmu_dt_tag        = cb_dt_tag;      
     
  end
  endcase
  
  // Data data
  //
  casez ({cb_req_dd, rf_req_dd})
  2'b1?:
  begin
    // Copy back 
    //
    dmu_req_dd       = 1'b1;       
    dmu_evict_rd     = cb_evict_rd;     
    dmu_dd_way_hot   = cb_dd_way_hot;   
    dmu_dd_we        = cb_dd_we;        
    dmu_dd_addr      = cb_dd_addr;      
    
    rf_ack_dd        = 1'b0;
  end
  
  2'b01:
  begin
    // Refill 
    //
    dmu_req_dd       = rf_req_dd;       
    dmu_evict_rd     = 1'b0;     
    dmu_dd_way_hot   = rf_dd_way_hot;   
    dmu_dd_we        = rf_dd_we;        
    dmu_dd_addr      = rf_dd_addr;      
    
    rf_ack_dd        = rf_req_dd;
  end
  
  default:
  begin
    // Default to the Copy back credentials
    //
    dmu_req_dd       = 1'b0;       
    dmu_evict_rd     = cb_evict_rd;     
    dmu_dd_way_hot   = cb_dd_way_hot;   
    dmu_dd_we        = 1'b0;        
    dmu_dd_addr      = cb_dd_addr;      
    
    rf_ack_dd        = 1'b0;
  end
  endcase
  
  
  // Status
  //
  casez ({cb_req_ds, rf_req_ds})
  2'b1?:
  begin
    // Copy back
    //
    dmu_req_ds       = 1'b1;
    dmu_ds_odd_sel   = cb_ds_odd_sel;
    dmu_ds_we        = cb_ds_we;        
    dmu_ds_wem       = cb_ds_wem;      
    dmu_ds_way_hot   = cb_ds_way_hot;
    dmu_ds_dirty     = 1'b0;    
    dmu_ds_lock      = 1'b0;     
    dmu_ds_lru       = cb_ds_lru;      
    dmu_ds_addr      = cb_ds_addr;     
    
  end
  
  2'b01:
  begin
    // Refill
    //
    dmu_req_ds       = rf_req_ds;  
    dmu_ds_odd_sel   = rf_ds_odd_sel;
    dmu_ds_we        = rf_ds_we;        
    dmu_ds_wem       = rf_ds_wem;     
    dmu_ds_way_hot   = rf_ds_way_hot;
    dmu_ds_dirty     = rf_ds_dirty;    
    dmu_ds_lock      = rf_ds_lock;     
    dmu_ds_lru       = rf_ds_lru;      
    dmu_ds_addr      = rf_ds_addr;  
    
  end
  
  default:
  begin
    // Default to the Copy back credentials
    //
    dmu_req_ds       = 1'b0;
    dmu_ds_odd_sel   = cb_ds_odd_sel;
    dmu_ds_we        = 1'b0;        
    dmu_ds_wem       = 3'b000;      
    dmu_ds_way_hot   = cb_ds_way_hot;
    dmu_ds_dirty     = 1'b0;    
    dmu_ds_lock      = 1'b0;     
    dmu_ds_lru       = 1'b0;      
    dmu_ds_addr      = cb_ds_addr;     
    
  end
  endcase
  
end

//////////////////////////////////////////////////////////////////////////////
// Instantiate LSMQ, MQ, CB, RF, LB
// 
//////////////////////////////////////////////////////////////////////////////


npuarc_alb_dmp_lsmq_fifo u_alb_dmp_lsmq_fifo (

                        // Outputs
   .lsmq_done              (lsmq_done),
   .lsmq_match0            (lsmq_match0), 
   .lsmq_match1            (lsmq_match1), 
   .dc4_lsmq_nomatch_replay(dc4_lsmq_nomatch_replay),
   .lsmq_ld_req            (lsmq_ld_req),
   .lsmq_st_req            (lsmq_st_req),
   .lsmq_st_err            (mq_wr_err),
   .lsmq_wr_mask           (lsmq_wr_mask[`npuarc_LBWR_MASK_RANGE]),
   .lsmq_addr              (lsmq_addr[`npuarc_DC_BLK_WRD_RANGE]),
   .lsmq_st_addr           (lsmq_st_addr[`npuarc_DC_BLK_WRD_RANGE]),
   .lsmq_data              (lsmq_data[`npuarc_LBWR_DATA_RANGE]),
   .lsmq_ld_data           (lsmq_ld_data[`npuarc_DMP_DATA_RANGE]),
   .lsmq_fwd_bank          (lsmq_fwd_bank[7:0]),
   .mq_size                (mq_size[1:0]),
   .mq_sex                 (mq_sex),
   .mq_rb_addr             (mq_rb_addr[`npuarc_PADDR_RANGE]),
   .mq_rb_tag              (mq_rb_tag[`npuarc_GRAD_TAG_RANGE]),
   .mq_rb_req              (mq_rb_req),
   .mq_rb_err              (mq_rb_err),
   .lsmq_bank_lo           (lsmq_bank_lo),
   .lsmq_bank_hi           (lsmq_bank_hi),
   .lsmq_full              (lsmq_full),
   .lsmq_empty             (lsmq_empty),
   .lsmq_two_empty         (lsmq_two_empty),
   // Inputs
   .clk                    (clk),
   .rst_a                  (rst_a),
   .dmp_mq_write           (dc4_mq_write[1:0]),
   .dmp_lsmq_write         (dc4_lsmq_write[1:0]),
   .dmp_lsmq_data          (dmp_lsmq_data[`npuarc_DMP_DATA_RANGE]),
   .ca_grad_tag            (ca_grad_tag[`npuarc_GRAD_TAG_RANGE]),  
   .ca_pass                (ca_pass),                       
   .ca_store_r             (ca_store_r), 
   .ca_load_r              (ca_load_r),                     
   .ca_sex_r               (ca_sex_r),                      
   .ca_size_r              (ca_size_r[1:0]),                
   .ca_mem_addr0_r         (ca_mem_addr0_r[`npuarc_PADDR_RANGE]),   
   .ca_mem_addr1           (ca_mem_addr1[`npuarc_PADDR_RANGE]), 
   .dc4_mq_addr_match      (dc4_mq_addr_match),
   .dc4_mq_set_match       (dc4_mq_set_match ),
   .dc4_dt_line_cross_r    (dc4_dt_line_cross_r),
   .dc4_dt_miss_r          (dc4_dt_miss_r),
   .mq_match0_val          (mq_match0_val[`npuarc_MQ_VPTR_RANGE]), 
   .mq_match1_val          (mq_match1_val[`npuarc_MQ_VPTR_RANGE]), 
   .mq_wrptr0              (mq_wrptr0[1:0]),                
   .mq_wrptr1              (mq_wrptr1[1:0]),                
   .mq_valid               (mq_valid),                      
   .mq_rdptr               (mq_rdptr[1:0]),                 
   .lb_valid_r             (lb_valid_r[`npuarc_LBUF_FIFO_RANGE]),  
   .lb_err_r               (lb_err_r),                      
   .lbuf_fwd_data          (lbuf_fwd_data[`npuarc_DC_DATA_RANGE]), 
   .mq_rb_ack              (mq_rb_ack)
);

npuarc_alb_dmp_mq_fifo u_alb_dmp_mq_fifo (


  .clk                     (clk                ),   
  .rst_a                   (rst_a              ),   

  .ca_pass                 (ca_pass            ),   
  .ca_enable               (ca_enable          ),   
  .ca_valid_r              (ca_valid_r         ),   
  .dmp_mq_write            (dc4_mq_write       ),   
  .ca_userm_r              (ca_userm_r         ),   
  .ca_store_r              (ca_store_r         ),  
  .ca_locked_r             (ca_locked_r        ),
  .ca_pre_alloc_r          (ca_pre_alloc_r     ),  
  .ca_prefw_r              (ca_prefw_r         ),  
  .ca_pref_r               (ca_pref_r          ),  
  .ca_pref_l2_r            (ca_pref_l2_r       ),  
  .ca_mem_addr0_r          (ca_mem_addr0_r     ), 
  .ca_mem_addr1            (ca_mem_addr1       ),   
  .ca_dt_miss_r            (dc4_dt_miss_r      ),
  .ca_hit0_way             (dc4_hit0_way       ),
  .aux_mq_write            (aux_mq_write       ),
  .aux_mq_flush            (aux_mq_flush       ),
  .aux_mq_purge            (aux_mq_purge       ),
  .aux_mq_refill           (aux_mq_refill      ),
  .aux_mq_way              (aux_mq_way         ),
  .aux_mq_lru_dirty        (aux_mq_lru_dirty   ),
  .aux_mq_addr             (aux_mq_addr        ),
  .mq_empty                (mq_empty           ),
  .mq_one_or_less_entry    (mq_one_or_less_entry),
  
  .dc3_valid               (dc3_ls_valid[1:0]  ),   
  .x3_load_r               (x3_load_r          ),   
  .x3_store_r              (x3_store_r         ),   
  .x3_size_r               (x3_size_r          ),   
  .x3_mem_addr0_r          (x3_mem_addr0_r     ),  
  .dc3_mem_addr1_r         (dc3_mem_addr1_r[`npuarc_DC_LBUF_RANGE]), 
  .dc3_dt_line_cross_r     (dc3_dt_line_cross_r),  
  .mq_match0_val           (mq_match0_val[`npuarc_MQ_VPTR_RANGE]),  
  .mq_match1_val           (mq_match1_val[`npuarc_MQ_VPTR_RANGE]),  
  .mq_wrptr0               (mq_wrptr0[1:0]     ),      
  .mq_wrptr1               (mq_wrptr1[1:0]     ),      
  
  .lb_valid_r              (lb_valid_r         ),  
  .lb_err_r                (lb_err_r           ), 
  .lsmq_done               (lsmq_done          ), 
  .lsmq_ld_err             (mq_rb_err          ),
  .lsmq_st_err             (mq_wr_err          ),
  .mq_fwd_addr             (mq_fwd_addr[`npuarc_LBUF_PTR_RANGE]),  
  .mq_lbfwd                (mq_lbfwd           ),     
  .mq_lbstore              (mq_lbstore         ),   
  .mq_stmask               (mq_stmask[`npuarc_LBWR_MASK_RANGE]),    
  .mq_fwd_bank             (mq_fwd_bank[3:0]   ),  

  .mq_addr0_hit            (mq_addr0_hit       ), 
  .mq_addr1_hit            (mq_addr1_hit       ), 

  .lbuf_rd_last            (lbuf_rd_last       ),   

  .cb_cache_complete       (cb_cache_complete  ),
  .cb_complete             (cb_complete        ),    
  .cb_way_select_r         (cb_way_select_r    ),  
  .cb_way_valid            (cb_way_valid       ),          


  .mq_valid                (mq_valid           ),
  .mq_dirty                (mq_dirty           ),
  .mq_userm                (mq_userm           ),
  .mq_cb_complete          (mq_cb_complete     ),
  .mq_replacement_way      (mq_replacement_way ),
  .mq_replacement_valid    (mq_replacement_valid),
  .mq_pre_alloc            (mq_pre_alloc       ),
  .mq_pref                 (mq_pref            ),
  .mq_scond                (mq_scond           ),
  .mq_addr                 (mq_addr            ), 
  .mq_rdptr                (mq_rdptr           ),
  .mq_cache_flush          (mq_cache_flush     ),    
  .mq_cache_purge          (mq_cache_purge     ),    
  .mq_cache_lock           (mq_cache_lock      ),    
  .mq_cache_cb_complete    (mq_cache_cb_complete), 
  .mq_bus_err_r            (mq_bus_err_r       ),

  .mq_cmd_valid            (mq_cmd_valid       ),
  .mq_cmd_pre_alloc        (mq_cmd_pre_alloc   ),
  .mq_cmd_cache_op         (mq_cmd_cache_op    ), 
  .mq_cmd_cache_rf         (mq_cmd_cache_rf    ), 
  .mq_cmd_userm            (mq_cmd_userm       ),
  .mq_cmd_addr             (mq_cmd_addr        ),  
  .rf_cmd_rptr_r           (rf_cmd_rptr_r      ),
     
  .mq_wr_pending           (dmu_wr_pending     ),
  .mq_entry_full           (mq_entry_full      ),
  .mq_full                 (mq_full            )
);
   
npuarc_alb_dmp_line_buf u_alb_dmp_line_buf (


  .clk                     (clk            ),   
  .rst_a                   (rst_a          ),   

  .rf_rd_valid             (rf_rd_valid    ),  
  .rf_rd_last              (rf_rd_last     ),   
  .rf_err_rd               (rf_err_rd      ),    
  .rf_rd_data              (rf_rd_data     ),   
  .rf_rd_accept            (rf_rd_accept   ), 

  .lbuf_initial            (lbuf_initial   ),  
  .mq_addr                 (mq_addr[`npuarc_DC_BLK_WRD_RANGE]),  
  .mq_pre_alloc            (mq_pre_alloc   ),     

  .lbuf_rd_valid           (lbuf_rd_valid    ), 
  .lbuf_rd_last            (lbuf_rd_last     ),  
  .lbuf_rd_last_r          (rf_lbuf_rd_last_r),  

  .lbuf_rd_data            (lbuf_rd_data   ),  
  .lbuf_fwd_data           (lbuf_fwd_data  ), 
  .lb_valid_r              (lb_valid_r     ),    

  .lsmq_ld_req             (lsmq_ld_req    ),   
  .lsmq_st_req             (lsmq_st_req    ),    
  .lsmq_wr_mask            (lsmq_wr_mask   ),  
  .lsmq_addr               (lsmq_addr      ),     
  .lsmq_st_addr            (lsmq_st_addr   ),  
  .lsmq_data               (lsmq_data      ),     
  
  .mq_fwd_addr             (mq_fwd_addr    ),   
  .mq_lbfwd                (mq_lbfwd       ),      
  .mq_stmask               (mq_stmask      ),     
  .mq_lbstore              (mq_lbstore     ),    
  .mq_addr0_hit            (mq_addr0_hit   ),  
  .x3_pass                 (x3_pass        ),       
  .ca_enable               (ca_enable      ),     
  .ca_mem_addr0_r          (ca_mem_addr0_r[2:0]),
  .ca_wr_data_r            (ca_wr_data_r   ),  

  .lb_err_r                (lb_err_r       ),     

  .lb_ready_to_dc          (lb_ready_to_dc ),
  .lb_empty                (lb_empty       )
);

npuarc_alb_dmp_cb u_alb_dmp_cb (


  .clk                      (clk                ),       
  .rst_a                    (rst_a              ),       

  .ecc_dmp_disable          (ecc_dmp_disable    ),
  .dc_pipe_busy             (dc_pipe_busy       ),
  
  .x3_load_r                (x3_load_r          ),       
  .x3_store_r               (x3_store_r         ),      
  .x3_mem_addr0_r           (x3_mem_addr0_r     ),  
  .dc3_dc_target            (dc3_dc_target      ),   
  .dc3_mem_addr1_r          (dc3_mem_addr1_r    ), 
  .dc3_dt_line_cross_r      (dc3_dt_line_cross_r),  
 
  .mq_valid                 (mq_valid           ),  
  .mq_addr                  (mq_addr            ),  
  .mq_cb_complete           (mq_cb_complete     ),  
  .mq_cache_flush           (mq_cache_flush     ),    
  .mq_cache_purge           (mq_cache_purge     ),    
  .mq_cache_lock            (mq_cache_lock      ),
  .mq_cache_cb_complete     (mq_cache_cb_complete),  
  .mq_cache_way             (mq_replacement_way ),      
 
  
  .cb_cache_complete        (cb_cache_complete  ),          
  .cb_complete              (cb_complete        ),          
  .cb_way_select_r          (cb_way_select_r    ),          
  .cb_way_valid             (cb_way_valid       ),          
  
  .cb_ack_ok                (dmu_ack_ok         ),          
  .cb_dc_start              (cb_dc_start        ),          
  .cb_dc_done               (cb_dc_done         ),          
  
  .cb_empty                 (cb_empty           ),          
  .cb_full                  (cb_full            ),          
  .cb_buf_busy_r            (cb_buf_busy_r      ),          
  .cb_dc_idle               (cb_dc_idle         ), 

  .cb_evict_error_r         (dmp_evict_error    ),
  .cb_evict_hit             (dmu_evict_hit      ),          
  .cb_flush_err_addr        (mq_flush_err_addr  ),          
  .cb_flush_err_req         (mq_flush_err_req   ),          
  .cb_flush_err_ack         (mq_flush_err_ack   ),          


  .cb_cmd_valid             (cb_cmd_valid      ),           
  .cb_cmd_accept            (cb_cmd_accept     ),           
  .cb_cmd_read              (cb_cmd_read       ),           
  .cb_cmd_addr              (cb_cmd_addr       ),           
  .cb_cmd_prot              (cb_cmd_prot       ),           
  .cb_cmd_wrap              (cb_cmd_wrap       ),           
  .cb_cmd_burst_size        (cb_cmd_burst_size ),           
  .cb_wr_valid              (cb_wr_valid       ),           
  .cb_wr_accept             (cb_wr_accept      ),           
  .cb_wr_last               (cb_wr_last        ),           
  .cb_wr_data               (cb_wr_data        ),           
  .cb_wr_mask               (cb_wr_mask        ),           
  .cb_wr_done               (cb_wr_done        ),           
  .cb_err_wr                (cb_err_wr         ),           
  
  .cb_req_dt_even           (cb_req_dt_even    ),           
  .cb_req_dt_odd            (cb_req_dt_odd     ),           
  .cb_dt_odd_sel            (cb_dt_odd_sel     ),           
  .cb_dt_way_hot            (cb_dt_way_hot     ),           
  .cb_dt_we                 (cb_dt_we          ),           
  .cb_dt_wem                (cb_dt_wem         ),           
  .cb_dt_addr               (cb_dt_addr        ),           
  .cb_dt_valid              (cb_dt_valid       ),           
  .cb_dt_tag                (cb_dt_tag         ),           
  
  .cb_req_dd                (cb_req_dd         ),           
  .cb_evict_rd              (cb_evict_rd       ),           
  .cb_dd_way_hot            (cb_dd_way_hot     ),           
  .cb_dd_we                 (cb_dd_we          ),           
  .cb_dd_addr               (cb_dd_addr        ),           
  
  .cb_req_ds                (cb_req_ds         ),           
  .cb_ds_odd_sel            (cb_ds_odd_sel     ),           
  .cb_ds_we                 (cb_ds_we          ),           
  .cb_ds_lru                (cb_ds_lru         ),
  .cb_ds_wem                (cb_ds_wem         ),           
  .cb_ds_way_hot            (cb_ds_way_hot     ),           
  .cb_ds_addr               (cb_ds_addr        ),           
  
  .cb_line_addr_r           (cb_line_addr_r    ),           
  
  .dc3_dt_tag               (dc3_dt_tag        ),           
  .dc3_dt_val               (dc3_dt_val        ),           
  .dc4_dt_ecc_corrected   (dc4_dt_ecc_corrected),

  .dc3_status_lru           (dc3_ds_lru        ),           
  .dc3_status_lock          (dc3_ds_lock       ),           
  .dc3_status_dirty         (dc3_ds_dirty      ),           
  
  .dc4_dd_data              (dc4_dd_data       )            
);


npuarc_alb_dmp_rf u_alb_dmp_rf (


  .clk                  (clk                ),         
  .rst_a                (rst_a              ),       

  .dc3_mq_addr_match    (dc3_mq_addr_match  ), 
  .dc4_mq_addr_match    (dc4_mq_addr_match  ), 

  .rf_cmd_valid         (rf_cmd_valid       ), 
  .rf_cmd_excl          (rf_cmd_excl        ),       
  .rf_cmd_accept        (rf_cmd_accept      ),
  .rf_cmd_read          (rf_cmd_read        ),  
  .rf_cmd_addr          (rf_cmd_addr        ),  
  .rf_cmd_prot          (rf_cmd_prot        ),  
  .rf_cmd_wrap          (rf_cmd_wrap        ),  
  .rf_cmd_burst_size    (rf_cmd_burst_size  ),


  .mq_cmd_valid         (mq_cmd_valid       ),       
  .mq_cmd_pre_alloc     (mq_cmd_pre_alloc   ),
  .mq_cmd_cache_rf      (mq_cmd_cache_rf    ),
  .mq_cmd_cache_op      (mq_cmd_cache_op    ), 
  .mq_cmd_userm         (mq_cmd_userm       ),       
  .mq_cmd_addr          (mq_cmd_addr        ),  
  .rf_cmd_rptr_r        (rf_cmd_rptr_r      ),     

  .mq_valid             (mq_valid           ),
  .mq_addr              (mq_addr            ), 
  .mq_cache_lock        (mq_cache_lock      ),
  .mq_pre_alloc         (mq_pre_alloc       ),
  .mq_pref              (mq_pref            ),
  .mq_scond             (mq_scond           ),
  .mq_dirty             (mq_dirty           ),
  .mq_cb_complete       (mq_cb_complete     ),
  .mq_replacement_way   (mq_replacement_way ),
  .mq_replacement_valid (mq_replacement_valid),
  .mq_bus_err_r         (mq_bus_err_r       ),

  .rf_ack_ok            (dmu_ack_ok         ),
  .rf_dc_start          (rf_dc_start        ),
  .rf_dc_ready          (rf_dc_ready        ),
  .rf_dc_done           (rf_dc_done         ),
  .cb_buf_busy_r        (cb_buf_busy_r      ),
  .cb_full              (cb_full            ),
  .wq_scond_entry       (wq_scond_entry     ),

  .lb_ready_to_dc       (lb_ready_to_dc     ),      
  .lb_err_r             (lb_err_r           ),      
  .lbuf_initial         (lbuf_initial       ),  
  .lbuf_rd_valid        (lbuf_rd_valid      ), 
  .lbuf_rd_last         (lbuf_rd_last       ),
  
  .rf_lbuf_rd_last_r    (rf_lbuf_rd_last_r  ),  
   
  .lsmq_done            (lsmq_done          ),      
  
  .rf_err_req           (rf_err_req         ),
  .rf_err_addr          (rf_err_addr        ),

  .dd_busy_nxt          (dd_busy_nxt        ),
  
  .rf_req_dt_even       (rf_req_dt_even     ),
  .rf_req_dt_odd        (rf_req_dt_odd      ),
  .rf_dt_odd_sel        (rf_dt_odd_sel      ),
  .rf_dt_way_hot        (rf_dt_way_hot      ),
  .rf_dt_we             (rf_dt_we           ),  
  .rf_dt_wem            (rf_dt_wem          ), 
  .rf_dt_addr           (rf_dt_addr         ), 
  .rf_dt_valid          (rf_dt_valid        ), 
  .rf_dt_tag            (rf_dt_tag          ), 
  .rf_req_dd            (rf_req_dd          ), 
  .rf_ack_dd            (rf_ack_dd          ), 
  .rf_dd_way_hot        (rf_dd_way_hot      ),
  .rf_dd_we             (rf_dd_we           ),  
  .rf_dd_addr           (rf_dd_addr         ), 
  
  .rf_req_ds            (rf_req_ds          ), 
  .rf_ds_odd_sel        (rf_ds_odd_sel      ),
  .rf_ds_we             (rf_ds_we           ),  
  .rf_ds_wem            (rf_ds_wem          ), 
  .rf_ds_way_hot        (rf_ds_way_hot      ),
  .rf_ds_addr           (rf_ds_addr         ),
  .rf_ds_lock           (rf_ds_lock         ),
  .rf_ds_dirty          (rf_ds_dirty        ),
  .rf_ds_lru            (rf_ds_lru          )  

);

// leda TEST_975 off
// LMD: Latch enabled by a clock affects data input of flipflops clocked by the trailing edge of the same clock
// LJ:
//
always @*
begin : dmp_evict_ecc_parity_error_reg_PROC
  dmp_evict_error     =  (dc4_dc_dt_ecc_db_error 
                          )
                        | dc4_dc_dd_ecc_db_error 
                        ;
end
// leda TEST_975 on


//////////////////////////////////////////////////////////////////////////
//                                                                        
// Synchronous processes   
//                                                                        
//////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: mq_hit_sync_PROC
  if (rst_a == 1'b1)
  begin
    mq_addr0_hit_r  <= 1'b0;
    mq_addr1_hit_r  <= 1'b0;
  end
  else if (ca_enable == 1'b1)
  begin
    mq_addr0_hit_r  <= mq_addr0_hit;
    mq_addr1_hit_r  <= mq_addr1_hit;
  end
end


// leda W175 on

endmodule // alb_dmp_dmu

