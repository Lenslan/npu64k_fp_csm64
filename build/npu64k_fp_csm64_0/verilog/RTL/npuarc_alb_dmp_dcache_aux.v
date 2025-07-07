// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2020 Synopsys, Inc. All rights reserved.
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
// ALB_DMP_DCACHE_AUX
// 
// 
// 
// 
//
// ===========================================================================
//
// Description:
//  This module implements the DCACHE aux registers functionallity, including
//  the associated cache instructions.
//    
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_dcache_aux.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  rst: "rst_a", edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_dmp_dcache_aux (
// LMD: non driving port
// LJ: some bits of inputs vectors are not used
    
  ////////// General input signals ///////////////////////////////////////////
  //
  input                        clk,            // clock
  input                        rst_a,          // reset
  input                        dbg_cache_rst_disable_r,

  ////////// Interface with aux ctl ///////////////////////////////////////////
  //
  input                       aux_read,        //  (X3) Aux region read
  input                       aux_write,       //  (x3) Aux reagion write
  input                       aux_ren_r,       //  (X3) Aux region select
  input [4:0]                 aux_raddr_r,     //  (X3) Aux region addr
  input                       aux_wen_r,       //  (WA) Aux region select
  input [4:0]                 aux_waddr_r,     //  (WA) Aux write addr 
  input  [`npuarc_DATA_RANGE]        aux_wdata_r,     //  (WA) Aux write data
  
  output reg [`npuarc_ADDR_RANGE]    aux_rdata,       //  (X3) LR read data
  output reg                  aux_illegal,     //  (X3) SR/LR illegal
  output reg                  aux_k_rd,        //  (X3) needs Kernel Read
  output reg                  aux_k_wr,        //  (X3) needs Kernel Write
  output reg                  aux_unimpl,      //  (X3) Invalid Reg
  output reg                  aux_serial_sr,   //  (X3) SR group flush pipe
  output reg                  aux_strict_sr,   //  (X3) SR flush pipe

  //////////// Interface with EXU /////////////////////////////////////////// 
  //
  output reg                  aux_x2_addr_pass,
  output reg [`npuarc_ADDR_RANGE]    aux_x2_addr,
  output reg [7:0]            aux_x2_addr_hi,
  //////////// Interface with cache front-end ///////////////////////////////// 
  //
  output reg                  aux_init_r, 
  output reg                  aux_busy,          
  output reg                  aux_cache_off,
  output reg [1:0]            aux_sg_off,

  input                          aux_ecc_scrub_in_progress_r,
  input [`npuarc_DC_ADR_RANGE]          aux_ecc_addr_r,
  input [`npuarc_DC_TAG_TAG_DATA_RANGE] aux_ecc_tag_r,
  input [1:0]                    aux_ecc_dt_way_hot_r,
  input [3:0]                    aux_ecc_data_mem_valid_r,
  input [3:0]                    dc4_dt_ecc_sb_error,
  input [3:0]                    dc4_dd_ecc_sb_error,
  input [3:0]                    dc4_dt_ecc_db_error,
  input                          dc4_dt_ecc_scrub_start,
  input                          dc4_dd_ecc_scrub_start,
  input                          aux_dc_dt_scrub_start_r,
  input                          aux_dc_dd_scrub_start_r,
  input [`npuarc_DATA_RANGE]            dc4_ecc_data_odd_hi,
  input [`npuarc_DATA_RANGE]            dc4_ecc_data_odd_lo,
  input [`npuarc_DATA_RANGE]            dc4_ecc_data_even_hi,
  input [`npuarc_DATA_RANGE]            dc4_ecc_data_even_lo,
  output reg                     aux_dt_read,
  output reg                     aux_ecc_done_r,

  output reg [3:0]               ecc_dc_tag_sbe_count_r,  // single bit error count on tag
  input                          dc_tag_ecc_sbe_clr,
  output reg [3:0]               ecc_dc_data_sbe_count_r, // single bit error count on data
  input                          dc_data_ecc_sbe_clr,

  output reg                  aux_req_dt_even,
//  input                       aux_ack_dt_even,
  output reg                  aux_req_dt_odd,
//  input                       aux_ack_dt_odd,
  output reg [`npuarc_DC_WAY_RANGE]  aux_dt_way_hot,
  output reg [`npuarc_DC_IDX_RANGE]  aux_dt_addr,
  output reg                  aux_dt_we,
  output reg [2:0]            aux_dt_wem,   // e, v, tag
  output reg                  aux_dt_valid,
  output reg [`npuarc_DC_TAG_RANGE]  aux_dt_tag,

  output reg                  aux_req_ds,
//  input                       aux_ack_ds,
  output reg [`npuarc_DC_IDX_RANGE]  aux_ds_addr,
  output reg                  aux_ds_odd_sel,
  output reg                  aux_ds_we,
  output reg [2:0]            aux_ds_wem,  // lock, dirty, lru
  output reg                  aux_ds_lock,
  output reg                  aux_ds_dirty,
  output reg                  aux_ds_lru,
  output reg [`npuarc_DC_WAY_RANGE]  aux_ds_way_hot,
  
  output reg                  aux_req_dd_even_lo,
  output reg                  aux_req_dd_even_hi,
  output reg                  aux_req_dd_odd_lo,
  output reg                  aux_req_dd_odd_hi,
  output reg [`npuarc_DC_ADR_RANGE]  aux_dd_addr,
  output reg [`npuarc_DC_WAY_RANGE]  aux_dd_way_hot, 
  output reg                  aux_dd_we,
  output reg [127:0]          aux_dd_din,
  output reg                  aux_dd_data_read,
  output reg                  aux_dd_direct_read,
  output reg [1:0]            aux_dd_data_bank,
  input [31:0]                dc_dd_data,
  
  //////////// SRAM inputs ////////////////////////////////////////////////// 
  //
  input  [1:0]                dc3_dt_even_hit_way_hot,
  input  [1:0]                dc3_dt_even_valid_hot,
  input  [1:0]                dc3_ds_even_dirty_hot,
  input  [1:0]                dc3_ds_even_lock_hot,
  
  input  [1:0]                dc3_dt_odd_hit_way_hot,
  input  [1:0]                dc3_dt_odd_valid_hot,
  input  [1:0]                dc3_ds_odd_dirty_hot,
  input  [1:0]                dc3_ds_odd_lock_hot,
  
  input [`npuarc_DC_TAG_TAG_RANGE]   dc3_dt_even_tag_w0,
  input [`npuarc_DC_TAG_TAG_RANGE]   dc3_dt_odd_tag_w0,
  input [`npuarc_DC_TAG_TAG_RANGE]   dc3_dt_even_tag_w1,
  input [`npuarc_DC_TAG_TAG_RANGE]   dc3_dt_odd_tag_w1,
  
  ////////// MQ interface ////////////////////////////////////////////////
  //   
  output reg                  aux_mq_write,  // write aux req 
  output reg                  aux_mq_flush,  // flush cache maintenance
  output reg                  aux_mq_purge,  // purge cache maintenance
  output reg                  aux_mq_refill, // lock rf cache maintenance
  output reg                  aux_mq_way,       // flush/rf way
  output reg [`npuarc_DC_LBUF_RANGE] aux_mq_addr,      // flush/rf address
  output reg                  aux_mq_lru_dirty, // lru is dirty (lock cobyback)
  input                       lb_err_r,         // Bus error
  input                       mq_empty,         // no valid entries in MQ
  input                       cb_full,          // two outstanding cb
//  input                       cb_wr_done,       // IBP wr done
  input                       cb_err_wr,        // IBP wr err

  ////////// Interface to perf counters //////////////////////////////////////
  //   
  output reg                  dc_pct_ivdc,      // Invalidate Data Cache
  output reg                  dc_pct_ivdl,      // Invalidate Data Line
  output reg                  dc_pct_flsh,      // Flush entire cache
  output reg                  dc_pct_fldl,      // Flush data line
  
  //////////// Interface with cache back-end ///////////////////////////////// 
  //
  input                       dc_pipe_empty,    // no ld/st instr in the  pipe
  input                       wq_empty,
  input                       dmu_empty, 
  input                       dmu_dc_idle

);

// leda W175 off
// LMD: A parameter has been defined but is not used.
// LJ:  Code more readable; 

// Local declarations.
//

// Clock gates
//
reg                    aux_dc_fler_cg0;    
   
reg                    aux_dc_tag_cg0;     
reg                    aux_dc_data_cg0;
reg                    aux_dc_op_cg0;
reg                    aux_dt_ecc_sb_error_r;
reg                    aux_dt_ecc_sb_error_nxt;
reg                    aux_dc_ecc_op_cg0;

reg                    aux_dc_ivdc_wen;
reg                    aux_dc_flsh_wen;
reg                    aux_dc_ivdl_wen; 
reg                    aux_dc_ldl_wen; 
reg                    aux_dc_fldl_wen;    
reg                    aux_dc_start_region_wen;    
reg                    aux_dc_ram_addr_wen;    
reg                    aux_dc_tag_wen;    
reg                    aux_dc_data_wen; 
reg                    aux_dc_ptag_hi_wen;  
reg                    aux_dc_ctrl_wen;    

// Aux registers
//
reg [11:0]             aux_dc_ctrl_r;
reg [`npuarc_DATA_RANGE]      aux_dc_data_r;
reg [7:0]              aux_dc_ptag_hi_r;
reg                    aux_dc_tag_valid_r;
reg                    aux_dc_tag_lock_r;
reg                    aux_dc_tag_dirty_r;
reg [`npuarc_DC_IDX_RANGE]    aux_dc_tag_index_r;
reg                    aux_dc_tag_bank_r;
reg [`npuarc_DC_TAG_RANGE]    aux_dc_tag_tag_r;

reg [`npuarc_DATA_RANGE]      aux_dc_data_nxt;
reg                    aux_dc_tag_valid_nxt;
reg                    aux_dc_tag_lock_nxt;
reg                    aux_dc_tag_dirty_nxt;
reg [`npuarc_DC_IDX_RANGE]    aux_dc_tag_index_nxt;
reg                    aux_dc_tag_bank_nxt;
reg [`npuarc_DC_TAG_RANGE]    aux_dc_tag_tag_nxt;

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg [`npuarc_PADDR_RANGE]    aux_dc_flush_end_r; 

reg [12:0]             aux_dc_op_r;
reg [12:0]             aux_dc_op_nxt;
reg                    aux_dc_line_op;
reg                    aux_dc_region_op;
reg                    aux_line_lock_op;
reg                    aux_line_flush_op;
reg                    aux_dc_read_lookup;

reg                    aux_dc_read_direct;

reg                    aux_dc_read;
reg                    aux_dc_wr_tag; 
reg                    aux_dc_wr_data;

reg [11:0]             aux_dc_ctrl_nxt;

reg                    aux_ctrl_sb_cg0;
reg                    aux_ctrl_sb_r;
reg                    aux_ctrl_sb_nxt;

reg                    aux_ctrl_fs_r;
reg                    aux_ctrl_fs_nxt;

reg [`npuarc_ADDR_RANGE]      aux_sr_wdata;

reg                    aux_lookup_addr_cg0; 
reg                    aux_dc_ram_addr_cg0; 
reg                    aux_lookup_incr;
reg [`npuarc_PADDR_RANGE]     aux_lookup_addr_r; 
reg [33:0]            aux_lookup_addr_incr; 
reg [`npuarc_PADDR_RANGE]     aux_dc_ram_addr_r; 
reg [`npuarc_PADDR_RANGE]     aux_lookup_addr_nxt; 

reg                    aux_dd_set_incr_cg0;
reg                    aux_dd_set_incr;
reg [`npuarc_DC_ADDR_BITS-1:0]aux_dd_set_addr_nxt;
reg [`npuarc_DC_ADDR_BITS-1:0]aux_dd_set_addr_r;

reg                    aux_region_ctrl_flush; 
reg                    aux_region_ctrl_inv;
reg                    aux_region_last;
reg                    aux_region_bad;    
reg                    aux_region_fail_cg0; 
reg                    aux_region_fail_r;
reg                    aux_region_fail_nxt;

reg                    aux_region_done_cg0; 
reg                    aux_region_done_r; 
reg                    aux_region_done_nxt; 

reg                    aux_init_nxt;
reg                    aux_done; 

reg                    aux_set_flush_pending;
reg                    aux_reset_flush_pending;

reg                    aux_sb_err;

reg                    aux_ecc_done_nxt;

reg [3:0]              ecc_dc_data_sbe_count_nxt;
reg [3:0]              ecc_dc_data_sbe_count_next;
reg                    ecc_dc_data_sbe_count_set_cg0;
reg                    ecc_dc_data_sbe_count_clr_cg0;


reg [3:0]              ecc_dc_tag_sbe_count_nxt;
reg [3:0]              ecc_dc_tag_sbe_count_next;
reg                    ecc_dc_tag_sbe_count_set_cg0;
reg                    ecc_dc_tag_sbe_count_clr_cg0;

reg                    aux_way_counter_cg0;
reg                    aux_way_counter_r;
reg                    aux_way_counter_nxt;

reg                    aux_set_even_cg0;   
reg                    aux_set_even_r;  
reg                    aux_set_even_nxt;   
   
reg                    aux_set_counter_cg0;
reg [`npuarc_DC_IDX_RANGE]    aux_set_counter_r;
reg [`npuarc_DC_IDX_RANGE]    aux_set_counter_nxt;
reg [`npuarc_DC_IDX_RANGE]    aux_set_counter_incr;  

reg                     aux_info_valid_cg0;
reg                     aux_info_valid_r;
reg                     aux_info_valid_nxt;

reg [`npuarc_DC_WAY_RANGE]     aux_ds_even_valid_hot_r;
reg [`npuarc_DC_WAY_RANGE]     aux_ds_even_dirty_hot_r;
reg [`npuarc_DC_WAY_RANGE]     aux_ds_even_lock_hot_r; 
reg [`npuarc_DC_WAY_RANGE]     aux_ds_odd_valid_hot_r;
reg [`npuarc_DC_WAY_RANGE]     aux_ds_odd_dirty_hot_r; 
reg [`npuarc_DC_WAY_RANGE]     aux_ds_odd_lock_hot_r; 

reg [`npuarc_DC_WAY_RANGE]    aux_hit_even_way_hot;  
reg [`npuarc_DC_WAY_RANGE]    aux_flush_even_way_hot;
reg [`npuarc_DC_WAY_RANGE]    aux_lock_even_way_hot;
reg [`npuarc_DC_WAY_RANGE]    aux_hit_odd_way_hot;  
reg [`npuarc_DC_WAY_RANGE]    aux_flush_odd_way_hot;
reg [`npuarc_DC_WAY_RANGE]    aux_lock_odd_way_hot;

reg [`npuarc_DC_WAY_RANGE]    aux_hit_way_hot;
reg [`npuarc_DC_WAY_RANGE]    aux_flush_way_hot;
reg [`npuarc_DC_WAY_RANGE]    aux_lock_way_hot;
reg                    aux_way0_dirty;
reg                    aux_all_locked;
reg                    aux_flush_line;
reg                    aux_no_flush_lock;
reg                    aux_lock_hit;  
reg                    aux_lock_dirty;

reg                    aux_hit_way_hot_cg0;
reg [`npuarc_DC_WAY_RANGE]    aux_hit_way_hot_r;
reg [`npuarc_DC_WAY_RANGE]    aux_hit_way_hot_nxt;
reg [`npuarc_DC_WAY_RANGE]    aux_flush_way_hot_r;
reg [`npuarc_DC_WAY_RANGE]    aux_lock_way_hot_r;
reg                    aux_all_locked_r;

reg                    aux_line_hit;
reg                    aux_line_dirty;
reg                    aux_line_locked;

reg                    aux_lock_flush_r;
reg                    aux_lock_flush_nxt;
reg                    aux_lock_rf_r;
// leda NTL_CON32 on
reg                    aux_lock_rf_nxt;
reg                    aux_lock_sb_r;
reg                    aux_lock_sb_nxt;

reg                    aux_tag_direct_valid;
reg                    aux_tag_direct_lock; 
reg                    aux_tag_direct_dirty;

reg [`npuarc_DC_TAG_RANGE]    aux_tag_direct_tag;

reg [3:0]              aux_state_r;
reg [3:0]              aux_state_nxt;

wire                   aux_dc_ctrl_lm;

parameter DC_RESET        = 0;
parameter DC_IVDC         = 1;
parameter DC_FLSH         = 2;
parameter DC_IVDL         = 3;
parameter DC_LDL          = 4;
parameter DC_FLDL         = 5;
parameter DC_FLDR         = 6;
parameter DC_IVDR         = 7;
parameter DC_READ         = 8;
parameter DC_WR_TAG       = 9;
parameter DC_WR_DATA      = 10;


// Incase of ECC, we have a separate parameter for scrubbing the tag and data that
// has a single bit error. This should be set inorder for the error data to be scrubbed.
//
parameter DC_DT_ECC_SCRUB = 11;
parameter DC_DD_ECC_SCRUB = 12;
parameter DC_BITS         = 13;

parameter DC_BIT          = 0;
parameter SB_BIT          = 2;
parameter AT_BIT          = 5;
parameter IM_BIT          = 6;
parameter LM_BIT          = 7;
parameter FS_BIT          = 8;

`define   DSG_RANGE         4:3

//////////////////////////////////////////////////////////////////////////////
// Reads
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_read_PROC
  aux_rdata      = {`npuarc_ADDR_SIZE{1'b0}};       
  aux_illegal    = 1'b0;     
  aux_k_rd       = 1'b0;        
  aux_k_wr       = 1'b0;       
  aux_unimpl     = 1'b1;      
  aux_serial_sr  = 1'b0;  
  aux_strict_sr  = 1'b0;
  
  if (aux_ren_r)
  begin
    // We have got selected
    //
    case ({7'b0000010, aux_raddr_r})
    `npuarc_DC_IVDC_AUX: 
    begin
      // K_WRITE
      //
      aux_illegal    = aux_read;
      aux_k_wr       = 1'b1; 
      aux_strict_sr  = aux_write;
      aux_unimpl     = 1'b0;    
    end
    
    `npuarc_DC_CTRL_AUX: 
    begin
      // K_RW
      //
      aux_rdata[11:0] = {aux_dc_ctrl_r[`npuarc_DC_REGION_CTRL_RANGE],
                         aux_ctrl_fs_r,
                         aux_dc_ctrl_r[7:5],
                         aux_dc_ctrl_r[`DSG_RANGE], 
                         aux_ctrl_sb_r,
                         1'b0,
                         aux_dc_ctrl_r[0]};     
      aux_k_rd       = 1'b1;    
      aux_k_wr       = 1'b1;    
      aux_serial_sr  = aux_write;
      aux_unimpl     = 1'b0;    
    end
    
    `npuarc_DC_FLSH_AUX: 
    begin
      // K_WRITE
      //
      aux_k_wr       = 1'b1; 
      aux_illegal    = aux_read;
      aux_strict_sr  = aux_write;
      aux_unimpl     = 1'b0;   
    end
    
    `npuarc_DC_LDL_AUX:  
    begin
      // K_WRITE
      //
      aux_k_rd       = 1'b1;    
      aux_k_wr       = 1'b1;    
      aux_illegal    = aux_read;
      aux_strict_sr  = aux_write;
      aux_unimpl     = 1'b0;   
    end
    
    `npuarc_DC_IVDL_AUX: 
    begin
      // K_WRITE
      //
      aux_k_rd       = 1'b1;    
      aux_k_wr       = 1'b1;    
      aux_illegal    = aux_read;
      aux_strict_sr  = aux_write;
      aux_unimpl     = 1'b0;   
    end
    
    `npuarc_DC_FLDL_AUX:
    begin
      // K_WRITE
      //
      aux_k_rd       = 1'b1;    
      aux_k_wr       = 1'b1;    
      aux_illegal    = aux_read;
      aux_strict_sr  = aux_write;
      aux_unimpl     = 1'b0;   
    end
    
    `npuarc_DC_STARTR_AUX:
    begin
      // K_WRITE
      //
      aux_k_rd       = 1'b1;    
      aux_k_wr       = 1'b1;    
      aux_illegal    = aux_read;
      aux_strict_sr  = aux_write;
      aux_unimpl     = 1'b0;   
    end
    
    `npuarc_DC_ENDR_AUX:
    begin
      // K_RW
      //
      aux_k_rd                  = 1'b1;    
      aux_k_wr                  = 1'b1;    
      aux_rdata[`npuarc_ADDR_MSB:`npuarc_DC_IDX_LSB] = aux_dc_flush_end_r[`npuarc_ADDR_MSB:`npuarc_DC_IDX_LSB];
      aux_unimpl                = 1'b0;   
    end

    `npuarc_DC_RAM_ADDR_AUX: 
    begin
      // K_RW
      //
      aux_k_rd       = 1'b1;                 
      aux_k_wr       = 1'b1;                 
      aux_rdata      = aux_dc_ram_addr_r[`npuarc_ADDR_RANGE];    
      aux_strict_sr  = aux_write;            
      aux_unimpl     = 1'b0;                 
    end
    
    `npuarc_DC_TAG_AUX: 
    begin
      // K_RW
      // 
      aux_rdata[0]                = aux_dc_tag_valid_r;
      aux_rdata[1]                = aux_dc_tag_lock_r;
      aux_rdata[2]                = aux_dc_tag_dirty_r;
      aux_rdata[`npuarc_DC_TAG_BANK_ID]  = aux_dc_tag_bank_r;
      aux_rdata[`npuarc_DC_IDX_RANGE]    = aux_dc_tag_index_r;
      aux_rdata[`npuarc_ADDR_MSB:`npuarc_DC_TAG_LSB]    
                                  = aux_dc_tag_tag_r[`npuarc_ADDR_MSB:`npuarc_DC_TAG_LSB];
      aux_k_rd                    = 1'b1;    
      aux_k_wr                    = 1'b1;    
      aux_strict_sr               = aux_write & (~aux_dc_ctrl_r[AT_BIT]);
      aux_illegal                 = aux_write & aux_dc_ctrl_r[AT_BIT];
      aux_unimpl                  = 1'b0;   
    end
    
    `npuarc_DC_DATA_AUX: 
    begin
      // K_RW
      //
      aux_rdata[`npuarc_DATA_RANGE] = aux_dc_data_r;
      aux_k_rd       = 1'b1;    
      aux_k_wr       = 1'b1;    
      aux_strict_sr  = aux_write & (~aux_dc_ctrl_r[AT_BIT]);
      aux_illegal    = aux_write & aux_dc_ctrl_r[AT_BIT];
      aux_unimpl     = 1'b0;   
    end

    `npuarc_DC_PTAG_HI:
    begin
      // K_RW
      //
      aux_rdata[7:0] = aux_dc_ptag_hi_r;
      aux_k_rd       = 1'b1;    
      aux_k_wr       = 1'b1;    
      aux_strict_sr  = 1'b0;
      aux_illegal    = 1'b0;
      aux_unimpl     = 1'b0;   
    end

// spyglass disable_block W193
// SMD: empty statements
// SJ:  empty default statements kept

    default:
      ;
    endcase  
  end
end

//////////////////////////////////////////////////////////////////////////////
// Writes
//
//////////////////////////////////////////////////////////////////////////////

always @*
begin : aux_write_PROC
  aux_dc_fler_cg0          = 1'b0;

  aux_dc_ivdc_wen          = 1'b0;
  aux_dc_flsh_wen          = 1'b0;
  aux_dc_ivdl_wen          = 1'b0;
  aux_dc_ldl_wen           = 1'b0;
  aux_dc_fldl_wen          = 1'b0;
  aux_dc_start_region_wen  = 1'b0;
  aux_dc_ram_addr_wen      = 1'b0;
  aux_dc_tag_wen           = 1'b0;
  aux_dc_data_wen          = 1'b0;
  aux_dc_ptag_hi_wen       = 1'b0;
  aux_dc_ctrl_wen          = 1'b0;
  
  // Write data
  //
  aux_sr_wdata             = {`npuarc_DATA_SIZE{aux_wen_r}} & aux_wdata_r;
  
  
  aux_dc_op_cg0            =  1'b0
                           ;
  
  aux_dc_ecc_op_cg0        = 1'b0
                           | aux_dc_dt_scrub_start_r
                           | aux_dc_dd_scrub_start_r
                           ;
  dc_pct_ivdc              = 1'b0;    
  dc_pct_ivdl              = 1'b0;    
  dc_pct_flsh              = 1'b0;   
  dc_pct_fldl              = 1'b0;   

  if (  aux_wen_r
      & (~(dc4_dt_ecc_scrub_start | aux_dc_dt_scrub_start_r))
      & (~(dc4_dd_ecc_scrub_start | aux_dc_dd_scrub_start_r))
     )
  begin
    case ({7'b0000010, aux_waddr_r})
    `npuarc_DC_IVDC_AUX: 
    begin
      aux_dc_ivdc_wen  = aux_sr_wdata[0];
      aux_dc_op_cg0    = aux_sr_wdata[0];
      dc_pct_ivdc      = aux_sr_wdata[0];
    end
    
    `npuarc_DC_CTRL_AUX: 
    begin
      aux_dc_ctrl_wen  = 1'b1;
    end
    
    `npuarc_DC_LDL_AUX:  
    begin
      aux_dc_ldl_wen   = 1'b1;
      aux_dc_op_cg0    = 1'b1;
    end

    `npuarc_DC_IVDL_AUX: 
    begin
      aux_dc_ivdl_wen  = 1'b1;
      aux_dc_op_cg0    = 1'b1;
      dc_pct_ivdl      = 1'b1;
    end

    `npuarc_DC_FLSH_AUX: 
    begin
      aux_dc_flsh_wen  = aux_sr_wdata[0];
      aux_dc_op_cg0    = aux_sr_wdata[0];
      dc_pct_flsh      = aux_sr_wdata[0];
    end
    
    
    `npuarc_DC_FLDL_AUX:
    begin
      aux_dc_fldl_wen  = 1'b1;
      aux_dc_op_cg0    = 1'b1;
      dc_pct_fldl      = 1'b1;
    end
    
    `npuarc_DC_STARTR_AUX:
    begin
      aux_dc_start_region_wen  = 1'b1;
      aux_dc_op_cg0            = 1'b1;
    end
    
    `npuarc_DC_ENDR_AUX:
    begin
      aux_dc_fler_cg0  = 1'b1;
    end
    
    `npuarc_DC_RAM_ADDR_AUX: 
    begin
      aux_dc_ram_addr_wen  = 1'b1;
      aux_dc_op_cg0        = 1'b1;
    end
    
    `npuarc_DC_TAG_AUX: 
    begin
      aux_dc_tag_wen  = 1'b1;
      aux_dc_op_cg0   = 1'b1;
    end
    
    `npuarc_DC_DATA_AUX: 
    begin
      aux_dc_data_wen = 1'b1;
      aux_dc_op_cg0   = 1'b1;
    end
    
    `npuarc_DC_PTAG_HI:
    begin
      aux_dc_ptag_hi_wen = 1'b1;
      aux_dc_op_cg0      = 1'b1;
    end

    default:
      ;
    endcase  
  end
end

//////////////////////////////////////////////////////////////////////////////
// Asynchronous logic defining nxt value of aux_dc_ctrl 
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_dc_ctrl_nxt_PROC
 
  aux_dc_ctrl_nxt         = aux_dc_ctrl_r;

  if (aux_dc_ctrl_wen)
  begin
    // SR to dc_ctrl
    //
    aux_dc_ctrl_nxt[7:0]                   = aux_sr_wdata[7:0];
    aux_dc_ctrl_nxt[`npuarc_DC_REGION_CTRL_RANGE] = aux_sr_wdata[`npuarc_DC_REGION_CTRL_RANGE];
  end
end

//////////////////////////////////////////////////////////////////////////////
// Asynchronous process
//
//////////////////////////////////////////////////////////////////////////////
// spyglass disable_block STARC05-2.8.1.3
// spyglass disable_block W398
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, code more readable, optimized by synthesizer.
always @*
begin : aux_flush_pending_PROC
  
  // Reset the FS bit when there is no outstanding write transactions on the
  // bus and we are done with the aux transaction
  //
  aux_reset_flush_pending =   dmu_empty
                            & (~aux_busy);
 
  casez ({aux_set_flush_pending, aux_reset_flush_pending})
  2'b1?:   aux_ctrl_fs_nxt = 1'b1;
  2'b?1:   aux_ctrl_fs_nxt = 1'b0;
  default: aux_ctrl_fs_nxt = aux_ctrl_fs_r;
  endcase
end

always @*
begin : aux_sb_err_PROC
  // The SB bit should be reset when the flush comes back with an error
  //
  aux_sb_err = aux_ctrl_fs_r & cb_err_wr;
end
// spyglass enable_block W398
// spyglass enable_block STARC05-2.8.1.3
//////////////////////////////////////////////////////////////////////////////
// Asynchronous process: set counter
//
//////////////////////////////////////////////////////////////////////////////
// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y
// LJ:  One bit incrementor, zero extended

// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow
always @*
begin : aux_set_counter_incr_PROC
  aux_set_counter_incr = aux_set_counter_r + 1'b1;
end
// leda W484 on
// leda BTTF_D002 on
// leda B_3200 on


// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y
// LJ:  One bit incrementor, zero extended

// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow

//////////////////////////////////////////////////////////////////////////////
// Asynchronous process: share the loopkup address
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_lookup_addr_nxt_PROC  
  aux_lookup_addr_cg0     =  aux_dc_ivdl_wen 
                           | aux_dc_fldl_wen
                           | aux_dc_ldl_wen
                           | aux_dc_start_region_wen
                           | aux_dc_ram_addr_wen
                           | aux_lookup_incr
                           ;

  aux_dc_ram_addr_cg0      = aux_dc_ram_addr_wen;

  aux_lookup_addr_nxt     = {aux_dc_ptag_hi_r, aux_sr_wdata}; 

  if (aux_lookup_incr)
  begin
    // Increment the lookup address for region based operations
    //
    aux_lookup_addr_nxt[`npuarc_PADDR_MSB:`npuarc_DC_BLOCK_BITS] = aux_lookup_addr_incr; 
  end
end

always @*
begin : aux_dd_set_incr_PROC
  //
  //
  aux_dd_set_incr_cg0 = aux_dd_set_incr;

  aux_dd_set_addr_nxt = aux_dd_set_addr_r;

  if (aux_dd_set_incr)
  begin
    // Increment the set address for cache reset
    //
    aux_dd_set_addr_nxt = aux_dd_set_addr_r + 1'b1;
     
  end
end

always @*
begin : aux_lookup_addr_incr_PROC
  aux_lookup_addr_incr  = aux_lookup_addr_r[`npuarc_PADDR_MSB:`npuarc_DC_BLOCK_BITS] + 1'b1;
end

//////////////////////////////////////////////////////////////////////////////
// Asynchronous process: last region address
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_region_last_PROC
  //
  aux_region_last       = (   aux_lookup_addr_incr
                           == aux_dc_flush_end_r[`npuarc_PADDR_MSB:`npuarc_DC_BLOCK_BITS]);
end

// leda W484 on
// leda BTTF_D002 on
// leda B_3200 on

//////////////////////////////////////////////////////////////////////////////
// Aysynchronous process: degenerated region
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_region_bad_PROC
  aux_region_bad =    ({aux_dc_ptag_hi_r, aux_sr_wdata[`npuarc_ADDR_MSB:`npuarc_DC_BLOCK_BITS]})
                   >= aux_dc_flush_end_r[`npuarc_PADDR_MSB:`npuarc_DC_BLOCK_BITS];


  aux_region_fail_cg0 = aux_dc_start_region_wen | aux_region_fail_r;
  aux_region_fail_nxt = aux_dc_start_region_wen & aux_region_bad;
end

//////////////////////////////////////////////////////////////////////////////
// Aysynchronous process: region ctrl 
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_region_ctrl_PROC
  aux_region_ctrl_flush =    aux_dc_ctrl_r[`npuarc_DC_REGION_CTRL_RANGE] 
                          == `npuarc_DC_REGION_CTRL_FLUSH; 
  aux_region_ctrl_inv   =     aux_dc_ctrl_r[`npuarc_DC_REGION_CTRL_RANGE]
                           == `npuarc_DC_REGION_CTRL_INV;
end

//////////////////////////////////////////////////////////////////////////////
// Asynchronous block defining some cache instructions
//
//////////////////////////////////////////////////////////////////////////////
reg aux_dc_dt_ecc_scrub;
reg aux_dc_dd_ecc_scrub;

always @*
begin : aux_dc_op_PROC
  aux_dc_line_op        = (  aux_dc_op_r[DC_IVDL] 
                           | aux_dc_op_r[DC_LDL] 
                           | aux_dc_op_r[DC_FLDL] 
                           | aux_dc_op_r[DC_FLDR]
                           | aux_dc_op_r[DC_IVDR])
                          ;  
  
  aux_dc_region_op      = (  aux_dc_op_r[DC_FLDR]
                           | aux_dc_op_r[DC_IVDR])
                          ;
  
  aux_line_flush_op     =  (  aux_dc_op_r[DC_FLDL] 
                            | aux_dc_op_r[DC_FLDR])
                           ;  
  
  aux_line_lock_op      = aux_dc_op_r[DC_LDL]; 
  
  aux_dc_read_lookup    =   aux_dc_op_r[DC_READ] 
                          & aux_dc_ctrl_r[AT_BIT]
                          ;  
  aux_dc_read_direct    =    aux_dc_op_r[DC_READ] 
                           & (~aux_dc_ctrl_r[AT_BIT])
                          ; 
 
  aux_dc_read           = aux_dc_op_r[DC_READ];
  aux_dc_wr_tag         = aux_dc_op_r[DC_WR_TAG];
  aux_dc_wr_data        = aux_dc_op_r[DC_WR_DATA];
  aux_dc_dt_ecc_scrub   = aux_dc_op_r[DC_DT_ECC_SCRUB];
  aux_dc_dd_ecc_scrub   = aux_dc_op_r[DC_DD_ECC_SCRUB];
end

//////////////////////////////////////////////////////////////////////////////
// Direct reads
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_tag_direct_PROC
  casez ({aux_set_even_r, aux_lookup_addr_r[`npuarc_DC_WAY_CACHE_RANGE]})
  2'b00:
  begin
    // Odd, way0
    //
    aux_tag_direct_valid     = aux_ds_odd_valid_hot_r[0];  
    aux_tag_direct_lock      = aux_ds_odd_lock_hot_r[0]; 
    aux_tag_direct_dirty     = aux_ds_odd_dirty_hot_r[0];
    aux_tag_direct_tag       = dc3_dt_odd_tag_w0[`npuarc_DC_TAG_TAG_RANGE];
  end
  
  2'b01:
  begin
    // Odd, way1
    //
    aux_tag_direct_valid     = aux_ds_odd_valid_hot_r[1];  
    aux_tag_direct_lock      = aux_ds_odd_lock_hot_r[1]; 
    aux_tag_direct_dirty     = aux_ds_odd_dirty_hot_r[1];
    aux_tag_direct_tag       = dc3_dt_odd_tag_w1[`npuarc_DC_TAG_TAG_RANGE];
  end
  
  2'b10:
  begin
    // Even, way0
    //
    aux_tag_direct_valid     = aux_ds_even_valid_hot_r[0];  
    aux_tag_direct_lock      = aux_ds_even_lock_hot_r[0]; 
    aux_tag_direct_dirty     = aux_ds_even_dirty_hot_r[0];
    aux_tag_direct_tag       = dc3_dt_even_tag_w0[`npuarc_DC_TAG_TAG_RANGE];
  end
  
  default:
  begin
    // Even, way1
    //
    aux_tag_direct_valid     = aux_ds_even_valid_hot_r[1];  
    aux_tag_direct_lock      = aux_ds_even_lock_hot_r[1]; 
    aux_tag_direct_dirty     = aux_ds_even_dirty_hot_r[1];
    aux_tag_direct_tag       = dc3_dt_even_tag_w1[`npuarc_DC_TAG_TAG_RANGE];
  end
  endcase
end

//////////////////////////////////////////////////////////////////////////////
// 
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_dc_tag_PROC
  
  aux_dc_tag_cg0            =   aux_dc_tag_wen
                              | (aux_done & aux_dc_read);
  aux_dc_tag_index_nxt      = aux_lookup_addr_r[`npuarc_DC_IDX_RANGE];
  aux_dc_tag_bank_nxt       = aux_lookup_addr_r[`npuarc_DC_TAG_BANK_ID];
  aux_dc_tag_tag_nxt        = aux_lookup_addr_r[`npuarc_DC_TAG_RANGE];
  
  casez ({aux_dc_tag_wen, 
          aux_dc_read_direct, 
          aux_set_even_r, 
          aux_hit_way_hot_r})
  5'b1_?_?_??:
  begin
    // SR to DC_TAG
    //
    aux_dc_tag_valid_nxt = aux_sr_wdata[0];
    aux_dc_tag_lock_nxt  = aux_sr_wdata[1];
    aux_dc_tag_dirty_nxt = aux_sr_wdata[2];
    aux_dc_tag_tag_nxt   = {aux_dc_ptag_hi_r, aux_sr_wdata[`npuarc_ADDR_MSB:`npuarc_DC_TAG_LSB]};
  end
  
  5'b0_1_?_??:
  begin
    // Read direct
    //
    aux_dc_tag_valid_nxt = aux_tag_direct_valid;  
    aux_dc_tag_lock_nxt  = aux_tag_direct_lock; 
    aux_dc_tag_dirty_nxt = aux_tag_direct_dirty;
    aux_dc_tag_tag_nxt   = aux_tag_direct_tag;
  end
  
  5'b0_0_0_10:
  begin
    // Odd, way 1
    //
    aux_dc_tag_valid_nxt = aux_ds_odd_valid_hot_r[1];
    aux_dc_tag_lock_nxt  = aux_ds_odd_lock_hot_r[1];
    aux_dc_tag_dirty_nxt = aux_ds_odd_dirty_hot_r[1];
  end
  
  5'b0_0_0_01:
  begin
    // Odd, way 0
    //
    aux_dc_tag_valid_nxt = aux_ds_odd_valid_hot_r[0];
    aux_dc_tag_lock_nxt  = aux_ds_odd_lock_hot_r[0];
    aux_dc_tag_dirty_nxt = aux_ds_odd_dirty_hot_r[0];
  end
  
  5'b0_0_1_10:
  begin
    // Even, way 1
    //
    aux_dc_tag_valid_nxt = aux_ds_even_valid_hot_r[1];
    aux_dc_tag_lock_nxt  = aux_ds_even_lock_hot_r[1];
    aux_dc_tag_dirty_nxt = aux_ds_even_dirty_hot_r[1];
  end

  5'b0_0_1_01:
  begin
    // Even, way 0
    // 
    aux_dc_tag_valid_nxt = aux_ds_even_valid_hot_r[0];
    aux_dc_tag_lock_nxt  = aux_ds_even_lock_hot_r[0];
    aux_dc_tag_dirty_nxt = aux_ds_even_dirty_hot_r[0];
  end
  
  default: 
  begin
    // Line is not in the cache
    //
    aux_dc_tag_valid_nxt = 1'b0;
    aux_dc_tag_lock_nxt  = 1'b0;
    aux_dc_tag_dirty_nxt = 1'b0;
  end
  endcase
end

//////////////////////////////////////////////////////////////////////////////
// 
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_dc_data_PROC
  aux_dc_data_cg0            =   aux_dc_data_wen
                              | (aux_done & aux_dc_read);
  if (aux_dc_data_wen)
  begin
    aux_dc_data_nxt = aux_sr_wdata;
  end
  else
  begin
    aux_dc_data_nxt = dc_dd_data;
  end
end

//////////////////////////////////////////////////////////////////////////////
// Next value of the dc_ptag_hi register
//
//////////////////////////////////////////////////////////////////////////////
reg       aux_dc_ptag_hi_cg0;
reg [7:0] aux_dc_ptag_hi_nxt;
always @*
begin : aux_dc_ptag_hi_nxt_PROC
  // Clock gate
  //
  aux_dc_ptag_hi_cg0 =  aux_dc_ptag_hi_wen 
                      | (aux_done & aux_dc_read);
  
  // Default
  //
  aux_dc_ptag_hi_nxt = aux_dc_ptag_hi_r;
  
  if (aux_dc_ptag_hi_wen) 
  begin
    // SR to ptag
    //
    aux_dc_ptag_hi_nxt = aux_sr_wdata[7:0];
  end
  else
  begin
    // Read cache operation
    //
    aux_dc_ptag_hi_nxt = aux_dc_tag_tag_nxt[`npuarc_PADDR_MSB:`npuarc_ADDR_SIZE];
  end                    
end


//////////////////////////////////////////////////////////////////////////////
// AUX FSM
//
//////////////////////////////////////////////////////////////////////////////
parameter AUX_DEFAULT            = 4'b0000; 
parameter AUX_RESET              = 4'b0001; 
parameter AUX_DC_LOOKUP0         = 4'b0010; 
parameter AUX_DC_LOOKUP1         = 4'b0011; 
parameter AUX_DC_ANALYZE         = 4'b0100; 
parameter AUX_DC_ANALYZE_LINE    = 4'b0101;
parameter AUX_DC_LOCK_LINE       = 4'b1011;
parameter AUX_DC_CHECK_LINE      = 4'b0110;
parameter AUX_DC_CHECK_ALL       = 4'b0111;
parameter AUX_DC_ADVANCED_WRITE  = 4'b1000;
parameter AUX_DC_DT_ECC_SCRUB    = 4'b1001;
parameter AUX_DC_DD_ECC_SCRUB    = 4'b1010;
parameter AUX_RESET_WAIT         = 4'b1100;
parameter AUX_PRE_RESET          = 4'b1111; 

//////////////////////////////////////////////////////////////////////////////
// Handy
//
//////////////////////////////////////////////////////////////////////////////

assign aux_dc_ctrl_lm = aux_dc_ctrl_r[LM_BIT];

always @*
begin : aux_fsm_PROC
  
  // Tag memory
  //
  aux_req_dt_even              = 1'b0;      
  aux_req_dt_odd               = 1'b0;      
  aux_dt_way_hot               = 2'b00;     
  aux_dt_addr                  = aux_set_counter_r; 
  aux_dt_we                    = 1'b0;     
  aux_dt_wem                   = 3'b000;     
  aux_dt_valid                 = 1'b0;
  aux_dt_tag                   = aux_dc_tag_tag_r; 

  // Status memory
  //
  aux_req_ds                   = 1'b0;
  aux_ds_addr                  = aux_set_counter_r; 
  aux_ds_odd_sel               = 1'b0; 
  aux_ds_we                    = 1'b0;
  aux_ds_wem                   = 3'b110;
  aux_ds_lock                  = 1'b0;
  aux_ds_dirty                 = 1'b0;
  aux_ds_lru                   = 1'b0;
  aux_ds_way_hot               = 2'b00;
    
  // Data memory
  //
  aux_req_dd_even_lo           = 1'b0;                             
  aux_req_dd_even_hi           = 1'b0;                             
  aux_req_dd_odd_lo            = 1'b0;                             
  aux_req_dd_odd_hi            = 1'b0;
  aux_dd_set_incr              = 1'b0; 
  aux_dd_addr                  = aux_lookup_addr_r[`npuarc_DC_ADR_RANGE]; 
  aux_dd_way_hot               = { aux_lookup_addr_r[`npuarc_DC_WAY_CACHE_RANGE],
                                  ~aux_lookup_addr_r[`npuarc_DC_WAY_CACHE_RANGE]}; 
  aux_dd_we                    = 1'b0;                             
  aux_dd_din                   = { aux_dc_data_r, aux_dc_data_r,
                                   aux_dc_data_r, aux_dc_data_r }; 
  aux_dd_data_read             = 1'b0;
  aux_dd_direct_read           = aux_dc_read_direct & dmu_dc_idle;
  aux_dd_data_bank             = aux_lookup_addr_r[3:2];
  
  // Default values
  //
  aux_init_nxt                 = aux_init_r;      
  aux_busy                     = 1'b1;
  aux_cache_off                = aux_dc_ctrl_r[DC_BIT];
  aux_sg_off                   = aux_dc_ctrl_r[`DSG_RANGE];
  aux_done                     = 1'b0;
  aux_set_flush_pending        = 1'b0;
  
  aux_ecc_done_nxt             = 1'b0;

  ecc_dc_data_sbe_count_nxt     = ecc_dc_data_sbe_count_r;
  ecc_dc_data_sbe_count_set_cg0 = 1'b0;
  ecc_dc_data_sbe_count_clr_cg0 = dc_data_ecc_sbe_clr;
  
  ecc_dc_tag_sbe_count_nxt      = ecc_dc_tag_sbe_count_r;
  ecc_dc_tag_sbe_count_set_cg0  = 1'b0;
  ecc_dc_tag_sbe_count_clr_cg0  = dc_tag_ecc_sbe_clr;

  aux_ctrl_sb_cg0              =  aux_dc_ctrl_wen 
                                | aux_region_fail_r
                                | aux_ctrl_fs_r;
  
  aux_ctrl_sb_nxt              = aux_ctrl_sb_r;
  casez ({aux_dc_ctrl_wen, aux_region_fail_r, aux_sb_err})
  3'b1zz: aux_ctrl_sb_nxt      = aux_sr_wdata[SB_BIT];
  3'b01z: aux_ctrl_sb_nxt      = 1'b0;
  3'b001: aux_ctrl_sb_nxt      = 1'b0;
  default:aux_ctrl_sb_nxt      = aux_ctrl_sb_r;
  endcase
   
  aux_way_counter_cg0          = 1'b0;
  aux_way_counter_nxt          = aux_way_counter_r;

  aux_set_even_cg0             = 1'b0;
  aux_set_even_nxt             = aux_set_even_r;
     
  aux_set_counter_cg0          = 1'b0;
  aux_set_counter_nxt          = aux_set_counter_r;
  
  aux_info_valid_cg0           = 1'b0;
  aux_info_valid_nxt           = aux_info_valid_r;
  
  aux_hit_way_hot_cg0          = 1'b0;
  aux_hit_way_hot_nxt          = aux_hit_way_hot;
  
  aux_region_done_cg0          = 1'b0;
  aux_region_done_nxt          = aux_region_done_r;
  
  aux_lookup_incr              = 1'b0;
  
  // AUX interface to the MQ
  //
  aux_mq_write                 = 1'b0;
  aux_mq_flush                 = 1'b0;
  aux_mq_purge                 = 1'b0;
  aux_mq_refill                = 1'b0;

  aux_mq_way                   = 1'b0;   
  aux_mq_addr                  = {`npuarc_DC_LBUF_SIZE{1'b0}}; 
  aux_mq_lru_dirty             = 1'b0;
  
  
  aux_lock_flush_nxt           = aux_lock_flush_r;
  aux_lock_rf_nxt              = aux_lock_rf_r;
  aux_lock_sb_nxt              = aux_lock_sb_r;

  aux_x2_addr_pass             = 1'b0;
  aux_x2_addr                  = aux_lookup_addr_r[`npuarc_ADDR_RANGE];
  aux_x2_addr_hi               = aux_lookup_addr_r[`npuarc_PADDR_MSB:`npuarc_ADDR_SIZE];
   
   aux_dt_read                 = 1'b0;
  
  aux_state_nxt                = aux_state_r;

  case (aux_state_r)
  AUX_DEFAULT:
  begin
    // Before starting a cache instruction, wait until the DMU and the WQ 
    // are empty
    //
    aux_busy                = (| aux_dc_op_r);

    aux_dd_direct_read      = 1'b0;
    aux_way_counter_nxt     = 1'b0;
    aux_set_even_nxt        = 1'b1;
    aux_set_counter_nxt     = {`npuarc_DC_IDX_BITS{1'b0}};
  
    if (| aux_dc_op_r)
    begin
      // Cache operation
      //
      aux_ctrl_sb_cg0     = aux_dc_region_op;
      aux_ctrl_sb_nxt     = 1'b0;
      
      if (  wq_empty
          & (  dmu_empty
             | aux_ecc_scrub_in_progress_r
            ) 
          & dc_pipe_empty) 
      begin
        aux_way_counter_cg0 = 1'b1;
        aux_set_counter_cg0 = 1'b1;
        aux_set_even_cg0    = 1'b1;

        // Set FS bit to 1 in case there is any cache instruction that
        // may perform a flush to memory
        //
        aux_set_flush_pending =  (aux_dc_op_r[DC_IVDC])
                               | (aux_dc_op_r[DC_IVDL] & aux_dc_ctrl_r[IM_BIT])  
                               | (aux_dc_op_r[DC_LDL]  & aux_dc_ctrl_lm)  
                               | (aux_dc_op_r[DC_FLDR])
                               | (aux_dc_op_r[DC_IVDR])
                               | (aux_dc_op_r[DC_FLSH])                              
                               | (aux_dc_op_r[DC_FLDL])  
                               ;                            
        
        // What cache instruction?
        //
        case (1'b1)
        aux_dc_op_r[DC_RESET]:  
        begin
          aux_state_nxt = AUX_RESET;
          aux_init_nxt  = 1'b1;
        end  
        
        aux_dc_line_op,
        aux_dc_read:
        begin
          // Line based
          //
          aux_set_counter_nxt = aux_lookup_addr_r[`npuarc_DC_IDX_RANGE];
          aux_set_even_nxt    = ~aux_lookup_addr_r[`npuarc_DC_TAG_BANK_ID];
          aux_state_nxt       = AUX_DC_LOOKUP0;
        end
        
        aux_dc_wr_tag,
        aux_dc_wr_data:
        begin
          // Advanced cache instruction: DC_WR_TAG or DC_WR_DATA
          //
          aux_state_nxt       = AUX_DC_ADVANCED_WRITE;
        end
      
        aux_dc_dt_ecc_scrub:
        begin
          if (!aux_ecc_done_r)
          begin
            aux_state_nxt    = AUX_DC_DT_ECC_SCRUB;
          end   
        end

        aux_dc_dd_ecc_scrub:
        begin
          if (!aux_ecc_done_r)
          begin
            aux_state_nxt    = AUX_DC_DD_ECC_SCRUB;
          end  
        end

        default:
        begin
          // Full cache operation
          //
          aux_state_nxt = AUX_DC_LOOKUP0;
        end  
        endcase  
      end
    end 
  end
  
  AUX_DC_LOOKUP0:
  begin
    // Tag memories: read two sets at the time
    //
    aux_req_dt_even    = 1'b1;
    aux_req_dt_odd     = 1'b1; 
    aux_dt_way_hot     = 2'b11;               // both ways 
    aux_dt_addr        = aux_set_counter_r;   // set index
   
    // Status memories: read two sets at the time
    //
    aux_req_ds         = 1'b1;
    aux_ds_addr        = aux_set_counter_r; 
    aux_ds_odd_sel     = 1'b0; 
        
    // Data Memory
    //
    aux_req_dd_even_lo = aux_dc_read & dmu_dc_idle;
    aux_req_dd_even_hi = aux_dc_read & dmu_dc_idle;
    aux_req_dd_odd_lo  = aux_dc_read & dmu_dc_idle;
    aux_req_dd_odd_hi  = aux_dc_read & dmu_dc_idle;
    
    aux_info_valid_cg0 = 1'b1;
    aux_info_valid_nxt = 1'b0;

    if (dmu_dc_idle)
    begin
      aux_state_nxt    = AUX_DC_LOOKUP1; 
    end
  end
  
  AUX_DC_LOOKUP1:
  begin
    // One more cycle for the info from tag & status to be available
    //
    aux_info_valid_cg0      = 1'b1;
    aux_info_valid_nxt      = 1'b1;
    
    // Inform the EXU to update the x3_mem_addr
    //
    aux_x2_addr_pass        =    ~(aux_dc_op_r[DC_IVDC] | aux_dc_op_r[DC_FLSH])
                               & (~aux_info_valid_r);
    aux_x2_addr             = aux_lookup_addr_r[`npuarc_ADDR_RANGE];
  aux_x2_addr_hi            = aux_lookup_addr_r[`npuarc_PADDR_MSB:`npuarc_ADDR_SIZE];
    
    aux_dd_data_read        = aux_dc_read;
    
    if (aux_info_valid_r)
    begin
      aux_hit_way_hot_cg0  = 1'b1;
      aux_info_valid_nxt   = 1'b0;
      aux_lock_flush_nxt   = 1'b1;

      aux_dt_read          = 1'b1;
      case (1'b1)
      aux_dc_line_op,
      aux_dc_read:     aux_state_nxt = AUX_DC_ANALYZE_LINE;
      default:         aux_state_nxt = AUX_DC_ANALYZE;
      endcase 
    end   
  end
  
  AUX_DC_ANALYZE:
  begin
    //
    //
    if (|dc4_dt_ecc_db_error)
    begin
      // The Aux operation is not success
      //
      aux_ctrl_sb_cg0         = 1'b1;
      aux_ctrl_sb_nxt         = 1'b0;
 
      // Fake like we walked through all the cache
      //
      aux_init_nxt            = 1'b0;
      aux_done                = 1'b1;
      aux_ecc_done_nxt        = 1'b1;
      aux_state_nxt           = AUX_DEFAULT;
    end
    else if (|dc4_dt_ecc_sb_error)
    begin
      aux_state_nxt           = AUX_DC_DT_ECC_SCRUB;
    end  
    else
    begin
      
      casez ({aux_set_even_r, aux_way_counter_r})
      2'b1_0:
      begin
        // Set even, way0
        //
        aux_mq_flush          =  aux_ds_even_valid_hot_r[0]
                               & aux_ds_even_dirty_hot_r[0]
                               & (~(   aux_ds_even_lock_hot_r[0] 
                                    & aux_no_flush_lock));
        aux_mq_purge          =   aux_ds_even_valid_hot_r[0]
                                & aux_dc_op_r[DC_IVDC];
        aux_mq_write          = aux_mq_flush | aux_mq_purge;
        aux_mq_way            = 1'b0;   
        aux_mq_addr           = {dc3_dt_even_tag_w0,   aux_set_counter_r, 1'b0}; 
        aux_state_nxt         = AUX_DC_CHECK_ALL;
      end            

      2'b1_1:
      begin
        // Set even, way1
        //
        aux_mq_flush          =  aux_ds_even_valid_hot_r[1]
                               & aux_ds_even_dirty_hot_r[1]
                               & (~(   aux_ds_even_lock_hot_r[1] 
                                    & aux_no_flush_lock));
        aux_mq_purge          =  aux_ds_even_valid_hot_r[1]
                               & aux_dc_op_r[DC_IVDC];
        aux_mq_write          = aux_mq_flush | aux_mq_purge;
        aux_mq_way            = 1'b1;   
        aux_mq_addr           = {dc3_dt_even_tag_w1,   aux_set_counter_r, 1'b0}; 
        aux_state_nxt         = AUX_DC_CHECK_ALL;
      end

      2'b0_0:
      begin
        // Set odd, way0
        //
        aux_mq_flush          = aux_ds_odd_valid_hot_r[0]
                               & aux_ds_odd_dirty_hot_r[0]
                               & (~(   aux_ds_odd_lock_hot_r[0] 
                                    & aux_no_flush_lock));
        aux_mq_purge          =  aux_ds_odd_valid_hot_r[0]
                               & aux_dc_op_r[DC_IVDC];
        aux_mq_write          = aux_mq_flush | aux_mq_purge;
        aux_mq_way            = 1'b0;   
        aux_mq_addr           = {dc3_dt_odd_tag_w0,   aux_set_counter_r, 1'b1}; 
        aux_state_nxt         = AUX_DC_CHECK_ALL;
      end    

      2'b0_1:
      begin
        // Set odd, way1
        //
        aux_mq_flush          = aux_ds_odd_valid_hot_r[1]
                               & aux_ds_odd_dirty_hot_r[1]
                               & (~(   aux_ds_odd_lock_hot_r[1] 
                                    & aux_no_flush_lock));
        aux_mq_purge          =  aux_ds_odd_valid_hot_r[1]
                               & aux_dc_op_r[DC_IVDC];
        aux_mq_write          = aux_mq_flush | aux_mq_purge;
        aux_mq_way            = 1'b1;   
        aux_mq_addr           = {dc3_dt_odd_tag_w1,   aux_set_counter_r, 1'b1}; 
        aux_state_nxt         = AUX_DC_CHECK_ALL;
      end

      default:
        ;
      endcase      
    end
  end
  
  AUX_DC_CHECK_ALL:
  begin
    if (  (& aux_set_counter_r)
        & (~aux_set_even_r)
        & aux_way_counter_r
        & mq_empty)
    begin
      // Walked through entire cache
      //
      aux_done              = 1'b1;
      
      aux_state_nxt         = AUX_DEFAULT;
    end 
    else if (  ~aux_set_even_r
             & aux_way_counter_r
             & mq_empty
             & (~cb_full))
    begin
      // Odd & way1: Walked through  the entire (double) set
      //
      aux_way_counter_cg0 = 1'b1;
      aux_way_counter_nxt = ~aux_way_counter_r; 
      
      aux_set_even_cg0    = 1'b1;
      aux_set_even_nxt    = ~aux_set_even_r;
         
      aux_set_counter_cg0 = 1'b1;
      aux_set_counter_nxt = aux_set_counter_incr;
      
      aux_state_nxt       = AUX_DC_LOOKUP0;
    end
    else if (  mq_empty
             & (~cb_full))
    begin
      // Increments
      //
      aux_way_counter_cg0 = 1'b1;
      aux_way_counter_nxt = ~aux_way_counter_r;    
      
      aux_set_even_cg0    = aux_way_counter_r;
      aux_set_even_nxt    = ~aux_set_even_r;
      
      aux_state_nxt       = AUX_DC_ANALYZE;
    end                   
  
  end
  
  AUX_DC_ANALYZE_LINE:
  begin
    if (|dc4_dt_ecc_db_error)
    begin
      // The Aux operation is not success
      //
      aux_ctrl_sb_cg0       = 1'b1;
      aux_ctrl_sb_nxt       = 1'b0;

      // Fake like we walked through all the cache
      //
      aux_init_nxt          = 1'b0;
      aux_done              = 1'b1;
      aux_ecc_done_nxt      = 1'b1;
      aux_state_nxt         = AUX_DEFAULT;
    end
    else if (|dc4_dt_ecc_sb_error)      
    begin
      aux_state_nxt         = AUX_DC_DT_ECC_SCRUB;
    end 
    else if (|dc4_dd_ecc_sb_error)
    begin
      aux_state_nxt         = AUX_DC_DD_ECC_SCRUB;
    end
    else
    begin
// spyglass disable_block STARC05-2.8.1.3
// spyglass disable_block W398
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, code more readable, optimized by synthesizer.
      aux_region_done_cg0     = aux_dc_region_op;
      aux_region_done_nxt     = aux_region_last;

      aux_lock_rf_nxt         = 1'b0;
      aux_lock_sb_nxt         = aux_line_lock_op;

      casez ({aux_line_lock_op, aux_line_flush_op, aux_dc_read})
      3'b1??:
      begin
        // Line locking operation
        //
        casez ({aux_lock_hit, 
                aux_lock_dirty, 
                aux_dc_ctrl_lm,
                aux_all_locked_r})
        4'b0??0:
        begin
          // Cache miss, not all the ways locked. Refill the line.
          //
          aux_mq_write        =  1'b1;
          aux_mq_addr         = {aux_lookup_addr_r[`npuarc_DC_TAG_RANGE], 
                                 aux_lookup_addr_r[`npuarc_DC_IDX_RANGE],     
                                 aux_lookup_addr_r[`npuarc_DC_TAG_BANK_ID]};  
          // Refill and lock the way0
          //
          aux_mq_refill       = 1'b1;
          aux_mq_way          = 1'b0;
          aux_mq_lru_dirty    = aux_way0_dirty;
          
          aux_state_nxt       = AUX_DC_CHECK_LINE;
        end

        4'b0??1:
        begin
          // Cache miss, way0 is already locked. Failure 
          //
          aux_lock_sb_nxt     = 1'b0;
          aux_state_nxt       = AUX_DC_CHECK_LINE;
        end

        4'b10??:
        begin
          // Cache hit, clean line. Need to refetch the line
          //
          if (aux_hit_way_hot_r[0])
          begin
            // Line hit in way0.  Refetch and lock the line
            //
            aux_mq_write        = 1'b1;
            aux_mq_refill       = 1'b1;
            aux_mq_way          = 1'b0;
            aux_mq_addr         = {aux_lookup_addr_r[`npuarc_DC_TAG_RANGE], 
                                   aux_lookup_addr_r[`npuarc_DC_IDX_RANGE],     
                                   aux_lookup_addr_r[`npuarc_DC_TAG_BANK_ID]};  
            aux_mq_refill       = 1'b1;
            aux_state_nxt       = AUX_DC_CHECK_LINE;
          end
          else
          begin
            // Line hit in way1.  Remove the line from the cache and recycle
            //
            aux_mq_write        =  1'b1;
            aux_mq_addr         = {aux_lookup_addr_r[`npuarc_DC_TAG_RANGE], 
                                   aux_lookup_addr_r[`npuarc_DC_IDX_RANGE],     
                                   aux_lookup_addr_r[`npuarc_DC_TAG_BANK_ID]};  
            aux_mq_way          = 1'b1;
            aux_mq_purge        = 1'b1;
            
            aux_state_nxt       = AUX_DEFAULT;
          end
        end

        4'b111?:
        begin
          // Cache hit, dirty line. LM bit is set: flush/purge the line and 
          // recycle
          //
          aux_mq_write        = 1'b1;
          aux_mq_flush        = 1'b1;
          aux_mq_purge        = 1'b1;
          aux_mq_way          = aux_hit_way_hot_r[1];
          aux_mq_addr         = {aux_lookup_addr_r[`npuarc_DC_TAG_RANGE], 
                                 aux_lookup_addr_r[`npuarc_DC_IDX_RANGE],     
                                 aux_lookup_addr_r[`npuarc_DC_TAG_BANK_ID]};  
          aux_state_nxt       = AUX_DEFAULT;
        end

        4'b110?:
        begin
          // Cache hit, dirty line. LM bit is not set. 
          //
          if (aux_hit_way_hot_r[0])
          begin
            // Line hit in way0.  Just lock the line
            //
            aux_state_nxt       = AUX_DC_LOCK_LINE;
          end
          else
          begin
            // Line hit in way1. Remove the line from the cache and recycle
            //
            aux_mq_write        =  1'b1;
            aux_mq_addr         = {aux_lookup_addr_r[`npuarc_DC_TAG_RANGE], 
                                   aux_lookup_addr_r[`npuarc_DC_IDX_RANGE],     
                                   aux_lookup_addr_r[`npuarc_DC_TAG_BANK_ID]};  
            aux_mq_way          = 1'b1;
            aux_mq_flush        = 1'b1;
            aux_mq_purge        = 1'b1;
            
            aux_state_nxt       = AUX_DEFAULT;
          end  
        end

        default:
          ;
        endcase
      end

      3'b?1?:
      begin
        // Line flushing op (flush)
        //
        // Conditions to write to the MQ: 
        // line is dirty  and not locked {Modified/Owned} (1)
        //
        aux_mq_write  =  aux_flush_line             // (1)
                       ;
        aux_mq_addr   = {aux_lookup_addr_r[`npuarc_DC_TAG_RANGE], 
                         aux_lookup_addr_r[`npuarc_DC_IDX_RANGE],     
                         aux_lookup_addr_r[`npuarc_DC_TAG_BANK_ID]};  
        aux_mq_flush  = aux_flush_line;
        aux_mq_way    = aux_hit_way_hot_r[1];
        
        aux_state_nxt = AUX_DC_CHECK_LINE;
      end

      3'b??1:
      begin
        // Advanced read. Go to AUX_DC_CHECK_LINE just to set the SB bit
        //
        aux_state_nxt = AUX_DC_CHECK_LINE;
      end
// spyglass enable_block W398
// spyglass enable_block STARC05-2.8.1.3
      default:
      begin
        // Line invalidation op (purge)
        // Conditions to write to the MQ: 
        // line is in the cache (1)
        //
        aux_mq_write  =  aux_line_hit                            // (1)
                       ;
        aux_mq_addr   = {aux_lookup_addr_r[`npuarc_DC_TAG_RANGE], 
                         aux_lookup_addr_r[`npuarc_DC_IDX_RANGE],     
                         aux_lookup_addr_r[`npuarc_DC_TAG_BANK_ID]};  
        aux_mq_flush  = aux_line_dirty & aux_dc_ctrl_r[IM_BIT];
        aux_mq_purge  = aux_line_hit;
        aux_mq_way    = aux_hit_way_hot_r[1];
        
       
        aux_state_nxt = AUX_DC_CHECK_LINE;
      end
      endcase  
    end
  end 
  
  AUX_DC_LOCK_LINE:
  begin
    aux_req_ds         = 1'b1;
    aux_ds_addr        = aux_lookup_addr_r[`npuarc_DC_IDX_RANGE];
    aux_ds_odd_sel     = aux_lookup_addr_r[`npuarc_DC_TAG_BANK_ID];
    aux_ds_we          = 1'b1;
    aux_ds_wem         = {3'b100}; // lock, dirty, lru
    aux_ds_lock        = 1'b1;
    aux_ds_way_hot     = 2'b01;    // only way0 can be locked
    
    aux_state_nxt      = AUX_DC_CHECK_LINE;
  end
  
  AUX_DC_CHECK_LINE:
  begin
    aux_lock_sb_nxt   = lb_err_r ? 1'b0 : aux_lock_sb_r;
   
    casez ({aux_dc_region_op, aux_region_done_r, mq_empty, cb_full})
    4'b10_10:
    begin
      // Region based. 
      //
      aux_set_even_cg0    = 1'b1;
      aux_set_counter_cg0 = ~aux_set_even_r;
      
      aux_ctrl_sb_cg0     = ~aux_ctrl_sb_r;
      aux_ctrl_sb_nxt     = aux_line_hit;
      
      aux_set_even_nxt    = ~aux_set_even_r;
      aux_set_counter_nxt = aux_set_counter_incr;
      aux_lookup_incr     = 1'b1;
      aux_state_nxt       = AUX_DC_LOOKUP0;
    end
    
    4'b11_1?:
    begin
      // Region Done
      //
      aux_region_done_cg0   = 1'b1;                
      aux_region_done_nxt   = 1'b0;                
      
      // Success bit
      //
      aux_ctrl_sb_cg0       = ~aux_ctrl_sb_r;      
      aux_ctrl_sb_nxt       = | aux_hit_way_hot_r; 
      
      aux_done              = 1'b1;
      aux_state_nxt         = AUX_DEFAULT;
    end
    
    4'b0?_1?:
    begin
      // Success bit
      //
      aux_ctrl_sb_cg0       =   aux_dc_line_op
                              | aux_dc_read_lookup;
      
      aux_ctrl_sb_nxt       =   (aux_dc_op_r[DC_LDL]  & aux_lock_sb_r)
                              | (aux_dc_op_r[DC_IVDL] & aux_line_hit)
                              | (aux_dc_op_r[DC_FLDL] & aux_line_hit)
                              | (aux_dc_region_op     & aux_line_hit)
                              | (aux_dc_read_lookup   & aux_line_hit);

      aux_done              = 1'b1;
      aux_state_nxt         = AUX_DEFAULT;
    end
    
    default:
      ;
    endcase
  end

// spyglass enable_block W193
  
  AUX_DC_ADVANCED_WRITE:
  begin
    // Tag 
    //
    aux_req_dt_even    =    aux_dc_op_r[DC_WR_TAG]
                         & (~aux_lookup_addr_r[`npuarc_DC_TAG_BANK_ID]);
    aux_req_dt_odd     =   aux_dc_op_r[DC_WR_TAG]
                         & aux_lookup_addr_r[`npuarc_DC_TAG_BANK_ID];
    aux_dt_way_hot     = { aux_lookup_addr_r[`npuarc_DC_WAY_CACHE_RANGE],
                          ~aux_lookup_addr_r[`npuarc_DC_WAY_CACHE_RANGE]};
    aux_dt_addr        = aux_lookup_addr_r[`npuarc_DC_IDX_RANGE];
    aux_dt_we          = 1'b1;
    aux_dt_wem         = 3'b011;  // e,v,tag
    aux_dt_valid       = aux_dc_tag_valid_r;
    aux_dt_tag         = aux_dc_tag_tag_r;
    
    // Lock & Dirty
    //
    aux_req_ds         = aux_dc_op_r[DC_WR_TAG];
    aux_ds_addr        = aux_lookup_addr_r[`npuarc_DC_IDX_RANGE];
    aux_ds_odd_sel     = aux_lookup_addr_r[`npuarc_DC_TAG_BANK_ID];
    aux_ds_we          = 1'b1;
    aux_ds_lock        = aux_dc_tag_lock_r;
    aux_ds_dirty       = aux_dc_tag_dirty_r;
    aux_ds_way_hot     = { aux_lookup_addr_r[`npuarc_DC_WAY_CACHE_RANGE],
                          ~aux_lookup_addr_r[`npuarc_DC_WAY_CACHE_RANGE]};
    
    // Data Memory
    //
    aux_req_dd_even_lo =   aux_dc_op_r[DC_WR_DATA]
                         & (aux_lookup_addr_r[3:2] == 2'b00);                             
    aux_req_dd_even_hi = aux_dc_op_r[DC_WR_DATA]
                         & (aux_lookup_addr_r[3:2] == 2'b01);                             
    aux_req_dd_odd_lo  = aux_dc_op_r[DC_WR_DATA]
                         & (aux_lookup_addr_r[3:2] == 2'b10);                             
    aux_req_dd_odd_hi  = aux_dc_op_r[DC_WR_DATA]
                         & (aux_lookup_addr_r[3:2] == 2'b11);                             
    aux_dd_we          = 1'b1;                             
  
    aux_done           = 1'b1;
    aux_state_nxt      = AUX_DEFAULT;
  end
 
  AUX_DC_DT_ECC_SCRUB:
  begin
    // Tag memories
    //
    aux_req_dt_even    = aux_ecc_data_mem_valid_r[0];
    aux_req_dt_odd     = aux_ecc_data_mem_valid_r[1];
    aux_dt_way_hot     = aux_ecc_dt_way_hot_r;
    aux_dt_addr        =   ((aux_dc_op_r == 13'h0800) | (aux_dc_op_r == 13'h1800))
                         ? aux_ecc_addr_r[`npuarc_DC_IDX_RANGE]  
                         : aux_set_counter_r
                         ;
    aux_dt_we          = 1'b1;
    aux_dt_wem         = 3'b011;
    aux_dt_valid       = aux_ecc_tag_r[`npuarc_DC_TAG_VALID_BIT];
    aux_dt_tag         = aux_ecc_tag_r[`npuarc_DC_TAG_TAG_RANGE];
    
    aux_ecc_done_nxt   = 1'b1;
    aux_state_nxt      =   ((aux_dc_op_r == 13'h0800) | (aux_dc_op_r == 13'h1800))
                         ? AUX_DEFAULT   
                         : AUX_DC_LOOKUP0
                         ;
 
    ecc_dc_tag_sbe_count_set_cg0 = ~ecc_dc_tag_sbe_count_clr_cg0
                                  & (ecc_dc_tag_sbe_count_r != 4'b1111);
    ecc_dc_tag_sbe_count_nxt     = ecc_dc_tag_sbe_count_r + 1'b1;    

  end
  
  AUX_DC_DD_ECC_SCRUB: 
  begin
    // Data Memory
    //
    aux_dd_addr        = (aux_dc_op_r == 13'h0100) ? aux_lookup_addr_r[`npuarc_DC_ADR_RANGE] : aux_ecc_addr_r[`npuarc_DC_ADR_RANGE];
    aux_dd_way_hot     = aux_ecc_dt_way_hot_r;
    aux_req_dd_even_lo = aux_ecc_data_mem_valid_r[0];
    aux_req_dd_even_hi = aux_ecc_data_mem_valid_r[1];
    aux_req_dd_odd_lo  = aux_ecc_data_mem_valid_r[2];
    aux_req_dd_odd_hi  = aux_ecc_data_mem_valid_r[3];
    aux_dd_din         = { dc4_ecc_data_odd_hi, dc4_ecc_data_odd_lo,
                           dc4_ecc_data_even_hi, dc4_ecc_data_even_lo }; 
    aux_dd_we          = 1'b1;                             

    aux_ecc_done_nxt   = 1'b1;

    aux_state_nxt      = (aux_dc_op_r == 13'h0100) 
                       ? aux_ecc_done_r ? AUX_DC_LOOKUP0 : AUX_DC_DD_ECC_SCRUB 
                       : AUX_DEFAULT;

    ecc_dc_data_sbe_count_set_cg0 = ~ecc_dc_data_sbe_count_clr_cg0
                                  & (~aux_ecc_done_r)    
                                  & (ecc_dc_data_sbe_count_r != 4'b1111);
// spyglass disable_block W164a
// SMD: LHS width < RHS in assignment
// SJ:  correct width will be used

    ecc_dc_data_sbe_count_nxt     = ecc_dc_data_sbe_count_r 
                                  + {1{aux_ecc_data_mem_valid_r[0]}}
                                  + {1{aux_ecc_data_mem_valid_r[1]}}
                                  + {1{aux_ecc_data_mem_valid_r[2]}}
                                  + {1{aux_ecc_data_mem_valid_r[3]}};
// spyglass enable_block W164a
  end
  
  AUX_PRE_RESET:
  begin
    // We only come here after a reset. Do not reset/invalidate the data
    // cache when dbg_cache_rst_disable_r is asserted
    //
    if (dbg_cache_rst_disable_r)
    begin
      aux_init_nxt  = 1'b0;
      aux_state_nxt = AUX_DEFAULT;
    end
    else
    begin
      aux_state_nxt = AUX_RESET;
    end
  end

  AUX_RESET:
  begin
    // Tag memories 
    //
    aux_req_dt_even     = aux_set_even_r;    // 1'b1;      
    aux_req_dt_odd      = ~aux_set_even_r;   // 1'b1;          
    aux_dt_way_hot      = 2'b11;             // both ways
    aux_dt_addr         = aux_set_counter_r; // set index
    aux_dt_we           = 1'b1;              // write
    aux_dt_wem          = 3'b111;            // e, v, tag
    aux_dt_valid        = 1'b0;
    aux_dt_tag          = {`npuarc_DC_TAG_BITS{1'b0}};
    
    // Dirty, lock and LRU flops
    //
    aux_req_ds          = 1'b1;
    aux_ds_addr         = aux_set_counter_r; 
    aux_ds_odd_sel      = ~aux_set_even_r; 
    aux_ds_we           = 1'b1;
    aux_ds_wem          = 3'b111;
    aux_ds_lock         = 1'b0;
    aux_ds_dirty        = 1'b0;
    aux_ds_lru          = 1'b0;
    aux_ds_way_hot      = 2'b11;
   

    // Request data data
    //
    aux_req_dd_even_lo  = dmu_dc_idle;
    aux_req_dd_even_hi  = dmu_dc_idle;
    aux_req_dd_odd_lo   = dmu_dc_idle;
    aux_req_dd_odd_hi   = dmu_dc_idle;

    aux_dd_addr         = aux_dd_set_addr_r;
    aux_dd_way_hot      = 2'b11; 
    aux_dd_we           = 1'b1;
    aux_dd_din          = 128'd0;

    // Increments
    //
    aux_set_counter_cg0 = ~aux_set_even_r;
    aux_set_counter_nxt = aux_set_counter_incr;
    
    aux_set_even_cg0    = 1'b1;
    aux_set_even_nxt    = ~aux_set_even_r;



    // Go to AUX_RESET_WAIT, because data data is accessed every other cycle
    //
    aux_state_nxt = AUX_RESET_WAIT;  


    if (  (& aux_set_counter_r)
        & (~aux_set_even_r))
    begin
      // Walked through all the cache
      //
      //
      // Make sure that the data data is also completed
      if (&aux_dd_set_addr_r)
      begin
        aux_init_nxt  = 1'b0;
        aux_done      = aux_dc_op_r[DC_RESET];
        aux_state_nxt = AUX_DEFAULT;
      end
      else
      begin
        aux_req_dt_even     = 1'b0;
        aux_req_dt_odd      = 1'b0;
        aux_set_counter_cg0 = 1'b0;
        aux_set_even_cg0    = 1'b0;
      end      
    end
  end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept  
  AUX_RESET_WAIT:
  begin
    // Request data data
    //
    if (dmu_dc_idle)
    begin
      //
      // Increment the sets

      aux_dd_set_incr = 1'b1;  
      aux_state_nxt   = AUX_RESET;  
    end
  end
  default:;
// spyglass enable_block W193
  endcase
end

//////////////////////////////////////////////////////////////////////////////
//Asynchronous process defining hit information 
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_hit_even_PROC
  aux_hit_even_way_hot    = dc3_dt_even_hit_way_hot;
  aux_flush_even_way_hot  = dc3_dt_even_hit_way_hot & dc3_ds_even_dirty_hot;
  aux_lock_even_way_hot   = dc3_ds_even_lock_hot;
end

always @*
begin : aux_hit_odd_PROC
  aux_hit_odd_way_hot    = dc3_dt_odd_hit_way_hot;
  aux_flush_odd_way_hot  = dc3_dt_odd_hit_way_hot & dc3_ds_odd_dirty_hot;
  aux_lock_odd_way_hot   = dc3_ds_odd_lock_hot;
end

always @*
begin : aux_hit_even_odd_way_select_PROC
  casez (aux_set_even_r)
  1'b1:   
  begin
    // Even
    //
    aux_hit_way_hot   = aux_hit_even_way_hot;
    aux_flush_way_hot = aux_flush_even_way_hot;
    aux_lock_way_hot  = aux_lock_even_way_hot;
    aux_all_locked    = (dc3_ds_even_lock_hot[0]);
    aux_way0_dirty    =   aux_ds_even_valid_hot_r[0]
                        & aux_ds_even_dirty_hot_r[0];                      
  end
  
  default:
  begin
    // Odd
    //
    aux_hit_way_hot   = aux_hit_odd_way_hot;
    aux_flush_way_hot = aux_flush_odd_way_hot;
    aux_lock_way_hot  = aux_lock_odd_way_hot;
    aux_all_locked    = (dc3_ds_odd_lock_hot[0]);
    aux_way0_dirty    =   aux_ds_odd_valid_hot_r[0]
                        & aux_ds_odd_dirty_hot_r[0];                      
  end
  endcase
end

//////////////////////////////////////////////////////////////////////////////
// Asynchronous process: handy variables (captured)
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_line_status_PROC
  aux_line_hit               = | aux_hit_way_hot_r;
  aux_line_dirty             = | aux_flush_way_hot_r;
  aux_line_locked            = | aux_lock_way_hot_r;
end

//////////////////////////////////////////////////////////////////////////////
// Aysynchronous process. Flushing a locked line 
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_lock_PROC
  aux_no_flush_lock = (  aux_dc_op_r[DC_FLDL] 
                       | aux_dc_op_r[DC_FLDR] 
                       | aux_dc_op_r[DC_FLSH])
                      & (~aux_dc_ctrl_lm);  


  aux_lock_hit       = aux_line_hit;
  aux_lock_dirty     = aux_line_dirty;
end

//////////////////////////////////////////////////////////////////////////////
// Aysynchronous process. Flush a cache line when valid & dirty
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_flush_line_PROC
  // Locked lines are flushed only when the LM bit is set
  //
  aux_flush_line =   aux_line_dirty 
                  & (~(aux_line_locked & (~aux_dc_ctrl_lm)));
end

//////////////////////////////////////////////////////////////////////////////
// Synchronous processes
//
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : aux_state_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_state_r <= AUX_PRE_RESET;
    aux_init_r  <= 1'b1;
  end
  else
  begin
    aux_state_r <= aux_state_nxt;
    aux_init_r  <= aux_init_nxt;
  end
end

always @*
begin : aux_dc_op_nxt_PROC
  aux_dc_op_nxt = aux_dc_op_r;
  begin
    if (aux_dc_op_cg0)
    begin
      aux_dc_op_nxt[DC_RESET]        = aux_dc_ivdc_wen & (~aux_dc_ctrl_r[IM_BIT]);
      aux_dc_op_nxt[DC_IVDC]         = aux_dc_ivdc_wen & aux_dc_ctrl_r[IM_BIT];
      aux_dc_op_nxt[DC_FLSH]         = aux_dc_flsh_wen;
      aux_dc_op_nxt[DC_IVDL]         = aux_dc_ivdl_wen;
      aux_dc_op_nxt[DC_LDL]          = aux_dc_ldl_wen;
      aux_dc_op_nxt[DC_FLDL]         = aux_dc_fldl_wen;
      aux_dc_op_nxt[DC_FLDR]         = aux_dc_start_region_wen 
                                    & aux_region_ctrl_flush
                                    & (~aux_region_bad);
      aux_dc_op_nxt[DC_IVDR]         =  aux_dc_start_region_wen 
                                    & aux_region_ctrl_inv
                                    & (~aux_region_bad);
      aux_dc_op_nxt[DC_READ]         = aux_dc_ram_addr_wen;
      aux_dc_op_nxt[DC_WR_TAG]       = aux_dc_tag_wen;
      aux_dc_op_nxt[DC_WR_DATA]      = aux_dc_data_wen;
      aux_dc_op_nxt[DC_DT_ECC_SCRUB] = 1'b0;
      aux_dc_op_nxt[DC_DD_ECC_SCRUB] = 1'b0;
    end
    else if (aux_done)
    begin
      aux_dc_op_nxt                = {DC_BITS{1'b0}};
    end
    else if (aux_dc_ecc_op_cg0)  
    begin
      aux_dc_op_nxt[DC_DT_ECC_SCRUB] = aux_dc_dt_scrub_start_r;
      aux_dc_op_nxt[DC_DD_ECC_SCRUB] = aux_dc_dd_scrub_start_r;
    end
    else if (aux_ecc_done_r)
    begin
      aux_dc_op_nxt[DC_DT_ECC_SCRUB] = 1'b0;
      aux_dc_op_nxt[DC_DD_ECC_SCRUB] = 1'b0;
    end
  end
end
always @(posedge clk or posedge rst_a)
begin : aux_dc_op_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_dc_op_r              <= {DC_BITS{1'b0}};
  end
  else
  begin
    aux_dc_op_r              <= aux_dc_op_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin : aux_ctrl_fs_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_ctrl_fs_r <= 1'b0;
  end
  else
  begin
    aux_ctrl_fs_r <= aux_ctrl_fs_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin : aux_ec_done_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_ecc_done_r       <= 1'b0;
  end
  else
  begin
    aux_ecc_done_r       <= aux_ecc_done_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin: aux_region_fail_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_region_fail_r <= 1'b0;
  end
  else if (aux_region_fail_cg0)
  begin
    aux_region_fail_r <= aux_region_fail_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin : aux_dc_ctrl_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_dc_ctrl_r <= {3'b000, 1'b0, 8'hc8};
  end
  else
  begin
    aux_dc_ctrl_r <= aux_dc_ctrl_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin : aux_ctrl_sb_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_ctrl_sb_r   <= 1'b0;
  end
  else if (aux_ctrl_sb_cg0)
  begin
    aux_ctrl_sb_r <= aux_ctrl_sb_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin : aux_lookup_addr_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_lookup_addr_r <= {`npuarc_PADDR_SIZE{1'b0}};
  end
  else if (aux_lookup_addr_cg0)   
  begin                  
    aux_lookup_addr_r <= aux_lookup_addr_nxt;  
  end                                         
end

always @(posedge clk or posedge rst_a)
begin : aux_dc_ram_addr_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_dc_ram_addr_r   <= {`npuarc_PADDR_SIZE{1'b0}};
  end
  else if (aux_dc_ram_addr_cg0)                     
  begin                                        
      aux_dc_ram_addr_r <= {aux_dc_ptag_hi_r, aux_sr_wdata}; 
  end                                         
end

always @(posedge clk or posedge rst_a)
begin : aux_region_done_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_region_done_r <= 1'b0;
  end
  else if (aux_region_done_cg0)
  begin
    aux_region_done_r <= aux_region_done_nxt;
  end
end

// leda TEST_975 off
// LMD: Latch enabled by a clock affects data input of flipflops clocked by the trailing edge of the same clock
// LJ:
always @(posedge clk or posedge rst_a)
begin : aux_dc_tag_status_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_dc_tag_valid_r        <= 1'b0;
    aux_dc_tag_lock_r         <= 1'b0;
    aux_dc_tag_dirty_r        <= 1'b0;
    aux_dc_tag_index_r        <= {`npuarc_DC_IDX_BITS{1'b0}};
    aux_dc_tag_bank_r         <= 1'b0;
    aux_dc_tag_tag_r          <= {`npuarc_DC_TAG_BITS{1'b0}};
  end
  else if (aux_dc_tag_cg0)
  begin
    aux_dc_tag_valid_r      <= aux_dc_tag_valid_nxt;
    aux_dc_tag_lock_r       <= aux_dc_tag_lock_nxt;
    aux_dc_tag_dirty_r      <= aux_dc_tag_dirty_nxt;
    aux_dc_tag_index_r      <= aux_dc_tag_index_nxt;
    aux_dc_tag_bank_r       <= aux_dc_tag_bank_nxt;
    aux_dc_tag_tag_r        <= aux_dc_tag_tag_nxt;  
  end
end
// leda TEST_975 on


always @(posedge clk or posedge rst_a)
begin : aux_set_counter_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_set_counter_r <= {`npuarc_DC_IDX_BITS{1'b0}};
  end
  else if (aux_set_counter_cg0)
  begin
    aux_set_counter_r <= aux_set_counter_nxt;
  end
end


always @(posedge clk or posedge rst_a)
begin : aux_way_counter_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_way_counter_r <= 1'b0;
  end
  else if (aux_way_counter_cg0)
  begin
    aux_way_counter_r <= aux_way_counter_nxt;
  end  
end
  
always @(posedge clk or posedge rst_a)
begin : aux_set_even_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_set_even_r <= 1'b1;
  end
  else if (aux_set_even_cg0)
  begin
    aux_set_even_r <= aux_set_even_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin : aux_info_valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_info_valid_r <= 1'b0;
  end
  else if (aux_info_valid_cg0)
  begin
    aux_info_valid_r <= aux_info_valid_nxt;
  end
end

// leda TEST_975 off
// LMD: Latch enabled by a clock affects data input of flipflops clocked by the trailing edge of the same clock
// LJ:
always @(posedge clk or posedge rst_a)
begin : aux_way_hot_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_flush_way_hot_r <= {`npuarc_DC_WAYS{1'b0}};
    aux_lock_way_hot_r  <= {`npuarc_DC_WAYS{1'b0}};
    aux_all_locked_r    <= 1'b0;
  end
  else if (aux_info_valid_cg0)
  begin
    aux_flush_way_hot_r <= aux_flush_way_hot;
    aux_lock_way_hot_r  <= aux_lock_way_hot;
    aux_all_locked_r    <= aux_all_locked;
  end
end

always @(posedge clk or posedge rst_a)
begin : aux_hit_way_hot_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_hit_way_hot_r   <= {`npuarc_DC_WAYS{1'b0}};
  end
  else if (aux_hit_way_hot_cg0)
  begin
    aux_hit_way_hot_r   <= aux_hit_way_hot_nxt;
  end
end
// leda TEST_975 on
 
always @(posedge clk or posedge rst_a)
begin : aux_lock_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_lock_flush_r <= 1'b0;
    aux_lock_rf_r    <= 1'b0;
    aux_lock_sb_r    <= 1'b0;
  end
  else
  begin
    aux_lock_flush_r <= aux_lock_flush_nxt;
    aux_lock_rf_r    <= aux_lock_rf_nxt;
    aux_lock_sb_r    <= aux_lock_sb_nxt;
  end  
end

// leda TEST_975 off
// LMD: Latch enabled by a clock affects data input of flipflops clocked by the trailing edge of the same clock
// LJ:
//
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
//  
always @(posedge clk or posedge rst_a)
begin : aux_ds_hot_reg_PROC  
  if (rst_a == 1'b1)
  begin
    aux_ds_even_valid_hot_r <= 2'b00;
    aux_ds_even_dirty_hot_r <= 2'b00;
    aux_ds_even_lock_hot_r  <= 2'b00;
    
    aux_ds_odd_valid_hot_r  <= 2'b00;
    aux_ds_odd_dirty_hot_r  <= 2'b00;
    aux_ds_odd_lock_hot_r   <= 2'b00;
  end
  else if (aux_info_valid_r)
  begin
    aux_ds_even_valid_hot_r <= dc3_dt_even_valid_hot;
    aux_ds_even_dirty_hot_r <= dc3_ds_even_dirty_hot;
    aux_ds_even_lock_hot_r  <= dc3_ds_even_lock_hot;
    
    aux_ds_odd_valid_hot_r  <= dc3_dt_odd_valid_hot;
    aux_ds_odd_dirty_hot_r  <= dc3_ds_odd_dirty_hot;
    aux_ds_odd_lock_hot_r   <= dc3_ds_odd_lock_hot;
  end
end



always @*
begin : aux_ds_hot_reg_ecc_nxt_PROC  
  aux_dt_ecc_sb_error_nxt = aux_dt_ecc_sb_error_r;
  if (|dc4_dt_ecc_sb_error)
  begin
    aux_dt_ecc_sb_error_nxt  = (|dc4_dt_ecc_sb_error);
  end
  else if (  aux_done
           | aux_ecc_done_nxt // scrubbing is done
          )  
  begin
    aux_dt_ecc_sb_error_nxt  = 1'b0;
  end
end
always @(posedge clk or posedge rst_a)
begin : aux_ds_hot_reg_ecc_PROC  
  if (rst_a == 1'b1)
  begin
    aux_dt_ecc_sb_error_r   <= 1'b0; 
  end
  else
  begin
    aux_dt_ecc_sb_error_r   <= aux_dt_ecc_sb_error_nxt;
  end
end


// leda NTL_CON32 on
// leda TEST_975 on


always @(posedge clk or posedge rst_a)
begin : aux_dc_flush_end_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_dc_flush_end_r    <= {`npuarc_PADDR_SIZE{1'b0}};
  end
  else if (aux_dc_fler_cg0)
  begin
    aux_dc_flush_end_r  <= {aux_dc_ptag_hi_r, aux_sr_wdata};
  end
end

always @(posedge clk or posedge rst_a)
begin : aux_dc_ptag_hi_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_dc_ptag_hi_r <= {8{1'b0}};
  end
  else if (aux_dc_ptag_hi_cg0 == 1'b1)
  begin
    aux_dc_ptag_hi_r <= aux_dc_ptag_hi_nxt;
  end
end

// leda NTL_RST03 off
// leda S_1C_R off
// LMD: A flipflop without reset
// LJ:  Data path signals that dont require a reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk)
begin : aux_dc_data_reg_PROC
  if (aux_dc_data_cg0 == 1'b1)
  begin
    aux_dc_data_r        <= aux_dc_data_nxt;
  end
end
// leda S_1C_R on
// leda NTL_RST03 on
// leda W175 on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

always @*
begin : ecc_dc_tag_sbe_count_comb_PROC
  ecc_dc_tag_sbe_count_next    = ecc_dc_tag_sbe_count_r;
  if (ecc_dc_tag_sbe_count_set_cg0 == 1'b1)
  begin
    ecc_dc_tag_sbe_count_next  = ecc_dc_tag_sbe_count_nxt;
  end
  else if (ecc_dc_tag_sbe_count_clr_cg0 == 1'b1)
  begin
    ecc_dc_tag_sbe_count_next  = 4'b0000;
  end
end

always @*
begin : ecc_dc_data_sbe_count_comb_PROC
  ecc_dc_data_sbe_count_next = ecc_dc_data_sbe_count_r;
  if (ecc_dc_data_sbe_count_set_cg0 == 1'b1)
  begin
    ecc_dc_data_sbe_count_next = ((ecc_dc_data_sbe_count_r[3:2] == 2'b11) && (ecc_dc_data_sbe_count_nxt[3:2] == 2'b00)) 
                                ? 4'b1111 
                                : ecc_dc_data_sbe_count_nxt;
  end
  else if (ecc_dc_data_sbe_count_clr_cg0 == 1'b1)
  begin
    ecc_dc_data_sbe_count_next = 4'b0000;
  end
end
always @(posedge clk or posedge rst_a)
begin : ecc_dc_tag_sbe_count_reg_PROC
  if (rst_a == 1'b1)
  begin
    ecc_dc_tag_sbe_count_r   <= 4'b0000;
  end
  else
  begin
    ecc_dc_tag_sbe_count_r <= ecc_dc_tag_sbe_count_next;
  end  
end

always @(posedge clk or posedge rst_a)
begin : ecc_dc_data_sbe_count_reg_PROC
  if (rst_a == 1'b1)
  begin
    ecc_dc_data_sbe_count_r   <= 4'b0000;
  end
  else
  begin
    ecc_dc_data_sbe_count_r <= ecc_dc_data_sbe_count_next;
  end  
end


always @(posedge clk or posedge rst_a)
begin : aux_dd_set_addr_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_dd_set_addr_r   <= `npuarc_DC_ADDR_BITS'b0;
  end
  else if (aux_dd_set_incr_cg0)
  begin
    aux_dd_set_addr_r <= aux_dd_set_addr_nxt;
  end
end

endmodule // alb_dmp_dcache_aux

