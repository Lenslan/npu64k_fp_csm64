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
//  #    ####     ##     ####   #    #  ######          ##    #    #  #    #
//  #   #    #   #  #   #    #  #    #  #              #  #   #    #   #  #
//  #   #       #    #  #       ######  #####         #    #  #    #    ##
//  #   #       ######  #       #    #  #             ######  #    #    ##
//  #   #    #  #    #  #    #  #    #  #             #    #  #    #   #  #
//  #    ####   #    #   ####   #    #  ###### #####  #    #   ####   #    #
// 
// ===========================================================================
//
// Description:
// This file implements Icache aux registers
// The aux interface needs to change next
//----------------------------------------------------------------------------

`include "npuarc_defines.v"
// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 }, edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_icache_aux (
  input                       clk,              // Processor clock
  input                       clk_en,           // icache clock phase
  input                       rst_a,            // Asynchronous reset


  input                       dbg_cache_rst_disable_r,


  ////////// Interface for SR instructions to write aux regs ///////////////
  //
  input                       aux_read,         // Aux read operation
  input                       aux_write,        // Aux write operation
  input                       aux_wen,          // write to reg
  input                       aux_ren,          // read from reg 
  input      [3:0]            aux_waddr,        // Aux address for write
  input      [3:0]            aux_raddr,        // Aux address for read
  input      [`npuarc_DATA_RANGE]    aux_wdata,        // Aux write data

  ////////// decoded output to cache controller to access cache
  output                      cache_op_req,     // start an AUX cache operation
  input                       cache_op_ack,     // ack from cache that the operation is finished
  output reg [7:0]            cache_op_mode,    // type of cache operation
  output [`npuarc_PADDR_RANGE]       cache_op_addr,    // address where the cache operation occurs
  output reg [`npuarc_IC_ALIAS_IDX_RANGE] aux_alias_r,
  output reg [`npuarc_DOUBLE_RANGE]  cache_op_wdata, //32bit is used for normal operation, 64 bits is for bist
  output reg [`npuarc_DOUBLE_BE_RANGE] cache_op_wmask, 
  output                      uncache_mode,
  output reg [3:0]            ic_waylock,
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ:  unused port range
// spyglass disable_block W240
// SMD: non driving port
// SJ : clk not used
  input [`npuarc_IC_BANK_WIDTH-1:0]  cache_op_rdata, //normal operation needs LSB 32 bits, bist uses all 64 bits
  input [`npuarc_IC_TRAM_RANGE]      aux_tag_mem_rdata,
// leda NTL_CON13C on
// leda NTL_CON37 on
// spyglass enable_block W240

  input                       cache_op_rdata_vld,
// leda NTL_CON13C off
// LMD: non driving port range
// LJ:  Generic bus and not all bits are used in module
  input [`npuarc_PADDR_RANGE]        cache_op_tag_rdata,
// leda NTL_CON13C on
  input                       cache_op_tag_rdata_vld,
  input                       cache_op_fail,

  input                       ecc_ifu_disable,
  output                      ic_aux_data_ecc_err,
  output                      ic_aux_data_ecc_sb_err,

  output                      ifu_ivic,
  output                      ifu_ivil,

  //serialization busy output
  output aux_busy,

  ////////// Interface for aux address / LR reads /////////////////////////
  //
  output reg  [`npuarc_DATA_RANGE]   ic_aux_rdata,     // LR read data
  output reg                  ic_aux_illegal,   // SR/LR operation is illegal
  output reg                  ic_aux_k_rd,      // op needs Kernel R perm
  output reg                  ic_aux_k_wr,      // op needs Kernel W perm
  output reg                  ic_aux_unimpl,    // LR/SR reg is not present
  output reg                  ic_aux_serial_sr, // SR must serialize the pipe
  output reg                  ic_aux_strict_sr  // SR must serialize the pipe

);

//reg       [`DATA_RANGE]       sr_data;          // gated write data

//write pulse for each registers
//reg                           aux_ic_ctrl_wen;
reg                           aux_ic_waylock_wen;
reg                           aux_ic_ivic_wen;
reg                           aux_ic_ivil_wen;
reg                           aux_ic_ivir_wen;
reg                           aux_ic_lil_wen;
reg                           aux_ic_ptag_hi_wen;
reg                           aux_ic_startr_wen;
reg                           aux_ic_ptag_wen;
reg                           aux_ic_endr_wen;
reg                           aux_ic_tag_wen;
reg                           aux_ic_data_wen;
reg                           aux_pc_load;

//registers
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg     [5:0]                 aux_ic_ctrl_nxt, aux_ic_ctrl_nxt_nxt, aux_ic_ctrl_r;
reg     [5:0]                 aux_ic_ctrl_next;
reg     [3:0]                 aux_ic_waylock_r, aux_ic_waylock_nxt, aux_ic_waylock_nxt_nxt;
reg     [`npuarc_PADDR_RANGE]        aux_ic_tag_data_nxt, aux_ic_tag_data_nxt_nxt, aux_ic_tag_data_r;
reg     [`npuarc_DATA_RANGE]         aux_ic_endr_nxt, aux_ic_endr_nxt_nxt, aux_ic_endr_r, aux_ic_startr_nxt_nxt;
// leda NTL_CON32 on

reg     [`npuarc_DATA_RANGE]         aux_pc_nxt, aux_pc_r, aux_pc_nxt_nxt;
reg     [`npuarc_DATA_RANGE]         aux_pc_incr;
reg                           region_end;
reg     [`npuarc_IC_AUX_STARTR_RANGE] aux_ic_startr_nxt, aux_ic_startr_r;
reg     [`npuarc_IC_ALIAS_IDX_RANGE] aux_alias_nxt;
reg     [`npuarc_IC_TAG_RANGE]       aux_ic_ptag_nxt, aux_ic_ptag_nxt_nxt, aux_ic_ptag_r;
reg     [`npuarc_DATA_RANGE]         aux_ic_data_nxt, aux_ic_data_nxt_nxt, aux_ic_data_r;
reg     [7:0]                 cache_op_mode_r;
reg     [7:0]                 cache_op_mode_new;
wire                          cache_op_req_r;
reg                           cache_op_reset_req_r;
reg                           cache_op_aux_req_r;

//region sm control
reg [1:0] region_state_nxt, region_state_r;
reg region_req;
reg region_req_flag;
reg region_req_start;
reg nc0; // unconnected overflow bit in adder

assign uncache_mode = aux_ic_ctrl_r[0];
wire aux_at_bit;
assign aux_at_bit     = aux_ic_ctrl_r[5];

//temp signal for tag_data register input
//we need to load the index with startr if tag read suceeds
//
reg [`npuarc_PADDR_RANGE] cache_op_tag_rdata_mod;


///////////////////////////// register write ///////////////////////////////
//
always @(*) 
begin : reg_wr_PROC

  // clear sr_data when not performing SR operations, to avoid toggling
  //
//  sr_data             = {32{aux_wen}} & aux_wdata;
  
//  aux_ic_ctrl_wen     = 1'b0;
  aux_ic_waylock_wen  = 1'b0;  
  aux_ic_ivic_wen     = 1'b0;
  aux_ic_ivil_wen     = 1'b0;
  aux_ic_ivir_wen     = 1'b0;
  aux_ic_lil_wen      = 1'b0;
  aux_ic_startr_wen   = 1'b0;
  aux_ic_ptag_wen     = 1'b0;
  aux_ic_endr_wen     = 1'b0;
  aux_ic_tag_wen      = 1'b0;
  aux_ic_ptag_hi_wen     = 1'b0;
  aux_ic_data_wen     = 1'b0;
  aux_pc_load         = 1'b0;

  aux_ic_ctrl_nxt     = aux_ic_ctrl_r;
  aux_ic_waylock_nxt  = aux_ic_waylock_r;
  aux_ic_startr_nxt   = aux_ic_startr_r;
  aux_ic_ptag_nxt     = aux_ic_ptag_r;
  aux_ic_endr_nxt     = aux_ic_endr_r;
  aux_ic_tag_data_nxt = aux_ic_tag_data_r;
  aux_ic_data_nxt     = aux_ic_data_r;

  if (aux_wen) begin
    case ({8'h01,aux_waddr})
    `npuarc_IC_CTRL_AUX: begin // K_RW
//      aux_ic_ctrl_wen  = 1'b1;
      aux_ic_ctrl_nxt  = aux_wdata[5:0];
    end
    `npuarc_IC_WAYLOCK_AUX: // K_RW
    begin  
      aux_ic_waylock_wen = 1'b1; 

      aux_ic_waylock_nxt = aux_wdata[3:0];
    end  
    `npuarc_IC_IVIC_AUX: // K_WRITE
    begin
      aux_ic_ivic_wen  = 1'b1;
    end
    `npuarc_IC_LIL_AUX:  // K_WRITE
    begin
      aux_ic_lil_wen   = 1'b1;
      aux_pc_load      = 1'b1;
    end
    `npuarc_IC_IVIL_AUX: // K_WRITE
    begin
      aux_ic_ivil_wen  = 1'b1;
      aux_pc_load      = 1'b1;
    end
    `npuarc_IC_IVIR_AUX: // K_WRITE
    begin
      aux_ic_ivir_wen = 1'b1;
      aux_pc_load     = 1'b1;
    end
    `npuarc_IC_STARTR_AUX: // K_RW
    begin
      aux_ic_startr_wen = 1'b1;
      aux_ic_startr_nxt = aux_ic_startr_r;
      aux_ic_startr_nxt[`npuarc_IC_IDX_MSB:2] = aux_wdata[`npuarc_IC_IDX_MSB:2];
      if (~aux_at_bit)       
      begin
         aux_ic_startr_nxt[`npuarc_IC_WAY_CACHE_RANGE] = aux_wdata[`npuarc_IC_WAY_CACHE_RANGE];
      end
      aux_pc_load       = 1'b1;
    end
    `npuarc_IC_PTAG_AUX: // K_RW
    begin
      aux_ic_ptag_wen = 1'b1;
      aux_ic_ptag_nxt[`npuarc_DATA_MSB:`npuarc_IC_TAG_LSB] = aux_wdata[`npuarc_DATA_MSB:`npuarc_IC_TAG_LSB];
    end
    `npuarc_IC_ENDR_AUX: // K_RW
    begin
      aux_ic_endr_wen = 1'b1;
      aux_ic_endr_nxt = aux_wdata;
    end
    `npuarc_IC_PTAG_HI_AUX: // K_RW
    begin
      aux_ic_ptag_hi_wen = 1'b1;
      aux_ic_tag_data_nxt [`npuarc_PADDR_HI_RANGE] = aux_wdata [7:0];
    end
    `npuarc_IC_TAG_AUX: // K_RW
    begin
      if (!aux_at_bit) begin
        aux_ic_tag_wen      = 1'b1;
        aux_ic_tag_data_nxt [`npuarc_DATA_RANGE] = {`npuarc_DATA_SIZE{1'b0}};
        aux_ic_tag_data_nxt[`npuarc_DATA_MSB:`npuarc_IC_TAG_LSB] = aux_wdata[`npuarc_DATA_MSB:`npuarc_IC_TAG_LSB];
        aux_ic_tag_data_nxt[1:0] = aux_wdata[1:0];
      end
    end
    `npuarc_IC_DATA_AUX: // K_RW
    begin
      if (!aux_at_bit) begin
        aux_ic_data_wen  = 1'b1;
        aux_ic_data_nxt  = aux_wdata;
      end
    end
    default:
    begin
      aux_ic_ctrl_nxt = aux_ic_ctrl_r;
    end
    endcase
  end
end // block: reg_wr_PROC

///////////////////////////// register read ///////////////////////////////
//status returns at register read.
//status depends on aux_read and aux_write 
//
always @(*) 
begin : reg_rd_PROC

  ic_aux_rdata        = `npuarc_DATA_SIZE'd0;
  ic_aux_k_rd         = 1'b0;
  ic_aux_k_wr         = 1'b0; 
  ic_aux_unimpl       = 1'b1;
  ic_aux_illegal      = 1'b0;
  ic_aux_serial_sr    = 1'b0;
  ic_aux_strict_sr    = 1'b0;
  
  if (aux_ren) begin
    ic_aux_unimpl     = 1'b0;
    ic_aux_serial_sr  = aux_write;
    ic_aux_strict_sr  = aux_write;
    case ({8'h01,aux_raddr})
    `npuarc_IC_CTRL_AUX: begin // K_RW
      ic_aux_rdata    = { 26'd0,
                          aux_ic_ctrl_r[5],  // AT
                          1'b0,              // RA
                          aux_ic_ctrl_r[3],  // SB
                          1'b0,
                          1'b0,              // EB
                          aux_ic_ctrl_r[0]
                        };
      ic_aux_k_rd     = 1'b1;
      ic_aux_k_wr     = 1'b1;
    end
    `npuarc_IC_WAYLOCK_AUX: // K_RW
    begin
      ic_aux_rdata    = { 28'd0, aux_ic_waylock_r[3:0]};
      ic_aux_k_rd     = 1'b1;
      ic_aux_k_wr     = 1'b1;
    end
    `npuarc_IC_IVIC_AUX: // K_WRITE
    begin
      ic_aux_k_wr     = 1'b1;
      ic_aux_illegal  = aux_read;
    end
    `npuarc_IC_LIL_AUX:  // K_WRITE
    begin
      ic_aux_k_wr     = 1'b1;
      ic_aux_illegal  = aux_read;
    end
    `npuarc_IC_IVIL_AUX: // K_WRITE
    begin
      ic_aux_k_wr     = 1'b1;
      ic_aux_illegal  = aux_read;
    end
    `npuarc_IC_IVIR_AUX: // K_WRITE
    begin
      ic_aux_k_wr     = 1'b1;
      ic_aux_illegal  = aux_read;
    end


    `npuarc_IC_STARTR_AUX: // K_RW
    begin
      ic_aux_rdata    = {`npuarc_DATA_SIZE{1'b0}};
      if (!aux_at_bit) 
      begin
        ic_aux_rdata[`npuarc_IC_IDX_MSB:2]    = aux_ic_startr_r[`npuarc_IC_IDX_MSB:2];
      end
      else
      begin
        ic_aux_rdata[`npuarc_IC_IDX_MSB:2]       = aux_ic_startr_r[`npuarc_IC_IDX_MSB:2];
        ic_aux_rdata[`npuarc_IC_WAY_CACHE_RANGE] = aux_ic_startr_r[`npuarc_IC_WAY_CACHE_RANGE];
      end
      ic_aux_k_rd     = 1'b1;
      ic_aux_k_wr     = 1'b1;
    end
    `npuarc_IC_PTAG_AUX: // K_RW
    begin
      ic_aux_rdata[`npuarc_DATA_MSB:`npuarc_IC_TAG_LSB] = aux_ic_ptag_r[`npuarc_DATA_MSB:`npuarc_IC_TAG_LSB];
      ic_aux_k_rd     = 1'b1;
      ic_aux_k_wr     = 1'b1;
    end


    `npuarc_IC_ENDR_AUX: // K_RW
    begin
      ic_aux_rdata    = {aux_ic_endr_r [`npuarc_DATA_MSB: `npuarc_IC_LINE_BITS]
                                       , {`npuarc_IC_LINE_BITS{1'b0}}};
      ic_aux_k_rd     = 1'b1;
      ic_aux_k_wr     = 1'b1;
    end
    `npuarc_IC_PTAG_HI_AUX: // K_RW
    begin
      ic_aux_rdata [7:0] = aux_ic_tag_data_r [`npuarc_PADDR_HI_RANGE];
      ic_aux_k_rd        = 1'b1;
      ic_aux_k_wr        = 1'b1;
    end


    `npuarc_IC_TAG_AUX: // K_RW
    begin
      ic_aux_rdata[0]  = aux_ic_tag_data_r[0];
      ic_aux_rdata[1]  = aux_ic_tag_data_r[1];
      ic_aux_rdata[`npuarc_DATA_MSB:`npuarc_IC_TAG_LSB]  = aux_ic_tag_data_r[`npuarc_DATA_MSB:`npuarc_IC_TAG_LSB];
      ic_aux_k_rd     = 1'b1;
      ic_aux_k_wr     = 1'b1;
      ic_aux_illegal  = aux_write & aux_at_bit;
    end
    `npuarc_IC_DATA_AUX: // K_RW
    begin
      ic_aux_rdata    = aux_ic_data_r;
      ic_aux_k_rd     = 1'b1;
      ic_aux_k_wr     = 1'b1;
      ic_aux_illegal  = aux_write & aux_at_bit;
    end
    default:
    begin
      // aux address is not implemented in the Icache
      //
      ic_aux_unimpl    = 1'b1;
      ic_aux_serial_sr = 1'b0;
      ic_aux_strict_sr = 1'b0;
    end
    endcase
  end
end // block: reg_rd_PROC

//////////////////// Interface with cache controller /////////////////////
//the interface is req-ack based
//return data has seperate valid input
//
parameter REG_CACHE_RD_IND = 0; // cache/tag memory read, normal read
parameter REG_CACHE_RD_DIR = 1; // cache/tag memory read, direct read
parameter REG_CACHE_WR_DIR = 2; // cache memory write, direct write
parameter REG_TAG_WR_DIR   = 3; // tag memory write, direct write
parameter REG_TAG_INVLD    = 4; // tag invalidate, all
parameter REG_TAG_INVLDL   = 5; // tag invalidate, line only
parameter REG_TAG_LOCK     = 6; // tag line lock
parameter REG_TAG_PREFETCH = 7; // tag line prefetch


always @*
begin: cache_op_mode_new_PROC
  cache_op_mode_new[REG_CACHE_RD_IND] = aux_ic_startr_wen & aux_at_bit;             //cache/tag ind read 
  cache_op_mode_new[REG_CACHE_RD_DIR] = aux_ic_startr_wen & (!aux_at_bit);          //cache/tag dir read
  cache_op_mode_new[REG_CACHE_WR_DIR] = aux_ic_data_wen & (!aux_at_bit);            //cache wr, only dir write is allowed
  cache_op_mode_new[REG_TAG_WR_DIR]   = aux_ic_tag_wen & (!aux_at_bit);             //tag wr, only dir write is allowed
  cache_op_mode_new[REG_TAG_INVLD]    = aux_ic_ivic_wen;                            //invalid all
  cache_op_mode_new[REG_TAG_INVLDL]   = aux_ic_ivil_wen                             //invalidate a single line
                                      |(region_req & (aux_pc_nxt[1:0] == 2'd0))     //invalidate a line of region
                                      ;
  cache_op_mode_new[REG_TAG_LOCK]     = (aux_ic_lil_wen & (aux_pc_nxt[0] == 1'd0))  //re-load and lock a single line
                                      |(region_req & (aux_pc_nxt[1:0] == 2'd2))     //lock a line of region
                                      ;  
  cache_op_mode_new[REG_TAG_PREFETCH] = (aux_ic_lil_wen & (aux_pc_nxt[0] == 1'd1))  //prefetch a single line
                                      |(region_req & (aux_pc_nxt[1:0] == 2'd1))     //prefetch a line of region
                                      ;  
  
end


reg       cache_op_reset_req_nxt;
reg       cache_op_reset_req_next;
reg       cache_op_aux_req_nxt;
reg       cache_op_aux_req_next;
reg [1:0] region_state_nxt_nxt;
reg [1:0] region_state_next;
reg [7:0] cache_op_mode_nxt;
reg [7:0] cache_op_mode_next;

always @(*)
begin: cache_op_logic_PROC

  cache_op_reset_req_nxt        = cache_op_reset_req_r;
  cache_op_aux_req_nxt          = cache_op_aux_req_r;
  region_state_nxt_nxt          = region_state_nxt;
  aux_ic_ctrl_nxt_nxt           = aux_ic_ctrl_r;
  cache_op_mode_nxt             = cache_op_mode_r;
  aux_ic_tag_data_nxt_nxt       = aux_ic_tag_data_r;
  aux_ic_data_nxt_nxt           = aux_ic_data_r;
  aux_ic_endr_nxt_nxt           = aux_ic_endr_r;
  aux_ic_startr_nxt_nxt         = aux_ic_startr_r; 
  aux_pc_nxt_nxt                = aux_pc_r;
  aux_ic_waylock_nxt_nxt        = aux_ic_waylock_r;
  aux_ic_ptag_nxt_nxt           = aux_ic_ptag_r;
  // register writes that trigger Icache operations
  //
  if (aux_ic_ivic_wen | aux_ic_ivil_wen
      | (region_req & (aux_pc_nxt[1:0] != 2'd3))
      | aux_ic_lil_wen | aux_ic_startr_wen | aux_ic_tag_wen | aux_ic_data_wen) 
  begin
    cache_op_aux_req_nxt      = 1'b1;
    cache_op_mode_nxt         = cache_op_mode_new;
  end
  else if (cache_op_ack) begin
    cache_op_reset_req_nxt    = 1'b0;
    cache_op_aux_req_nxt      = 1'b0;
  end
  else if (dbg_cache_rst_disable_r) begin
    cache_op_reset_req_nxt    = 1'b0;
  end

  if(aux_ic_startr_wen == 1'b1)
     aux_ic_startr_nxt_nxt =  aux_ic_startr_nxt;  

  if (aux_ic_ptag_wen == 1'b1)
     aux_ic_ptag_nxt_nxt = aux_ic_ptag_nxt;

    if (aux_ic_endr_wen == 1'b1)
      aux_ic_endr_nxt_nxt   = aux_ic_endr_nxt;

    aux_pc_nxt_nxt           = aux_pc_nxt;

  // returned registers from icache
  if (cache_op_mode_r[REG_CACHE_RD_IND] && cache_op_tag_rdata_vld && clk_en) begin
    if (!cache_op_fail) begin //only update IC_TAG when there is valid entry in cache
      aux_ic_tag_data_nxt_nxt = cache_op_tag_rdata_mod;
    end
  end
    else if (cache_op_mode_r[REG_CACHE_RD_DIR] && cache_op_tag_rdata_vld && clk_en) begin
      aux_ic_tag_data_nxt_nxt = cache_op_tag_rdata_mod;
    end
    else begin
      aux_ic_tag_data_nxt_nxt = aux_ic_tag_data_nxt;
    end

    if (cache_op_mode_r[REG_CACHE_RD_IND] && cache_op_rdata_vld && clk_en) begin
      if (aux_ic_ctrl_r[3]) begin //only update IC_DATA when there is valid entry in cache
        aux_ic_data_nxt_nxt   = cache_op_rdata[`npuarc_DATA_RANGE];
      end
    end
    else if (cache_op_mode_r[REG_CACHE_RD_DIR] && cache_op_rdata_vld && clk_en) begin
      aux_ic_data_nxt_nxt     = cache_op_rdata[`npuarc_DATA_RANGE];
    end
    else begin
      aux_ic_data_nxt_nxt     = aux_ic_data_nxt;
    end

    // control register including status bit
    {aux_ic_ctrl_nxt_nxt[5:4], aux_ic_ctrl_nxt_nxt[2:0]}   = {aux_ic_ctrl_nxt[5:4], aux_ic_ctrl_nxt[2:0]};

    if (aux_ic_waylock_wen )
      aux_ic_waylock_nxt_nxt   =  aux_ic_waylock_nxt;

    if (region_req_start) 
    begin
      if (cache_op_mode_new[REG_TAG_INVLDL])
         aux_ic_ctrl_nxt_nxt[3]  = 1'b0;
      else
         aux_ic_ctrl_nxt_nxt[3]  = 1'b1;
    end
    else if (cache_op_mode_r[REG_CACHE_RD_IND] && cache_op_tag_rdata_vld && clk_en) 
    begin
      aux_ic_ctrl_nxt_nxt[3]     = cache_op_tag_rdata[0];
    end
    else if (cache_op_ack && (cache_op_mode_r[REG_TAG_INVLDL] || cache_op_mode_r[REG_TAG_LOCK] || cache_op_mode_r[REG_TAG_PREFETCH])) 
    begin
      if (region_req_flag) 
      begin  
        if (cache_op_mode_r[REG_TAG_INVLDL])    
          aux_ic_ctrl_nxt_nxt[3] = aux_ic_ctrl_r[3] | (!cache_op_fail);
        else 
          aux_ic_ctrl_nxt_nxt[3] = aux_ic_ctrl_r[3] & (!cache_op_fail);
      end
      else 
      begin
        aux_ic_ctrl_nxt_nxt[3]   = !cache_op_fail;
      end
    end
    else 
    begin
      aux_ic_ctrl_nxt_nxt[3]     = aux_ic_ctrl_nxt[3];
    end
end
//
always @ *
begin: cache_op_ctrl_comb_PROC
  cache_op_reset_req_next  = cache_op_reset_req_r ; 
  cache_op_aux_req_next    = cache_op_aux_req_r   ; 
  cache_op_mode_next       = cache_op_mode_r      ; 
  region_state_next        = region_state_r       ; 
  aux_ic_ctrl_next         = aux_ic_ctrl_r        ; 
  begin
    cache_op_reset_req_next= cache_op_reset_req_nxt;
    cache_op_aux_req_next  = cache_op_aux_req_nxt; 
    cache_op_mode_next     = cache_op_mode_nxt;
    region_state_next      = region_state_nxt_nxt;
    aux_ic_ctrl_next       = aux_ic_ctrl_nxt_nxt;
  end
end // block: cache_op_ctrl_comb_PROC
always @(posedge clk or posedge rst_a) 
begin: cache_op_ctrl_reg_PROC
  if (rst_a == 1'b1) begin
    cache_op_reset_req_r  <= 1'b1;  // to initialize tag
    cache_op_aux_req_r    <= 1'b0;
    cache_op_mode_r       <= 8'h10; // mode set to invalidate tag at reset
    region_state_r        <= 2'd0;
    aux_ic_ctrl_r         <= {5'b0, 1'b`npuarc_IC_DISABLE_ON_RESET};
  end
  else 
  begin
    cache_op_reset_req_r  <= cache_op_reset_req_next;
    cache_op_aux_req_r    <= cache_op_aux_req_next; 
    cache_op_mode_r       <= cache_op_mode_next;
    region_state_r        <= region_state_next;
    aux_ic_ctrl_r         <= aux_ic_ctrl_next;
  end
end // block: cache_op_ctrl_reg_PROC
//
always @(posedge clk or posedge rst_a) 
begin: cache_op_reg_PROC
  if (rst_a == 1'b1) begin

    aux_ic_waylock_r      <= 4'b0;
    aux_ic_tag_data_r     <= {`npuarc_PADDR_SIZE{1'b0}};
    aux_ic_startr_r       <= {`npuarc_IC_AUX_STARTR_BITS{1'b0}};
    aux_ic_endr_r         <= {`npuarc_DATA_SIZE{1'b0}};
    aux_ic_data_r         <= {`npuarc_DATA_SIZE{1'b0}};
    aux_pc_r              <= {`npuarc_DATA_SIZE{1'b0}}; 
    aux_alias_r           <= {`npuarc_IC_ALIAS_BITS{1'b0}}; 
    aux_ic_ptag_r         <= {`npuarc_IC_TAG_BITS{1'b0}};
  end
  else 
  begin

    // address registers for cache accesses
    aux_ic_startr_r       <= aux_ic_startr_nxt_nxt[`npuarc_IC_AUX_STARTR_RANGE];
    aux_ic_ptag_r         <= aux_ic_ptag_nxt_nxt;
    aux_ic_endr_r         <= aux_ic_endr_nxt_nxt;

    aux_pc_r              <= aux_pc_nxt_nxt;

    aux_alias_r           <= aux_alias_nxt;
    aux_ic_tag_data_r     <= aux_ic_tag_data_nxt_nxt;
    aux_ic_data_r         <= aux_ic_data_nxt_nxt;
    aux_ic_waylock_r      <= aux_ic_waylock_nxt_nxt;
  end
end //block: cache_op_reg_PROC


reg [`npuarc_PADDR_RANGE] cache_op_addr_func;

reg [`npuarc_DATA_RANGE] aux_pc_ptag;
always @*
begin: ptag_PROC
  aux_pc_ptag = aux_pc_r;
  aux_pc_ptag[`npuarc_DATA_MSB:`npuarc_IC_TAG_LSB] = aux_ic_ptag_r[`npuarc_DATA_MSB:`npuarc_IC_TAG_LSB];
end

assign cache_op_req_r = cache_op_aux_req_r 
                      | (cache_op_reset_req_r & (!dbg_cache_rst_disable_r));

always @*
begin: addr_func_PROC


  cache_op_addr_func = {`npuarc_PADDR_SIZE{1'b0}};
  if (cache_op_mode_r[REG_CACHE_WR_DIR]
      || cache_op_mode_r[REG_TAG_WR_DIR]
      || cache_op_mode_r[REG_CACHE_RD_DIR]
      )
  begin
    cache_op_addr_func[`npuarc_IC_AUX_STARTR_RANGE] = aux_ic_startr_r[`npuarc_IC_AUX_STARTR_RANGE];
  end
  else
  begin
    cache_op_addr_func = {aux_ic_tag_data_r [`npuarc_PADDR_HI_RANGE]
                       ,  aux_pc_ptag};
  end


end // block: addr_func_PROC


assign cache_op_addr = cache_op_addr_func;
assign cache_op_req  = cache_op_req_r;

always @(*) 
begin: cache_op_wdata_PROC
  cache_op_wmask = {`npuarc_DOUBLE_BE_SIZE{1'b1}};
  if (cache_op_mode_r[REG_CACHE_WR_DIR])
    begin
    cache_op_wdata = {aux_ic_data_r, aux_ic_data_r};
    end
  else
    begin
    cache_op_wdata = {`npuarc_DOUBLE_SIZE{1'b0}};
    cache_op_wdata[`npuarc_IC_TAG_TAG_RANGE] = aux_ic_tag_data_r[`npuarc_IC_TAG_RANGE];
    cache_op_wdata[`npuarc_IC_TAG_LOCK_BIT]  = aux_ic_tag_data_r[1];
    cache_op_wdata[`npuarc_IC_TAG_VALID_BIT] = aux_ic_tag_data_r[0];
    end 
end

always @(*)
begin: cache_op_tag_rdata_PROC
  cache_op_tag_rdata_mod = {`npuarc_PADDR_SIZE{1'b0}};
  cache_op_tag_rdata_mod[`npuarc_IC_TAG_RANGE] = cache_op_tag_rdata[`npuarc_IC_TAG_RANGE];
  cache_op_tag_rdata_mod[1:0] = cache_op_tag_rdata[1:0];
end

always @(*)
begin: cache_op_mode_PROC
  cache_op_mode = cache_op_mode_r;
  ic_waylock = aux_ic_waylock_r;
end    

//sm for region based operation
always @(*)
begin: region_invld_PROC
  aux_pc_nxt      = aux_pc_r;
  aux_alias_nxt   = aux_alias_r;
  region_state_nxt = region_state_r;
  region_req = 1'b0;
  region_req_flag = 1'b0;
  region_req_start= 1'b0;
  {nc0,aux_pc_incr} = aux_pc_r + `npuarc_PC_SIZE'd`npuarc_IC_BSIZE; 
  region_end = (aux_pc_incr[`npuarc_PC_SIZE-1:`npuarc_IC_BLK_BITS] == aux_ic_endr_r[`npuarc_PC_SIZE-1:`npuarc_IC_BLK_BITS]);
  case (region_state_r)
  2'd0:
    begin
      if (aux_pc_load)
      begin
        aux_pc_nxt = aux_wdata;
        aux_alias_nxt = aux_wdata[`npuarc_IC_ALIAS_IDX_RANGE];
      end

      if (aux_ic_ivir_wen)
      begin
        region_state_nxt   = 2'd1; 
      end
    end
  2'd1:
    begin
      if (aux_pc_r[`npuarc_PC_SIZE-1:`npuarc_IC_BLK_BITS] == aux_ic_endr_r[`npuarc_PC_SIZE-1:`npuarc_IC_BLK_BITS])
      begin
        region_state_nxt   = 2'd0; 
      end
      else 
      begin
        region_req       = 1'b1; 
        region_req_start = 1'b1;
        region_state_nxt = 2'd2; 
      end
    end
  default: 
    begin
      region_req_flag = 1'b1; 
      region_req = 1'b1;
      if (cache_op_ack)
      begin
        aux_pc_nxt = aux_pc_incr; 
        aux_alias_nxt = aux_pc_nxt[`npuarc_IC_ALIAS_IDX_RANGE];
        if (region_end)
        begin
          region_state_nxt = 2'd0; 
          region_req = 1'b0;
        end
      end
    end
  endcase
end

assign aux_busy = cache_op_req_r; 
assign ifu_ivic = cache_op_mode_r[REG_TAG_INVLD]
                & cache_op_ack
                ;
assign ifu_ivil = cache_op_mode_r[REG_TAG_INVLDL]
                & cache_op_ack
                ;



reg                          ic_aux_data_ecc_en;
reg                          ic_aux_data_ecc_en_nxt;
wire                         cache_op_rdata_r_en;
wire[31:0]                   cache_op_rdata_r;
reg [`npuarc_IC_ECC_CODE_BITS-1:0]  cache_op_rdata_ecc_r;


// Generate ECC enable signal for the aux reads

always @(*) 
begin: ic_aux_data_ecc_en_logic_PROC
  ic_aux_data_ecc_en_nxt = ic_aux_data_ecc_en;

  if(clk_en & cache_op_rdata_vld 
            & (( cache_op_mode_r[REG_CACHE_RD_IND] & aux_ic_ctrl_r[3])  // Enable ECC only of the search is successful
               | cache_op_mode_r[REG_CACHE_RD_DIR]
    ))
  begin
    ic_aux_data_ecc_en_nxt = 1'b1;
  end
  else begin
    ic_aux_data_ecc_en_nxt = 1'b0; 
  end
end

always @(posedge clk or posedge rst_a) 
begin: ic_aux_data_ecc_en_reg_PROC
  if (rst_a == 1'b1) begin
    ic_aux_data_ecc_en <= 1'b0;
  end
  else begin
    ic_aux_data_ecc_en <= ic_aux_data_ecc_en_nxt;
  end
end

// Enable signal to capture the data from the Data RAM for ECC checking
assign cache_op_rdata_r_en = clk_en  
                           & cache_op_rdata_vld 
                           & ((cache_op_mode_r[REG_CACHE_RD_IND] & aux_ic_ctrl_r[3])  // Enable ECC only of the search is successful
                             | cache_op_mode_r[REG_CACHE_RD_DIR]
                             );

// Use the data captured by the aux interface logic
assign cache_op_rdata_r = aux_ic_data_r;

// Register the ECC code data from the Data RAM 
always @(posedge clk or posedge rst_a) 
begin: ic_aux_data_ecc_reg_PROC
  if (rst_a == 1'b1) begin
    cache_op_rdata_ecc_r <= `npuarc_IC_ECC_CODE_BITS'd0;
  end
else if(cache_op_rdata_r_en ) begin 
    cache_op_rdata_ecc_r <= cache_op_rdata[32+`npuarc_IC_ECC_CODE_BITS-1:32];
  end
end


wire [31:0]                  ic_aux_data_out_unused;   
wire [`npuarc_SYNDROME_MSB:0] ic_aux_data_syndrome;


npuarc_alb_ecc_cac32 #( .D_SIZE (`npuarc_IC_TAG_BITS+1)) uic_aux_alb_ecc_cac32(

 .clk         (clk                      ),
 .rst_a       (rst_a                    ),

  ////////// ECC Data Input //////////////////////////////////////////
  //
 .data_in     (cache_op_rdata_r[31:0]   ),    // 32-bit data in
 .ecc_code_in (cache_op_rdata_ecc_r     ),    // ECC code in
 
 .ecc_chk_en  (1'b1                     ), 

  ///////// ECC outputs /////////////////////////////////////////////
  //
 .ecc_error   (ic_aux_data_ecc_err_int      ),    // error detected
 .sb_error    (ic_aux_data_sb_ecc_err_int   ),    // single bit error detected
 .db_error    (ic_aux_data_db_ecc_err_int   ),    // double bit error detected
 .syndrome    (ic_aux_data_syndrome     ),
 .data_out    (ic_aux_data_out_unused   )     // corrected data out   
  );




assign ic_aux_data_ecc_err = ic_aux_data_db_ecc_err_int 
                           & ic_aux_data_ecc_en
                           & (!ecc_ifu_disable);

assign ic_aux_data_ecc_sb_err = ic_aux_data_sb_ecc_err_int 
                              & ic_aux_data_ecc_en
                              & (!ecc_ifu_disable);




/////////////////////////////// sanity check ////////////////////////////
//`define IC_AUX_SANITY_CHECK
endmodule
  
