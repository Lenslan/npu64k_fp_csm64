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
// ######   #######  ######   #     #   #####
// #     #  #        #     #  #     #  #     #
// #     #  #        #     #  #     #  #
// #     #  #####    ######   #     #  #  ####
// #     #  #        #     #  #     #  #     #
// #     #  #        #     #  #     #  #     #
// ######   #######  ######    #####    #####
//
// ===========================================================================
//
// @f:debug
//
// Description:
//
// @p
//  The |debug| module implements the Debug interface of the ARCv2HS processor.
//  It provides a connection to the processor via a 32-bit BVCI target port
//  through which an external debug host can issue a range of debug commands,
//  as defined by the ARCompact host debug interface.
// @e
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_debug (

  ////////// General input signals /////////////////////////////////////////
  //
  input                         clk,              // Processor clock
  input                         rst_a,            // Asynchronous reset
  input                         l1_clock_active,  //
  ////////// Inputs from the Debug Target (CPU) ////////////////////////////
  //
  input                         hlt_debug_evt,    //
  input       [`npuarc_DATA_RANGE]     wa_rf_wdata0_lo_r,// writeback data (port 0)
  input       [`npuarc_DATA_RANGE]     wa_rf_wdata1_lo_r,// writeback data (port 1)
  input                         gb_sys_halt_r,    // CPU is halted (STATUS32.H)

  input                         wa_commit_dbg,    // debug inst commit
  input                         wa_invalid_instr_r, // illegal_instr => failure
  input                         dbg_ra_r,         // 'reset applied' bit

  ////////// BVCI debug interface /////////////////////////////////////////
  //
  input                         dbg_cmdval,     // |cmdval| from JTAG
  output  reg                   dbg_cmdack,     // BVCI |cmd| acknowledge
  input       [`npuarc_DBG_ADDR_RANGE] dbg_address,    // |addres|s from JTAG
  input       [`npuarc_DBG_BE_RANGE]   dbg_be,         // |be| from JTAG
  input       [`npuarc_DBG_CMD_RANGE]  dbg_cmd,        // |cmd| from JTAG
  input       [`npuarc_DBG_DATA_RANGE] dbg_wdata,      // |wdata| from JTAG

  input                         dbg_rspack,     // |rspack| from JTAG
  output                        dbg_rspval,     // BVCI response valid
  output      [`npuarc_DBG_DATA_RANGE] dbg_rdata,      // BVCI response EOP
  output                        dbg_reop,       // BVCI response error
  output                        dbg_rerr,       // BVCI data to Debug host

  ////////// APB debug interface //////////////////////////////////////////

  input                         dbg_prot_sel,

  input                       pclkdbg_en,
  input                     presetdbgn,
  input [31:2]                paddrdbg,
  input                       pseldbg,
  input                       penabledbg,
  input                       pwritedbg,
  input [31:0]                pwdatadbg,

  output                      preadydbg,
  output [31:0]               prdatadbg,
  output                      pslverrdbg,

  input   [7:0]               arcnum,
  input                       dbgen,
  input                       niden,

  ////////// Outputs to the Debug target (CPU) /////////////////////////////
  //
  output  reg                   db_request,    // Request to issue |db_inst|   
  output  reg                   db_valid,      // Valid |db_inst| being issued 
  output  reg                   db_active,     // Active |db_inst| in pipeline 
  output  reg [`npuarc_DATA_RANGE]     db_inst,       // The debug instruction        
  output      [`npuarc_DATA_RANGE]     db_limm,       // limm for debug instruction 
  output  reg [`npuarc_DATA_RANGE]     db_data,       // Data for db_inst             
  
  output  reg                   db_sel_limm0,  // select debug limm for opd_1  
  output  reg                   db_sel_limm1,  // select debug limm for store  

  output                        debug_reset,    // Reset from debug host 
  input                         db_restart,
  
  //////////  clock control block //////////////////////////////////////////
  //
  output  reg                   db_clock_enable_nxt,  // Clock needs to be enb
  input                         ar_clock_enable_r
);
// spyglass disable_block Ac_fifo01
// SMD: FIFO Overflow/Underflow (n/a, spyglass bug)
// SJ:  CDC accross pseudo-bvci interface handled by protocol/clk ratio

// Define the debug commands
//
// @h2:dbgmacros:Macro definitions in the Debug module
//  There are three sets of macro definitions to guide the behavior of the
//  debug module, and one set of state definitions for the debug instruction
//  issue state machine.
// @e
// @d:dbg_opcodes:Debug operation codes
localparam DB_MEM_WR    = 4'h0;
localparam DB_CORE_WR   = 4'h1;
localparam DB_AUX_WR    = 4'h2;
localparam DB_RST_CMD   = 4'h3;
localparam DB_MEM_RD    = 4'h4;
localparam DB_CORE_RD   = 4'h5;
localparam DB_AUX_RD    = 4'h6;
// @e

// Define the debug register addresses
//
// @d:dbg_addrs:Debug auxiliary register addresses
localparam DB_SPACE    = 24'hffff00;
localparam DB_STAT     = 8'h00;
localparam DB_CMD      = 8'h04;
localparam DB_ADDR     = 8'h08;
localparam DB_DATA     = 8'h0c;
localparam DB_RESET    = 8'h10;

localparam DBP_SPACE    = 24'h0000_04;
localparam DB_CSR1      = 8'h00;
localparam DB_CSR2      = 8'h04;
localparam DB_CSR3      = 8'h0C;
localparam DB_CSR4      = 8'h08;
localparam DB_CSR5      = 8'h10;
localparam db_csr1      = 32'h0000_0090;
localparam db_csr2      = 32'h04B0_0001;
localparam db_csr3      = 32'h0000_0000;
reg                         dbp_space_sel;     // 1 if address match

// @e

// ===========================================================================
// Pseudo-debug instructions issued by the debug unit to the CPU
// ===========================================================================
// Command    Instruction       Instruction Encoding              Hex Pattern
// ---------------------------------------------------------------------------
// DB_MEM_RD  LD.DI limm,[limm]  00010110000000000111100000111110  1600783e
// DB_MEM_WR  ST.DI limm,[limm]  00011110000000000111111110100000  1e007fa0
// DB_AUX_RD  LR    limm,[limm]  00100110001010100111111110000000  262a7f80
// DB_AUX_WR  SR    limm,[limm]  00100110001010110111111110000000  262b7f80
// DB_CORE_RD MOV   limm,Rn      00100110000010100111nnnnnn000000  260a7000 +N
// DB_CORE_WR MOV   Rn,limm      00100nnn000010100NNN111110000000  200a0f80 +N
// ===========================================================================
//
// @d:dbg_insts:Debug instruction encodings
localparam INST_NOP     = 32'h264a7000;
localparam INST_MEMRD   = 32'h1600783e;
localparam INST_MEMWR   = 32'h1e007fa0;
localparam INST_AUXRD   = 32'h262a7f80;
localparam INST_AUXWR   = 32'h262b7f80;
localparam INST_CORERD  = 32'h260a7000;
localparam INST_COREWR  = 32'h200a0f80;
// @e

// @d:dbg_fsm:States of the debug instruction issue and execution FSM
//
localparam DB_FSM_IDLE   = 3'd0;
localparam DB_FSM_AIM    = 3'd1;
localparam DB_FSM_FIRE   = 3'd2;
localparam DB_FSM_LIMM   = 3'd3;
localparam DB_FSM_RELOAD = 3'd4;
localparam DB_FSM_END    = 3'd5;
// @e

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Debug registers                                                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg   [`npuarc_DATA_RANGE]         db_addr_r;        // Debug Address Register
reg   [`npuarc_DATA_RANGE]         db_data_r;        // Debug Data Register
reg   [3:0]                 db_cmd_r;         // Debug Command Register
reg   [1:0]                 db_reset_r;       // Debug Reset Register
reg                         db_ready_r;       // 0=>executing; 1=>ready
reg                         db_failed_r;      // 1=>op.failed; 0=>op.ok
reg   [2:0]                 db_fsm_r;         // execution FSM state var.

reg                         db_addr_incr;     // Incr.debug register 
wire  [`npuarc_DATA_RANGE]         db_addr_plus_stp; // Debug addr reg + 4 or + 1

// leda NTL_CON13A off
//LMD: do not care carry bit
//LJ: can be ignored
wire                        unused_cout;      // Unused carry out of incr op
// leda NTL_CON13A on

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Local reg and wire signals                                             //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg                         rspval_r;         // rspval state variable
reg                         rspval_nxt;       // set by FSM

reg   [`npuarc_DATA_RANGE]         db_addr_nxt;      // Debug Address next value
reg   [`npuarc_DATA_RANGE]         db_data_nxt;      // Debug Data next value
reg   [3:0]                 db_cmd_nxt;       // Debug Command next value
reg   [1:0]                 db_reset_nxt;     // Debug Reset next value
reg                         db_ready_nxt;     // Next value for db_ready_r
reg                         db_failed_nxt;    // Next value for db_failed_r
reg   [2:0]                 db_fsm_nxt;       // next FSM state value

reg                         db_addr_enb;      // enable Debug Address write
reg                         db_data_enb;      // enable Debug Data write
reg                         db_cmd_enb;       // enable Debug Command write
reg                         db_reset_enb;     // enable Debug Reset write
reg                         db_ready_enb;     // enable for db_ready_r
reg                         db_failed_enb;    // enable for db_failed_r

reg                         reset_db;         // 1=>apply reset command
reg                         db_space_sel;     // 1 if address match
reg                         db_addr_match;    // 1 if no address match

reg                         db_addr_err;      // 1 if unmatched access
reg                         db_cmd_err;       // 1 if illegal cmd given
reg                         db_read_err;      // 1 if read from reset reg
reg                         db_be_err;        // 1 if some BE bits not set
reg                         db_any_err;       // 1 if any debug error set

reg                         bvci_read;        // 1 if BVCI cmd == read
reg                         bvci_write;       // 1 if BVCI cmd == write

reg                         do_execute;       // execute cmd when ready
reg                         do_db_reset;      // execute reset immediately

reg                         reset_done_r;     // global reset deasserted

reg  [`npuarc_DBG_DATA_RANGE]      i_dbg_rdata;
wire [31:0]                 i_dbg_address;
wire [31:0]                 i_dbg_wdata;

reg  [31:2]                 i_paddr_r;
reg  [31:0]                 i_pwdata_r;
reg  [31:0]                 i_prdata_r;
reg                         i_pwrite_r;
reg                         i_psel_r;
reg                         i_psel_r1;
reg                         i_penable_r;
reg                         i_penable_r1;
wire                        i_ready;
wire [31:0]                 i_data;

reg  [31:0]                 i_csr_a;

reg                         i_dbgen_r;
reg                         i_niden_r;

reg                         i_pwrite_pulse_r;

wire                        to_start;
wire                        to_flag; 


// Compute db_addr_r + 1 (regs), or + 4 (mem) , for incrementing addresses
//
// leda B_3208 off
// LMD: Unequal length LHS and RHS in assignment
// LJ: arithmetic calculation has a potential dont_care carry bit
assign { unused_cout, db_addr_plus_stp} = db_addr_r + 
          (((db_cmd_r == DB_MEM_RD) || (db_cmd_r == DB_MEM_WR)) ? 4 : 1);
// leda B_3208 on
  

// spyglass disable_block STARC05-1.3.1.3
// SMD: Asynchronous reset signal used as non-reset/synchronous-reset at instance
// SJ:  presetdbgn is converted to synchronous reset on clk
////////////////////////////////////////////////////////////////////////////
//                                                                        //
//  Dummy process to terminate/drive all APB signals                      // 
//                                                                        //
////////////////////////////////////////////////////////////////////////////

// spyglass disable_block Reset_sync02 Reset_check07 Ar_glitch01
//SJ: The clk and pclkdbg are synchronous to each other with a ratio by `DBG_APB_RATIO  
// SMD: Clear pin can glitch 
// SJ:  Clear pin working as designed. Causes no issues as domains are synchronous with a ratio by `DBG_APB_RATIO 
 
always @(posedge clk or negedge presetdbgn)
begin
  if (presetdbgn == 1'b0) begin
    i_paddr_r <= 30'b0;
    i_pwrite_r <= 1'b0;
    i_pwdata_r <= 32'b0;
    i_penable_r <= 1'b0;
    i_penable_r1 <= 1'b0;
    i_psel_r <= 1'b0;
    i_psel_r1 <= 1'b0;
  end
  else if (pclkdbg_en == 1'b1) begin
    i_paddr_r <= paddrdbg;
    i_pwrite_r <= pwritedbg;
    i_pwdata_r <= pwdatadbg;
    i_penable_r <= penabledbg;
    i_penable_r1 <= i_penable_r & penabledbg;
    i_psel_r <= pseldbg;
    i_psel_r1 <= i_psel_r;
  end
end

// spyglass enable_block Reset_check07 Ar_glitch01

always @(posedge clk or negedge presetdbgn)
begin
  if (presetdbgn == 1'b0) begin
    i_prdata_r <= 32'b0;
  end
  else if (pclkdbg_en == 1'b1)  begin
    i_prdata_r <= dbg_rdata;
  end
end

always @(posedge clk or negedge presetdbgn)
begin
  if (presetdbgn == 1'b0)
    i_pwrite_pulse_r <= 1'b0;
  else
    i_pwrite_pulse_r <= i_penable_r & i_psel_r;
end


assign prdatadbg = i_prdata_r;


assign pslverrdbg = to_flag; // error responses when time-out triggered
assign preadydbg = to_flag | 
                        ( (~(ar_clock_enable_r & ~i_penable_r1))
                           & ar_clock_enable_r 
                           & reset_done_r
                           & l1_clock_active )
                        ;



assign to_start =
                 penabledbg & ~i_penable_r;

// Time-out monitor
npuarc_to_monitor #(
.TO_EN        (1),// timeout monitor enable (0: disable, 1:enable)
.TO_CNT_WIDTH (2) // timeout counter width
) u_to_monitor (
.clk      (clk        ), // clock source
.clk_en   (pclkdbg_en ),// 
.rst_a    (~presetdbgn), // async reset, active high
.to_start (to_start   ), // timeout monitor start setting, start timeout counter (detect rising edge)
.to_end   (preadydbg  ), // timeout monitor end setting, reset timeout counter (detect rising edge)
.to_flag  (to_flag    )  // timeout trigger status, once triggered will be sticky till receive to_end
);

// Authentication interface registers
always @(posedge clk or negedge presetdbgn)
begin
  if (presetdbgn == 1'b0) begin    
    i_dbgen_r   <= 1'b0;
    i_niden_r   <= 1'b0;
  end
  else if (pclkdbg_en == 1'b1) begin
    i_dbgen_r   <= dbgen;
    i_niden_r   <= niden;
  end
end

//spyglass enable_block Reset_sync02
// spyglass enable_block STARC05-1.3.1.3
////////////////////////////////////////////////////////////////////////////
//
assign i_dbg_address = (dbg_prot_sel) ? {i_paddr_r, 2'b0} : dbg_address;
assign i_dbg_wdata   = (dbg_prot_sel) ? i_pwdata_r : dbg_wdata;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous process to determine next values and write enables for    //
// all of the debug registers.                                            //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

wire   db_status_ready = db_ready_r
                       ;

always @*
begin : db_next_PROC

  // Decode the incoming BVCI address
  //
  db_space_sel   = (dbg_prot_sel == 1'b1) 
                 ? (i_psel_r && ((i_dbg_address[11:5] == 7'b0) && (~i_dbg_address[4] || i_dbg_address[3:0]== 4'b0)))
                 : (dbg_address[31:8] == DB_SPACE);
  dbp_space_sel   = (i_dbg_address[31:8] == DBP_SPACE);
  db_addr_match  = 1'b0;

  // Detect the reset command in DB_CMD
  //
  reset_db       = (db_cmd_r == DB_RST_CMD);

  db_addr_enb    = 1'b0;
// spyglass disable_block Ac_conv01
// SMD: synchronizers converge on combinational gate
// SJ:  functionally independent signals
  db_data_enb    = ((db_fsm_r == DB_FSM_RELOAD) & hlt_debug_evt)
                   ;
// spyglass enable_block Ac_conv01
  db_cmd_enb     = 1'b0;
  db_reset_enb   = 1'b0;
  db_failed_enb  = (   (db_fsm_r == DB_FSM_RELOAD)
                       & (wa_commit_dbg | wa_invalid_instr_r))
                   ;
  db_ready_enb   = 1'b1;

  // Set the default next-register values
  //
  db_addr_nxt    = `npuarc_ADDR_SIZE'd0;

  db_data_nxt    =   reset_db                  ? `npuarc_DATA_SIZE'd0
                   : (db_cmd_r == DB_MEM_RD)   ? wa_rf_wdata1_lo_r
                      : wa_rf_wdata0_lo_r
                     ;

  db_cmd_nxt     = DB_RST_CMD;
  db_reset_nxt   = 2'b00;
  db_failed_nxt  = wa_invalid_instr_r;
  db_ready_nxt   = (db_fsm_r == DB_FSM_IDLE);

  // Decode the Read and Write commands
  //
  // spyglass disable_block Ac_conv02 Ac_conv01
  // SMD: Combinational Convergence of same domain synchronized signals
  // SMD: Synchronizers converging on combonational gate
  // SJ:  CDC accross pseudo-bvci interface handled by protocol/clk ratio
  bvci_read      = (dbg_prot_sel) ? (i_penable_r & i_psel_r & ~i_pwrite_r & i_dbgen_r) :
                                    (dbg_cmdval & (dbg_cmd == `npuarc_BVCI_CMD_RD));
  bvci_write     = (dbg_prot_sel) ? (i_penable_r & i_psel_r & i_pwrite_r & i_dbgen_r & ~i_pwrite_pulse_r) :
                                    (dbg_cmdval & (dbg_cmd == `npuarc_BVCI_CMD_WR));
  // spyglass enable_block Ac_conv02 Ac_conv01

  // Set the error condition default values
  //
  db_cmd_err     = (dbg_prot_sel) ? 1'b0 :
                   (dbg_cmdval & (~(bvci_read | bvci_write)));
  db_read_err    = 1'b0;
  db_be_err      = (dbg_prot_sel) ? 1'b0 :
                   (dbg_cmdval & (~(&dbg_be)));

  // Set the default value of dbg_rdata to avoid latch inference.
  //
  i_dbg_rdata    = `npuarc_DATA_SIZE'd0;

  // Determine whether a debug reset should take place.
  //
  do_db_reset    = 1'b0;

  // Set the default value of do_execute to false
  //
  do_execute     = 1'b0;


  // If dbg_cmdval == 1'b1, then enable the register for update
  // that is addressed by dbg_address, and set its next value
  // from dbg_wdata.
  //
  if (db_space_sel == 1'b1)
    begin
      case ( i_dbg_address[7:0] )
      DB_STAT: // read-only, but synonymous with DB_EXEC when writing
          begin
          db_addr_match = 1'b1;
          i_dbg_rdata     = { 26'd0,          // Reserved bits, read as zero
                            dbg_ra_r,         // RA (bit 5)
                            !gb_sys_halt_r,   // RU (bit 4)
                            1'b0,             // PC (bit 3) is always 0
                            db_status_ready,  // RD (bit 2)
                            db_failed_r,      // FL (bit 1)
                            !db_status_ready  // ST (bit 0)
                          };
          do_execute    = bvci_write & db_status_ready & (~reset_db);

          // When initiating a debug operation, clear db_failed_r
          // and clear db_ready_r (making it busy).
          //
          if (do_execute == 1'b1)
            begin
            db_failed_nxt = 1'b0;
            db_failed_enb = 1'b1;
            db_ready_nxt  = 1'b0;
            db_ready_enb  = 1'b1;
            end
          end

      DB_CMD:
          if (db_status_ready == 1'b1)
            begin
            db_addr_match = 1'b1;
            db_cmd_enb    = bvci_write;
            db_cmd_nxt    = i_dbg_wdata[3:0];
            i_dbg_rdata   = { 28'd0, db_cmd_r };
            end

      DB_DATA:
          if (db_status_ready == 1'b1)
            begin
            db_addr_match = 1'b1;
            db_data_enb   = bvci_write;
            db_data_nxt   = i_dbg_wdata;
            i_dbg_rdata   = db_data_r;
            end

      DB_ADDR:
          if (db_status_ready == 1'b1)
            begin
            db_addr_match = 1'b1;
            db_addr_enb   = bvci_write;
            db_addr_nxt   = i_dbg_wdata;
            i_dbg_rdata   = db_addr_r;
            end

      DB_RESET:
          if (db_status_ready == 1'b1)
            begin
            db_addr_match = 1'b1;
            do_db_reset   = bvci_write;
            db_reset_enb  = bvci_write;
            db_reset_nxt  = i_dbg_wdata[1:0];
            db_read_err   = bvci_read;
            end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept
      default: ; // do nothing, as db_addr_match is set to 0 by default
      endcase
    end
// spyglass enable_block W193

  if (dbp_space_sel == 1'b1)
    begin
      case ( i_dbg_address[7:0] )
      DB_CSR1:
          if (db_ready_r == 1'b1)
            begin
            db_addr_match = 1'b1;
            db_data_enb   = 1'b0;
            i_dbg_rdata   = db_csr1[`npuarc_DBL_LO_RANGE];
            end

      DB_CSR2:
          if (db_ready_r == 1'b1)
            begin
            db_addr_match = 1'b1;
            db_data_enb   = 1'b0;
            i_dbg_rdata   = db_csr2[`npuarc_DBL_LO_RANGE];
            end

      DB_CSR3,
      DB_CSR4,
      DB_CSR5:
          if (db_ready_r == 1'b1)
            begin
            db_addr_match = 1'b1;
            db_data_enb   = 1'b0;
            i_dbg_rdata   = db_csr3[`npuarc_DBL_LO_RANGE];
            end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept
      default: ; // do nothing, as db_addr_match is set to 0 by default
      endcase
    end
// spyglass enable_block W193

  // for jtag, ack will be immed (clk already on)
// spyglass disable_block Ac_conv01
// SMD: cdc sync signals converging on combinational gate
// SJ:  cdc syncs are independent and chance of glitch is very low
  dbg_cmdack = dbg_cmdval 
             & ar_clock_enable_r 
             & reset_done_r
             & l1_clock_active
              ; 
// spyglass enable_block Ac_conv01
  // If reset register is written, enable all registers to receive
  // their reset values. No need to wait for outstanding operation
  // to complete.
  //
  if (do_db_reset == 1'b1)
    begin
    db_ready_nxt  = 1'b1;
    db_addr_enb   = 1'b1;
    db_data_enb   = 1'b1;
    db_ready_enb  = 1'b1;
    db_failed_enb = 1'b1;
    db_failed_nxt = 1'b0;
    end

  // It is an address error if the address of a request from the
  // BVCI bus does not match one of the debug registers.
  //
  db_addr_err   = dbg_cmdval & (~db_addr_match);

end

// register any_err (dbg_rerr) to avoid in2out timing critical path
always @(posedge clk or posedge rst_a)
begin : db_any_err_PROC
  if (rst_a == 1'b1) begin
    db_any_err <= 1'b0;
  end
  else begin
    db_any_err <= db_addr_err
                | db_cmd_err
                | db_read_err
                | db_be_err
                | (db_any_err & ~dbg_rspack)
                ;
  end
end

wire [7:0] rtt_bcr = {`npuarc_ARC_RTT_VERSION};


reg  [4-1:0] claimtag;
wire [4-1:0] claimtag_ns;
wire [4-1:0] claimset;
wire [4-1:0] claimset_qual;
wire [4-1:0] claimclr_qual;
assign claimset = {4{1'b1}};
assign claimset_qual = claimset & i_dbg_wdata[4-1:0];
assign claimclr_qual = claimset ^ i_dbg_wdata[4-1:0];
assign claimtag_ns = (i_dbg_address[11:0] == 12'hFA0) ? (claimtag | claimset_qual) :   //claimset write 1 to set
                     (i_dbg_address[11:0] == 12'hFA4) ? (claimtag & claimclr_qual) :   //claimclr write 1 to clear
                     claimtag;
always @(posedge clk or negedge presetdbgn)
begin
  if (presetdbgn == 1'b0)
  begin
    claimtag   <= {(4-1){1'b0}};
  end
  else if (bvci_write && ((i_dbg_address[11:0] == 12'hFA0) || (i_dbg_address[11:0] == 12'hFA4))) begin
    claimtag   <= claimtag_ns;
  end
end

wire [7:0] i_authstatus;

assign i_authstatus[7:6] = 2'b00;
assign i_authstatus[5:4] = 2'b00;
// spyglass disable_block Ac_conv01
// SMD: synchronizers converge on combinational gate
// SJ:  functionally independent signals
assign i_authstatus[3:2] = (i_niden_r | i_dbgen_r) ? 2'b11 : 2'b10;
// spyglass enable_block Ac_conv01
assign i_authstatus[1:0] = (i_dbgen_r) ? 2'b11 : 2'b10;

always @*
begin : ROM_table_regs_PROC

  case (i_dbg_address[11:0])
     12'hF00: i_csr_a = {31'h00000000, 1'b0};  // ITCTRL
     12'hFA0: i_csr_a = {{(32-4){1'b0}}, claimset}; // CLAIMSET bits implemented
     12'hFA4: i_csr_a = {{(32-4){1'b0}}, claimtag}; // CLAIMCLR return claimtag bits on read
     12'hFA8: i_csr_a = 32'h0000000;           // DEVAFF0
     12'hFAC: i_csr_a = 32'h0000000;           // DEVAFF1
     12'hFB0: i_csr_a = 32'h0000000;           // LAR, WO
     12'hFB4: i_csr_a = {29'h0000000,1'b0,1'b0,1'b0}; // LSR
     12'hFB8: i_csr_a = {24'h000000, i_authstatus};  // AUTHSTATUS
     12'hFBC: i_csr_a = {11'h258,1'b1,4'h0,16'h0101};  // DEVARCH
     12'hFC0: i_csr_a = 32'h0000000;              // DEVID2
     12'hFC4: i_csr_a = {24'h0,rtt_bcr};        // DEVID1
     12'hFC8: i_csr_a = {`npuarc_CHIPID,arcnum,`npuarc_ARCVER}; // DEVID
     12'hFCC: i_csr_a = {32'h000000, 8'h15};   // DEVTYPE
     12'hFD0: i_csr_a = {32'h000000, 8'h04};   // PIDR4
     12'hFD4: i_csr_a = {32'h000000, 8'h00};   // PIDR5
     12'hFD8: i_csr_a = {32'h000000, 8'h00};   // PIDR6
     12'hFDC: i_csr_a = {32'h000000, 8'h00};   // PIDR7
     12'hFE0: i_csr_a = {32'h000000, 8'h01};   // PIDR0
     12'hFE4: i_csr_a = {32'h000000, 8'h80};   // PIDR1
     12'hFE8: i_csr_a = {32'h000000, 8'h0D};   // PIDR2
     12'hFEC: i_csr_a = {32'h000000, 8'h00};   // PIDR3
     12'hFF0: i_csr_a = {32'h000000, 8'h0D};   // CIDR0
     12'hFF4: i_csr_a = {32'h000000, 8'h90};   // CIDR1
     12'hFF8: i_csr_a = {32'h000000, 8'h05};   // CIDR2
     12'hFFC: i_csr_a = {24'h000000, 8'hB1};   // CIDR3
     default: i_csr_a = i_dbg_rdata;
  endcase 

end
        
assign dbg_rdata = i_csr_a;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous process to encode the next debug instruction to issue     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg   [`npuarc_DATA_RANGE]  b_reg_opd;
reg   [`npuarc_DATA_RANGE]  c_reg_opd;
reg   [`npuarc_DATA_RANGE]  instr;

always @*
begin : db_inst_PROC

  // Encode the register operand from db_addr_r[5:0] according to the
  // B and C field syntax, as used by the MOV instruction.
  //
  b_reg_opd = { 5'd0,  db_addr_r[2:0], 9'd0, db_addr_r[5:3], 12'd0 };
  c_reg_opd = { 20'd0, db_addr_r[5:0], 6'd0 };

  // Select the required instruction + encoded B or C register
  // which will later be enabled on the db_inst output in middle-endian
  // byte ordering.
  //
  case ( db_cmd_r )
    DB_MEM_WR:  instr = INST_MEMWR;
    DB_CORE_WR: instr = INST_COREWR | b_reg_opd;
    DB_AUX_WR:  instr = INST_AUXWR;
    DB_MEM_RD:  instr = INST_MEMRD;
    DB_CORE_RD: instr = INST_CORERD | c_reg_opd;
    DB_AUX_RD:  instr = INST_AUXRD;
    default:    instr = INST_NOP;
  endcase
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous process to define the debug execution FSM, which issues   //
// debug instructions into the processor pipeline.                        //
//                                                                        //
// There are five states in this FSM. The reset state is DB_FSM_IDLE.     //
//                                                                        //
//  DB_FSM_IDLE   : In this state the instruction-issue FSM for the debug //
//                  unit is idle. The CPU is free to fetch and execute    //
//                  its own instructions according to normal operation.   //
//                  It remains in this state until the do_execute signal  //
//                  is asserted, when it moves into the  DB_FSM_AIM state //
//                                                                        //
//  DB_FSM_AIM    : In this state the db_request signal is asserted, and  //
//                  this causes the CPU to respond by flushing the        //
//                  pipeline. The state-machine detects this by           //
//                  monitoring the debug_evt signal. When asserted, it    //
//                  moves into the DB_FSM_FIRE state to issue the debug   //
//                  instruction.                                          //
//                                                                        //
//  DB_FSM_FIRE   : In this state the db_valid, the db_active and the     //
//                  db_fetch signals are asserted. The db_valid signal    //
//                  tells the Fetch stage to accept db_inst as the next   //
//                  instruction to be issued. The db_fetch signal         //
//                  prevents normal instruction fetching. The db_active   //
//                  signal indicates to all pipeline stages that any      //
//                  valid instruction they see must be treated as a debug //
//                  instruction.                                          //
//                                                                        //
//  DB_FSM_LIMM   : In this state the db_valid, the db_active, and the    //
//                  db_fetch signals are asserted, and the LIMM operand   //
//                  for the debug instruction is output on the db_inst    //
//                  signals.                                              //
//                  The pipeline will accept db_inst as the LIMM data     //
//                  for the debug instruction during this cycle.          //
//                                                                        //
//  DB_FSM_RELOAD : In this state the db_active and db_fetch signals      //
//                  continue to be asserted, thereby keeping the pipeline //
//                  free of other instructions until the debug            //
//                  instruction is finished.                              //
//                  The FSM remains in this state until the wa_commit_dbg //
//                  signal is asserted, indicating that the current debug //
//                  instruction is in the final (writeback) stage.        //
//                  On exit from this state, the db_data_r register is    //
//                  updated with either wa_rf_wdata0 or wa_rf_wdata1,     //
//                  depending on the type of instruction (load vs mov/lr) //
//                  and the FSM moves to the DB_FSM_END state.            //
//                  When performing a Store instruction, to write to      //
//                  memory, the db_data value must be forced onto the     //
//                  store_opd wires in the operands module. This is       //
//                  achieved by asserting db_sel_limm1. A similar thing   //
//                  happens for SR instructions, to write to aux          //
//                  registers, in which case the db_sel_limm0 signals is  //
//                  asserted to force db_data into opd1_early and thence  //
//                  to opd_1 (in the operands module).                    //
//                                                                        //
//  DB_FSM_END    : In this state the db_active signal remains asserted,  //
//                  to prevent unwanted state updates in the writeback    //
//                  stage, and the db_request signal is asserted for one  //
//                  cycle to restart the pipeline from the correct PC.    //
//                  The db_fetch signal is de-asserted to allow the Fetch //
//                  stage to begin fetching on the next cycle from the    //
//                  restart PC address.                                   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg   [`npuarc_DATA_RANGE]  issue_word;

always @*
begin : db_fsm_PROC

  issue_word   = instr;
  db_addr_incr = 1'b0;
  db_active    = 1'b0;
  db_request   = 1'b0;
  db_valid     = 1'b0;
  db_sel_limm0 = 1'b0;
  db_sel_limm1 = 1'b0;

  db_fsm_nxt = db_fsm_r;    // remain in current state by default

  case ( db_fsm_r )
    DB_FSM_IDLE:
      begin
        if (do_execute == 1'b1
            )
        begin
          db_fsm_nxt = DB_FSM_AIM;
        end          
      end

    DB_FSM_AIM:
      begin
        db_request = 1'b1;  // request a pipeline flush prior to debug insn
        if (hlt_debug_evt == 1'b1)
          db_fsm_nxt = DB_FSM_FIRE;
      end

    DB_FSM_FIRE:
      begin
        db_valid   = 1'b1;  // validate debug inst and limm to Fetch stage
        db_active  = 1'b1;  // inform pipeline that debug is active
        if (db_cmd_r == DB_CORE_RD)
          db_fsm_nxt = DB_FSM_RELOAD;
        else
          db_fsm_nxt = DB_FSM_LIMM;
      end

    DB_FSM_LIMM:
      begin
        // Select db_data_r or db_addr_r as LIMM value to be issued
        // for current debug instruction, depending on the command.
        // All commands except DB_CORE_WR use db_addr_r as their LIMM
        // value. DB_CORE_WR uses db_data_r as the LIMM value.
        //
        db_active  = 1'b1;  // inform pipeline that debug is active
        db_fsm_nxt = DB_FSM_RELOAD;
      end

    DB_FSM_RELOAD:
      begin
        db_active    = 1'b1;  // inform pipeline that debug is active
        db_sel_limm0 = (db_cmd_r == DB_AUX_WR);
        db_sel_limm1 = (db_cmd_r == DB_MEM_WR);

        if (hlt_debug_evt == 1'b1)
          db_fsm_nxt = DB_FSM_END;
       else if (db_restart == 1'b1)
          db_fsm_nxt = DB_FSM_FIRE;

        // Process db_next_PROC detects wa_commit in this state and uses
        // it to enable the update of db_data_r with the result value.
      end

    DB_FSM_END:
      begin
        db_addr_incr = 1'b1;  // increment addr for all ops
        db_active    = 1'b1;
        db_fsm_nxt   = DB_FSM_IDLE;
      end

// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept
    default: ;
  endcase
// spyglass enable_block W193

  // Assign db_inst to be the middle-endian version of issue_word
  //
  db_inst = issue_word;
  db_data = db_data_r;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Aynchronous processes to define clock enable output                    //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
always @*
begin : clock_enable_PROC
  db_clock_enable_nxt = (
                         (dbg_cmdval & !dbg_prot_sel)
                      | ((pseldbg | i_psel_r) & dbg_prot_sel)
                      | (db_fsm_r != DB_FSM_IDLE)
                      | rspval_r)
                      ;  // Debug instruction flowing in the pipe
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous processes to define next state of rspval signal            //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : rspval_nxt_PROC
  rspval_nxt =(   (    dbg_cmdval 
                  &    dbg_cmdack
                  & l1_clock_active
                  )  
              |  (   rspval_r 
                  & (~dbg_rspack)
                 )
              )
              ;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous processes to define each of the Debug registers            //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

// -- the debug command register DB_CMD

// leda NTL_CLK05 off
// LMD: All asynchronous inputs to a clock system must be clocked twice.
// LJ:  CDC accross pseudo-bvci interface handled by protocol/clk ratio
// spyglass disable_block Ac_cdc04a Ac_conv01 Ac_unsync02 Ar_resetcross01
// SMD: detect clock-domain crossings where there is a possibility of data 
// being unstable when an enable is active.
// SJ:  CDC accross pseudo-bvci interface handled by protocol/clk ratio
//
always @(posedge clk or posedge rst_a)
begin : db_cmd_PROC
  if (rst_a == 1'b1)
    db_cmd_r  <=  DB_RST_CMD;
  else if (db_cmd_enb == 1'b1)
    db_cmd_r  <=  db_cmd_nxt;
end

// -- the debug address register DB_ADDR

wire [`npuarc_DATA_RANGE] db_addr_inter = {
  db_addr_enb ? db_addr_nxt : (db_addr_incr ? db_addr_plus_stp : db_addr_r)
};

/*
always @*
begin : db_addr_inter_PROC
  if (db_addr_enb == 1'b1)
  begin
    db_addr_inter  =  db_addr_nxt; 
  end  
  else if (db_addr_incr)
  begin
    db_addr_inter  = db_addr_plus_stp; 
  end   
end
*/

always @(posedge clk or posedge rst_a)
begin : db_addr_PROC
  if (rst_a == 1'b1)
  begin
    db_addr_r  <=  `npuarc_DATA_SIZE'd0;
  end
  else
  begin
    db_addr_r  <= db_addr_inter; 
    end  
  end  

// -- the debug data register DB_DATA

always @(posedge clk or posedge rst_a)
begin : db_data_PROC
  if (rst_a == 1'b1)
    db_data_r  <=  `npuarc_DATA_SIZE'd0;
  else if (db_data_enb == 1'b1)
    db_data_r  <=  db_data_nxt;
end

// -- the debug ready bit DB_STAT.RD  (DB_STAT[2])
// spyglass disable_block FlopEConst
// SMD: Enable pin is always high/low 
// SJ:  Done on purpose
always @(posedge clk or posedge rst_a)
begin : db_ready_PROC
  if (rst_a == 1'b1)
    db_ready_r  <=  1'b0;
  else if (db_ready_enb == 1'b1)
    db_ready_r  <=  db_ready_nxt;
end
// spyglass enable_block FlopEConst
// -- the debug operation failed bit DB_STAT.FL (DB_STAT[1])

always @(posedge clk or posedge rst_a)
begin : db_failed_PROC
  if (rst_a == 1'b1)
    db_failed_r  <=  1'b0;
  else if (db_failed_enb == 1'b1)
    db_failed_r  <=  db_failed_nxt;
end

// When the debugger writes 1 to either bit 1 or bit 0 of the DB_RESET
// register, a reset request is sent to the top-level system reset_ctrl
// module. This leads to the asynchronous assertion of rst_a, which in
// turn will clear the db_reset_r register. However, the reset_ctrl
// module keeps the rst_a signal asserted for a certain minimum period
// to ensure all flip-flops are properly cleared.
//
// In this implementation, there is no distinction between a CPU reset
// and a system reset.
//
always @(posedge clk or posedge rst_a)
begin : db_reset_PROC
  if (rst_a == 1'b1)
    db_reset_r  <=  2'b00;
  else if (db_reset_enb == 1'b1)
    db_reset_r  <=  db_reset_nxt;
end


always @(posedge clk or posedge rst_a)
begin : reset_done_PROC
  if (rst_a == 1'b1)
    reset_done_r  <=  1'b0;
  else
    reset_done_r  <=  1'b1;
end


// -- the debug execution state variable

always @(posedge clk or posedge rst_a)
begin : db_state_PROC
  if (rst_a == 1'b1) begin
    db_fsm_r      <=  3'd0;
    rspval_r      <=  1'b0;
    end
  else begin
    db_fsm_r      <=  db_fsm_nxt;
    rspval_r      <=  rspval_nxt;
    end
end
//
// leda NTL_CLK05 on
// spyglass enable_block Ac_cdc04a Ac_conv01 Ac_unsync02 Ar_resetcross01
//

//
// 
// 

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Output assignments                                                     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

assign dbg_rspval  = rspval_r;                 // rspval signal back to host
assign dbg_reop    = rspval_r;                 // reflect EOP to originator
assign dbg_rerr    = db_any_err;               // report any errors
assign debug_reset = (|db_reset_r)
//`if (`DBG_APB_OPTION == 1) //{
//                      & (dbg_rspack | dbg_prot_sel)
//`else
//                      & dbg_rspack
//`endif //}
                   ;// dbg reset for the system

assign db_limm     = ((db_cmd_r == DB_CORE_WR)
                   ? db_data_r
                   : db_addr_r)
                   ;


// spyglass enable_block Ac_fifo01

endmodule

