// Library ARC_Trace-3.0.999999999
// Copyright (C) 2019 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//   arct_apb_if
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o arct_dbg_if.vpp
//
// ===========================================================================
`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"

module npuarc_arct_dbg_if (
  input                         pclkdbg,
  input                         pclkdbg_en,
  input                         presetdbgn,
  input [31:2]                  paddrdbg,
  input                         pseldbg,
  input                         penabledbg,
  input                         pwritedbg,
  input [31:0]                  pwdatadbg,

  output wire                   preadydbg,
  output wire [31:0]            prdatadbg,
  output wire                   pslverrdbg,

  input                         dbgen,
  input                         niden,

  input [31:0]                  rtt_datar,
  input [`npuarc_AUX_DATA-1:0]         rtt_bcr_pad,
  output wire                   rtt_write,
  output wire                   rtt_read,
  output wire [31:0]            rtt_addr,
  output wire [31:0]            rtt_dataw,
  input                         has_rtt_iso_disable
);

localparam DB_AUX_WR    = 4'h2;
localparam DB_AUX_RD    = 4'h6;
localparam DB_RST_CMD   = 4'h3;

// Define the debug register addresses
//
// @d:dbg_addrs:Debug auxiliary register addresses
localparam rtt_verh = `npuarc_RTT_VERSION >>4;
localparam rtt_verl = `npuarc_RTT_VERSION;
localparam DB_CSR1_PARM     = 32'h0000_0090;
localparam DB_CSR2_PARM     = {rtt_verl[3:0],20'h4B0_00,rtt_verh[3:0],4'h2};
localparam DB_CSR3_PARM     = 32'h0;
localparam DB_CSR4_PARM     = 32'h0;
localparam DB_CSR5_PARM     = 32'h0;

localparam DB_SPACE    = 24'hffff00;
localparam DB_STAT     = 8'h00;
localparam DB_CMD      = 8'h04;
localparam DB_ADDR     = 8'h08;
localparam DB_DATA     = 8'h0c;
localparam DB_DATA_HI  = 8'h14;
localparam DB_RESET    = 8'h10;

reg  [31:2]                 i_paddr_r;
reg  [31:0]                 i_pwdata_r;
reg                         i_pwrite_r;
reg                         i_psel_r;
reg                         i_penable_r;
reg                         i_penable_r1;
wire                        i_ready;
wire [31:0]                 i_data;
wire [31:0]                 dbg_rdata;
wire [31:0]                 arct_apb2rom_address;
reg  [31:0]                 i_csr_a;

reg                         i_dbgen_r;
reg                         i_niden_r;

wire [7:0]                  i_authstatus;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Debug registers                                                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg   [31:0]                db_addr_r;        // Debug Address Register
reg   [31:0]                db_data_r;        // Debug Data Register
reg   [3:0]                 db_cmd_r;         // Debug Command Register
reg                         db_ready_r;       // 0=>executing; 1=>ready
reg   [2:0]                 db_fsm_r;         // execution FSM state var.
reg   [31:0]                db_status;

wire                        db_addr_incr;     // Incr.debug register 
wire  [31:0]                db_addr_plus_stp; // Debug addr reg + 4 or + 1
wire                        unused_cout;
reg   [31:0]                db_addr_nxt;      // Debug Address next value
reg   [31:0]                db_data_nxt;      // Debug Data next value
reg   [3:0]                 db_cmd_nxt;       // Debug Command next value

reg db_status_ready;
reg db_space_sel;
reg db_addr_enb;
reg db_data_enb;
reg db_cmd_enb;
reg db_ready_nxt;
reg db_ready_enb;
reg do_db_reset;

wire apb_read;
wire apb_write;
wire lsr_sli;

reg  [4-1:0] claimtag;
wire [4-1:0] claimtag_ns;
wire [4-1:0] claimset;
wire [4-1:0] claimset_qual;
wire [4-1:0] claimclr_qual;

wire              lsr_slk;
assign            lsr_sli = 1'b0;
assign            lsr_slk = 1'b0;

assign i_authstatus[7:6] = 2'b00;
assign i_authstatus[5:4] = 2'b00;
// spyglass disable_block Ac_conv01
// SMD: synchronizers converge on combinational gate
// SJ:  functionally independent signals
assign i_authstatus[3:2] = (i_niden_r | i_dbgen_r) ? 2'b11 : 2'b10;
assign i_authstatus[1:0] = (i_dbgen_r) ? 2'b11 : 2'b10;
// spyglass enable_block Ac_conv01

always @(posedge pclkdbg or negedge presetdbgn)
begin
  if (presetdbgn == 1'b0)
  begin
    i_paddr_r <= 30'b0;
    i_pwrite_r <= 1'b0;
    i_pwdata_r <= 32'b0;
    i_penable_r <= 1'b0;
    i_penable_r1 <= 1'b0;
    i_psel_r <= 1'b0;
  end
  else
  if (pclkdbg_en)
  begin
    i_paddr_r <= paddrdbg;
    i_pwrite_r <= pwritedbg;
    i_pwdata_r <= pwdatadbg;
    i_penable_r <= penabledbg;
    i_penable_r1 <= i_penable_r & penabledbg;
    i_psel_r <= pseldbg;
  end
end

assign prdatadbg = dbg_rdata;
assign preadydbg = ~(i_psel_r & ~i_penable_r1);

assign pslverrdbg = 1'b0; // No error responses

// Authentication interface registers
always @(posedge pclkdbg or negedge presetdbgn)
begin
  if (presetdbgn == 1'b0)
  begin
    i_dbgen_r   <= 1'b0;
    i_niden_r   <= 1'b0;
  end
  else
  if (pclkdbg_en)
  begin
    i_dbgen_r   <= dbgen;
    i_niden_r   <= niden;
  end
end

////////////////////////////////////////////////////////////////////////////
//
assign rtt_addr = has_rtt_iso_disable ? db_addr_r : 32'b0;
assign arct_apb2rom_address = {i_paddr_r, 2'b0};
assign rtt_dataw   = has_rtt_iso_disable ? db_data_r : 32'b0;

////////////////////////////////////////////////////////////////////////////
// spyglass disable_block Ac_conv01
// SMD: synchronizers converge on combinational gate
// SJ:  functionally independent signals
assign apb_write = i_pwrite_r & i_psel_r & (i_dbgen_r||i_niden_r) & ~i_penable_r;
assign apb_read = ~i_pwrite_r & i_psel_r & (i_dbgen_r||i_niden_r) & ~i_penable_r;
// spyglass enable_block Ac_conv01

assign rtt_write = has_rtt_iso_disable ? ((db_cmd_r == DB_AUX_WR) & db_ready_r) : 1'b0;
assign rtt_read  = has_rtt_iso_disable ? ((db_cmd_r == DB_AUX_RD) & db_ready_r) : 1'b0;

////////////////////////////////////////////////////////////////////////////

// spyglass disable_block W193
// SMD: Empty statement
// SJ:  Default case intentionally left empty.
always @*
begin : db_next_PROC

  // Decode the incoming apb address
  //
// spyglass disable_block Ac_conv01
// SMD: synchronizers converge on combinational gate
// SJ:  functionally independent signals
  db_space_sel   = (i_psel_r && (i_dbgen_r||i_niden_r) && ((arct_apb2rom_address[11:5] == 7'b0) && (~arct_apb2rom_address[4] || arct_apb2rom_address[3:0]== 4'b0)));
// spyglass enable_block Ac_conv01
  db_ready_enb   = 1'b0;

  db_addr_enb    = 1'b0;
// spyglass disable_block Ac_conv01
// SMD: synchronizers converge on combinational gate
// SJ:  functionally independent signals
  db_data_enb    = rtt_read;
// spyglass enable_block Ac_conv01
  db_cmd_enb     = 1'b0;

  // Set the default next-register values
  //
  db_addr_nxt    = `npuarc_ADDR_SIZE'd0;

  db_data_nxt    =   rtt_datar;

  db_cmd_nxt     = DB_RST_CMD;
  db_ready_nxt   = 1'b0;

  // Determine whether a debug reset should take place.
  //
  do_db_reset    = 1'b0;
  
  db_status_ready = 1'b1;
  db_status       = 32'b0;

  // If dbg_cmdval == 1'b1, then enable the register for update
  // that is addressed by dbg_address, and set its next value
  // from dbg_wdata.
  //
  if (db_space_sel == 1'b1)
    begin
      case ( arct_apb2rom_address[7:0] )
      DB_STAT: // read-only, but synonymous with DB_EXEC when writing
          begin
          db_status     = { 26'd0,            // Reserved bits, read as zero
                            1'b0,             // RA (bit 5)
                            1'b0,             // RU (bit 4)
                            1'b0,             // PC (bit 3) is always 0
                            db_status_ready,  // RD (bit 2)
                            1'b0,             // FL (bit 1)
                            !db_status_ready  // ST (bit 0)
                          };
          if (db_status_ready == 1'b1)
            begin
            db_ready_nxt  = apb_write;
            db_ready_enb  = 1'b1;
            end
          end

      DB_CMD:
          if (db_status_ready == 1'b1)
            begin
            db_cmd_enb    = apb_write;
            db_cmd_nxt    = i_pwdata_r[3:0];
            end

      DB_DATA:
          if (db_status_ready == 1'b1)
            begin
            db_data_enb   = apb_write;
            db_data_nxt   = i_pwdata_r;
            end


      DB_ADDR:
          if (db_status_ready == 1'b1)
            begin
            db_addr_enb   = apb_write;
            db_addr_nxt   = i_pwdata_r;
            end

      default: ; // do nothing
      endcase
    end
end
// spyglass enable_block W193

// -- the debug command register DB_CMD

// leda NTL_CLK05 off
// LMD: All asynchronous inputs to a clock system must be clocked twice.
// LJ:  CDC accross pseudo-bvci interface handled by protocol/clk ratio
// spyglass disable_block Ac_cdc04a, Ac_conv01, Ac_unsync02, Ar_resetcross01, Ac_glitch04
// SMD: detect clock-domain crossings where there is a possibility of data 
// being unstable when an enable is active.
// SJ:  CDC accross pseudo-bvci interface handled by protocol/clk ratio
//
always @(posedge pclkdbg or negedge presetdbgn)
begin : db_cmd_PROC
  if (presetdbgn == 1'b0)
    db_cmd_r  <=  DB_RST_CMD;
  else if ((pclkdbg_en) && (db_cmd_enb == 1'b1))
    db_cmd_r  <=  db_cmd_nxt;
end

// -- the debug address register DB_ADDR

// Compute db_addr_r + 1 (regs) for incrementing addresses
//
// leda B_3208 off
// LMD: Unequal length LHS and RHS in assignment
// LJ: arithmetic calculation has a potential dont_care carry bit
assign { unused_cout, db_addr_plus_stp} = db_addr_r + 1;
// leda B_3208 on

assign db_addr_incr = db_ready_r;
wire [31:0] db_addr_inter = {
  db_addr_enb ? db_addr_nxt : (db_addr_incr ? db_addr_plus_stp : db_addr_r)
};

always @(posedge pclkdbg or negedge presetdbgn)
begin : db_addr_PROC
  if (presetdbgn == 1'b0)
  begin
    db_addr_r  <=  `npuarc_DATA_SIZE'd0;
  end
  else if ((pclkdbg_en) && (db_addr_enb))
  begin
    db_addr_r  <= db_addr_nxt; 
  end  
  else if ((pclkdbg_en) && (db_addr_incr))
  begin
    db_addr_r  <= db_addr_plus_stp; 
  end  
end

// -- the debug data register DB_DATA

always @(posedge pclkdbg or negedge presetdbgn)
begin : db_data_PROC
  if (presetdbgn == 1'b0)
    db_data_r  <=  32'd0;
  else if ((pclkdbg_en) && (db_data_enb == 1'b1))
    db_data_r  <=  db_data_nxt;
end


// -- the debug ready bit DB_STAT.RD  (DB_STAT[2])
// spyglass disable_block FlopEConst
// SMD: Enable pin is always high/low 
// SJ:  Done on purpose
always @(posedge pclkdbg or negedge presetdbgn)
begin : db_ready_PROC
  if (presetdbgn == 1'b0)
    db_ready_r  <=  1'b0;
  else if ((pclkdbg_en) && (db_ready_enb == 1'b1))
    db_ready_r  <=  db_ready_nxt;
end
// spyglass enable_block FlopEConst

// leda NTL_CLK05 on
// spyglass enable_block Ac_cdc04a, Ac_conv01, Ac_unsync02, Ar_resetcross01, Ac_glitch04
//

assign claimset = {4{1'b1}};
assign claimset_qual = claimset & i_pwdata_r[4-1:0];
assign claimclr_qual = claimset ^ i_pwdata_r[4-1:0];
assign claimtag_ns = (arct_apb2rom_address[11:0] == 12'hFA0) ? (claimtag | claimset_qual) :   //claimset write 1 to set
                     (arct_apb2rom_address[11:0] == 12'hFA4) ? (claimtag & claimclr_qual) :   //claimclr write 1 to clear
                     claimtag;
always @(posedge pclkdbg or negedge presetdbgn)
begin
  if (presetdbgn == 1'b0)
  begin
    claimtag   <= {(4-1){1'b0}};
  end
  else if (apb_write && ((arct_apb2rom_address[11:0] == 12'hFA0) || (arct_apb2rom_address[11:0] == 12'hFA4)))
  begin
    claimtag   <= claimtag_ns;
  end
end


always @*
begin : ROM_table_regs_PROC

  case (arct_apb2rom_address[11:0])
     12'h000: i_csr_a = db_status;             // DB_STATUS
     12'h004: i_csr_a = { 28'd0, db_cmd_r };   // DB_CMD
     12'h008: i_csr_a = db_addr_r;             // DB_ADDR
     12'h00C: i_csr_a = db_data_r;             // DB_DATA
     12'h400: i_csr_a = DB_CSR1_PARM;          // DB_CSR1
     12'h404: i_csr_a = DB_CSR2_PARM;          // DB_CSR2
     12'h408: i_csr_a = DB_CSR3_PARM;          // DB_CSR3
     12'h40c: i_csr_a = DB_CSR4_PARM;          // DB_CSR4
     12'h410: i_csr_a = DB_CSR5_PARM;          // DB_CSR5
     12'hF00: i_csr_a = {31'h00000000, 1'b0};  // ITCTRL
     12'hFA0: i_csr_a = {{(32-4){1'b0}}, claimset}; // CLAIMSET bits implemented
     12'hFA4: i_csr_a = {{(32-4){1'b0}}, claimtag}; // CLAIMCLR return claimtag bits on read
     12'hFA8: i_csr_a = 32'h00000000;          // DEVAFF0
     12'hFAC: i_csr_a = 32'h00000000;          // DEVAFF1
     12'hFB0: i_csr_a = 32'h00000000;          // LAR, WO
     12'hFB4: i_csr_a = {29'h0000000,1'b0,lsr_slk,lsr_sli}; // LSR implemented
     12'hFB8: i_csr_a = {24'h000000, i_authstatus};  // AUTHSTATUS
     12'hFBC: i_csr_a = {11'h258,1'b1,4'h0,16'h0201};  // DEVARCH
     12'hFC0: i_csr_a = 32'h0000000;           // DEVID2
     12'hFC4: i_csr_a = rtt_bcr_pad;           // DEVID1
     12'hFC8: i_csr_a = 32'h00000000;          // DEVID
     12'hFCC: i_csr_a = {24'h000000, 8'h35};   // DEVTYPE Data Engine Debug Logic
     12'hFD0: i_csr_a = {24'h000000, 8'h04};   // PIDR4 8KB
     12'hFD4: i_csr_a = {24'h000000, 8'h00};   // PIDR5
     12'hFD8: i_csr_a = {24'h000000, 8'h00};   // PIDR6
     12'hFDC: i_csr_a = {24'h000000, 8'h00};   // PIDR7
     12'hFE0: i_csr_a = {24'h000000, 8'h01};   // PIDR0
     12'hFE4: i_csr_a = {24'h000000, 8'h80};   // PIDR1
     12'hFE8: i_csr_a = {24'h000000, 8'h0D};   // PIDR2
     12'hFEC: i_csr_a = {24'h000000, 8'h00};   // PIDR3
     12'hFF0: i_csr_a = {24'h000000, 8'h0D};   // CIDR0
     12'hFF4: i_csr_a = {24'h000000, 8'h90};   // CIDR1
     12'hFF8: i_csr_a = {24'h000000, 8'h05};   // CIDR2
     12'hFFC: i_csr_a = {24'h000000, 8'hB1};   // CIDR3
     default: i_csr_a = 32'h00000000;          // ARCT0 register spaces
  endcase

end

assign dbg_rdata = i_csr_a;

endmodule
