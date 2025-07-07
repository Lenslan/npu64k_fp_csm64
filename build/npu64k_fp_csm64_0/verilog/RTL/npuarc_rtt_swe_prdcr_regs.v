// Library ARC_Trace-3.0.999999999
// Copyright (C) 2012-2013 Synopsys, Inc. All rights reserved.
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
//   rtt_swe_prdcr_regs
//
// ===========================================================================
//
// Description:
//  Contains the programming registers of producers
//  can support 1,2 or 4 core configurations
//
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_swe_prdcr_reg.vpp
//
// ===========================================================================



`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_swe_prdcr_regs
( rtt_clk,
  rst_a, //active low reset
  rtt_addr,
  rtt_dataw ,
  rtt_write,
  rtt_read,
  pr0_rtt_datar,
  swe_prdcr_sel,
  pr0_atid,
  pr0_syncrfr,
  rtt_flush_command,
  flush_done,
  rtt_time_stamp_en,
  pr0_csts_en,
  swe_rtt_bcr_pad

  );

localparam BCR_OCMW_PP = !`npuarc_OCM ? 2'b00: ((`npuarc_b_d_w == 32) ? 2'b00 :
                                         (`npuarc_b_d_w == 64) ? 2'b01 :
                                         (`npuarc_b_d_w == 128)? 2'b10 : 2'b11);

  input                            rtt_clk; //RTT clock
  input                            rst_a;//Active Low Reset
  input  [`npuarc_RTT_ADDR8:0]            rtt_addr ;   // Producer Interface address connected to the aux if of
                                      // ARC
  input  [`npuarc_AUX_DATA-1:0]            rtt_dataw; // Register Write data
  input                             rtt_write;  // Register Write enable
  input                             rtt_read;   // Register Read Enable
  output [`npuarc_AUX_DATA-1:0]            pr0_rtt_datar;  // Register read data
  output reg [`npuarc_RTT_NUM_SWE_PORTS-1:0]  swe_prdcr_sel;
  output  [`npuarc_ATID_WDT-1:0]           pr0_atid;
  output  [`npuarc_SYNCRFR_WDT-1:0]        pr0_syncrfr;
  output                            rtt_flush_command;
  input                             flush_done;
  output                            rtt_time_stamp_en;
  output                            pr0_csts_en;
  output [`npuarc_AUX_DATA-1:0]            swe_rtt_bcr_pad;

//nets declarations
  reg [`npuarc_AUX_DATA-1:0]               pr0_rtt_datar;
   //filters
   reg  [`npuarc_ATID_WDT-1:0]             pr0_atid;
   reg  [`npuarc_SYNCRFR_WDT-1:0]          pr0_syncrfr;
   wire [`npuarc_AUX_DATA-1:0]             rtt_syncrfr_pad;
   reg                              rtt_flush_command;
   reg                              pr0_csts_en;

  reg   [2-2:0]       pr0_src_en ;

reg rtt_time_stamp_en;
generate
if (`npuarc_SYNCRFR_WDT != 32) begin:_pad_1_SYNCRFR_REG_ADDR
 assign rtt_syncrfr_pad = {{(32-`npuarc_SYNCRFR_WDT){1'b0}},pr0_syncrfr};
end
else begin:_pad_0_SYNCRFR_REG_ADDR
 assign rtt_syncrfr_pad = pr0_syncrfr;
end
endgenerate

 wire swe_prdcr_bnk_en;
 wire swe_prdcr_bnk_rd;
 wire swe_prdcr_bnk_wr;
 assign swe_prdcr_bnk_en = (rtt_addr[8:5] == 4'd`npuarc_SWE_PRDCR_BNK);    //0x060 - 0x07F
 assign swe_prdcr_bnk_rd = swe_prdcr_bnk_en && rtt_read;  //0x060 - 0x07F
 assign swe_prdcr_bnk_wr = swe_prdcr_bnk_en && rtt_write; //0x060 - 0x07F

 wire [`npuarc_BCR-1:0] swe_rtt_bcr;

 assign swe_rtt_bcr = {1'b0, BCR_OCMW_PP,2'd0,1'b0,1'b`npuarc_RTT_CORESIGHT_OPTION,1'b`npuarc_HAS_NEXUS_IF,`npuarc_NEXUS_MSEO_WDT,`npuarc_MDO_PORTS,`npuarc_OCM,`npuarc_INT_MEM,6'd17,6'd`npuarc_RTT_VERSION};

//RTT Time Stamp Register
always @ (posedge rtt_clk or posedge rst_a)
begin : CTRL_RTT_TIME_STAMP_PROC
  if (rst_a == 1'b1) begin
    rtt_time_stamp_en <= 1'b0;
  end // end if of reset
  else if ((rtt_addr[4:0] == `npuarc_RTT_TST) && swe_prdcr_bnk_wr) begin
     rtt_time_stamp_en <= rtt_dataw[0];
  end
end

// Flush register
always @ (posedge rtt_clk or posedge rst_a)
begin : CTRL_RTT_FLUSH_COMMAND_PROC
  if (rst_a == 1'b1) begin
    rtt_flush_command <= 1'b0;
  end  // end of reset
  else if (flush_done) begin
    rtt_flush_command <= 1'b0;
  end
  else if ((rtt_addr[4:0] == `npuarc_FLUSH_COMMAND) && swe_prdcr_bnk_wr && (rtt_dataw[0] == 1'b1)) begin
    rtt_flush_command <= 1'b1;
  end // end of flush command write register
end // end of flush register

// leda DFT_022 off
// LMD: Incomplete case statement
// LJ: the case statement is put under the sequential process and
//     will not make any harm for not putting the default statement.
//     A Default statement in this case will insert an extra 32 registers


//Filter Register
always @ (posedge rtt_clk or posedge rst_a)
begin : PRODUCER0_FILTER_PROC
  if (rst_a == 1'b1) begin
    swe_prdcr_sel          <= {(`npuarc_RTT_NUM_SWE_PORTS){1'b0}};
    pr0_atid               <= {{(`npuarc_ATID_WDT-1'b1){1'b0}},1'b1};
    pr0_syncrfr            <= {`npuarc_SYNCRFR_WDT{1'b0}};
    pr0_csts_en            <= 1'b0;
  end  // end of reset
  else if(swe_prdcr_bnk_wr)
     begin
  if (rtt_addr[4:0] == `npuarc_PR_SRC_EN) begin
       swe_prdcr_sel           <= rtt_dataw[`npuarc_RTT_NUM_SWE_PORTS-1:0] ;
  end
  if (rtt_addr[4:0] == `npuarc_ATID_REG_ADDR) begin
       pr0_atid                <= rtt_dataw[`npuarc_ATID_WDT-1:0];
  end
  if (rtt_addr[4:0] == `npuarc_SYNCRFR_REG_ADDR) begin
       pr0_syncrfr             <= rtt_dataw[`npuarc_SYNCRFR_WDT-1:0];
  end
  if (rtt_addr[4:0] == `npuarc_CSTSEN_REG_ADDR) begin
       pr0_csts_en             <= rtt_dataw[0];
  end
end // end of else statement
end // end of always

// leda DFT_022 on

wire [`npuarc_AUX_DATA-1:0] swe_rtt_bcr_pad;
generate
if (`npuarc_BCR != 32) begin:_pad_1_swe_RTT_BCR
       assign swe_rtt_bcr_pad = {{(32-`npuarc_BCR){1'b0}},swe_rtt_bcr} ;
end
else begin:_pad_0_swe_RTT_BCR
       assign swe_rtt_bcr_pad = swe_rtt_bcr;
end
endgenerate

// spyglass disable_block SelfDeterminedExpr-ML
//Producer0 register Reads
always @*
begin : PR0_REG_READ_PROC

  if (swe_prdcr_bnk_rd)
  begin // {
//    case (rtt_addr[4:0])
//       `RTT_BCR          :      pr0_rtt_datar = swe_rtt_bcr_pad ;
//       `RTT_TST          :      pr0_rtt_datar = {31'b0,rtt_time_stamp_en};
//       `FLUSH_COMMAND    :      pr0_rtt_datar = {31'b0,rtt_flush_command};
//       default : pr0_rtt_datar = 32'h0;
//    endcase
      if (rtt_addr[4:0] == `npuarc_RTT_BCR) begin
         pr0_rtt_datar = swe_rtt_bcr_pad;
      end
      else if (rtt_addr[4:0] == `npuarc_RTT_TST) begin
       pr0_rtt_datar = {31'b0,rtt_time_stamp_en};
      end
      else if (rtt_addr[4:0] == `npuarc_FLUSH_COMMAND) begin
         pr0_rtt_datar = {31'b0,rtt_flush_command};
      end
//      case (rtt_addr[4:0])
//          `PR_SRC_EN               :   pr0_rtt_datar = {{(32-`RTT_NUM_swe_SLICES*2){1'b0}},swe_prdcr_sel};
//          `ATID_REG_ADDR           :   pr0_rtt_datar = {{(32-`ATID_WDT){1'b0}},pr0_atid};
//          `SYNCRFR_REG_ADDR        :   pr0_rtt_datar = rtt_syncrfr_pad;
//          `CSTSEN_REG_ADDR         :   pr0_rtt_datar = {31'b0, pr0_csts_en};
//           default : pr0_rtt_datar = 32'h0;
//      endcase
      else if (rtt_addr[4:0] == `npuarc_PR_SRC_EN) begin
         pr0_rtt_datar = {{(32-`npuarc_RTT_NUM_SWE_PORTS){1'b0}},swe_prdcr_sel};
      end
      else if (rtt_addr[4:0] == `npuarc_ATID_REG_ADDR) begin
       pr0_rtt_datar = {{(32-`npuarc_ATID_WDT){1'b0}},pr0_atid};
      end
      else if (rtt_addr[4:0] == `npuarc_SYNCRFR_REG_ADDR) begin
          pr0_rtt_datar = rtt_syncrfr_pad;
      end
     else if (rtt_addr[4:0] == `npuarc_CSTSEN_REG_ADDR) begin
          pr0_rtt_datar = {31'b0, pr0_csts_en};
     end
      else
         pr0_rtt_datar = 32'h0;
   end // }
   else  begin
     pr0_rtt_datar = 32'h0;
   end
end //end of always
// spyglass enable_block SelfDeterminedExpr-ML



endmodule // end of progamming interface module
