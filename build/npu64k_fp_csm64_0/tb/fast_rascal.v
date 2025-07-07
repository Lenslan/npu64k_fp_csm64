/*
 * Copyright (C) 2021-2022 Synopsys, Inc. All rights reserved.
 *
 * SYNOPSYS CONFIDENTIAL - This is an unpublished, confidential, and
 * proprietary work of Synopsys, Inc., and may be subject to patent,
 * copyright, trade secret, and other legal or contractual protection.
 * This work may be used only pursuant to the terms and conditions of a
 * written license agreement with Synopsys, Inc. All other use, reproduction,
 * distribution, or disclosure of this work is strictly prohibited.
 *
 * The entire notice above must be reproduced on all authorized copies.
 */


`include "npuarc_cpu_defs.v"
module fast_rascal #(
  parameter cpu_id = 1,
  parameter halt_sig = ""
) (
  // BVCI outputs
  output                                dbg_cmdval,     // cmdval from rascal
  output reg                            dbg_eop,        // eop from rascal
  output reg  [`npuarc_DBG_ADDR_RANGE]  dbg_address,    // address from rascal
  output reg  [`npuarc_DBG_BE_RANGE]    dbg_be,         // be from rascal
  output reg  [`npuarc_DBG_CMD_RANGE]   dbg_cmd,        // cmd from rascal
  output reg  [`npuarc_DBG_DATA_RANGE]  dbg_wdata,      // wdata from rascal
  output reg                            dbg_rspack,     // rspack from rascal
  // BVCI inputs
  input                                 dbg_cmdack,     // BVCI cmd acknowledge
  input                                 dbg_rspval,     // BVCI response valid
  input  [`npuarc_DBG_DATA_RANGE]       dbg_rdata,      // BVCI response data
  input                                 dbg_reop,       // BVCI response EOP
  input                                 dbg_rerr,       // BVCI data to Debug host
  //input                                 sys_halt_r,     // ARC core halt status output signal
  // APB inputs
  input                                 pclkdbg_en,
  input                                 presetdbgn,
  input                                 preadydbg,
  input [31:0]                          prdatadbg,
  input                                 pslverrdbg,
  // APB outputs
  output [31:2]                         paddrdbg,
  output                                pseldbg,
  output                                penabledbg,
  output                                pwritedbg,
  output [31:0]                         pwdatadbg,
  // Misc signals
  output                                dbgen,
  output                                niden,
  output                                dbg_prot_sel,
  input                                 rst_a,
  input                                 clk
);

reg int_cmdval;

wire int_cmdack, int_rspval, int_reop, int_rerror;
wire [31:0] int_rdata;

wire apb_cmdack, apb_rspval, apb_reop, apb_rerror;
wire [31:0] apb_rdata;

// Inputs to fast rascal, from gasket conversion.
wire                   param_cmdack 	  = int_cmdack;
wire [`npuarc_DBG_DATA_RANGE] param_rdata = int_rdata;
wire                   param_reop 	  = int_reop;
wire                   param_rspval 	  = int_rspval;
wire                   param_rerror 	  = int_rerror;

initial begin
  $rascal2bvci_mcpu(
    rst_a,            
    clk,
    dbg_address, 
    dbg_be,      
    dbg_cmd,     
    int_cmdval,  
    dbg_eop,     
    dbg_rspack,  
    dbg_wdata,   
    // These come from either the bvci bus directly or from the gasket.
    param_cmdack,  
    param_rdata,   
    param_reop,    
    param_rspval,  
    param_rerror,
    3,			// halt signal is below (inverted run signal)
    cpu_id,
    halt_sig
  );
end

assign dbg_prot_sel = `npuarc_DBG_APB_OPTION; // 0 for BVCI, 1 for APB

assign int_cmdack = (dbg_prot_sel) ? apb_cmdack : dbg_cmdack;
assign int_rspval = (dbg_prot_sel) ? apb_rspval : dbg_rspval;
assign int_rdata  = (dbg_prot_sel) ? apb_rdata  : dbg_rdata;
assign int_reop   = (dbg_prot_sel) ? apb_reop   : dbg_reop;
assign int_rerror = (dbg_prot_sel) ? apb_rerror : dbg_rerr;
assign dbg_cmdval = int_cmdval & !dbg_prot_sel;

dbg_bvci2apb u_dbg_b2apb (
  .clk		(clk),
  .rst_a	(rst_a),
  .pclkdbg_en	(pclkdbg_en),
     
  .presetdbgn	(presetdbgn),

  .dbg_cmdval	(int_cmdval & dbg_prot_sel),
  .dbg_cmdack	(apb_cmdack), 
  .dbg_address	(dbg_address),
  .dbg_be	(dbg_be),
  .dbg_cmd	(dbg_cmd),
  .dbg_wdata	(dbg_wdata),
  .dbg_rspack	(dbg_rspack),
  .dbg_rspval	(apb_rspval),
  .dbg_rdata	(apb_rdata),
  .dbg_reop	(apb_reop),
  .dbg_rerr	(apb_rerror),

  .pseldbg	(pseldbg),
  .paddrdbg	(paddrdbg),
  .pwritedbg	(pwritedbg),
  .penabledbg	(penabledbg),
  .pwdatadbg	(pwdatadbg),
  .prdatadbg	(prdatadbg),
  .preadydbg	(preadydbg),
  .pslverrdbg	(pslverrdbg)
);

// Authentication interface

assign dbgen = 1'b1;
assign niden = 1'b1;


endmodule
