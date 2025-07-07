// Library ARC_Trace-3.0.999999999
// Copyright (C) 2016 Synopsys, Inc. All rights reserved.
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
//   rtt_atb_ctrl
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_atb_fifo.vpp
//
// ===========================================================================

module npuarc_rtt_atb_fifo(rtt_clk,
    atclken,
                        rst_a, push_req_n, pop_req_n,
                        data_in,
                        push_hf, push_af,
                        pop_empty,
                        push_count, pop_count, data_out);

parameter width = 8;
parameter depth = 8;
parameter push_af_lvl = 2;
parameter use_atclken_pp = 1;

localparam effective_depth = (depth==4?4:(depth==8?8:(depth==16?16:(depth==32?32:(depth==64?64:(depth==128?128:(depth==256?256:(depth+2-(depth %2)))))))));
localparam addr_width  = ((depth>16)?((depth>64)?((depth>128)?8:7):((depth>32)?6:5)):((depth>4)?((depth>8)?4:3):((depth>2)?2:1)));
localparam count_width = ((depth+1>256)?((depth+1>4096)?((depth+1>16384)?((depth+1>32768)?16:15):((depth+1>8192)?14:13)):((depth+1>1024)?((depth+1>2048)?12:11):((depth+1>512)?10:9))):((depth+1>16)?((depth+1>64)?((depth+1>128)?8:7):((depth+1>32)?6:5)):((depth+1>4)?((depth+1>8)?4:3):((depth+1>2)?2:1))));
localparam ONE_UNIT    = 1'b1;

input rtt_clk;
input atclken;
input rst_a, push_req_n, pop_req_n;
input [width-1 : 0] data_in;

output push_hf, push_af;
output pop_empty;
output [count_width-1 : 0] push_count;
output [count_width-1 : 0] pop_count;
output [width-1 : 0] data_out;

//-------------------------------------------------------------------
//parametes can be overwrite
//-------------------------------------------------------------------
localparam hf_mark         = effective_depth>>1;
localparam af_mark         = effective_depth-push_af_lvl;

wire                           push_af;
wire                           push_hf;
wire                           empty;
reg    [count_width-1:0]       num_fill;
wire   [count_width-1:0]       num_fill_xx;
wire   [count_width-1:0]       num_fill_yy;

reg                            fifo_full;
reg                            fifo_empty;
reg    [addr_width-1:0]        wr_ptr;      // Write pointer
wire   [addr_width-1:0]        wr_ptr_xx;
reg    [addr_width-1:0]        rd_ptr;
wire   [addr_width-1:0]        rd_ptr_xx;

wire   [width-1 : 0]           data_out;

reg  [count_width-1 : 0] pop_count;
wire [count_width-1 : 0] push_count;

wire pop_empty;

wire rd_en, rd_en_p, wr_en, rd_vld;
reg rd_en_d1;

assign wr_en = ~push_req_n;
assign rd_en = ~pop_req_n && atclken;

assign push_count = num_fill;
assign pop_empty = fifo_empty;

always @(posedge rtt_clk or posedge rst_a)
begin : RDEN_PROC
  if(rst_a)
    rd_en_d1 <= 1'b0;
  else
    rd_en_d1 <= ~pop_req_n;
end

reg    [width-1:0] fifo_mem [(effective_depth-1):0]; // Memory

// spyglass disable_block SelfDeterminedExpr-ML
// MD: pointer wraps are expected by design
// leda W396 off
// LMD: Register with no reset/set
// LJ: Memory Data does not have reset. Only enable has reset.
// spyglass disable_block STARC-2.3.4.3 ResetFlop-ML
// SMD: Register with no reset/set
// SJ: flops used as memory, no reset required
// spyglass disable_block Ar_resetcross01
// SMD: Unsynchronized reset crossing detected
// SJ: flops used as memory, no reset required
//------------------------------------------------------
// Writing Data into Memory
//------------------------------------------------------
always @(posedge rtt_clk)
begin : MEM_WR_BLK_PROC
  if(wr_en)
    fifo_mem[wr_ptr] <= data_in;
end
// spyglass enable_block Ar_resetcross01

//------------------------------------------------------
// Reading Data from Memory
//------------------------------------------------------
assign data_out = fifo_mem[rd_ptr];

// spyglass enable_block STARC-2.3.4.3 ResetFlop-ML
//leda BTTF_D002 off
//leda B_3200 off

//-------------------------------------------------------
// Write Pointer
//-------------------------------------------------------

assign wr_ptr_xx = {wr_ptr + ONE_UNIT};

always @( posedge rtt_clk or posedge rst_a )
begin : WR_PTR_PROC
  if( rst_a == 1'b1 )
    wr_ptr <= {(addr_width){1'b0}};
  else if( wr_en )
    wr_ptr <= wr_ptr_xx[addr_width-1:0];
end

//-------------------------------------------------------
// Read Pointer
//-------------------------------------------------------

assign rd_ptr_xx = {rd_ptr + ONE_UNIT};


always @( posedge rtt_clk or posedge rst_a )
begin : RD_PTR_PROC
  if( rst_a == 1'b1 )
    rd_ptr <= {(addr_width){1'b0}};
  else if( rd_en )
    rd_ptr <= rd_ptr_xx[addr_width-1:0];
end

//-------------------------------------------------------
// FIFO Empty Generation Logic
//-------------------------------------------------------
always @( posedge rtt_clk or posedge rst_a )
begin : FIFO_EMP_GEN_PROC
  if( rst_a == 1'b1 )
    fifo_empty <= 1'b1;
  else if( wr_en && (~rd_en) )
    fifo_empty <= 1'b0;
  else if((rd_en && (~wr_en)) &&
          (rd_ptr_xx[addr_width-1:0] == wr_ptr))
    fifo_empty <= 1'b1;
end

//-------------------------------------------------------
// Almost Full Generation Logic
//-------------------------------------------------------
assign push_af= num_fill >= af_mark[count_width-1:0];
assign push_hf= num_fill >= hf_mark[count_width-1:0];

//-------------------------------------------------------
// FIFO Full Generation Logic
//-------------------------------------------------------
always @( posedge rtt_clk or posedge rst_a )
begin : FIFO_FUL_GEN_PROC
  if( rst_a == 1'b1 )
    fifo_full <= 1'b0;
  else if( wr_en && (~rd_en) &&
           (wr_ptr_xx[addr_width-1:0] == rd_ptr))
    fifo_full <= 1'b1;
  else if( rd_en && (~wr_en) )
    fifo_full <= 1'b0;
end

assign num_fill_xx = {num_fill + ONE_UNIT};
assign num_fill_yy = {num_fill - ONE_UNIT};

//-------------------------------------------------------
// Generation of No. of locations filled logic
//-------------------------------------------------------
always @(posedge rtt_clk or posedge rst_a)
begin : NO_FILL_GEN_PROC
  if(rst_a== 1'b1 )
    num_fill <= {(count_width){1'b0}};
  else
    case( {wr_en,rd_en} )
      2'b10 : num_fill <= num_fill_xx[count_width-1:0];
      2'b01 : num_fill <= num_fill_yy[count_width-1:0];
      default : num_fill <= num_fill;
    endcase
end
// leda W631 on
// leda NTL_CON32 on
//leda BTTF_D002 on
//leda B_3200 on

//spyglass disable_block Reset_sync02
//SMD: Reset signal used to reset pop_count is generated from domain rtt_clk
generate
if (use_atclken_pp) begin: popc
always @(posedge rtt_clk or posedge rst_a)
begin : POP_NUM_FILL_PROC
  if(rst_a)

    pop_count <= {(count_width){1'b0}};
  else if (atclken)
    case( {wr_en,rd_en} )
      2'b10 : pop_count <= num_fill_xx[count_width-1:0];
      2'b01 : pop_count <= num_fill_yy[count_width-1:0];
      default : pop_count <= num_fill;
    endcase
end
end
else begin: popc
always @(posedge rtt_clk or posedge rst_a)
begin : POP_NUM_FILL_PROC
  if(rst_a)
    pop_count <= {(count_width){1'b0}};
  else
    case( {wr_en,rd_en} )
      2'b10 : pop_count <= num_fill_xx[count_width-1:0];
      2'b01 : pop_count <= num_fill_yy[count_width-1:0];
      default : pop_count <= num_fill;
    endcase
end
end
endgenerate
//spyglass enable_block Reset_sync02
// spyglass enable_block SelfDeterminedExpr-ML

endmodule
