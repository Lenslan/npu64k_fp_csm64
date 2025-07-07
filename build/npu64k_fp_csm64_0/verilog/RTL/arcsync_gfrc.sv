/*
 * Copyright (C) 2021-2023 Synopsys, Inc. All rights reserved.
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

`include "arcsync_defines.v"
module arcsync_gfrc
#(
  parameter ADDR_WIDTH = 32  ,
  parameter DATA_WIDTH = 64

)
(
  input     logic                         mmio_sel,   // select target register group, valid at the cycle when *en is high
  input     logic       [ADDR_WIDTH-1:0]  mmio_addr,  // register address, valid at the cycle when *en is high
  input     logic                         mmio_wen,   // write enable for register
  input     logic                         mmio_ren,   // read enable for register
  input     logic                         mmio_gfrc_read_64b,   // read the whole 64-b value of gfrc 
  output    logic       [DATA_WIDTH-1:0]  mmio_rdata, // read data, valid at the cycle when ren is high
  input     logic       [DATA_WIDTH-1:0]  mmio_wdata, // write data, valid at the cycle when wen is high
  output    logic       [1:0]             mmio_resp,  // {err, ack} the response is received at the cycle when *en is high

  // Clock, reset and configuration
  input     logic               rst_a,      // Asynchronous reset, active high
  input     logic               clk         // Clock
);


///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                   local wires and regs  declaration                       //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
logic        dec_gfrc_wr_enable;
logic        dec_gfrc_rd_enable;
logic        dec_gfrc_wr_clear ;
logic        dec_gfrc_rd_hi    ;
logic        dec_gfrc_rd_lo    ;
logic [31:0] dec_gfrc_wr_data  ;
//read back data
logic [DATA_WIDTH-1:0] gfrc_rdata;

logic        gfrc_ack          ;
logic        gfrc_error        ;
logic        gfrc_clk_enable   ;

//GFRC_ENABLE register
logic        gfrc_enable_r;
//GFRC_CLEAR register
logic        gfrc_clear_r ;
//next state of 64-bits gfrc counter
logic  [64-1:0]  gfrc_counter_next;
//64-bits gfrc counter
logic  [64-1:0]  gfrc_counter_r;

///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                    decode and return {error,ack}                          //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
assign dec_gfrc_wr_data[31:0] = mmio_wdata[31:0]  ;
assign mmio_rdata[DATA_WIDTH-1:0]  = gfrc_rdata[DATA_WIDTH-1:0];
assign mmio_resp          = {gfrc_error, gfrc_ack};

assign dec_gfrc_wr_enable =(mmio_addr == `ADDR_GFRC_ENABLE && mmio_sel && mmio_wen);
assign dec_gfrc_rd_enable =(mmio_addr == `ADDR_GFRC_ENABLE && mmio_sel && mmio_ren);
assign dec_gfrc_wr_clear  =(mmio_addr == `ADDR_GFRC_CLEAR  && mmio_sel && mmio_wen);
assign dec_gfrc_rd_hi     =(mmio_addr == `ADDR_GFRC_READ_HI && mmio_sel && mmio_ren);
assign dec_gfrc_rd_lo     =(mmio_addr == `ADDR_GFRC_READ_LO && mmio_sel && mmio_ren);


//return the error if access the address doesn't exist or write access to the read only register
//reading GFRC_READ_HI with 64bit data width,the data will only show the high part,so meanwhile error need to pull up 
assign gfrc_error = (    mmio_sel & (mmio_wen | mmio_ren) 
                     & ~(mmio_addr == `ADDR_GFRC_ENABLE 
                        |mmio_addr == `ADDR_GFRC_CLEAR 
                        |mmio_addr == `ADDR_GFRC_READ_HI
                        |mmio_addr == `ADDR_GFRC_READ_LO)
                    )
                 |(mmio_addr == `ADDR_GFRC_READ_HI && mmio_sel && mmio_ren && mmio_gfrc_read_64b)   
                 |1'b0 ;

assign gfrc_ack   = (mmio_sel & (mmio_wen | mmio_ren)) 
                    | 1'b0 ;

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
//           Control Logic of ARCsync_gfrc_main                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////
//
//write to GFRC_ENABLE and GFRC_CLEAR
//

//GFRC_ENABLE rst value 1'b1
always @(posedge clk or posedge rst_a)
begin: gfrc_enable_r_PROC
  if(rst_a == 1'b1)begin
    gfrc_enable_r <= 1'b1 ;
  end else if (dec_gfrc_wr_enable)begin
    gfrc_enable_r <= dec_gfrc_wr_data[0];
  end 
end: gfrc_enable_r_PROC

//GFRC_CLEAR rst value 1'b0
always @(posedge clk or posedge rst_a)
begin: gfrc_clear_r_PROC
  if(rst_a == 1'b1)begin
    gfrc_clear_r <= 1'b0;
  end else if (dec_gfrc_wr_clear)begin
    gfrc_clear_r <= dec_gfrc_wr_data[0];
  end else begin
    gfrc_clear_r <= 1'b0;
  end
end: gfrc_clear_r_PROC

/////////////////////////////////////////////////////////////////////
//read output from GFRC_ENABLE GFRC_READ_LO GFRC_READ_HI GFRC_CLEAR                          
//read GFRC_CLEAR,ignored return 0
//
assign gfrc_rdata = (mmio_gfrc_read_64b)? 
                    ({{63'b0} , {dec_gfrc_rd_enable & gfrc_enable_r}}
                    |64'b0 
                    |({64{dec_gfrc_rd_lo}} & gfrc_counter_r[64-1:0])
                    ):
                    ({{63'b0} , {dec_gfrc_rd_enable & gfrc_enable_r}}  //read GFRC_ENABLE,return current status
                    |{64{1'b0}}                                      
                    |{32'b0,({32{dec_gfrc_rd_hi}} & gfrc_counter_r[63:32])} //read GFRC_READ_HI
                    |{32'b0,({32{dec_gfrc_rd_lo}} & gfrc_counter_r[31:0])} 
                    ); //read GFRC_READ_LO

///////////////////////////////////////////////////////////////////////////
//64-bits global free running counter//enable,disable,clear all here
//
assign gfrc_counter_next  = (gfrc_clear_r)?
                             64'b0:
                             (gfrc_enable_r?(gfrc_counter_r + 64'd1):gfrc_counter_r) ;

////////////////////////////////////////////////////////////////////////////////////////
//when GFRC is disabled, the clock source of GFRC is gated to reduce power consumption
//when GFRC is enabled, the clock source of GFRC is un-gated automatically
//when GFRC_ENABLE or GFRC_CLEAR writen to 1'b1 ,the counter need to be updated
//use gfrc_clk_enable to control the flip of the counter
//
assign gfrc_clk_enable =(gfrc_enable_r == 1'b1) | (gfrc_clear_r == 1'b1);

always @( posedge clk or posedge rst_a )
begin: global_gfrc_r_PROC
  if(rst_a == 1'b1)
    gfrc_counter_r <= 64'b0;
  else if(gfrc_clk_enable)
    gfrc_counter_r <= gfrc_counter_next;     
end: global_gfrc_r_PROC



//-------------------------------------------------------------------------------------------------------
// Global Free Running Counter PROPERTY
//-------------------------------------------------------------------------------------------------------
`ifdef FORMAL_ASSERT_ON
  `include "prop_arcsync_gfrc.sv"
`endif

endmodule
