// Library ARCv2HS-3.5.999999999
///---------------------------------------------------------------------------
///
/// Copyright (C) 2012-2013 Synopsys, Inc. All rights reserved.
///
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
/// work of Synopsys, Inc., and is fully protected under copyright and 
/// trade secret laws. You may not view, use, disclose, copy, or distribute 
/// this file or any information contained herein except pursuant to a 
/// valid written license from Synopsys, Inc.
///
/// The entire notice above must be reproduced on all authorized copies.
///
///---------------------------------------------------------------------------

module npuarc_alb_ifu_clk_ctrl (
  input clk,
  input rst_a,
  input restart,
  input mem_busy,
  input bist_en,
  output reg clk2_en_r,
  output clk2
);

wire clk2_restart;

assign clk2_restart = bist_en || (restart && (!mem_busy));

wire clk2_en;
always @(posedge clk or posedge rst_a) 
begin: clk2_en_reg_PROC
  if (rst_a == 1'b1) begin
    clk2_en_r <= 1'b0;
  end
  else begin
    clk2_en_r <= clk2_restart ? 1'b0 : ~clk2_en;
  end
end
  
assign clk2_en = clk2_en_r | clk2_restart;
npuarc_clkgate u_clk2gate (
  .clk_in            (clk),
  .clock_enable      (clk2_en),
  .clk_out           (clk2)
);


endmodule

