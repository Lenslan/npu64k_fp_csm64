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

// Set simulation timescale
//
// synopsys translate_off

///////////////////////////////////////////////////////////////////////////
// Common Verilog definitions
///////////////////////////////////////////////////////////////////////////

// Verilog simulator timescale definition for all modules
//
`timescale 1 ns / 10 ps

// synopsys translate_on


module npuarc_alb_2cyc_checker 
  #( 
     parameter WIDTH  = 1
     ) 
    (
     input [WIDTH-1:0]  data_in,
     output [WIDTH-1:0]  data_out,
//leda NTL_CON37 off
//leda NTL_CON13C off
// spyglass disable_block W240
// SMD: Signal declared but not used
// SJ:  not used in all configs
     input clk
// spyglass enable_block W240  
//leda NTL_CON13C on
//leda NTL_CON37 on
     )  /* synthesis syn_hier = "fixed" */;


`ifdef MCP_ASSERT_ON // {
  stable_check:
    assert property (@(posedge clk)
      (data_in != $past(data_in, 1)) |=> $stable(data_in)
    )
    else
      $error("[ERROR - %m]: Violation found \n");
`endif // } MCP_ASSERT_ON

// Check 2-cycle timing paths: 
// When data_in changes value, data_out is forced to X until the next clock cycle.
// Only in the 2nd cycle data_out gets the value of data_in.

// leda off
// LMD: turn Leda checking off
// LJ: this module contains special checker code that should be excepted from Synthesis and Leda checks

  // This signal is used to control the 2 cycle checker output by TB to prevent 'x' propagation 
  // to external signals. When this signal is 1, the checker output is same as the input.
  // default chekcer output 'x'
  wire checker_out_ctrl;
  assign checker_out_ctrl = 1'b0;

`ifdef NO_2CYC_CHECKER
  assign   data_out = data_in;

`else

`ifndef TTVTOC
  assign   data_out = data_in;
`endif

//synopsys translate_off
  reg [WIDTH-1:0] data_out2;
  assign data_out = (checker_out_ctrl) ? data_in :
                                         data_out2;

`ifndef TTVTOC
  always @(data_in) 
  begin: alb_2cyc_chk_PROC
    assign data_out2 = {WIDTH{1'bx}};
    #0.01 deassign data_out2;
  end
`endif

  always @(posedge clk)
  begin
    data_out2 <= data_in;
  end


`ifdef TB_ALB_2CYC_DATA_STABLE_CHECK // {

  reg [31:0] set;
  reg [31:0] cnt;

  initial begin
    set = 0;
    cnt = 0;

    forever begin
      @(data_in);
      if (`MPTB_SYS_CYCLE > 50)
      begin
        @(posedge clk);
        set = 1;

        fork
        begin : cyc_stable_check
          forever begin
            @(data_in);
            if (set)
            begin
              $display ("[WARNING - %m]: %s found on data_in (Time - %t, Cycle - %d)", (set > 1)?"Glitch":"Violation", $time, `MPTB_SYS_CYCLE);
              `MPTB_MCP_VIOL = 1;
              cnt++;
              // $finish;
            end
            set += 1;
          end
        end
        join_none

        @(posedge clk);
        set = 0;
        disable cyc_stable_check;

        if (cnt > 2)
        begin
          $display ("[INFO - %m]: Stopping MCP assertion check (Cycle - %d)", `MPTB_SYS_CYCLE);
          break;
        end

      end
      else set = 0;
    end
  end

`endif // } TB_ALB_2CYC_DATA_STABLE_CHECK

//synopsys translate_on

`endif

// leda on

endmodule  

