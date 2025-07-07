//----------------------------------------------------------------------------
//
// Copyright 2010-2015 Synopsys, Inc. All rights reserved.
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

// LEDA off
//spyglass disable_block ALL
module arcsync_clkgate (
  input   clk_in,
  input   clock_enable_r,
  
  output  clk_out
);

// Note: This is a behavioral block that is replaced by the RDF flow before synthesis
// The replaced block instantiates the proper clockgate cell of the synthesis library

reg latch;


always @*
begin
  if (!clk_in)
  begin
    // COMBDLY from Verilator warns against delayed (non-blocking)
    // assignments in combo blocks - and it is considered hazardous
    // code that risks simulation and synthesis not matching.
    //
    latch = clock_enable_r;
  end

end

 

assign clk_out = clk_in & latch;

endmodule // cln_clkgate
//spyglass enable_block ALL
// LEDA on
