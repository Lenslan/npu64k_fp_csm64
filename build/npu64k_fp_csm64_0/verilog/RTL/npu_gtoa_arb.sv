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

/*
 * This module implements the arbiter for multiple input sources / output destinations
 * the module:
 * - selects input/output data and handshake signals based on io mask
 * - also does conversion of feature-map inputs into accumulator type 
 * - and conversion of accumulator outputs into feature-map type
 */

module npu_gtoa_arb
  import npu_types::*;
  import npu_gtoa_types::*;
  (
   // clock and reset
   input  logic                       clk,           // clock
   input  logic                       rst_a,         // async reset, active high
   // input hlapi
   input  tmask_t                     io_en,         // hlapi io mask
   // primary input handshake and data
   input  logic                       accr0_valid,   // primary accumulator valid
   input  logic                       fmr0_valid,    // primary feature-map valid
   input  logic                       astr0_valid,   // primary streaming valid
   output logic                       arb_rd0_valid, // primary valid arbitrated
   output logic                       accr0_accept,  // primary accumulator accept
   output logic                       fmr0_accept,   // primary feature-map accept
   output logic                       astr0_accept,  // primary streaming accept
   input  logic                       arb_rd0_accept,// primary accept for arbitration
   input  vyixacc_t                   accr0_data,    // primary accumulator data
   input  vyixpix_t                   fmr0_data,     // primary feature-map data
   input  vyixacc_t                   astr0_data,    // primary streaming data
   output vyixacc_t                   arb_rd0_data,  // primary data arbitrated
   // secondary input handshake and data
   input  logic                       accr1_valid,   // secondary accumulator valid
   input  logic                       fmr1_valid,    // secondary feature-map valid
// spyglass disable_block W240
//SMD:Unread input
//SJ :Used in some config
   input  logic                       fstr1_valid,   // secondary streaming valid
// spyglass enable_block W240
   output logic                       arb_rd1_valid, // secondary valid arbitrated
   output logic                       accr1_accept,  // secondary accumulator accept
   output logic                       fmr1_accept,   // secondary feature-map accept
   output logic                       fstr1_accept,  // secondary streaming accept
   input  logic                       arb_rd1_accept,// secondary accept for arbitration
   input  vyixacc_t                   accr1_data,    // secondary accumulator data
   input  vyixpix_t                   fmr1_data,     // secondary feature-map data
// spyglass disable_block W240
//SMD:Unread input
//SJ :Used in some config
   input  vyixpix_t                   fstr1_data,    // secondary streaming data
// spyglass enable_block W240
   output vyixacc_t                   arb_rd1_data,  // secondary data arbitrated
   // output handshake and data
   output logic                       accw_valid,   // output accumulator valid
   output logic                       fmw_valid,    // output feature-map valid
   input  logic                       arb_wr_valid, // output valid for arbitration
   input  logic                       accw_accept,  // output accumulator accept
   input  logic                       fmw_accept,   // output feature-map accept
   output logic                       arb_wr_accept,// output accept arbitrated
   input  logic                       out_dbl,      // 16b output
   output vyixacc_t                   accw_data,    // output accumulator data
   output vyixpix_t                   fmw_data,     // output feature-map data
   input  vyixacc_t                   arb_wr_data   // output data for arbitration
   );
  // local wires
  logic                               fmr0_en;
  logic                               accr0_en;
  logic                               astr0_en;
  logic                               fmr1_en;
  logic                               accr1_en;
  logic                               fstr1_en;
  logic                               accw_en;
  logic                               fmw_en;
  // ping-pong state for double output
  logic                               odd_r;
  logic                               odd_nxt;
  logic                               odd_en;

  
  // simple assignments
  assign fmr0_en  = ((io_en & act_io_en_fm0_e)  == act_io_en_fm0_e) || 
                    ((io_en & act_io_en_gth_e)  == act_io_en_gth_e);
  assign accr0_en = (io_en & act_io_en_ac0_e)   == act_io_en_ac0_e;
  assign astr0_en = (io_en & act_io_en_astr0_e) == act_io_en_astr0_e;
  assign fmr1_en  = (io_en & act_io_en_fm1_e)   == act_io_en_fm1_e;
  assign accr1_en = (io_en & act_io_en_ac1_e)   == act_io_en_ac1_e;
  assign fstr1_en = 1'b0;
  assign accw_en  = (io_en & act_io_en_oac_e)   == act_io_en_oac_e;
  assign fmw_en   = (io_en & act_io_en_ofm_e)   == act_io_en_ofm_e;
  assign odd_nxt  = ~odd_r;
  assign odd_en   = fmw_valid & fmw_accept & out_dbl;

  // double wide feature-map output toggle
  // outputs: odd_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : tgl_reg_PROC
    if (rst_a == 1'b1)
    begin
      odd_r <= 1'b0;
    end
    else if (odd_en)
    begin
      odd_r <= odd_nxt;
    end
  end : tgl_reg_PROC

  // arbitration
  always_comb
  begin : arb_PROC
    // default outputs
    arb_rd0_valid = 1'b0;
    accr0_accept  = 1'b0;
    fmr0_accept   = 1'b0;
    astr0_accept  = 1'b0;
    arb_rd0_data  = '0;
    arb_rd1_valid = 1'b0;
    accr1_accept  = 1'b0;
    fmr1_accept   = 1'b0;
    fstr1_accept  = 1'b0;
    arb_rd1_data  = '0;
    accw_valid    = 1'b0;
    fmw_valid     = 1'b0;
    arb_wr_accept = 1'b0;
    accw_data     = '0;
    fmw_data      = '0;
    // primary inputs, OR bus
    if (astr0_en) 
    begin
      // streaming mode
      arb_rd0_valid |= astr0_valid;
      astr0_accept  |= arb_rd0_accept;
      arb_rd0_data  |= astr0_data;
    end
    if (fmr0_en)
    begin
      arb_rd0_valid |= fmr0_valid;
      fmr0_accept   |= arb_rd0_accept;
      for (int v = 0; v < VSIZE; v++)
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          arb_rd0_data[v][i][ACC_W-1: PIX_W] |= {(ACC_W-PIX_W){fmr0_data[v][i][PIX_W-1]}};
          arb_rd0_data[v][i][PIX_W-1: 0]     |= fmr0_data[v][i][PIX_W-1: 0];
        end
      end
    end
    if (accr0_en)
    begin
      arb_rd0_valid |= accr0_valid;
      accr0_accept  |= arb_rd0_accept;
      arb_rd0_data  |= accr0_data;
    end
    // secondary inputs, MUX bus
    if (fmr1_en)
    begin
      arb_rd1_valid = fmr1_valid;
      fmr1_accept   = arb_rd1_accept;
      for (int v = 0; v < VSIZE; v++)
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          arb_rd1_data[v][i][ACC_W-1: PIX_W] = {(ACC_W-PIX_W){fmr1_data[v][i][PIX_W-1]}};
          arb_rd1_data[v][i][PIX_W-1: 0]     = fmr1_data[v][i][PIX_W-1: 0];
        end
      end
    end
    else // accr1_en
    begin
      arb_rd1_valid = accr1_valid;
      accr1_accept  = arb_rd1_accept;
      arb_rd1_data  = accr1_data;
    end
    // outputs, MUX bus
    if (accw_en)
    begin
      accw_valid    = arb_wr_valid;
      arb_wr_accept = accw_accept;
    end
    else // if (fmw_en)
    begin
      fmw_valid     = arb_wr_valid;
      arb_wr_accept = fmw_accept & (odd_r | ~out_dbl);
    end
    // data outputs
    accw_data       = arb_wr_data;
    if (out_dbl)
    begin
// spyglass disable_block SelfDeterminedExpr-ML
//SMD:Self determined expression (i + (ISIZE / 2))
//SJ :Ignore
      for (int v = 0; v < VSIZE; v++)
      begin
        for (int i = 0; i < ISIZE/2; i++)
        begin
          // write double wide o16 in two cycles
          fmw_data[v][2*i+:2] = odd_r ? arb_wr_data[v][i+ISIZE/2][2*PIX_W-1:0]: arb_wr_data[v][i][2*PIX_W-1:0];
        end
      end
    end
// spyglass enable_block SelfDeterminedExpr-ML
    else
    begin
      for (int v = 0; v < VSIZE; v++)
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          fmw_data[v][i] = arb_wr_data[v][i][PIX_W-1:0];
        end
      end
    end
  end : arb_PROC

`ifdef ABV_ON
  //
  // Assertions
  //
  property prop_astr0_uniq;
  @(posedge clk) disable iff (rst_a !== 1'b0) astr0_en |-> (~fmr0_en & ~accr0_en);
  endproperty : prop_astr0_uniq
  a_astr0_uniq: assert property (prop_astr0_uniq) else $fatal(1, "Error: streaming input on port 0 is not unique one");
  property prop_fmr0_uniq;
  @(posedge clk) disable iff (rst_a !== 1'b0) fmr0_en |-> (~astr0_en & ~accr0_en);
  endproperty : prop_fmr0_uniq
  a_fmr0_uniq: assert property (prop_fmr0_uniq) else $fatal(1, "Error: feature-map input on port 0 is not unique one");
  property prop_accr0_uniq;
  @(posedge clk) disable iff (rst_a !== 1'b0) accr0_en |-> (~astr0_en & ~fmr0_en);
  endproperty : prop_accr0_uniq
  a_accr0_uniq: assert property (prop_accr0_uniq) else $fatal(1, "Error: accumulator input on port 0 is not unique one");
  property prop_fmr1_uniq;
  @(posedge clk) disable iff (rst_a !== 1'b0) fmr1_en |-> ~accr1_en;
  endproperty : prop_fmr1_uniq
  a_fmr1_uniq: assert property (prop_fmr1_uniq) else $fatal(1, "Error: feature-map input on port 1 is not unique one");
  property prop_accr1_uniq;
  @(posedge clk) disable iff (rst_a !== 1'b0) accr1_en |-> ~fmr1_en;
  endproperty : prop_accr1_uniq
  a_accr1_uniq: assert property (prop_accr1_uniq) else $fatal(1, "Error: accumulator input on port 1 is not unique one");
  property prop_fmw_uniq;
  @(posedge clk) disable iff (rst_a !== 1'b0) fmw_en |-> ~accw_en;
  endproperty : prop_fmw_uniq
  a_fmw_uniq: assert property (prop_fmw_uniq) else $fatal(1, "Error: feature-map output is not unique one");
  property prop_accw_uniq;
  @(posedge clk) disable iff (rst_a !== 1'b0) accw_en |-> ~fmw_en;
  endproperty : prop_accw_uniq
  a_accw_uniq: assert property (prop_accw_uniq) else $fatal(1, "Error: accumulator output is not unique one");
`endif

endmodule : npu_gtoa_arb
