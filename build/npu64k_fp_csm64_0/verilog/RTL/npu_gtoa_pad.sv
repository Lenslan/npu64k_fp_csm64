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
 * NPU padding logic, pads input data and returns the column index of the data
 * The GTOA padding logic start applies 2D padding if enabled
 * padding can be done by the MININT or 0 value
 * As a sideband signal padding will return the column padding index for ARGMAX applications
 * Even if padding is disabled the padding index is updated
 * Padding iterators and associated 2D offsets and column stride are passed as input signals
 */

module npu_gtoa_pad
  import npu_types::*;
  import npu_gtoa_types::*;
  // interface signals
  (
   // clock and reset
   input  logic                                    clk,              // clock
   input  logic                                    rst_a,            // asynchronous reset, active high
   // padding configuration
   input  logic                                    cf_en,            // new configuration is valid
   input  logic                                    cf_paden,         // enable padding
   input  pad_mode_t                               cf_padmode,       // padding mode
   input  pad_inc_t                                cf_padinc,        // padding increment mode
   input  offset_t        [1:0]                    cf_padlim,        // maxpooling and reduction window boundaries row&column
   input  offset_t        [1:0]                    cf_padpos,        // padding start row&column
   input  offset_t        [ACT_FM_LOOPS-1:0][1:0]  cf_padoffs,       // padding loop offset
   input  offset_t        [ACT_FM_LOOPS-1:0]       cf_paditer,       // padding loop iterator
   input  offset_t                                 cf_padstride,     // padding vector stride
   // to fu_in, to update non-padding pixel counter
   output logic                                    out_first,        // iterator first flags
   // data stream from input 0
   input  logic                                    padacc,           // accept padding
   // to pad_fu, per lane padding
   output logic                                    paden,            // enable padding
   output pad_mode_t                               padmode,          // pad mode: 0, -1, min, max
   output pad_inc_t                                padinc,           // pad increment mode: i16, v2i8, v4i4
   output offset_t        [VSIZE-1:0][ISIZE/4-1:0] padcpos,          // padding column position
   output logic           [VSIZE-1:0][ISIZE/4-1:0] padi4v            // vector for per i4 padding bits
   );
  logic                             in_req;             // new iteration loop
  logic                             in_ack;             // for verification only
  logic                             p_en;               // enable running position register
  logic                             cf_paden_r;         // enable padding
  pad_mode_t                        cf_padmode_r;       // if true pad with MININT
  pad_inc_t                         cf_padinc_r;        // padding increment mode register
  offset_t [1:0]                    cf_padlim_r;        // maxpooling and reduction window boundaries row&column
  offset_t [1:0]                    cf_padpos_r;        // padding start row&column
  offset_t [ACT_FM_LOOPS-1:0][1:0]  cf_padoffs_r;       // padding loop offset
  offset_t                          cf_padstride_r;     // padding vector stride
  logic                             it_req;             // iterator output valid
  logic                             it_ack;             // pass data from in to output
  logic    [ACT_FM_LOOPS-1:0]       it_first;           // iterator first flags
  logic    [ACT_FM_LOOPS-1:0]       it_last;            // iterator last flags
  offset_t [1:0]                    pos_nxt;            // next padding position
  offset_t [1:0]                    pos_upd;            // updated padding position
  logic                             out_en;             // enable output
  logic                             outval_r;           // output is valid
  offset_t [VSIZE-1:0][ISIZE/4-1:0] padcpos_r;          // output row position
  logic                             padrow_r;           // output row padding
  logic                             first_r;            // first pad in HLAPI
  logic                             outval_nxt;         // output is valid next
  offset_t [VSIZE-1:0][ISIZE/4-1:0] padcpos_nxt;        // output row position next
  logic                             padrow_nxt;         // output row padding next
  logic                             first_nxt;          // first pad in HLAPI

  
  // simple assignments
  assign in_req     = cf_en & cf_paden;
  assign p_en       = cf_en | (it_req & it_ack);
  assign pos_nxt    = cf_en ? cf_padpos : pos_upd;
  assign paden      = cf_paden_r;
  assign padmode    = cf_padmode_r;
  assign padinc     = cf_padinc_r;
  assign padcpos    = padcpos_r;
  assign out_en     = it_req & it_ack;
  assign it_ack     = padacc | ~outval_r;
  assign outval_nxt = (outval_r & (~padacc)) | (it_req & it_ack);
  assign padrow_nxt = signed'(cf_padpos_r[1]) < signed'(0) || signed'(cf_padpos_r[1]) > signed'(cf_padlim_r[1]);
  assign first_nxt  = &it_first;
  assign out_first  = first_r;

  
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :Intentionally unconnected
  //
  // Iterator instance
  //
  npu_iterator
    #(.N ( ACT_FM_LOOPS )) // number of nested loops
  iter_inst
    (
     .clk      ( clk        ), // clock
     .rst_a    ( rst_a      ), // asynchronous reset, active high
     .soft_rst ( 1'b0       ), // soft reset of address generator
     .in_req   ( in_req     ), // start new iteration
     .in_ack   ( in_ack     ), // acknowledge start, intentionally unconnected
     .in_shp   ( cf_paditer ), // shape of the iterator
     .it_req   ( it_req     ), // intentionally left open
     .it_ack   ( it_ack     ), // iterator accept
     .it_first ( it_first   ),
     .it_last  ( it_last    ), // last bits
     .it_vald  (            )  // intentionally left open
     );
// spyglass enable_block W287b

  // padding updates
  // outputs: pos_upd
  always_comb
  begin : pad_nxt_PROC
    offset_t [1:0] inc;
    // select offset
    inc = cf_padoffs_r[0];
    for (int r = 1; r < ACT_FM_LOOPS; r++)
    begin
      if (~it_last[r])
      begin
        inc = cf_padoffs_r[r];
      end
    end
    // inrement by offset
    pos_upd[0] = cf_padpos_r[0] + inc[0];
    pos_upd[1] = cf_padpos_r[1] + inc[1];
  end : pad_nxt_PROC

  
  // precompute column position
  // outputs: padcpos_nxt
// spyglass disable_block W164a
//SMD:Width Mismatch
//SJ :No overflow in below "+" operation and it won't influence result
generate
  if(VSIZE==8) begin
  always_comb
  begin : pad_PROC
    // strided offsets
    offset_t [11:0] sumof2;
    offset_t [31:0] sumof3;
    sumof2[0] = cf_padpos_r[0] + cf_padstride_r;                   // +1*stride
    sumof2[1] = cf_padpos_r[0] + {cf_padstride_r[14:0],1'b0};      // +2*stride
    sumof2[2] = cf_padpos_r[0] + {cf_padstride_r[13:0],2'b00};     // +4*stride
    sumof2[3] = cf_padpos_r[0] + {cf_padstride_r[12:0],3'b001};    // +8*stride+1
    sumof2[4] = cf_padpos_r[0] + {cf_padstride_r[12:0],3'b000};    // +8*stride
    sumof2[5] = cf_padpos_r[0] + {cf_padstride_r[11:0],4'b0001};   // +16*stride+1
    sumof2[6] = cf_padpos_r[0] + {cf_padstride_r[11:0],4'b0000};   // +16*stride
    sumof2[7] = cf_padpos_r[0] + {cf_padstride_r[10:0],5'b00001};  // +32*stride+1
    // extra offsets
    sumof2[8]  = {cf_padstride_r[14:0],1'b0}   + cf_padstride_r;               // 3*stride
    sumof2[9]  = {cf_padstride_r[13:0],2'b00}  + cf_padstride_r;               // 5*stride
    sumof2[10] = {cf_padstride_r[13:0],2'b00}  + {cf_padstride_r[14:0],1'b0};  // 6*stride
    sumof2[11] = {cf_padstride_r[12:0],3'b001} + ~ cf_padstride_r;             // 7*stride

    sumof3[0]  = cf_padpos_r[0];                                   // +0*stride
    sumof3[1]  = sumof2[0];                                        // +1*stride
    sumof3[2]  = sumof2[1];                                        // +2*stride
    sumof3[3]  = sumof2[1] + cf_padstride_r;                       // +3*stride=(1+2)*stride
    sumof3[4]  = sumof2[2];                                        // +4*Stride
    sumof3[5]  = sumof2[2] + cf_padstride_r;                       // +5*stride=(1+4)*stride
    sumof3[6]  = sumof2[2] + {cf_padstride_r[14:0], 1'b0};         // +6*stride=(2+4)*stride
    sumof3[7]  = sumof2[3] + ~cf_padstride_r;                      // +7*stride=(8-1)*stride=8*stride+~stride+1
    sumof3[8]  = sumof2[4];                                        // +8*stride
    sumof3[9]  = sumof2[4] + cf_padstride_r;                       // +9*stride=(1+8)*stride
    sumof3[10] = sumof2[4] + {cf_padstride_r[14:0], 1'b0};         // +10*stride=(2+8)*stride
    sumof3[11] = sumof2[4] + sumof2[8];                            // +11*stride=(3+8)*stride
    sumof3[12] = sumof2[4] + {cf_padstride_r[13:0], 2'b00};        // +12*stride=(4+8)*stride
    sumof3[13] = sumof2[4] + sumof2[9];                            // +13*stride=(5+8)*stride
    sumof3[14] = sumof2[5] + ~{cf_padstride_r[14:0], 1'b0};        // +14*stride=(16-2)*stride=16*stride+~2*stride+1
    sumof3[15] = sumof2[5] + ~cf_padstride_r;                      // +15*stride=(16-1)*stride=16*stride+~stride+1
    sumof3[16] = sumof2[6];                                        // +16*stride
    sumof3[17] = sumof2[6] + cf_padstride_r;                       // +17*stride=(1+16)*stride
    sumof3[18] = sumof2[6] + {cf_padstride_r[14:0], 1'b0};         // +18*stride=(2+16)*stride
    sumof3[19] = sumof2[6] + sumof2[8];                            // +19*stride=(3+16)*stride
    sumof3[20] = sumof2[6] + {cf_padstride_r[13:0],2'b00};         // +20*stride=(4+16)*stride
    sumof3[21] = sumof2[6] + sumof2[9];                            // +21*stride=(5+16)*stride
    sumof3[22] = sumof2[6] + sumof2[10];                           // +22*stride=(6+16)*stride
    sumof3[23] = sumof2[6] + sumof2[11];                           // +23*stride=(7+16)*stride
    sumof3[24] = sumof2[6] + {cf_padstride_r[12:0],3'b000};        // +24*stride=(8+16)*stride
    sumof3[25] = sumof2[7] + ~sumof2[11];                          // +25*stride=(32-7)*stride=32*stride+~7*stride+1
    sumof3[26] = sumof2[7] + ~sumof2[10];                          // +26*stride=(32-6)*stride=32*stride+~6*stride+1
    sumof3[27] = sumof2[7] + ~sumof2[9];                           // +27*stride=(32-5)*stride=32*stride+~5*stride+1
    sumof3[28] = sumof2[7] + ~{cf_padstride_r[13:0],2'b00};        // +28*stride=(32-4)*stride=32*stride+~4*stride+1
    sumof3[29] = sumof2[7] + ~sumof2[8];                           // +29*stride=(32-3)*stride=32*stride+~3*stride+1
    sumof3[30] = sumof2[7] + ~{cf_padstride_r[14:0],1'b0};         // +30*stride=(32-2)*stride=32*stride+~2*stride+1
    sumof3[31] = sumof2[7] + ~cf_padstride_r;                      // +31*stride=(32-1)*stride=32*stride+~1*stride+1
    case(cf_padinc_r)
    pad_inc_v2i8_e:
      begin
        for (int v = 0; v < VSIZE; v++)
        begin
          padcpos_nxt[v][0] = sumof3[2*v];
          padcpos_nxt[v][1] = sumof3[2*v];
          padcpos_nxt[v][2] = sumof3[2*v+1];
          padcpos_nxt[v][3] = sumof3[2*v+1];
        end
      end
    pad_inc_v4i4_e:
      begin
        for (int v = 0; v < VSIZE; v++)
        begin
          padcpos_nxt[v][0] = sumof3[4*v];
          padcpos_nxt[v][1] = sumof3[4*v+1];
          padcpos_nxt[v][2] = sumof3[4*v+2];
          padcpos_nxt[v][3] = sumof3[4*v+3];
        end
      end
    default:
      begin
        for (int v = 0; v < VSIZE; v++)
        begin
          for (int j = 0; j < ISIZE/4; j++)
          begin
            padcpos_nxt[v][j] = sumof3[v];
          end
        end
      end
    endcase
  end : pad_PROC
// spyglass enable_block W164a
  end
  else if(VSIZE==2) begin
    always_comb
    begin : pad_PROC
      offset_t [3:0] sumof2;
      sumof2[0] = cf_padpos_r[0] + cf_padstride_r;                   // +1*stride
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
      sumof2[1] = cf_padpos_r[0] + {cf_padstride_r[14:0],1'b0};      // +2*stride
      sumof2[2] = cf_padpos_r[0] + {cf_padstride_r[13:0],2'b00};     // +4*stride
      sumof2[3] = cf_padpos_r[0] + {cf_padstride_r[12:0],3'b001};    // +8*stride+1
// spyglass enable_block W164a
      // strided offsets
      case(cf_padinc_r)
      pad_inc_v2i8_e:
        begin
          padcpos_nxt[0][0] = cf_padpos_r[0];                                  // +0*stride
          padcpos_nxt[0][1] = cf_padpos_r[0];                                  // +0*stride
          padcpos_nxt[0][2] = sumof2[0];                                       // +1*stride
          padcpos_nxt[0][3] = sumof2[0];                                       // +1*stride
          padcpos_nxt[1][0] = sumof2[1];                                       // +2*stride
          padcpos_nxt[1][1] = sumof2[1];                                       // +2*stride
          padcpos_nxt[1][2] = sumof2[1] + cf_padstride_r;                      // +3*stride
          padcpos_nxt[1][3] = sumof2[1] + cf_padstride_r;                      // +3*stride
        end
      pad_inc_v4i4_e:
        begin
          padcpos_nxt[0][0] = cf_padpos_r[0];                                  // +0*stride
          padcpos_nxt[0][1] = sumof2[0];                                       // +1*stride
          padcpos_nxt[0][2] = sumof2[1];                                       // +2*stride
          padcpos_nxt[0][3] = sumof2[1] + cf_padstride_r;                      // +3*stride
          padcpos_nxt[1][0] = sumof2[2];                                       // +4*stride
          padcpos_nxt[1][1] = sumof2[2] + cf_padstride_r;                      // +5*stride
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
          padcpos_nxt[1][2] = sumof2[2] + {cf_padstride_r[14:0],1'b0};         // +6*stride
// spyglass enable_block W164a
          padcpos_nxt[1][3] = sumof2[3] + ~cf_padstride_r;                     // +7*stride=(8-1)*stride=8*stride+~stride+1
        end
      default:
        begin
          for (int j = 0; j < ISIZE/4; j++)
          begin
            padcpos_nxt[0][j] = cf_padpos_r[0];                                // +0*stride
            padcpos_nxt[1][j] = sumof2[0];                                     // +1*stride
          end
        end
      endcase
    end : pad_PROC
  end
endgenerate

  // precompute padding bit per position
  always_comb
  begin : padv_PROC
    offset_t cposv;
    for (int v = 0; v < VSIZE; v++)
    begin
      for (int j = 0; j < ISIZE/4; j++)
      begin
        cposv = padcpos_r[v][j];
        padi4v[v][j] = padrow_r || (signed'(cposv) < signed'(0)) || (signed'(cposv) > signed'(cf_padlim_r[0]));
      end
    end
  end : padv_PROC
  
  // capture configuration and running position counter
  always_ff @(posedge clk or
              posedge rst_a)
  begin : pad_reg_PROC
    if (rst_a == 1'b1)
    begin
      cf_paden_r     <= '0;
      cf_padmode_r   <= pad_mode_zero_e;
      cf_padinc_r    <= pad_inc_i16_e;
      cf_padlim_r    <= '0;
      cf_padoffs_r   <= '0;
      cf_padstride_r <= '0;
      cf_padpos_r    <= '0;
      outval_r       <= 1'b0;
      padrow_r       <= 1'b0;
      padcpos_r      <= '0;
      first_r        <=  1'b0;
    end
    else
    begin
      if (cf_en)
      begin
        cf_paden_r     <= cf_paden;
        cf_padmode_r   <= cf_padmode;
        cf_padinc_r    <= cf_padinc;
        cf_padlim_r    <= cf_padlim;
        cf_padoffs_r   <= cf_padoffs;
        cf_padstride_r <= cf_padstride;
      end
      if (p_en)
      begin
        cf_padpos_r    <= pos_nxt;
      end
      outval_r         <= outval_nxt; 
      if (out_en)
      begin
        padrow_r       <= padrow_nxt;
        padcpos_r      <= padcpos_nxt;
        first_r        <= first_nxt;
      end
    end
  end : pad_reg_PROC
  
`ifdef ABV_ON
  //
  // Assertions
  //
  property prop_ackempty;
  @(posedge clk) disable iff (rst_a !== 1'b0) padacc |-> (outval_r | ~cf_paden_r);
  endproperty : prop_ackempty
  a_ackempty: assert property (prop_ackempty) else $fatal(1, "Error: invalid padding flow");
  property prop_idle;
    @(posedge clk) disable iff (rst_a !== 1'b0) cf_en |-> in_ack;
  endproperty : prop_idle
  a_idle: assert property (prop_idle) else $fatal(1, "Error: cannot accept new padding sequence");
`endif
  
endmodule : npu_gtoa_pad
