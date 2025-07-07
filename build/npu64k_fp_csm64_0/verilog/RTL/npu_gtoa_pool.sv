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
 * This module implements the fused maxpooling unit
 */

module npu_gtoa_pool
  import npu_types::*;
  import npu_gtoa_types::*;
  (
   input  logic                         clk,               // clock
   input  logic                         rst_a,             // asynchronous reset, active high
   // input data and handshake
   input  logic                         in_valid,          // input data valid
   output logic                         in_accept,         // input data is accepted
   input  vyixacc_t                     in_data,           // input data 
   // hlapi inputs
   input  logic                         hlp_valid,         // hlapi is valid
   input  logic                         iter_req,          // request start new iteration
   input  offset_t [ACT_POOL_LOOPS-1:0] pool_par_iter,     // hlapi pooling iterations
   input  act_pool_mode_t               pool_par_mode,     // hlapi pooling mode
   input  act_pool_size_t               pool_par_size,     // hlapi pooling size
   input  logic                         pool_par_dbl,      // hlapi pooling double wide
   input  fmode_t                       pool_fmode,        // hlapi pooling floating point mode
   input  offset_t                      padpos_col,        // padding start column
   // maxpool stash read/write
   input  logic                         mpst_rd_valid,     // maxpool stash read data valid , 1 bit only
   output logic                         mpst_rd_accept,    // maxpool stash read data accept
   input  ixpix_t         [1:0]         mpst_rd_data,      // maxpool stash read data
   output logic                         mpst_wr_valid,     // maxpool stash write data valid
   input  logic                         mpst_wr_accept,    // maxpool stash write accept
   output ixpix_t         [1:0]         mpst_wr_data,      // maxpool stash write data
   // streaming output
   output logic                         out_valid,         // output data valid
   input  logic                         out_accept,        // accept output data
   output vyixacc_t                     out_data,          // output data
   // flow control
   output logic                         busy,              // pooling is busy
   output logic                         ostall             // stall output
   );

  
  // local types
  typedef enum logic [1:0] { pool_state_idle, pool_state_init, pool_state_run } pool_state_t;
  typedef logic unsigned [8:0] pix9_t;
  typedef pix9_t   [ISIZE-1:0] ixpix9_t;
  typedef ixpix9_t [VSIZE-1:0] vyixpix9_t;
  // local wires
  logic                               bp_val_r;          // bypass output valid
  logic                               bp_val_nxt;        // bypass output valid next
  logic                         [3:0] wr_val_r;          // output valid, delay line
  logic                         [3:0] wr_val_nxt;        // output valid, next, delay line
  logic                         [3:0] wr_val_cyc2_r;     // output valid cycle 2, delay line
  logic                         [3:0] wr_val_cyc2_nxt;   // output valid cycle 2, next, delay line
  vyixacc_t                           in_data_i;         // input data converted
  vyixpix_t                           stg0_data_r;       // output data stage 0
  vyixpix_t                           stg0_data_i;       // output data stage 0 internal
  vyixpix_t                           stg0_data_nxt;     // output data stage 0 next
  ixpix9_t              [VSIZE+2-1:0] stg1_data_r;       // output data stage 1
  ixpix9_t              [VSIZE+2-1:0] stg1_data_nxt;     // output data stage 1 next
  vyixpix9_t                          stg2_data_r;       // output data stage 2
  vyixpix9_t                          stg2_data_nxt;     // output data stage 2 next
  vyixacc_t                           stg3_data_r;       // output data stage 3
  vyixacc_t                           stg3_data_nxt;     // output data stage 3 next
  logic                         [3:0] wr_en;             // write enable
  logic                               stall_int;         // internal stall
  logic                               stall_int_r;       // internal stall delayed
  logic                               in_hs;             // input handshake
  logic                               in_hs1;            // input handshake, excluding stash read stall
  logic                               in_hs_r;           // input handshake delayed
  logic                               pool_bypass;       // bypass pooling
  act_pool_mode_t                     pool_par_mode_r;   // pooling parameter mode register
  act_pool_size_t                     pool_par_size_r;   // pooling parameter size register
  logic                               pool_par_dbl_r;    // pooling double wide register
  fmode_t                             pool_fmode_r;      // pooling floating point mode register
  act_pool_mode_t                     pool_par_mode_mc2; // pooling parameter mode register
  act_pool_size_t                     pool_par_size_mc2; // pooling parameter size register
  logic                               pool_par_dbl_mc2;  // pooling double wide register
  fmode_t                             pool_fmode_mc2;    // pooling floating point mode register
  offset_t                            padpos_col_r;      // padding start column register
  // FSM
  pool_state_t                        pool_state_r;      // pooling FSM state
  pool_state_t                        pool_state_nxt;    // pooling FSM next state
  logic                               pool_state_en;     // pooling FSM register enable
  logic                               pool_init_en;      // pooling FSM initialize enable
  // iterator
  logic                               iter_reqi;         // iterator request internal
  logic                               it_req;            // iterator valid
  logic          [ACT_POOL_LOOPS-1:0] it_first;          // first bits
  logic          [ACT_POOL_LOOPS-1:0] it_last;           // last bits
  // stash read/write control
  logic                               mpst_rstall_r;     // stall on maxpool stash read/write
  logic                               mpst_wstall_r;     // stall on maxpool stash read/write
  logic                               mpst_rstall_nxt;   // stall on maxpool stash read/write next
  logic                               mpst_wstall_nxt;   // stall on maxpool stash read/write next
  logic                               mpst_rstall_en;    // stall read enable
  logic                               mpst_wstall_en;    // stall write enable
  ixpix_t                       [1:0] mpst_rd_data_r;    // maxpool stash read data
  // pooling state variables, delay line
  logic          [ACT_POOL_LOOPS-1:0] stg0_it_first_r;   // first bits delayed for stage 1
  logic          [ACT_POOL_LOOPS-1:0] stg0_it_first_nxt; // first bits delayed for stage 1 next
  logic                               pool_ptr_upd_en;   // pooling pointer update enable
  logic                               pool_valid_in;     // pooling valid at input stage
  logic                         [3:0] pool_valid_r;      // delay line of pooling valid (stage 0,1,2,3)
  logic                         [3:0] pool_valid_nxt;    // delay line of pooling valid next (stage 0,1,2,3)
  offset_t                            chni_r;            // index of current channel group
  offset_t                            chni_nxt;          // index of current channel group next
  offset_t                            rcnti_r;           // row count from 0 for strided output
  offset_t                            rcnti_nxt;         // row count from 0 for strided output next
  offset_t                      [1:0] chn_r;             // delay line of index of current channel group (stage 0,1)
  offset_t                      [1:0] chn_nxt;           // delay line of index of current channel group next (stage 0,1)
  vyixpix9_t                    [3:0] pre_r;             // previous line for 4 channels, already max'ed across the row (stage 2)
  vyixpix9_t                    [3:0] pre_nxt;           // previous line next for 4 channels, already max'ed across the row (stage 2)
  vyixpix9_t                    [3:0] prepre_r;          // previous line 2 for 4 channels, already max'ed across the row (stage 2)
  vyixpix9_t                    [3:0] prepre_nxt;        // previous line 2 next for 4 channels, already max'ed across the row (stage 2)
  // internal wires for pooling
  logic                               stash_one;         // stash one column
  logic                               stash_two;         // stash two columns
  logic                               st_gte_hi;         // stash greater or equal msb
  logic                               st_eq_hi;          // stash equal msb
  logic                               st_gte_lo;         // stash greater or equal lsb
  logic                               st_lo_sel;         // stash selector lsb
  act_pool_mode_t                     modei;             // pooling mode
  act_pool_size_t                     sizei;             // pooling size
  vyixpix_t                           pix_data;          // internal pixel data
  vyixpix_t                           pix_res;           // internal pixel result
  vyixpix_t                           pix_res_i;         // internal pixel result convert
  vyixpix_t                           pix_res_r;         // internal pixel result registered
  vyixpix9_t                          cmax;              // internal column max
  vyixpix9_t                          rmax;              // internal row max
  vyixpix9_t                          out9;              // internal 9bit output
  logic                 [ISIZE/2-1:0] cexta;             // column extended bit a
  logic                 [ISIZE/2-1:0] cextb;             // column extended bit b
  logic                 [ISIZE/2-1:0] cextc;             // column extended bit c
  logic                 [ISIZE/2-1:0] rexta;             // row extended bit a
  logic                 [ISIZE/2-1:0] rextb;             // row extended bit b
  logic                 [ISIZE/2-1:0] rextc;             // row extended bit c
  ixpix_t               [VSIZE+2-1:0] cur;               // internal current line
  ixpix9_t              [VSIZE+2-1:0] cur9;              // internal current line extended
  pix9_t                              hi_mask;           // mask for msb to convert to unsigned comparison
  pix9_t                              lo_mask;           // mask for lsb to convert to unsigned comparison
  ixpix_t                             cp;                // internal compare data
  logic                         [1:0] pad_st_col;        // pad stash column
  ixpix_t                             pad_val;           // padding value for stash
  logic                         [1:0] cgte;              // column greater than or equal flag
  logic                         [1:0] ceq;               // column equal flag
  logic                         [1:0] rgte;              // row greater than or equal flag
  logic                         [1:0] req;               // row equal flag
  logic                  signed [8:0] st_tmpa;           // stash temp a
  logic                  signed [8:0] st_tmpb;           // stash temp b
  pix9_t                              ctmpb;             // column temp extended b
  pix9_t                              ctmpc;             // column temp extended c
  pix9_t                              rtmpb;             // row temp extended b
  pix9_t                              rtmpc;             // row temp extended c
  logic                               dp_accept;         // data path can accept
  logic                               dp_accept1;        // data path can accept, excluding stash read stall
  logic                               dbl_tgl_r;         // toggle for double feature-map input
  logic                               dbl_tgl_nxt;       // toggle for double feature-map input next
  logic                               dbl_tgl_en;        // toggle enable
  logic                               out_valid_i;       // output valid internal
  logic                               in_accept_i;       // input accept internal
  localparam int IXP_SZ   = $bits(ixpix_t);
  localparam int CUR_SZ   = (VSIZE+2)*IXP_SZ;
  localparam int MPST_SZ  = 2*IXP_SZ;


  // simple assignments
  assign pool_bypass  = pool_par_mode_mc2 == pnone;
  assign ostall       = pool_bypass ? (in_valid & bp_val_r & ~out_accept) : (out_valid_i & ~out_accept);
  assign stall_int    = mpst_rstall_nxt | mpst_wstall_nxt | ostall;
  assign out_valid    = pool_bypass ? bp_val_r : out_valid_i;
  assign out_data     = stg3_data_r;
  assign dp_accept    = ((pool_state_r == pool_state_run) & (~stall_int));
  assign dp_accept1   = ((pool_state_r == pool_state_run) & (~ostall) & (~mpst_wstall_nxt));
  assign in_accept    = pool_bypass ? (~bp_val_r | out_accept) : in_accept_i;
  assign in_hs        = dp_accept & in_valid;
  assign in_hs1       = dp_accept1 & in_valid;
  assign stash_one    = ((pool_par_mode_mc2 == pcol) || (pool_par_mode_mc2 == prowcol)) && ((pool_par_size_mc2 == p2s1) || (pool_par_size_mc2 == p3s2));
  assign stash_two    = ((pool_par_mode_mc2 == pcol) || (pool_par_mode_mc2 == prowcol)) && (pool_par_size_mc2 == p3s1);
  assign mpst_rd_accept = pool_bypass ? 1'b0 : ((mpst_rstall_r & in_hs_r) | in_hs1) && (stash_one || stash_two);
  assign mpst_wr_valid  = pool_bypass ? 1'b0 : (mpst_wstall_r | (~stall_int_r & in_hs_r)) && (stash_one || stash_two);
  assign busy         = pool_bypass ? bp_val_r : (wr_val_r != '0);
  assign modei        = pool_par_mode_mc2;
  assign sizei        = pool_par_size_mc2;
  assign dbl_tgl_en   = pool_par_dbl_mc2 & in_hs;
  assign hi_mask      = 9'b010000000;
  assign lo_mask      = pool_par_dbl_mc2 ? 9'b0 : 9'b010000000;

  // double wide feature-map input toggle
  // outputs: dbl_tgl_nxt
  always_comb
  begin : dbl_tgl_PROC
    if(dbl_tgl_en)
    begin
      dbl_tgl_nxt = ~dbl_tgl_r;
    end
    else
    begin
      dbl_tgl_nxt = dbl_tgl_r;
    end
  end : dbl_tgl_PROC

  // stash read/write stall
  always_comb
  begin : mpst_stall_PROC
    // default outputs
    mpst_rstall_nxt = 1'b0;
    mpst_wstall_nxt = 1'b0;
    mpst_rstall_en  = 1'b0;
    mpst_wstall_en  = 1'b0;
    if (mpst_rd_accept)
    begin
      mpst_rstall_en = 1'b1;
      if (~mpst_rd_valid)
      begin
        mpst_rstall_nxt = 1'b1;
      end
    end
    if (mpst_wr_valid)
      begin
      mpst_wstall_en = 1'b1;
      if (~mpst_wr_accept)
      begin
        mpst_wstall_nxt = 1'b1;
      end
    end
  end : mpst_stall_PROC

  // pooling FSM
  // next state of FSM
  // outputs: pool_state_en, pool_state_nxt
  always_comb
  begin : pool_fsm_nxt_PROC
    // default outputs
    pool_state_en  = 1'b0;
    pool_init_en   = 1'b0;
    iter_reqi      = 1'b0;
    pool_state_nxt = pool_state_idle;
    // state dependent
    case (pool_state_r)
      pool_state_run:
        begin
          if (it_req && in_hs && (&it_last))
          begin
            // done, go back to idle
            pool_state_en  = 1'b1;
            pool_state_nxt = pool_state_idle;
          end
        end
      pool_state_init:
        begin
          if (iter_req)
          begin
            // start pooling iteration
            pool_state_en  = 1'b1;
            pool_init_en   = 1'b1;
            iter_reqi      = (pool_par_mode_r != pnone);
            pool_state_nxt = pool_state_run;
          end
        end
      default: // pool_state_idle
        begin
          if (hlp_valid && (pool_par_mode != pnone))
          begin
            // start pooling iteration
            pool_state_en  = 1'b1;
            pool_init_en   = 1'b1;
            iter_reqi      = iter_req;
            pool_state_nxt = pool_state_init;
          end
        end
    endcase // case (pool_state_r)
  end :  pool_fsm_nxt_PROC

// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :Intentionally unconnected
  //
  // Pooling iterator
  //
  npu_iterator
    #(.N ( ACT_POOL_LOOPS )) // number of nested loops
  pool_iter_inst
    (
     .clk      ( clk             ), // clock
     .rst_a    ( rst_a           ), // asynchronous reset, active high
     .soft_rst ( 1'b0            ), // soft reset
     .in_req   ( iter_reqi       ), // start new iteration
     .in_ack   (                 ), // acknowledge start, intentionally unconnected
     .in_shp   ( pool_par_iter   ), // shape of the iterator
     .it_req   ( it_req          ), // iterator valid
     .it_ack   ( in_hs           ), // iterator accept
     .it_first ( it_first        ), // first bits
     .it_last  ( it_last         ), // last bits
     .it_vald  (                 )  // intentionally left open
     );
// spyglass enable_block W287b

  // shift write pipeline
  // outputs: wr_val_nxt, wr_en
  always_comb
  begin : wdel_PROC
    // shift data
    wr_val_nxt[0] = (wr_val_r[0] & stall_int) | (in_valid    & ~stall_int);
    wr_val_nxt[1] = (wr_val_r[1] & stall_int) | (wr_val_r[0] & ~stall_int);
    wr_val_nxt[2] = (wr_val_r[2] & stall_int) | (wr_val_r[1] & ~stall_int);
    wr_val_nxt[3] = (wr_val_r[3] & ostall   ) | (wr_val_r[2] & ~stall_int);
    bp_val_nxt    = pool_bypass & (in_valid | (bp_val_r & ~out_accept));
    wr_val_cyc2_nxt[0] = (wr_val_cyc2_r[0] & stall_int) | (in_valid & dbl_tgl_r & ~stall_int);
    wr_val_cyc2_nxt[1] = (wr_val_cyc2_r[1] & stall_int) | (wr_val_cyc2_r[0] & ~stall_int);
    wr_val_cyc2_nxt[2] = (wr_val_cyc2_r[2] & stall_int) | (wr_val_cyc2_r[1] & ~stall_int);
    wr_val_cyc2_nxt[3] = (wr_val_cyc2_r[3] & ostall   ) | (wr_val_cyc2_r[2] & ~stall_int);
    wr_en[0]      = in_valid    & (~stall_int) & (~pool_bypass);
    wr_en[1]      = wr_val_r[0] & (~stall_int) & (~pool_bypass);
    wr_en[2]      = wr_val_r[1] & (~stall_int) & (~pool_bypass);
    wr_en[3]      = (wr_val_r[2] & (~stall_int) & (~pool_bypass)) | (pool_bypass & in_valid & ~ostall);
  end : wdel_PROC

  // pooling pointer update
  // outputs: pool_ptr_upd_en, rcnti_nxt, chni_nxt
  always_comb
  begin : pool_ptr_PROC
    // default outputs
    pool_ptr_upd_en  = 1'b0;
    rcnti_nxt        = '0;
    chni_nxt         = '0;
    // initialize pointer when pool_init
    if (pool_init_en)
    begin
      pool_ptr_upd_en  = 1'b1;
      chni_nxt         = '0;
      rcnti_nxt        = '0;
    end
    // update pointer for new input
    else if (in_hs & (~pool_bypass))
    begin
      pool_ptr_upd_en = 1'b1;
      if (it_last[3:1] == 3'b111)
      begin
        rcnti_nxt = '0;
        chni_nxt  = '0;
      end
      else if (it_last[3:2] == 2'b11)
      begin
        rcnti_nxt = '0;
        chni_nxt  = '0;
      end
      else if (it_last[3] == 1'b1)
      begin
        rcnti_nxt = rcnti_r + 1'd1;
        chni_nxt  = '0;
      end
      else
      begin
        // next
        rcnti_nxt = rcnti_r;
        chni_nxt  = chni_r + 1'd1;
      end
    end
  end :  pool_ptr_PROC

  // output valid pipeline
  // outputs: pool_valid_nxt
  always_comb
  begin : odel_PROC
    pool_valid_in = 1'b0;
    if (in_hs)
    begin
      if(modei == pcol)
      begin
         case (sizei)
          p2s1:    pool_valid_in = 1'b1;
          p3s1:    pool_valid_in = 1'b1;
          p2s2:    pool_valid_in = (rcnti_r[0] == 1'b0);
          default: pool_valid_in = (rcnti_r[0] == 1'b0);
        endcase
      end
      else if((modei == prow) || (modei == prowcol))
      begin
        case (sizei)
          p2s1:    pool_valid_in = (rcnti_r > 0);
          p3s1:    pool_valid_in = (rcnti_r > 1);
          p2s2:    pool_valid_in = (rcnti_r[0] == 1'b1);
          default: pool_valid_in = (rcnti_r >1) && (rcnti_r[0] == 1'b0);
        endcase
      end
    end
    pool_valid_nxt[0] = (pool_valid_r[0] & stall_int) | (pool_valid_in   & ~stall_int);
    pool_valid_nxt[1] = (pool_valid_r[1] & stall_int) | (pool_valid_r[0] & ~stall_int);
    pool_valid_nxt[2] = (pool_valid_r[2] & stall_int) | (pool_valid_r[1] & ~stall_int);
    pool_valid_nxt[3] = (pool_valid_r[3] & ostall   ) | (pool_valid_r[2] & ~stall_int);
  end : odel_PROC

  // output based on dbl modes
  // outputs: out_valid_i, in_accept_i
  always_comb
  begin : oval_PROC
    if (pool_par_dbl_mc2)
    begin
      out_valid_i = wr_val_cyc2_r[3];
      in_accept_i = dp_accept & dbl_tgl_r;
    end
    else
    begin
      out_valid_i = wr_val_r[3];
      in_accept_i = dp_accept;
    end
    out_valid_i &= pool_valid_r[3];
  end : oval_PROC

  // 4 stage datapath
  // first stage
  always_comb
  begin : stg0_nxt_PROC
    // default output
    in_data_i     = '0;
    stg0_data_nxt = '0;
    chn_nxt[0]    = chni_r;
    stg0_it_first_nxt = it_first;
    // - read pooling put, set acceptance for stash read data
// spyglass disable_block SelfDeterminedExpr-ML
//SMD:Self determined expression
//SJ :Ignore (2 * i) and (2 * i + 1) self determine index
    if (pool_fmode_mc2 == fmode_fp16_e || pool_fmode_mc2 == fmode_bf16_e)
    begin
      for (int v = 0; v < VSIZE; v++)
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          in_data_i[v][i] = in_data[v][i] ^ {17'b0, {15{in_data[v][i][15]}}};
          if((pool_fmode_mc2 == fmode_fp16_e) && (in_data[v][i][14:10] == '1))
          begin
            in_data_i[v][i] = 32'h00008000;
          end
          else if((pool_fmode_mc2 == fmode_bf16_e) && (in_data[v][i][14:7] == '1))
          begin
            in_data_i[v][i] = 32'h00008000;
          end
        end
      end
    end
    else
    begin
      in_data_i = in_data;
    end
    for (int v = 0; v < VSIZE; v++)
    begin
      for (int i = 0; i < ISIZE/2; i++)
      begin
        if (~pool_par_dbl_mc2)
        begin
          stg0_data_nxt[v][2*i  ] = in_data_i[v][2*i  ][7:0];
          stg0_data_nxt[v][2*i+1] = in_data_i[v][2*i+1][7:0];
        end
        else if (~dbl_tgl_r)
        begin
          stg0_data_nxt[v][2*i  ] = in_data_i[v][i][ 7:0];
          stg0_data_nxt[v][2*i+1] = in_data_i[v][i][15:8];
        end
        else
        begin
          stg0_data_nxt[v][2*i  ] = in_data_i[v][i+ISIZE/2][ 7:0];
          stg0_data_nxt[v][2*i+1] = in_data_i[v][i+ISIZE/2][15:8];
        end
      end
    end
  end : stg0_nxt_PROC

  // second stage
  always_comb
  begin : stg1_nxt_PROC
    // default output
    // registers
    chn_nxt[1]    = '0;
    // read write ports
    mpst_wr_data  = {MPST_SZ{1'b0}};
    // data
    stg1_data_nxt = '0;
    // internal
    cur           = '0;
    cur9          = '0;
    cp            = '0;
    pad_val       = '0;
    pad_st_col    = '0;
    st_gte_hi     = '0;
    st_eq_hi      = '0;
    st_gte_lo     = '0;
    st_lo_sel     = '0;
    st_tmpa       = '0;
    st_tmpb       = '0;
    // - swap data with stash to get current line
    pix_data = stg0_data_r;
    for (int i = 0; i < ISIZE/2; i++)
    begin
      pad_val[2*i+1] = 8'h80;
      pad_val[2*i  ] = pool_par_dbl_mc2 ? 8'h00 : 8'h80;
    end

    // swapping with stash
    pad_st_col[0] = (stg0_it_first_r[1] == 1'b1) & (padpos_col_r < 16'h1);
    pad_st_col[1] = (stg0_it_first_r[1] == 1'b1) & (padpos_col_r < 16'h2);
    if (stash_one)
    begin
      cur[1] = pad_st_col[0] ? pad_val : mpst_rd_data_r[0];
      for (int i = 0; i < ISIZE/2; i++)
      begin
        st_gte_hi = pix_data[VSIZE-1][2*i+1] >= pix_data[VSIZE-2][2*i+1];
        st_eq_hi  = pix_data[VSIZE-1][2*i+1] == pix_data[VSIZE-2][2*i+1];
        st_tmpa   = pool_par_dbl_mc2 ? {1'b0, pix_data[VSIZE-1][2*i]} : {pix_data[VSIZE-1][2*i][7], pix_data[VSIZE-1][2*i]};
        st_tmpb   = pool_par_dbl_mc2 ? {1'b0, pix_data[VSIZE-2][2*i]} : {pix_data[VSIZE-2][2*i][7], pix_data[VSIZE-2][2*i]};
        st_gte_lo = st_tmpa >= st_tmpb;
        st_lo_sel = ((~pool_par_dbl_mc2) | (pool_par_dbl_mc2 & st_eq_hi)) ? st_gte_lo : st_gte_hi;
        cp[2*i+1] = st_gte_hi ? pix_data[VSIZE-1][2*i+1] : pix_data[VSIZE-2][2*i+1];
        cp[2*i  ] = st_lo_sel ? pix_data[VSIZE-1][2*i  ] : pix_data[VSIZE-2][2*i  ];
      end
      if(mpst_wr_valid)
      begin
        mpst_wr_data[0] = ((sizei == p3s2)? cp : pix_data[VSIZE-1]);
      end
      cur[0] = cur[1];
    end
    else if (stash_two)
    begin
      cur[1] = pad_st_col[0] ? pad_val: mpst_rd_data_r[0];
      cur[0] = pad_st_col[1] ? pad_val: mpst_rd_data_r[1];
      if(mpst_wr_valid)
      begin
        mpst_wr_data[0]     = pix_data[VSIZE-1];
        mpst_wr_data[1]     = pix_data[VSIZE-2];
      end
    end
    // filling current line
    for (int v = 0; v < VSIZE; v++)
    begin
      for (int i = 0; i < ISIZE; i++)
      begin
        cur[v+2][i] = pix_data[v][i];
      end
    end
    for (int v = 0; v < VSIZE+2; v++)
    begin
      for (int i = 0; i < ISIZE/2; i++)
      begin
        cur9[v][2*i+1] = {1'b0,cur[v][2*i+1]}^hi_mask;
        cur9[v][2*i  ] = {1'b0,cur[v][2*i  ]}^lo_mask;
      end
    end
// spyglass enable_block SelfDeterminedExpr-ML
    stg1_data_nxt = cur9;
    // kept next values
    chn_nxt[1] = chn_r[0];
  end : stg1_nxt_PROC

  // third stage
  always_comb
  begin : stg2_nxt_PROC
    // default output
    // registers
    pre_nxt      = pre_r;
    prepre_nxt   = prepre_r;
    // data
    stg2_data_nxt = '0;
    // internal
    cmax          = '0;
    rmax          = '0;
    cexta         = '0;
    cextb         = '0;
    cextc         = '0;
    rexta         = '0;
    rextb         = '0;
    rextc         = '0;
    cgte          = '0;
    ceq           = '0;
    rgte          = '0;
    req           = '0;
    ctmpb         = '0;
    ctmpc         = '0;
    rtmpb         = '0;
    rtmpc         = '0;
    // - column and row dimension pooling
// spyglass disable_block SelfDeterminedExpr-ML ImproperRangeIndex-ML
//SMD:Self determined expression
//SJ :Ignore (2 * i) and (2 * i + 1) self determine index
    for (int v = 0; v < VSIZE; v++)
    begin
      for (int i = 0; i < ISIZE/2; i++)
      begin
        // 2*i+1 half
        cmax[v][2*i+1] = stg1_data_r[v+2][2*i+1];
        if((modei == pcol) || (modei == prowcol))
        begin
          cgte[0] = cmax[v][2*i+1] >= stg1_data_r[v+1][2*i+1];
          ceq[0]  = cmax[v][2*i+1] == stg1_data_r[v+1][2*i+1];
          cexta[i] = (pool_par_dbl_mc2 & cgte[0]);
          cextb[i] = (pool_par_dbl_mc2 & (~cgte[0] | ceq[0]));
          cmax[v][2*i+1] = cgte[0] ? cmax[v][2*i+1] : stg1_data_r[v+1][2*i+1];
          if((sizei == p3s1) || (sizei == p3s2))
          begin
            cgte[1] = cmax[v][2*i+1] >= stg1_data_r[v][2*i+1];
            ceq[1]  = cmax[v][2*i+1] == stg1_data_r[v][2*i+1];
            cexta[i] = (pool_par_dbl_mc2 & cgte[0] & cgte[1]);
            cextb[i] = (pool_par_dbl_mc2 & (~cgte[0] | ceq[0]) & cgte[1]);
            cextc[i] = (pool_par_dbl_mc2 & (~cgte[1] | ceq[1]));
            cmax[v][2*i+1] = cgte[1] ? cmax[v][2*i+1] : stg1_data_r[v][2*i+1];
          end
        end
        rmax[v][2*i+1] = cmax[v][2*i+1];
        if((modei == prow) || (modei == prowcol))
        begin
          rgte[0] = rmax[v][2*i+1] >= pre_r[chn_r[1]][v][2*i+1];
          req[0]  = rmax[v][2*i+1] == pre_r[chn_r[1]][v][2*i+1];
          rexta[i] = (pool_par_dbl_mc2 & rgte[0]);
          rextb[i] = (pool_par_dbl_mc2 & (~rgte[0] | req[0]));
          rmax[v][2*i+1] = rgte[0] ? rmax[v][2*i+1] : pre_r[chn_r[1]][v][2*i+1];
          if((sizei == p3s1) || (sizei == p3s2))
          begin
            rgte[1] = rmax[v][2*i+1] >= prepre_r[chn_r[1]][v][2*i+1];
            req[1]  = rmax[v][2*i+1] == prepre_r[chn_r[1]][v][2*i+1];
            rexta[i] = (pool_par_dbl_mc2 & rgte[0] & rgte[1]);
            rextb[i] = (pool_par_dbl_mc2 & (~rgte[0] | req[0]) & rgte[1]);
            rextc[i] = (pool_par_dbl_mc2 & (~rgte[1] | req[1]));
            rmax[v][2*i+1] = rgte[1] ? rmax[v][2*i+1] : prepre_r[chn_r[1]][v][2*i+1];
          end
        end
        // 2*i+0 half
        ctmpb = {cextb[i],stg1_data_r[v+1][2*i][7:0]};
        ctmpc = {cextc[i],stg1_data_r[v][2*i][7:0]};
        rtmpb = {rextb[i],pre_r[chn_r[1]][v][2*i][7:0]};
        rtmpc = {rextc[i],prepre_r[chn_r[1]][v][2*i][7:0]};
        cmax[v][2*i] = {cexta[i],stg1_data_r[v+2][2*i][7:0]};
        if((modei == pcol) || (modei == prowcol))
        begin
          cmax[v][2*i] = cmax[v][2*i] >= ctmpb ? cmax[v][2*i] : ctmpb;
          if((sizei == p3s1) || (sizei == p3s2))
          begin
            cmax[v][2*i] = cmax[v][2*i] >= ctmpc ? cmax[v][2*i] : ctmpc;
          end
        end
        cmax[v][2*i] &= 9'b011111111;
        rmax[v][2*i] = {rexta[i], cmax[v][2*i][7:0]};
        if((modei == prow) || (modei == prowcol))
        begin
          rmax[v][2*i] = rmax[v][2*i] >= rtmpb ? rmax[v][2*i] : rtmpb;
          if((sizei == p3s1) || (sizei == p3s2))
          begin
            rmax[v][2*i] = rmax[v][2*i] >= rtmpc ? rmax[v][2*i] : rtmpc;
          end
        end
      end
    end
    prepre_nxt[chn_r[1]] = pre_r[chn_r[1]];
    pre_nxt[chn_r[1]] = cmax;
    stg2_data_nxt = rmax;
// spyglass enable_block SelfDeterminedExpr-ML ImproperRangeIndex-ML
  end : stg2_nxt_PROC

// fourth stage
  always_comb
  begin : stg3_nxt_PROC
    // default output
    stg3_data_nxt = '0;
    pix_res       = '0;
    pix_res_i     = '0;
    out9          = '0;
// spyglass disable_block SelfDeterminedExpr-ML
//SMD:Self determined expression
//SJ :Ignore
    // - pooling data output
    for (int v = 0; v < VSIZE; v++)
    begin
      for (int i = 0; i < ISIZE/2; i++)
      begin
        out9[v][2*i+1] = stg2_data_r[v][2*i+1] ^ hi_mask;
        out9[v][2*i  ] = stg2_data_r[v][2*i  ] ^ lo_mask;
      end
    end
    for (int v = 0; v < VSIZE/2; v++)
    begin
      for (int i = 0; i < ISIZE; i++)
      begin
        if ((modei == pcol) || (modei == prowcol))
        begin
          case (sizei)
            p2s1:
              begin
                pix_res_i[2*v  ][i] = out9[2*v  ][i][7:0];
                pix_res_i[2*v+1][i] = out9[2*v+1][i][7:0];
              end
            p3s1:
              begin
                pix_res_i[2*v  ][i] = out9[2*v  ][i][7:0];
                pix_res_i[2*v+1][i] = out9[2*v+1][i][7:0];
              end
            p3s2:
              begin
                pix_res_i[v][i] = out9[2*v][i][7:0];
              end
            default:  // p2s2
              begin
                pix_res_i[v][i] = out9[2*v+1][i][7:0];
              end
          endcase
        end
        else
        begin
          pix_res_i[2*v  ][i] = out9[2*v  ][i][7:0];
          pix_res_i[2*v+1][i] = out9[2*v+1][i][7:0];
        end
      end
    end
    if (pool_fmode_mc2 == fmode_fp16_e || pool_fmode_mc2 == fmode_bf16_e)
    begin
      for (int v = 0; v < VSIZE; v++)
      begin
        for (int i = 0; i < ISIZE/2; i++)
        begin
          pix_res[v][2*i  ] = pix_res_i[v][2*i  ] ^ {8{pix_res_i[v][2*i+1][7]}};
          pix_res[v][2*i+1] = pix_res_i[v][2*i+1] ^ {1'b0,{7{pix_res_i[v][2*i+1][7]}}};
        end
      end
    end
    else
    begin
      pix_res = pix_res_i;
    end
    for (int v = 0; v < VSIZE; v++)
    begin
      for (int i = 0; i < ISIZE/2; i++)
      begin
        if (~pool_par_dbl_mc2)
        begin
          stg3_data_nxt[v][i        ] = {24'h0,pix_res[v][i        ]};
          stg3_data_nxt[v][i+ISIZE/2] = {24'h0,pix_res[v][i+ISIZE/2]};
        end
        else begin
          stg3_data_nxt[v][i        ] = {16'h0,pix_res_r[v][2*i+1], pix_res_r[v][2*i]};
          stg3_data_nxt[v][i+ISIZE/2] = {16'h0,  pix_res[v][2*i+1],   pix_res[v][2*i]};
        end
      end
    end
    if (pool_bypass)
    begin
      stg3_data_nxt = in_data;
    end
// spyglass enable_block SelfDeterminedExpr-ML
  end : stg3_nxt_PROC

  // register
  always_ff @(posedge clk or
              posedge rst_a)
  begin : reg_PROC
    if (rst_a == 1'b1)
    begin
      bp_val_r       <= 1'b0;
      wr_val_r       <= '0;
      wr_val_cyc2_r  <= '0;
      stg0_data_r    <= '0;
      stg1_data_r    <= '0;
      stg2_data_r    <= '0;
      stg3_data_r    <= '0;
      pool_par_mode_r<= pnone;
      pool_par_size_r<= p2s1;
      pool_par_dbl_r <= 1'b0;
      pool_fmode_r   <= fmode_int32_e;
      padpos_col_r   <= '0;
      pool_state_r   <= pool_state_idle;
      pool_valid_r   <= '0;
      stg0_it_first_r<= '0;
      chni_r         <= '0;
      rcnti_r        <= '0;
      chn_r          <= '0;
      mpst_rd_data_r <= '0;
      pre_r          <= '0;
      prepre_r       <= '0;
      in_hs_r        <= 1'b0;
      mpst_rstall_r  <= 1'b0;
      mpst_wstall_r  <= 1'b0;
      stall_int_r    <= 1'b0;
      dbl_tgl_r      <= 1'b0;
      pix_res_r      <= '0;
    end
    else
    begin
      bp_val_r       <= bp_val_nxt;
      wr_val_r       <= wr_val_nxt;
      wr_val_cyc2_r  <= wr_val_cyc2_nxt;
      in_hs_r        <= in_hs;
      pool_valid_r   <= pool_valid_nxt;
      stall_int_r    <= stall_int;
      if (hlp_valid)
      begin
        pool_par_mode_r <= pool_par_mode;
        pool_par_size_r <= pool_par_size;
        pool_par_dbl_r  <= pool_par_dbl;
        pool_fmode_r    <= pool_fmode;
        padpos_col_r    <= padpos_col;
      end
      if (dbl_tgl_en)
      begin
        dbl_tgl_r <= dbl_tgl_nxt;
      end
      if (pool_state_en)
      begin
        pool_state_r <= pool_state_nxt;
      end
      if (pool_ptr_upd_en)
      begin
        rcnti_r      <= rcnti_nxt;
        chni_r       <= chni_nxt;
      end
      if (mpst_rstall_en)
      begin
        mpst_rstall_r <= mpst_rstall_nxt;
      end
      if (mpst_wstall_en)
      begin
        mpst_wstall_r <= mpst_wstall_nxt;
      end
      if (mpst_rd_valid & mpst_rd_accept)
      begin
        mpst_rd_data_r <= mpst_rd_data;
      end
      if (wr_en[0])
      begin
        stg0_data_r  <= stg0_data_nxt;
        chn_r[0]     <= chn_nxt[0];
        stg0_it_first_r <= stg0_it_first_nxt;
      end
      if (wr_en[1])
      begin
        stg1_data_r  <= stg1_data_nxt;
        chn_r[1]     <= chn_nxt[1];
      end
      if (wr_en[2])
      begin
        stg2_data_r  <= stg2_data_nxt;
        pre_r        <= pre_nxt;
        prepre_r     <= prepre_nxt;
      end
      if (wr_en[3])
      begin
        stg3_data_r  <= stg3_data_nxt;
        if (pool_par_dbl_mc2)
        begin
          pix_res_r <= pix_res;
        end
      end
    end
  end : reg_PROC


  //
  // Multi-cycle paths
  //
  npu_2cyc_checker 
    #( 
       .WIDTH ( $bits(act_pool_mode_t) )
       )
  u_pool_par_mode_mc2_inst
    (
     .clk      ( clk                                           ),
     .rst_a    ( rst_a                                         ),
     .valid    ( 1'b1                                          ),
     .data_in  ( pool_par_mode_r[$bits(act_pool_mode_t)-1:0]   ),
     .data_out ( pool_par_mode_mc2[$bits(act_pool_mode_t)-1:0] )
     );
  npu_2cyc_checker 
    #( 
       .WIDTH ( $bits(act_pool_size_t) )
       )
  u_pool_par_size_mc2_inst
    (
     .clk      ( clk                                           ),
     .rst_a    ( rst_a                                         ),
     .valid    ( 1'b1                                          ),
     .data_in  ( pool_par_size_r[$bits(act_pool_size_t)-1:0]   ),
     .data_out ( pool_par_size_mc2[$bits(act_pool_size_t)-1:0] )
     );
  npu_2cyc_checker 
    #( 
       .WIDTH ( 1 )
       )
  u_pool_par_dbl_mc2_inst
    (
     .clk      ( clk               ),
     .rst_a    ( rst_a             ),
     .valid    ( 1'b1              ),
     .data_in  ( pool_par_dbl_r    ),
     .data_out ( pool_par_dbl_mc2  )
     );
  npu_2cyc_checker 
    #( 
       .WIDTH ( $bits(fmode_t) )
       )
  u_pool_fmode_mc2_inst
    (
     .clk      ( clk                                ),
     .rst_a    ( rst_a                              ),
     .valid    ( 1'b1                               ),
     .data_in  ( pool_fmode_r[$bits(fmode_t)-1:0]   ),
     .data_out ( pool_fmode_mc2[$bits(fmode_t)-1:0] )
     );

endmodule : npu_gtoa_pool
