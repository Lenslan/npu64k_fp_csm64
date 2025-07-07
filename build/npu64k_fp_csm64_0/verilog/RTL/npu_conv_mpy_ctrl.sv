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

//
// convolution multiplier array module
// vcs -sverilog +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_iterator.sv npu_conv_types.sv npu_conv_mpy_ctrl.sv
// analyze -format sverilog [list ../../../shared/RTL/npu_types.sv ../../../shared/RTL/npu_iterator.sv ../npu_conv_types.sv ../npu_conv_mpy_ctrl.sv]
//

`include "npu_defines.v"

`include "npu_conv_macros.svh"


module npu_conv_mpy_ctrl
  import npu_types::*;
  import npu_conv_types::*;
  #(parameter logic NPU_HAS_FLOAT = 1)
  (
   // Clock and reset
   input  logic                    clk,                 // Clock, all logic clocked at posedge
   input  logic                    rst_a,               // Asynchronous reset, active high
   // HLAPI interface
   input  logic                    hlapi_valid,         // Request new HLAPI start
   output logic                    hlapi_accept,        // Acknowledge new HLAPI start
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore packed signal
   input  conv_hlapi_i_t           hlapi_i,             // HLAPI parameters
// spyglass enable_block W240
   // Stash interface
   input  logic                    stash_valid,         // Stash output to multipliers is valid
   output logic                    stash_accept,        // Multiplier accepts stash output
   // Coefficient interface
   input  logic                    coef_valid,          // Coefficient output to multipliers is valid
   output logic                    coef_accept,         // Multiplier accepts coefficient output
   // AM read interface
   input  logic                    ar_valid,            // Accumulator is valid
   output logic                    ar_accept,           // Accumulator is accepted
   // AM write interface
   output logic                    aw_valid,            // Accumulator is valid
   input  logic                    aw_accept,           // Accumulator is accepted
   output logic                    aw_keep,             // If true then keep result in AM else stream
   input  logic                    aw_buf_valid,        // If true then VM buffer has valid value to write out 
   // HLAPI done interface
   output logic                    hlapi_o_valid,       // HLAPI done handshake valid
   input  logic                    hlapi_o_accept,      // HLAPI done handshake accept
   // pipeline controls
   output logic                    fm_en,               // feature-map input enable
   output logic                    fm_first_in_col,     // set for the first feature-map read in a column
   input  logic                    fm_busy,             // if asserted, accept one more line before shifting pipeline
   output logic                    cf_en,               // coefficient input enable
   output logic                    ctrl_tgl,            // toggle control register
   output logic          [1:0]     ctrl_sel,            // control register select
   output logic                    cf_first_in_tns,     // set for the first coefficient accept in the operation
   output logic                    mpy_en,              // multiplier output register enable
   output logic                    sum_en,              // summation output register enable
   output logic                    sn_en,               // sum/norm output register enable
   output logic                    norm_en,             // normalization output register enable
   output logic                    a_init,              // initialialize the accumulator, one cycle early in norm stage
   // attributes
   output conv_mode_t              conv_mode,           // convolution mode attribute
   output logic                    onn,                 // onn == 2
   output mpy_cfg_t                mpy_cfg,             // mpy config
   output logic                    del_r,               // Delay accept
   output logic                    attr_en,             // hlapi valid
   output logic   [VSIZE-1:0][1:0] acc_en               // accumulator enable bits (early config)
   );                               
  //                                
  // Local types                    
  //

   
  typedef enum logic [2:0] {
                            state_idle_e,   // feature-map and coefficient accept is idle
                            state_fmok_e,   // first row of feature-map accepted
                            state_fmokb_e,  // first row of feature-map accepted
                            state_cfok_e,   // coefficients have been accepted
                            state_fmrow_e   // next row of feature-map accepted
                           } state_t;
  //
  // Local parameters
  //
  //-Convolution Iteration Loop(CIT) ONN(7) --> INN --> ROW --> COL --> QD --> NI --> NO --> GRP
  localparam int CIT_GRP=0; localparam int CIT_NO=1;  localparam int CIT_NI=2;  localparam int CIT_QD=3;
  localparam int CIT_COL=4; localparam int CIT_ROW=5; localparam int CIT_INN=6; localparam int CIT_ONN=7; 
  localparam int CIT_FC=8;  localparam int CIT_CFDBL=9; // CFDBL not in iterator!
  localparam int CIT_NUM=CIT_FC+1;

  //-Pipeline Stage(PA) MUL(0) --> SUM --> SUM/NORM --> NORM --> ACC --> WB --> ACK
  localparam int CMPY_PA_MUL=0; 
  localparam int CMPY_PA_SUM=1; 
  localparam int CMPY_PA_SN=2; 
  localparam int CMPY_PA_NORM=3; 
  localparam int CMPY_PA_ACC=4;
  localparam int CMPY_PA_WB=5;  
  localparam int CMPY_PA_ACK=6; 
  localparam int CMPY_PA_NUM=CMPY_PA_ACK+1;

  //
  // Local wires
  //
  // iterator output stream
  logic                                           it_req;           // iterator valid
  logic                                           it_ack;           // iterator accept
  logic       [CIT_NUM-1:0]                       it_first;         // first bits
  logic       [CIT_NUM-1:0]                       it_last;          // last bits
  logic                                           it_vald;          // first/last valid bits
  // HLAPI accept and attribute storage
  logic                                           hlapi_valid_i;    // HLAPI input is valid and idle
  logic                                           hlapi_accept_i;   // accept new HLAPI non gated with idle
  conv_mode_t                                     attr_conv_mode_r; // convolution mode attribute
  logic                                           attr_onn_r;       // onn == 2
  logic                                           attr_cf_dbl_r;    // double coefficients
  logic                                           attr_keep_r;      // If true then keep result
  logic                                           attr_cf_tgl_r;    // Toggle coefficients
  logic                                           attr_spat_one_r;  // Simple accumulator load/store
  logic                                           attr_spat_one_nxt;// Simple accumulator load/store next
  conv_mode_t                                     attr_conv_mode_mc2; // convolution mode attribute
  logic                                           attr_onn_mc2;       // onn == 2
  logic                                           attr_cf_dbl_mc2;    // double coefficients
  logic                                           attr_keep_mc2;      // If true then keep result
  logic                                           attr_cf_tgl_mc2;    // Toggle coefficients
  logic                                           attr_spat_one_mc2;  // Simple accumulator load/store
  mpy_cfg_t                                       mpy_cfg_mc2;      // mpy config next value
  // control signals
  logic                                           idle;             // datapath is idle
  logic       [CMPY_PA_NUM-1:0]                   en;               // control pipeline signals 
  logic                                           a_en;             // accumulator stage enable
  logic       [CMPY_PA_NUM-1:0]                   val_r;            // per pipeline stage valid
  logic       [CMPY_PA_NUM-1:0][CIT_NUM:0]        first_r;          // per pipeline stage first
  logic       [CMPY_PA_NUM-1:0][CIT_NUM:0]        last_r;           // per pipeline stage last
  logic       [CMPY_PA_NUM-1:0]                   val_nxt;
  logic       [CMPY_PA_NUM-1:0][CIT_NUM:0]        first_nxt;
  logic       [CMPY_PA_NUM-1:0][CIT_NUM:0]        last_nxt;
  logic       [1:0]                               c_sel_r;          // even/odd coefficient select
  logic       [1:0]                               c_sel_nxt;
  offset_t    [CIT_NUM-1:0]                       iter_int;         // internal iterator
  // input accept state
  logic                                           acc_odd_r;        // if true then accumulate second cycle in 16b coef
  logic                                           acc_en_en;        // rotating accumulator enable enable
  logic      [VSIZE-1:0][1:0]                     acc_en_r;         // rotating accumulator enable
  logic      [VSIZE-1:0][1:0]                     acc_en_nxt;       // rotating accumulator enable, next
  state_t                                         state_r;          // input state
  state_t                                         state_nxt;        // input state next
  logic                                           state_en;         // enable state register
  logic                                           tgl_r;            // toggle for double coefficients
  logic                                           tgl_nxt;          // toggle for double coefficients next
  logic                                           cf_first_r;       // First Coef in iteration
  logic                                           cf_first_nxt;     // First Coef in iteration next
  logic                                           cf_first_en;      // First Coef in iteration enable
  mpy_cfg_t                                       mpy_cfg_nxt;      // mpy config next value
  mpy_cfg_t                                       mpy_cfg_r;        // mpy config Register

  
  //
  // Main iterator
  //
  always_comb
    begin : rc_PROC
      logic [2:0] ri;    // row increment
      logic       set_dl;
      offset_t    rows;
      rows = signed'(hlapi_i.iter[5]);
      case (hlapi_i.conv_mode)
      `NINO(conv_mode_4x1g2s1):    begin  ri = 'd0; set_dl = 1'b0; end
      `NINO(conv_mode_2x1g2s2):    begin  ri = 'd0; set_dl = 1'b0; end
      `NINO(conv_mode_4x1g2s1dl2): begin  ri = 'd0; set_dl = 1'b0; end
      `DINO(conv_mode_1x1):        begin  ri = 'd0; set_dl = 1'b0; end
      `NINO(conv_mode_1x1):        begin  ri = 'd0; set_dl = 1'b0; end
      `NINO(conv_mode_2x1s1):      begin  ri = 'd0; set_dl = 1'b0; end
      `NINO(conv_mode_2x1s2):      begin  ri = 'd0; set_dl = 1'b0; end
      `NINO(conv_mode_2x1s1dl2):   begin  ri = 'd0; set_dl = 1'b0; end
      `VIVO(conv_mode_3x3dws1),
      `NINO(conv_mode_3x3dws1):    begin  ri = 'd2; set_dl = 1'b1; end
      `NINO(conv_mode_2x3dws2):    begin  ri = 'd1; set_dl = 1'b1; rows = signed'(rows<<1'b1); end
      `NINO(conv_mode_3x3dws1dl2): begin  ri = 'd4; set_dl = 1'b1; end
      `NINO(conv_mode_8x1dws1):    begin  ri = 'd0; set_dl = 1'b1; end
      default:                     begin  ri = 'd0; set_dl = 1'b0; end //`FC(conv_mode_fc)
      endcase // case (hlapi_i.conv_mode)
      rows        = signed'(rows + ri);
      iter_int    = hlapi_i.iter;
      iter_int[CIT_ROW] = ((hlapi_i.fm_cfg==fm_cfg_16b_e || hlapi_i.fm_cfg==fm_cfg_bf16_e || hlapi_i.fm_cfg==fm_cfg_fp16_e) && set_dl) ? signed'(rows<<1'b1) : rows;
      iter_int[CIT_INN] = hlapi_i.iter[CIT_INN][1] ? 'sd2 : 'sd1;
      iter_int[CIT_ONN] = hlapi_i.iter[CIT_ONN][1] ? 'sd2 : 'sd1;
      iter_int[CIT_FC] = (hlapi_i.conv_mode == `FC(conv_mode_fc)) ? signed'(VSIZE) : signed'(1);
      // check if we can avoid accumulator load/store
      attr_spat_one_nxt = 1'b0;
      if (hlapi_i.iter[CIT_ONN] == 'd1 && hlapi_i.iter[CIT_ROW] == 'd1 && hlapi_i.iter[CIT_COL] == 'd1 && (~(hlapi_i.fm_cfg==fm_cfg_bf16_e||hlapi_i.fm_cfg==fm_cfg_fp16_e)))
      begin
        attr_spat_one_nxt = 1'b1;
      end
    end : rc_PROC
  

  //
  // Main iterator [grp][co][ci][qd][col][row][inn][onn]
  //
  assign idle          = (~it_req) & (val_r == '0) & (~aw_buf_valid);
  assign hlapi_accept  = idle & hlapi_accept_i & del_r;
  assign hlapi_valid_i = del_r;

  // delay pipeline request
  always_ff @(posedge clk or posedge rst_a)
  begin : del_reg_PROC
    if (rst_a == 1'b1)
    begin
      del_r <= 1'b0;
    end
    else
    begin
      del_r <= attr_en;
    end
  end : del_reg_PROC
    
  npu_iterator
  #(.N ( CIT_NUM )) // number of nested loops
  u_iter_inst
  (
   .clk      ( clk            ),
   .rst_a    ( rst_a          ),
   .soft_rst ( 1'b0           ),
   .in_req   ( hlapi_valid_i  ),
   .in_ack   ( hlapi_accept_i ),
   .in_shp   ( iter_int       ),
   .it_req   ( it_req         ),
   .it_ack   ( it_ack         ),
   .it_first ( it_first       ),
   .it_last  ( it_last        ),
   .it_vald  ( it_vald        )
   );


  //
  // Store some HLAPI attributes
  //
  assign attr_en = hlapi_valid & hlapi_accept_i & idle & (~del_r);


  // mpy cfg logic
  always_comb
  begin : mpy_cfg_PROC
    mpy_cfg_nxt = i_8b8b_e;
    if (NPU_HAS_FLOAT && hlapi_i.fm_cfg==fm_cfg_bf16_e) 
    begin
      mpy_cfg_nxt = f_bfloat16_e;
    end
    else if (NPU_HAS_FLOAT && hlapi_i.fm_cfg==fm_cfg_fp16_e) 
    begin
      mpy_cfg_nxt = f_fp16_e;
    end
    else if (hlapi_i.cf_mode == coef_mode_sparse) 
    begin
      mpy_cfg_nxt = i_sparse_e;
    end
    else if (hlapi_i.fm_cfg==fm_cfg_16b_e && hlapi_i.cf_cfg==cf_cfg_16b_e) 
    begin
      mpy_cfg_nxt = i_16b16b_e;
    end
    else if (hlapi_i.fm_cfg==fm_cfg_16b_e) 
    begin
      mpy_cfg_nxt = i_16b8b_e;
    end
    else if (hlapi_i.cf_cfg==cf_cfg_16b_e) 
    begin
      mpy_cfg_nxt = i_8b16b_e;
    end           
  end

  // captured control logic
  always_ff @(posedge clk or posedge rst_a)
  begin : attr_reg_PROC
    if (rst_a == 1'b1)
    begin
      attr_conv_mode_r <= `DINO(conv_mode_1x1);
      attr_onn_r       <= 1'b0;
      attr_cf_dbl_r    <= 1'b0;
      attr_keep_r      <= 1'b0;
      attr_cf_tgl_r    <= 1'b0;
      attr_spat_one_r  <= 1'b0;
      mpy_cfg_r        <= i_8b8b_e;
    end
    else if (attr_en)
    begin
      attr_conv_mode_r <= hlapi_i.conv_mode;
      attr_onn_r       <= hlapi_i.iter[CIT_ONN][1]; // set if value is 2, else 1
      attr_cf_dbl_r    <= hlapi_i.cf_cfg==cf_cfg_16b_e;
      attr_keep_r      <= hlapi_i.keep_acc;
      attr_cf_tgl_r    <= hlapi_i.iter[CIT_INN][1] | hlapi_i.iter[CIT_ONN][1] | hlapi_i.cf_cfg==cf_cfg_16b_e; // toggle c_sel if ONN=2|INN=2|CF_DBL
      attr_spat_one_r  <= attr_spat_one_nxt;
      mpy_cfg_r        <= mpy_cfg_nxt;
    end
  end : attr_reg_PROC
  // output assignments
  assign aw_keep   = attr_keep_mc2 | (last_r[CMPY_PA_WB][CIT_QD:CIT_NI] != 2'b11);

  assign conv_mode = attr_conv_mode_mc2;
  assign onn       = attr_onn_mc2;


  //
  // All config signals are mc because iterator is delayed by one cycle
  //
  logic [$bits(mpy_cfg_t)-1:0]     mpy_cfg_mc2_cast_out;
  assign mpy_cfg_mc2 = mpy_cfg_t'(mpy_cfg_mc2_cast_out);
  npu_2cyc_checker
  #(
    .WIDTH ( $bits(conv_mode_t)+5+$bits(mpy_cfg_t) )
  )
  u_mpy_cfg_mc2_inst
  (
   .clk      ( clk      ),
   .rst_a    ( rst_a    ),
   .valid    ( attr_en  ),
   .data_in  ( {attr_conv_mode_r,
                attr_onn_r,
                attr_cf_dbl_r,
                attr_keep_r,
                attr_cf_tgl_r,
                attr_spat_one_r,
                mpy_cfg_r} ),
   .data_out ( {attr_conv_mode_mc2,
                attr_onn_mc2,
                attr_cf_dbl_mc2,
                attr_keep_mc2,
                attr_cf_tgl_mc2,
                attr_spat_one_mc2,
                mpy_cfg_mc2_cast_out})
   );

  
  //
  // Accumulator enable next state
  //
  assign acc_en = a_en ? acc_en_r : '0;
  always_comb
  begin : acc_en_PROC
    // default
    acc_en_nxt = '0;
    if (hlapi_valid && hlapi_accept)
    begin
      // initialize the accumulator enable
      acc_en_en = 1'b1;
      if (hlapi_i.conv_mode == `FC(conv_mode_fc))
      begin
        acc_en_nxt[0]  = 2'b01;
        if ((hlapi_i.cf_mode == coef_mode_sparse) || (hlapi_i.fm_cfg==fm_cfg_16b_e && hlapi_i.cf_cfg==cf_cfg_16b_e)) 
        begin
          // two accumulators
          acc_en_nxt[0]  = 2'b11;
        end
        if (hlapi_i.fm_cfg==fm_cfg_fp16_e || hlapi_i.fm_cfg==fm_cfg_bf16_e) begin
          // fp mode only uses acc1
          acc_en_nxt[0]  = 2'b10;
        end
      end
      else
      begin
// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self-determin expression
// SJ: Reviewed
        for (int i=0;i<VSIZE;i++) begin
          acc_en_nxt[i]  = 2'b01;
        end
        if ((hlapi_i.cf_mode == coef_mode_sparse) || (hlapi_i.fm_cfg==fm_cfg_16b_e && hlapi_i.cf_cfg==cf_cfg_16b_e))
        begin
          // two accumulators
          for (int i=0;i<VSIZE;i++) begin
            acc_en_nxt[i]  = 2'b11;
          end
        end
        if (hlapi_i.fm_cfg==fm_cfg_fp16_e || hlapi_i.fm_cfg==fm_cfg_bf16_e) begin
          // fp mode only uses acc1
          for (int i=0;i<VSIZE;i++) begin
            acc_en_nxt[i]  = 2'b10;
          end
        end
// spyglass enable_block SelfDeterminedExpr-ML
      end
    end
    else
    begin
      // rotate accumulator enable if 8b cf or msb or 16b cf
      acc_en_en   = a_en & (acc_odd_r || (~attr_cf_dbl_mc2));
      acc_en_nxt = acc_en << 2;  // shift up by 2 bits to do [VSIZE-1:1]<=[VSIZE-2:0]
      acc_en_nxt[0] = acc_en_r[VSIZE-1];  // rotate [VSIZE-1] down to [0]
    end
  end : acc_en_PROC
  

  //
  // Control delay line
  //
  // simple control signals
  assign fm_en           = stash_valid & stash_accept;
  assign cf_en           = coef_valid  & coef_accept;
  assign fm_first_in_col = &it_first[CIT_ONN:CIT_ROW];
  assign cf_first_in_tns = cf_first_r;
  assign ctrl_tgl        = mpy_en & attr_cf_tgl_mc2;
  assign ctrl_sel        = c_sel_nxt;
  assign cf_first_en     = ((coef_valid & coef_accept) | (&it_first));
  assign cf_first_nxt    = &it_first;


  // pipeline control
  // outputs: en, it_ack, val_nxt, state_en, state_nxt, tgl_nxt, first_nxt, last_nxt, stash_accept, coef_accept, ar_accept, aw_valid, hlapi_o_valid, mpy_en, sum_en, sn_en, norm_en, a_en
  always_comb
  begin : ctrl_nxt_PROC
    // default pipeline state
    en              = '0;
    state_en        = 1'b0;
    state_nxt       = state_idle_e;
    tgl_nxt         = tgl_r;
    it_ack          = 1'b0;
    val_nxt         = val_r;
    last_nxt        = '0;
    first_nxt       = '0;
    stash_accept    = 1'b0;
    coef_accept     = 1'b0;
    ar_accept       = 1'b0;
    aw_valid        = 1'b0;
    hlapi_o_valid   = 1'b0;
    mpy_en          = 1'b0;
    sum_en          = 1'b0;
    sn_en          = 1'b0;
    norm_en          = 1'b0;
    a_en            = 1'b0;

    // HLAPI acknowledge stage
    if (val_nxt[CMPY_PA_ACK])
    begin
      if (&last_r[CMPY_PA_ACK])
      begin
        // last HLAPI iteration
        hlapi_o_valid = 1'b1;
        if (hlapi_o_accept)
        begin
          // successful handshake
          val_nxt[CMPY_PA_ACK] = 1'b0;
          en[CMPY_PA_ACK]      = 1'b1;
        end
        // else stall
      end
      else
      begin
        // no handshake required
        val_nxt[CMPY_PA_ACK] = 1'b0;
        en[CMPY_PA_ACK]      = 1'b1;
      end
    end

    // accumulator write-back stage
    if (val_nxt[CMPY_PA_WB] & ~val_nxt[CMPY_PA_ACK])
    begin
      if (last_r[CMPY_PA_WB][CIT_CFDBL] & last_r[CMPY_PA_WB][CIT_FC] & last_r[CMPY_PA_WB][CIT_INN] & ((&last_r[CMPY_PA_WB][CIT_QD:CIT_NI]) | (~attr_spat_one_mc2)))
      begin
        // last inn and fc iteration
        aw_valid                          = 1'b1;
        if (aw_accept)
        begin
          // successful write-back
          val_nxt[CMPY_PA_ACK:CMPY_PA_WB] = 2'b10;
          first_nxt[CMPY_PA_ACK]          = first_r[CMPY_PA_WB];
          last_nxt[CMPY_PA_ACK]           = last_r[CMPY_PA_WB];
          en[CMPY_PA_ACK:CMPY_PA_WB]      = 2'b11;
        end
        // else stall
      end
      else
      begin
        // no write-back required
        val_nxt[CMPY_PA_ACK:CMPY_PA_WB]   = 2'b10;
        first_nxt[CMPY_PA_ACK]            = first_r[CMPY_PA_WB];
        last_nxt[CMPY_PA_ACK]             = last_r[CMPY_PA_WB];
        en[CMPY_PA_ACK:CMPY_PA_WB]        = 2'b11;
      end
    end

    // accumulation stage and accumulator read stage
    if (val_nxt[CMPY_PA_ACC] & ~val_nxt[CMPY_PA_WB])
    begin
      // next stage is free
      ar_accept = first_r[CMPY_PA_ACC][CIT_CFDBL] & last_r[CMPY_PA_ACC][CIT_FC]  & first_r[CMPY_PA_ACC][CIT_INN] & ((&first_r[CMPY_PA_ACC][CIT_QD:CIT_NI]) | (~attr_spat_one_mc2));
      if         (first_r[CMPY_PA_ACC][CIT_CFDBL] & first_r[CMPY_PA_ACC][CIT_FC] & first_r[CMPY_PA_ACC][CIT_INN] & ((&first_r[CMPY_PA_ACC][CIT_QD:CIT_NI]) | (~attr_spat_one_mc2)))
      begin
        // first inn and first ni iteration or spatial is one
        if (ar_valid)
        begin
          // successful accumulation
          a_en                            = 1'b1;
          val_nxt[CMPY_PA_WB:CMPY_PA_ACC] = 2'b10;
          first_nxt[CMPY_PA_WB]           = first_r[CMPY_PA_ACC];
          last_nxt[CMPY_PA_WB]            = last_r[CMPY_PA_ACC];
          en[CMPY_PA_WB:CMPY_PA_ACC]      = 2'b11;
        end
        // else stall
      end
      else
      begin
        // no initialization required
        a_en                              = 1'b1;
        val_nxt[CMPY_PA_WB:CMPY_PA_ACC]   = 2'b10;
        first_nxt[CMPY_PA_WB]             = first_r[CMPY_PA_ACC];
        last_nxt[CMPY_PA_WB]              = last_r[CMPY_PA_ACC];
        en[CMPY_PA_WB:CMPY_PA_ACC]        = 2'b11;
      end
    end


    // normalization stage
    if (val_nxt[CMPY_PA_NORM] & ~val_nxt[CMPY_PA_ACC])
    begin
      // next stage is free
      norm_en                             = 1'b1;
      val_nxt[CMPY_PA_ACC:CMPY_PA_NORM]   = 2'b10;
      first_nxt[CMPY_PA_ACC]             = first_r[CMPY_PA_NORM];
      last_nxt[CMPY_PA_ACC]              = last_r[CMPY_PA_NORM];
      en[CMPY_PA_ACC:CMPY_PA_NORM]        = 2'b11;
    end

    // summation stage
    if (val_nxt[CMPY_PA_SN] & ~val_nxt[CMPY_PA_NORM])
    begin
      // next stage is free
      sn_en                              = 1'b1;
      val_nxt[CMPY_PA_NORM:CMPY_PA_SN]   = 2'b10;
      first_nxt[CMPY_PA_NORM]             = first_r[CMPY_PA_SN];
      last_nxt[CMPY_PA_NORM]              = last_r[CMPY_PA_SN];
      en[CMPY_PA_NORM:CMPY_PA_SN]        = 2'b11;
    end
    
    // summation stage
    if (val_nxt[CMPY_PA_SUM] & ~val_nxt[CMPY_PA_SN])
    begin
      // next stage is free
      sum_en                             = 1'b1;
      val_nxt[CMPY_PA_SN:CMPY_PA_SUM]   = 2'b10;
      first_nxt[CMPY_PA_SN]             = first_r[CMPY_PA_SUM];
      last_nxt[CMPY_PA_SN]              = last_r[CMPY_PA_SUM];
      en[CMPY_PA_SN:CMPY_PA_SUM]        = 2'b11;
    end
    
    // multiplier stage
    if (val_nxt[CMPY_PA_MUL] & ~val_nxt[CMPY_PA_SUM])
    begin
      // next stage is free
      mpy_en                             = 1'b1;
      val_nxt[CMPY_PA_SUM:CMPY_PA_MUL]   = 2'b10;
      first_nxt[CMPY_PA_SUM]             = first_r[CMPY_PA_MUL];
      last_nxt[CMPY_PA_SUM]              = last_r[CMPY_PA_MUL];
      en[CMPY_PA_SUM:CMPY_PA_MUL]        = 2'b11;
    end
    
    if (it_req & ~val_nxt[CMPY_PA_MUL])
    begin
      // initial stage to load feature-map and coefficients
      case (state_r)
      state_fmokb_e:
        begin
          // first row of feature-map accepted but need one more row, wait for coefficients 
          stash_accept    = 1'b1;
          coef_accept     = 1'b1;
          case ({stash_valid,coef_valid})
          2'b11:
            begin
              // both valid
              if (fm_busy)
              begin
                // need one more feature-map row
                state_en  = 1'b1;
                state_nxt = state_fmrow_e;
                it_ack    = 1'b1;
              end
              else
              begin
                // feature-map and coefficients accepted pass to next stage, go to in idle state
                // pass new operation into pipeline
                first_nxt[CMPY_PA_MUL]     = {1'b1,it_first};
                last_nxt[CMPY_PA_MUL]      = {1'b1,it_last};
                if (attr_cf_dbl_mc2)
                begin
                  tgl_nxt                  = ~tgl_r;
                  first_nxt[CMPY_PA_MUL][CIT_CFDBL] = ~tgl_r;
                  last_nxt[CMPY_PA_MUL][CIT_CFDBL]  =  tgl_r;
                  if (tgl_r)
                  begin
                    // second cycle
                    it_ack                 = 1'b1;
                  end
                end
                else
                begin
                  it_ack                   = 1'b1;
                end
                // go to idle state
                val_nxt[CMPY_PA_MUL]       = 1'b1;
                en[CMPY_PA_MUL]            = 1'b1;
                state_en  = 1'b1;
                state_nxt = state_idle_e;
              end
            end
          2'b10:
            begin
              // feature-map valid, coefficients invalid
              if (!fm_busy)
              begin
                // all rows of feature-emap done, wait for coefficients
                state_en  = 1'b1;
                state_nxt = state_fmok_e;
              end
              else 
              begin
                // else need one more feature-map row, stay in this state
                it_ack  = 1'b1;
              end
            end
          2'b01:
            begin
              // coefficients done, require more feature-map rows
              state_en  = 1'b1;
              state_nxt = state_fmrow_e;
            end
          default:
            begin
              // wait in state
            end
          endcase
        end // case: state_fmokb_e
      state_fmok_e:
        begin
          // feature-map accepted, wait for coefficients
          coef_accept     = 1'b1;
          stash_accept    = 1'b0;
          if (coef_valid)
          begin
            // feature-map and coefficients accepted pass to next stage, go to in idle state
            // pass new operation into pipeline
            first_nxt[CMPY_PA_MUL]     = {1'b1,it_first};
            last_nxt[CMPY_PA_MUL]      = {1'b1,it_last};
            if (attr_cf_dbl_mc2)
            begin
              tgl_nxt                  = ~tgl_r;
              first_nxt[CMPY_PA_MUL][CIT_CFDBL] = ~tgl_r;
              last_nxt[CMPY_PA_MUL][CIT_CFDBL]  =  tgl_r;
              if (tgl_r)
              begin
                // second cycle
                it_ack                 = 1'b1;
              end
            end
            else
            begin
              it_ack                   = 1'b1;
            end
            // go to idle state
            val_nxt[CMPY_PA_MUL]       = 1'b1;
            en[CMPY_PA_MUL]            = 1'b1;
            state_en  = 1'b1;
            state_nxt = state_idle_e;
          end
        end
      state_cfok_e:
        begin
          // coefficients have been accepted, no feature-map accepted
          stash_accept    = 1'b1;
          if (stash_valid)
          begin
            if (fm_busy)
            begin
              // need one more feature-map row
              state_en  = 1'b1;
              state_nxt = state_fmrow_e;
              // iterator to next row
              it_ack = 1'b1;
            end
            else
            begin
              // feature-map and coefficients accepted pass to next stage, go to in idle state
              // pass new operation into pipeline
              first_nxt[CMPY_PA_MUL]     = {1'b1,it_first};
              last_nxt[CMPY_PA_MUL]      = {1'b1,it_last};
              if (attr_cf_dbl_mc2)
              begin
                tgl_nxt                  = ~tgl_r;
                first_nxt[CMPY_PA_MUL][CIT_CFDBL] = ~tgl_r;
                last_nxt[CMPY_PA_MUL][CIT_CFDBL]  =  tgl_r;
                if (tgl_r)
                begin
                  // second cycle
                  it_ack                 = 1'b1;
                end
              end
              else
              begin
                it_ack                   = 1'b1;
              end
              // go to idle state
              val_nxt[CMPY_PA_MUL]       = 1'b1;
              en[CMPY_PA_MUL]            = 1'b1;
              state_en  = 1'b1;
              state_nxt = state_idle_e;
            end
          end
        end
      state_fmrow_e:
        begin
          // next row of feature-map accepted
          stash_accept  = 1'b1;
          if (stash_valid & ~fm_busy)
          begin
            // pass new operation into pipeline
            first_nxt[CMPY_PA_MUL]     = {1'b1,it_first};
            last_nxt[CMPY_PA_MUL]      = {1'b1,it_last};
            if (attr_cf_dbl_mc2)
            begin
              tgl_nxt                  = ~tgl_r;
              first_nxt[CMPY_PA_MUL][CIT_CFDBL] = ~tgl_r;
              last_nxt[CMPY_PA_MUL][CIT_CFDBL]  =  tgl_r;
              if (tgl_r)
              begin
                // second cycle
                it_ack                 = 1'b1;
              end
            end
            else
            begin
              it_ack                   = 1'b1;
            end
            // go to idle state
            val_nxt[CMPY_PA_MUL]       = 1'b1;
            en[CMPY_PA_MUL]            = 1'b1;
            state_en  = 1'b1;
            state_nxt = state_idle_e;
          end
          else if (stash_valid & fm_busy)
          begin
            // iterator to next row
            it_ack = 1'b1;
          end
        end
      default: // state_idle_e
        begin
          // feature-map and coefficient accept is idle
          // accept feature-map on first onn and FC
          stash_accept    = it_first[CIT_ONN] & it_first[CIT_FC] & (~tgl_r);
          // accept coefficients on first col&row&inn&onn
          coef_accept     = (&it_first[CIT_ONN:CIT_COL]) & (~tgl_r);
          // determine next state
          casez ({stash_valid, stash_accept, coef_valid, coef_accept})
          4'b1111:
            begin
              // feature-map row and coefficients accepted
              if (fm_busy)
              begin
                // need one more feature-map row
                state_en  = 1'b1;
                state_nxt = state_fmrow_e;
                it_ack    = 1'b1;
              end
              else
              begin
                // feature-map and coefficients accepted pass to next stage, stay in idle state
                // pass new operation into pipeline
                first_nxt[CMPY_PA_MUL]     = {1'b1,it_first};
                last_nxt[CMPY_PA_MUL]      = {1'b1,it_last};
                if (attr_cf_dbl_mc2)
                begin
                  tgl_nxt                  = ~tgl_r;
                  first_nxt[CMPY_PA_MUL][CIT_CFDBL] = ~tgl_r;
                  last_nxt[CMPY_PA_MUL][CIT_CFDBL]  =  tgl_r;
                  if (tgl_r)
                  begin
                    // second cycle
                    it_ack                 = 1'b1;
                  end
                end
                else
                begin
                  it_ack                   = 1'b1;
                end
                // go to idle state
                val_nxt[CMPY_PA_MUL]       = 1'b1;
                en[CMPY_PA_MUL]            = 1'b1;
                state_en  = 1'b1;
                state_nxt = state_idle_e;
              end
            end
          4'b?011:
            begin
              // no feature-map required, only coefficients accepted, pass to next stage, stay in idle state
              // pass new operation into pipeline
              first_nxt[CMPY_PA_MUL]     = {1'b1,it_first};
              last_nxt[CMPY_PA_MUL]      = {1'b1,it_last};
              if (attr_cf_dbl_mc2)
              begin
                tgl_nxt                  = ~tgl_r;
                first_nxt[CMPY_PA_MUL][CIT_CFDBL] = ~tgl_r;
                last_nxt[CMPY_PA_MUL][CIT_CFDBL]  =  tgl_r;
                if (tgl_r)
                begin
                  // second cycle
                  it_ack                 = 1'b1;
                end
              end
              else
              begin
                it_ack                   = 1'b1;
              end
              // go to idle state
              val_nxt[CMPY_PA_MUL]       = 1'b1;
              en[CMPY_PA_MUL]            = 1'b1;
              state_en  = 1'b1;
              state_nxt = state_idle_e;
              end
          4'b11?0:
            begin
              // only feature-map accepted, no coefficients required
              if (fm_busy)
              begin
                // need one more feature-map row
                state_en  = 1'b1;
                state_nxt = state_fmrow_e;
                it_ack    = 1'b1;
              end
              else
              begin
                // feature-map and coefficients accepted pass to next stage, stay in idle state
                // pass new operation into pipeline
                first_nxt[CMPY_PA_MUL]     = {1'b1,it_first};
                last_nxt[CMPY_PA_MUL]      = {1'b1,it_last};
                if (attr_cf_dbl_mc2)
                begin
                  tgl_nxt                  = ~tgl_r;
                  first_nxt[CMPY_PA_MUL][CIT_CFDBL] = ~tgl_r;
                  last_nxt[CMPY_PA_MUL][CIT_CFDBL]  =  tgl_r;
                  if (tgl_r)
                  begin
                    // second cycle
                    it_ack                 = 1'b1;
                  end
                end
                else
                begin
                  it_ack                   = 1'b1;
                end
                // go to idle state
                val_nxt[CMPY_PA_MUL]       = 1'b1;
                en[CMPY_PA_MUL]            = 1'b1;
                state_en  = 1'b1;
                state_nxt = state_idle_e;
              end
            end
          4'b0111:
            begin
              // feature-map row and coefficients required but coefficients valid only, wait for feature-map
              state_en  = 1'b1;
              state_nxt = state_cfok_e;
            end
          4'b1101:
            begin
              // feature-map row and coefficients required but feature-map valid only, wait for coefficients
              if (fm_busy)
              begin
                // need another feature-map row
                state_en  = 1'b1;
                state_nxt = state_fmokb_e;
                it_ack    = 1'b1;
              end
              else
              begin
                state_en  = 1'b1;
                state_nxt = state_fmok_e;
              end
            end
          4'b?0?0:
            begin
              // no new coefficients or feature-map required
              // pass new operation into pipeline
              first_nxt[CMPY_PA_MUL]     = {1'b1,it_first};
              last_nxt[CMPY_PA_MUL]      = {1'b1,it_last};
              if (attr_cf_dbl_mc2)
              begin
                tgl_nxt                  = ~tgl_r;
                first_nxt[CMPY_PA_MUL][CIT_CFDBL] = ~tgl_r;
                last_nxt[CMPY_PA_MUL][CIT_CFDBL]  =  tgl_r;
                if (tgl_r)
                begin
                  // second cycle
                  it_ack                 = 1'b1;
                end
              end
              else
              begin
                it_ack                   = 1'b1;
              end
              // go to idle state
              val_nxt[CMPY_PA_MUL]       = 1'b1;
              en[CMPY_PA_MUL]            = 1'b1;
              state_en  = 1'b1;
              state_nxt = state_idle_e;
            end
          default: // 4'b0001, 4'b0100, 4'b0101, 4'b0110, 4'b1001,
            begin
              // stay in idle
            end
          endcase // casez ({stash_valid, stash_accept, coef_valid, coef_accept})
        end
      endcase // case (state_r)
    end // if (it_req & ~val_nxt[0])
  end : ctrl_nxt_PROC


  // state
  assign c_sel_nxt = c_sel_r ^ {attr_cf_tgl_mc2,attr_cf_tgl_mc2};
  assign a_init    = first_nxt[CMPY_PA_ACC][CIT_CFDBL] & first_nxt[CMPY_PA_ACC][CIT_INN] & ((first_nxt[CMPY_PA_ACC][CIT_NI]&first_nxt[CMPY_PA_ACC][CIT_QD]) | (~attr_spat_one_mc2));
  assign mpy_cfg   = mpy_cfg_mc2;
  // outputs: val_r, first_r, last_r, state_r, acc_en_r, c_sel_r
  always_ff @(posedge clk or posedge rst_a)
  begin : state_reg_PROC
    if (rst_a ==  1'b1)
    begin
      // reset control state
      val_r         <= '0;
      first_r       <= '0;
      last_r        <= '0;
      state_r       <= state_idle_e;
      tgl_r         <= 1'b0;
      acc_en_r      <= '0;
      c_sel_r       <= 2'b01;
      acc_odd_r     <= 1'b0;
      cf_first_r    <= 1'b0;
    end
    else
    begin
      tgl_r         <= tgl_nxt;
      if (state_en)
      begin
        state_r <= state_nxt;
      end
// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self-determin expression
// SJ: Reviewed
      for (int i = 0; i < CMPY_PA_NUM; i++)
      begin
        if (en[i])
        begin
          val_r[i]   <= val_nxt[i];
          first_r[i] <= first_nxt[i];
          last_r[i]  <= last_nxt[i];
        end
      end
// spyglass enable_block SelfDeterminedExpr-ML
      if (mpy_en)
      begin
        c_sel_r     <= c_sel_nxt;
      end
      if (a_en)
      begin
        acc_odd_r   <= attr_cf_dbl_mc2 ^ acc_odd_r;
      end
      if (acc_en_en)
      begin
        acc_en_r    <= acc_en_nxt;
      end
      if (cf_first_en)
      begin
        cf_first_r  <= cf_first_nxt;
      end
    end
  end :  state_reg_PROC

endmodule : npu_conv_mpy_ctrl
