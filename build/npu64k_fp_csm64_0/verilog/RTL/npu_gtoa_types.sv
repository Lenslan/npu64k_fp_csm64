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
 * npu_gtoa_types.sv
 *
 * File defining GTOA datatypes
 *
 */

 `ifndef NPU_GTOA_TYPES_INCLUDED
 `define NPU_GTOA_TYPES_INCLUDED

`include "npu_defines.v"

package npu_gtoa_types;
  import npu_types::*;

  //
  // Fixed value parameters
  //
  localparam int ACT_SREG_NUM   = 8;
  localparam int ACT_VREG_NUM   = 8;
  localparam int ACT_BREG_NUM   = 8;
  localparam int ACT_LUT_SIZE   = 16;
  localparam int ACT_PROG_LEN   = 18;
  localparam int ACT_NUM_LOOPS  = 3;
  localparam int ACT_FM_LOOPS   = 6;
  localparam int ACT_AM_LOOPS   = 4;
  localparam int ACT_POOL_LOOPS = 4;
  // SRs that can be init from HLAPI
  localparam int ACT_SREG_INI   = 4;
  
  // ID field in the MMIO ID registers
  localparam int GTOA_ID = 1;
  localparam int GTOA_ID_ALU2 = 10;
  localparam int GTOA_ID_STR0 = 11;
  localparam int GTOA_ID_ALU2_STR0 = 12;
  // MAJOR version field in the MMIO ID register
  localparam int GTOA_MAJ = 2;
  // MINOR version field in the MMIO ID register
  localparam int GTOA_MIN = 0;


  //
  // GTOA Instruction encoded types
  //

  // scalar register encoding
  typedef enum logic [2:0] { sr0, sr1, sr2, sr3, sr4, sr5, sr6, sr7 } act_sidx_t;

  // vector register encoding
  typedef enum logic [2:0] { vr0, vr1, vr2, vr3, vr4, vr5, vr6, vr7 } act_vidx_t;

  // parameter register encoding
  typedef enum logic [2:0] { brw0, brw1, brw2, brw3, brw4, brw5, brw6, brw7 } act_widx_t;
  typedef enum logic [2:0] { brh0, brh1, brh2, brh3, brh4, brh5, brh6, brh7 } act_hidx_t;
  typedef enum logic [2:0] { brb0, brb1, brb2, brb3, brb4, brb5, brb6, brb7 } act_bidx_t;

  // constant values for io_en (one bit per port)
  localparam logic [15:0] act_io_en_fm0_e   = 16'h0001;
  localparam logic [15:0] act_io_en_ac0_e   = 16'h0002;
  localparam logic [15:0] act_io_en_astr0_e = 16'h0004;
  localparam logic [15:0] act_io_en_fm1_e   = 16'h0008;
  localparam logic [15:0] act_io_en_ac1_e   = 16'h0010;
  localparam logic [15:0] act_io_en_fstr1_e = 16'h0020;
  localparam logic [15:0] act_io_en_oac_e   = 16'h0040;
  localparam logic [15:0] act_io_en_ofm_e   = 16'h0080;
  localparam logic [15:0] act_io_en_gth_e   = 16'h0100;

  // HLAPI type enum
  typedef enum logic { act_typ_fu_e, act_typ_lut_e } act_typ_t; // do function or initialize LUT
  
  // scalar register file type
  typedef logic [31:0] act_scalar_t;

  // padding mode
  typedef enum logic [1:0] {pad_mode_zero_e=2'b00, pad_mode_mone_e=2'b01, pad_mode_minint_e=2'b10, pad_mode_maxint_e=2'b11 } pad_mode_t;

  // padding increment mode
  typedef enum logic [1:0] {pad_inc_i16_e=2'b00, pad_inc_v2i8_e=2'b01, pad_inc_v4i4_e=2'b10} pad_inc_t;

  // floating data modes
  typedef enum logic [2:0] {fmode_int32_e=3'b000, fmode_fp32_e=3'b001, fmode_fp16_e=3'b010, fmode_bf16_e=3'b011, fmode_fp8_e=3'b100 } fmode_t;

  // predication conditions
  typedef enum logic [3:0] { pred_never=0, // never execute
                             pred_first0,  // enable at first iteration of outer loop
                             pred_first1,  // enable at first iteration of middle loop
                             pred_first2,  // enable at first iteration of inner loop
                             pred_last2,   // enable in last iteration of inner loop
                             pred_last1,   // enable in last iteration of middle loop
                             pred_last0,   // enable in unless last iteration of outer loop
                             pred_nfirst0, // enable at unless first iteration of outer loop
                             pred_nfirst1, // enable at unless first iteration of middle loop
                             pred_nfirst2, // enable at unless first iteration of inner loop
                             pred_nlast2,  // enable in unless last iteration of inner loop
                             pred_nlast1,  // enable in unless last iteration of middle loop
                             pred_nlast0,  // enable in unless last iteration of outer loop
                             pred_even,    // enable in even iterations
                             pred_odd,     // enable in odd iterations
                             pred_always   // always enable
                             } act_pred_t;
  
  // instruction encodings
  typedef enum logic [2:0] { fu_in0, fu_in1, fu_out, fu_alu0, fu_alu1, fu_mul0, fu_bpar } act_fu_t;
  typedef enum logic [2:0] { ot_no, ot_op, ot_s, ot_v, ot_w, ot_h, ot_b } act_ot_t; // operand type
  typedef enum logic [5:0] { op_add, op_sub, op_rsub, op_eadd, op_min, op_max,
                             op_relun, op_mirror, op_replic, op_renorm,
                             op_eq, op_neq, op_gt, op_gte, op_lt, op_lte, 
                             op_band, op_bor, op_bxor, 
                             op_select,
                             op_asr, op_lsr, op_sl, 
                             op_fadd, op_fsub, op_frsub, op_fmin, op_fmax,
                             op_faddf, op_fsubf, op_frsubf, op_fminf, op_fmaxf,
                             op_feq, op_fneq, op_fgt, op_fgte, op_flt, op_flte,
                             op_frelun, op_frelunf,
                             op_balu_spare0, op_balu_spare1, op_balu_spare2, op_balu_spare3,
                             op_fpopin, op_fpopinf, op_bin_spare0, op_bin_spare1, op_fpushout,
                             op_mpyh, op_mpyb, op_mpy
                             } act_bin_op_t;
  typedef enum logic [5:0] { op_getid, op_strv, op_strc, op_movf,
                             op_bcc, op_bcv,
                             op_abs, op_bnot, op_sat8, op_sat16, op_shv, op_shc, op_shrc,
                             op_andf, op_orf, op_xorf,
                             op_fabs, op_frelu, op_ftoi, op_itof, op_trunc, op_fract,
                             op_trnsp, op_selecth, op_selectb,
                             op_raddv, op_randv, op_rorv, op_rmaxv, op_rminv,
                             op_raddc, op_randc, op_rorc, op_rmaxc, op_rminc,
                             op_lutq0, op_exp0, op_recip0, op_rsqrt0, 
                             op_lutq1, op_exp1, op_recip1, op_rsqrt1,
                             op_ualu_spare0, op_ualu_spare1, op_ualu_spare2, op_ualu_spare3,
                             op_mac0, op_mac1, op_rmpyv, op_umpy_spare0, op_umpy_spare1, 
                             op_popin, op_popidx, op_poppad, op_fpoprecip, op_gather, op_gather2d, op_uin_spare0, op_pushout,
                             op_poppars
                             } act_una_op_t;

  // source and destination operand indices
  typedef union packed {
    act_sidx_t    s;
    act_vidx_t    v;
    act_widx_t    w;
    act_hidx_t    h;
    act_bidx_t    b;
  } act_op_t;

  // activation program counter type
  typedef logic [4:0] act_pc_t;
  
  // GTOA instruction type
  typedef struct packed {
    // pad to 40b
    logic         [0:0] p;
    // source 3/binary opcode    : 6 bits
    union packed {
      act_bin_op_t      bo;   // binary opcode
    }                   src2;
    // source 1/unary opcode     : 6 bits
    union packed {               
      act_una_op_t      uo;   // unary opcode
      struct packed {
        logic     [2:0] p;    // padding
        act_op_t        o;    // operand
      }                 op;
    }                   src1;
    // source 0                  : 3 bits
    act_op_t            src0;
    // destination               : 3 bits
    act_op_t            dst;
    // operand types             : 3*3bits
    act_ot_t      [2:0] fmt;
    // mapping to functional unit: 3 bits
    act_fu_t            fu;
    // predicates                : 4 bits
    act_pred_t          pred;
    // position in schedule      : 5 bits
    act_pc_t            pc;
  } act_inst_t;


  //
  // GTOA decoded instruction types
  //

  // In instructions, same order as ternary, binary, unary enum types
  typedef enum logic [6:0] { dec_fpopin, dec_fpopinf, dec_popin, dec_popidx, dec_poppad, dec_fpoprecip, dec_gather, dec_gather2d } act_dec_in_t;

  // Out instructions, same order as ternary, binary, unary enum types
  typedef enum logic [6:0] { dec_fpushout, dec_pushout } act_dec_out_t;

  // ALU instructions, same order as ternary, binary, unary enum types
  typedef enum logic [6:0] { dec_add, dec_sub, dec_rsub, dec_eadd, dec_min, dec_max,
                             dec_relun, dec_mirror, dec_replic, dec_renorm,
                             dec_eq, dec_neq, dec_gt, dec_gte, dec_lt, dec_lte, 
                             dec_band, dec_bor, dec_bxor,
                             dec_select,
                             dec_asr, dec_lsr, dec_sl,
                             dec_fadd, dec_fsub, dec_frsub, dec_fmin, dec_fmax,
                             dec_faddf, dec_fsubf, dec_frsubf, dec_fminf, dec_fmaxf,
                             dec_feq, dec_fneq, dec_fgt, dec_fgte, dec_flt, dec_flte,
                             dec_frelun, dec_frelunf,
                             dec_getid, dec_strv, dec_strc, dec_movf,
                             dec_bcc, dec_bcv, 
                             dec_abs, dec_bnot, dec_sat8, dec_sat16, dec_shv, dec_shc, dec_shrc,
                             dec_andf, dec_orf, dec_xorf,
                             dec_fabs, dec_frelu, dec_ftoi, dec_itof, dec_trunc, dec_fract,
                             dec_trnsp, dec_selecth, dec_selectb,
                             dec_raddv, dec_randv, dec_rorv, dec_rmaxv, dec_rminv,
                             dec_raddc, dec_randc, dec_rorc, dec_rmaxc, dec_rminc,
                             dec_lutq0, dec_exp0, dec_recip0, dec_rsqrt0,
                             dec_lutq1, dec_exp1, dec_recip1, dec_rsqrt1
                             } act_dec_alu_t;

  // Multiplier instructions, same order as ternary, binary, unary enum types
  typedef enum logic [6:0] { dec_mpyh, dec_mpyb, dec_mpy, dec_mac0, dec_mac1, dec_rmpyv } act_dec_mpy_t;

  // Decoded instruction
  typedef struct packed {
    union packed {                       // out, bpar no opcode
      act_dec_in_t         i;            // popin operation
      act_dec_out_t        o;            // pushout operation
      act_dec_alu_t        a;            // ALU operation
      act_dec_mpy_t        m;            // multiplier operation
    }                      opc;          // FU opcode
    logic                  bodd;         // Odd B parameter set
    act_op_t         [2:0] ops;          // operands
    act_ot_t         [2:0] fmt;          // operand types 4*3b
  } act_dec_inst_t;

  // Pending operand one-hot types
  typedef struct packed {
    logic                  b;            // pending b access
    logic [1:0]            q;            // look-up queue 0 and 1
    logic [7:0]            s;            // scalar register
    logic [7:0]            v;            // vector register
  } act_pend_t;

  // Decoded instruction with hazard information
  typedef struct packed {
    act_dec_inst_t         inst;         // decoded instruction index
    act_fu_t               fu;           // mapping to functional unit: 4 bits
    logic            [2:0] lat;          // latency of instruction
    act_pend_t             src;          // source operand mask
    act_pend_t             dst;          // destination operand mask
  } act_haz_inst_t;

  // Operand select signal types
`ifdef NPU_GTOA_RF_MUX_ORBUS
  typedef struct packed {
    logic [1:0]  sel_mux;     // bits for mux selection
    logic [1:0]  sel_oh;      // bits for one-hot selection
  } act_op_sel_e_t;
  typedef act_op_sel_e_t [VSIZE-1:0] act_op_sel_t; // replicate per lane
  function automatic act_op_sel_t vr_decode(logic e, act_vidx_t i);
    act_op_sel_e_t r;
    r.sel_mux   = i[1:0];
    r.sel_oh[0] = e & ~i[2];
    r.sel_oh[1] = e &  i[2];  
    return {VSIZE{r}};
  endfunction : vr_decode
  function automatic logic vr_check(act_op_sel_t s);
    return (s[0].sel_oh != '0);
  endfunction : vr_check
  function automatic vyixacc_t vr_read(act_op_sel_t s, vyixacc_t [ACT_VREG_NUM-1:0] vr);
    vyixacc_t       r; // result
    // defaults
    r = '0;
    for (int v = 0; v < VSIZE; v++)
    begin
      ixacc_t [1:0] t; // vector muxed data
      // MUX4 selection
      case (s[v].sel_mux) // synopsys infer_mux_override
      2'b00:
        begin
          t[0] = vr[0][v];
          t[1] = vr[4][v];
        end
      2'b01:
        begin
          t[0] = vr[1][v];
          t[1] = vr[5][v];
        end
      2'b10:
        begin
          t[0] = vr[2][v];
          t[1] = vr[6][v];
        end
      default: // 2'b11
        begin
          t[0] = vr[3][v];
          t[1] = vr[7][v];
        end
      endcase // case (s.sel_mux)
      // AND-OR bus
      if (s[v].sel_oh[0])
      begin
        r[v] |= t[0];
      end
      if (s[v].sel_oh[1])
      begin
        r[v] |= t[1];
      end
    end
    return r;
  endfunction : vr_read
`else
  typedef logic [ACT_VREG_NUM-1:0] act_op_sel_t; // one-hot0 vector
  function automatic act_op_sel_t vr_decode(logic e, act_vidx_t i);
    act_op_sel_t r;
    r    = '0;
    r[i] = e;
    return r;
  endfunction : vr_decode
  function automatic logic vr_check(act_op_sel_t s);
    return (s != '0);
  endfunction : vr_check
  function automatic vyixacc_t vr_read(act_op_sel_t s, vyixacc_t [ACT_VREG_NUM-1:0] v);
    vyixacc_t       r; // result
    // defaults
    r = '0;
    // AND-OR bus
    for (int i = 0; i < ACT_VREG_NUM; i++)
    begin
      r |= s[i] ? v[i] : '0;
    end
    return r;
  endfunction : vr_read
`endif
  
  //
  // GTOA LUT
  //  
  typedef struct packed {
    logic        sgn;
    logic [7:0]  ex;
    logic [22:0] mant;
  } act_e8m23_t;
  
  typedef struct packed {
    logic        sgn;
    logic [7:0]  ex;
    logic [14:0] mant;
  } act_e8m15_t;
  
  typedef struct packed {
    logic       sgn;
    logic [7:0] ex;
    logic [6:0] mant;
  } act_e8m7_t;

  typedef struct packed {
    logic [3:0] ex;
    logic [3:0] mant;
  } act_ue4m4_t;
  
  typedef struct packed {
    logic [7:0] ex;
    logic [3:0] mant;
  } act_ue8m4_t;
  
  // LUT command
  typedef enum logic [1:0] { cmd_normal_e, cmd_nan_e, cmd_exp_repl_e,  cmd_exp_repl_neg_e } act_lut_cmd_t;
  // LUT fp scaling
  typedef struct packed {
    act_e8m15_t     ofs;
    act_e8m23_t     mul;
    logic [7:0]     exp_offset;
    act_lut_cmd_t   command;
  } act_fp_lut_mul_queue_t;
  typedef act_fp_lut_mul_queue_t [ISIZE-1:0] ix_fplut_queue_t;
  
  //
  // floating-point one-hot decided instruction indices
  //
  localparam int fp_add_oh_idx    = 0;
  localparam int fp_ftoi_oh_idx   = 1;
  localparam int fp_itof_oh_idx   = 2;
  localparam int fp_trunc_oh_idx  = 3;
  localparam int fp_fract_oh_idx  = 4;
  localparam int fp_renorm_oh_idx = 5;
  typedef logic [5:0] fp_oh_idx_t;
                 
  //
  // Wide accumulators
  //
  typedef logic signed  [47:0]        accw_t;         // 48b accumulator
  typedef accw_t        [ISIZE-1:0]   ixaccw_t;       // 1D vector of accumulators

  //
  // Pooling
  //
  typedef enum logic [1:0] { p2s1, p2s2, p3s1, p3s2 }     act_pool_size_t;
  typedef enum logic [1:0] { pnone, prow, pcol, prowcol } act_pool_mode_t;
  // HLAPI pooling control fields: 4*2+2+2=12B
  typedef struct packed {
    logic             [15:4]               pad;         // pad to 16b
    act_pool_size_t                        size;        // pooling input size
    act_pool_mode_t                        mode;        // 0D, 1D or 2D pooling
    vm_addr_t                              ptr;         // pointer to base of overlap stash
    offset_t          [ACT_POOL_LOOPS-1:0] iter;        // pooling loop iterators (onn*rows*modespec, cols, chan)
  } act_pool_t;


  //
  // AGU types
  //
  // VM address generator struct: 6*(2+2)+2+2+4 = 32B size
  typedef struct packed {
    offset_t  [ACT_FM_LOOPS-1:0]   iter;            // iteration loop number
    offset_t  [ACT_FM_LOOPS-1:0]   offsets;         // VM offsets
    offset_t                       stride;          // vector input/output stride
    buf_t                          buffer;          // cyclic buffer
    vm_addr_t                      ptr;             // pointer into buffer
  } act_hlapi_vm_agu_t;
  // AM address generator struct: 4*(2+2)+2 = 14B size
  typedef struct packed {
    offset_t  [ACT_AM_LOOPS-1:0]   iter;            // iteration loop number
    offset_t  [ACT_AM_LOOPS-1:0]   offsets;         // AM offsets
    logic     [15:10]              pad;             // pad to 16b
    am_addr_t                      ptr;             // pointer into buffer
  } act_hlapi_am_agu_t;

  //
  // Input and output operands
  //
  // input stream parameters
  typedef union packed {
    struct packed {
      logic              [$bits(act_hlapi_vm_agu_t)-
                          $bits(act_hlapi_am_agu_t)-1:0]  pad;                 // pad to match union
      act_hlapi_am_agu_t                                  am_agu;              // input accumulator AGU parameters
    }                                                     a;                   // accumulator fields
    act_hlapi_vm_agu_t                                    fm_agu;              // input feature-map AGU parameters
  } act_in_t;
  
  // output stream parameters: 32+12+4=48
  typedef union packed {
    struct packed {
      logic               [$bits(act_hlapi_vm_agu_t)+$bits(act_pool_t)+32-
                           $bits(act_hlapi_am_agu_t)-1:0] pad;                 // pad to match union
      act_hlapi_am_agu_t                                  am_agu;              // primary input accumulator AGU parameters
    }                                                     a;                   // accumulator output fields
    struct packed {
      //logic               [31:8]                          pad;
      logic               [31:VSIZE]                      pad;
      //logic               [7:0]                           enable;              // write enable per lane
      logic               [VSIZE-1:0]                     enable;              // write enable per lane
      act_pool_t                                          pool;                // pooling control parameters
      act_hlapi_vm_agu_t                                  fm;                  // feature-map output fields
    }                                                     p;
  } act_out_t;
  
  //
  // GTOA HLAPI types
  //
  // Activation function HLAPI type
  typedef struct packed {
    logic                  [7:3]                          pad0;
    pad_inc_t                                             pad_inc;             // padding increment mode
    logic                                                 acc_lay;             // accumulator layout 016 or o32
    logic                  [7:5]                          pad1;
    fmode_t                                               out_fmode;           // float mode (0-int, 1-fp32, 2-fp16, 3-bf16, 4-fp8)
    logic                                                 out_sat;             // saturate output
    logic                                                 out_dbl;             // double wide feature-map
    logic                  [7:4]                          pad2;
    fmode_t                                               in_fmode1;           // float mode (0-int, 1-fp32, 2-fp16, 3-bf16, 4-fp8)
    logic                                                 in_dbl1;             // double wide feature-map
    logic                                                 pad;
    fmode_t                                               in_fmode0;           // float mode (0-int, 1-fp32, 2-fp16, 3-bf16, 4-fp8)
    pad_mode_t                                            in_pmode;            // padding mode
    logic                                                 in_pen0;             // enable input padding on 0
    logic                                                 in_dbl0;             // double wide feature-map
    tmask_t                                               io_en;               // mask for input and output enables
    offset_t                                              pad_stride;          // input padding column stride
    offset_t               [ACT_FM_LOOPS-1:0][1:0]        pad_offs;            // input padding row&column offsets
    offset_t               [1:0]                          pad_lim;             // maxpooling and reduction window boundaries row&column
    offset_t               [1:0]                          pad_pos;             // padding start row&column
    act_out_t                                             out;                 // output fields
    act_in_t                                              secondary;           // secondary input
    act_in_t                                              primary;             // primary input
    logic                  [ISIZE-1:0]                    cmaskn;              // channel mask inverted
    logic                  [47:0]                         pad3;
    act_inst_t             [ACT_PROG_LEN-1:0]             act_prog;            // array of instructions
    vm_addr_t                                             bptr;                // pointer to per channel parameters
    offset_t                                              bnum;                // total number of ixpix_t parameters to read
    offset_t               [ACT_NUM_LOOPS-1:0]            iter;                // [no/onn][col*row][onn]
    act_scalar_t           [ACT_SREG_INI-1:0]             scl;                 // input/output values
  } act_hlapi_i_fu_t;

  typedef struct packed {
    logic [$bits(act_hlapi_i_fu_t)-($bits(act_ue4m4_t)*ACT_LUT_SIZE)-($bits(act_e8m15_t)*(4+ACT_LUT_SIZE*3))-1:0] pad;
    act_ue4m4_t [ACT_LUT_SIZE-1:0]                       lim;
    act_e8m15_t [ACT_LUT_SIZE-1:0]                       coef2;
    act_e8m15_t [ACT_LUT_SIZE-1:0]                       coef1;
    act_e8m15_t [ACT_LUT_SIZE-1:0]                       coef0;
    act_e8m15_t [1:0]                                    lim_deriv;
    act_e8m15_t [1:0]                                    lim_offs;
  } act_lut_t;

  typedef struct packed {
    act_ue8m4_t                          lim;
    act_e8m15_t                          coef2;
    act_e8m15_t                          coef1;
    act_e8m15_t                          coef0;
  } act_lut_entry_t;
  
  typedef struct packed {
    act_lut_entry_t [ACT_LUT_SIZE/2-1:0] entries;
    act_e8m15_t                          lim_deriv;
    act_e8m15_t                          lim_offs;
  } act_lut_half_t;

  typedef struct packed {
    act_lut_half_t [1:0] half;
  } act_lutt_t;

  // HLAPI input type
  typedef struct packed {
    union packed {
      act_lut_t                                   lut;     // look-up table parameters
      act_hlapi_i_fu_t                            fu;      // function
    } u;                                                   // union of function and padding
    logic              [31-$bits(act_typ_t):0]    pad;     // pad to 32b
    act_typ_t                                     typ;     // LUT download or actual operation
    hlapi_i_t                                     common;  // common hlapi parameters
  } act_hlapi_i_t;

  // Top-level HLAPI type
  typedef struct packed {
    hlapi_o_t      o;
    hlapi_io_t     io;
    act_hlapi_i_t  i;
  } act_hlapi_t;
endpackage : npu_gtoa_types
`endif
