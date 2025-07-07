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
 * NPU core logic
 */
// vcs -sverilog  +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_iterator.sv ../../shared/RTL/npu_slice_int.sv ../../shared/RTL/npu_fifo.sv npu_gtoa_types.sv npu_gtoa_core.sv npu_gtoa_fu_alu.sv npu_gtoa_fu_bpar.sv npu_gtoa_fu_in.sv npu_gtoa_fu_mul.sv npu_gtoa_fu_out.sv npu_gtoa_pool.sv npu_gtoa_pcu_issue.sv npu_gtoa_pcu_iter.sv npu_gtoa_pcu.sv npu_gtoa_rf.sv npu_gtoa_lane.sv npu_gtoa_fu_alu_lut.sv npu_gtoa_pad.sv npu_gtoa_fu_pad.sv -y $SYNOPSYS/dw/sim_ver +libext+.v
// analyze -format sverilog -vcs "+incdir+../../../shared/RTL ../../../shared/RTL/npu_types.sv ../../../shared/RTL/npu_iterator.sv ../../../shared/RTL/npu_skid.sv ../../../shared/RTL/npu_slice_int.sv ../../../shared/RTL/npu_fifo.sv ../npu_gtoa_types.sv ../npu_gtoa_core.sv ../npu_gtoa_fu_alu.sv ../npu_gtoa_fu_bpar.sv ../npu_gtoa_fu_in.sv ../npu_gtoa_fu_mul.sv ../npu_gtoa_fu_out.sv ../npu_gtoa_pool.sv ../npu_gtoa_pcu_issue.sv ../npu_gtoa_pcu_iter.sv ../npu_gtoa_pcu.sv ../npu_gtoa_rf.sv"
// set_app_var link_library "* $target_library dw_foundation.sldb"


`include "npu_defines.v"
`include "npu_vm_macros.svh"
`include "npu_am_macros.svh"

module npu_gtoa_core
  import npu_types::*;
  import npu_gtoa_types::*;
  // interface signals
  (
   // clock and reset
   input  logic                                    clk,              // clock
   input  logic                                    rst_a,            // asynchronous reset, active high
   // static inputs
   input  logic           [7:0]                    slc_id,           // unique slice ID
   // interface from HLAPI
   input  logic                                    iter_req,         // request start iterations
   output logic                                    iter_ack,         // acknowledge iteration start
   input  offset_t        [ACT_NUM_LOOPS-1:0]      iter_shp,         // shape of the iterator
   input  act_inst_t      [ACT_PROG_LEN-1:0]       iter_prog,        // iteration program
   input  logic                                    iter_lay,         // accumulator layout
   input  act_scalar_t    [ACT_SREG_INI-1:0]       hlp_scalin,       // scalar array from HLAPI
   input  logic                                    lut_init,         // lut initialization pulse
// spyglass disable_block W240
//SMD:Unread input
//SJ :Macro defined packed signal can be ignore
   input  act_lut_t                                lut_data,         // lut data
// spyglass enable_block W240
   // result to HLAPI struct
   output logic                                    hlapi_o_valid,    // HLAPI output is valid
   input  logic                                    hlapi_o_accept,   // HLAPI output is accepted
   output act_scalar_t                             hlapi_o_res,      // scalar to HLAPI
   // per channel parameter loading
   input  logic           [5:0]                    bpar_q_lvl,       // parameter level
   output logic                                    bpar_pop_q,       // if true then pop parameters from the queue
   output logic           [3:0]                    bpar_pop_q_num,   // number of parameters to pop from queue -1
   input  ixacc_t         [ACT_BREG_NUM-1:0]       bpar_nxt,         // per channel parameters
   // hlapi sat and pool parameters
   input  tmask_t                                  cf_io_en,         // input/output selection
   input  logic                                    cf_i0dbl,         // double width input 0
   input  fmode_t                                  cf_i0fmode,       // float mode input 0
   input  logic                                    cf_i1dbl,         // double width input 0
   input  fmode_t                                  cf_i1fmode,       // float mode input 1
   input  logic                                    cf_osat,          // saturation enable
   input  logic                                    cf_odbl,          // double width enable
   input  fmode_t                                  cf_ofmode,        // float mode output
   input  logic                                    cf_paden,         // enable padding
   input  pad_mode_t                               cf_padmode,       // pad mode: 0, -1, min, max
   input  pad_inc_t                                cf_padinc,        // pad increment mode: i16, v2i8, v4i4
   input  offset_t        [1:0]                    cf_padlim,        // maxpooling and reduction window boundaries row&column
   input  offset_t        [1:0]                    cf_padpos,        // padding start row&column
   input  offset_t        [ACT_FM_LOOPS-1:0][1:0]  cf_padoffs,       // padding loop offset
   input  offset_t        [ACT_FM_LOOPS-1:0]       cf_paditer,       // padding loop iterator
   input  offset_t                                 cf_padstride,     // padding vector stride
   input  offset_t                                 cf_prim_base,     // primary buffer base
   input  offset_t        [ACT_FM_LOOPS-1:0]       cf_prim_offsets,  // primary feature-map input offsets
   output logic                                    gather_valid,     // gather valid
   input  logic                                    gather_accept,    // gather accept
   output offset_t        [VSIZE-1:0]              gather_prod,      // gather product 
// spyglass disable_block W240
//SMD:Unread input
//SJ :Macro defined packed signal can be ignore
   input  act_pool_t                               pool_par,         // pooling parameters
// spyglass enable_block W240
   // maxpool stash read/write
   input  logic                                    mpst_rd_valid,    // maxpool stash read data valid
   output logic                                    mpst_rd_accept,   // maxpool stash read data accept
   input  ixpix_t         [1:0]                    mpst_rd_data,     // maxpool stash read data
   output logic                                    mpst_wr_valid,    // maxpool stash write data valid
   input  logic                                    mpst_wr_accept,   // maxpool stash write accept
   output ixpix_t         [1:0]                    mpst_wr_data,     // maxpool stash write data
   // source&destination control
   output tmask_t                                  ctrl_io_en,       // input/output selection
   // streaming inputs
   input  logic           [1:0]                    in_valid,         // input data valid
   output logic           [1:0]                    in_accept,        // accept input data
   input  vyixacc_t       [1:0]                    in_data,          // input data
   // streaming output
   output logic                                    out_valid,        // input data valid
   input  logic                                    out_accept,       // accept input data
   output vyixacc_t                                out_data,         // input data
   output logic                                    out_dbl           // double output
   );
  // local parameters
  localparam int ISS_SIZE = 32;                       // issue table size
  localparam int NUM_FU   = 7;                        // number of outputs to functional units
  //                         poppar mpy alu1 alu0 out in1 in0
  localparam int NRD      =      1+  2+   1+   2+  2+  2+  2;       // number of read ports
  localparam int NWR      =      0+  1+   1+   1+  0+  1+  1;       // number of write ports
  localparam int VRD      =    'b0__11____1___11__01__00__00;       // vector read port enable
  localparam int SRD      =    'b1__00____0___01__00__00__00;       // scalar read port enable
  localparam int WRD      =    'b0__10____1___10__00__01__01;       // parameter word read port enable
  localparam int HRD      =    'b0__10____0___10__10__00__00;       // parameter half-word read port enable
  localparam int BRD      =    'b0__00____0___10__10__10__10;       // parameter byte read port enable
  localparam int SWR      =        'b0____0____1_______0___0;       // scalar write port enable

  // local types
  typedef enum logic [1:0] {state_idle_e, state_req_e, state_active_e, state_resp_e} state_t;
  
  // local wires
  logic                                         iter_reqi;       // qualified request
  logic                                         hlp_valid;       // if true then start HLAPI
  logic           [NUM_FU-1:0]                  fu_valid;        // instruction valid per functional unit
  act_dec_inst_t  [VSIZE-1:0][NUM_FU-1:0]       fu_inst;         // instruction to be executed per functional units
  logic           [4:0]                         ostall;          // stall per block
  logic                                         stall;           // global stall
  logic                                         busy;            // datapath is busy
  logic                                         bpar_we;         // write next block of per channel parameters
  logic           [NRD-1:0]                     rd_ren;          // read enable
  act_op_sel_t    [NRD-1:0]                     rd_vad;          // vector read operand select
  logic           [NRD-1:0][ACT_SREG_NUM-1:0]   rd_sad_oh;       // scalar read operand address
  logic           [NRD-1:0]                     rd_b_oh;         // if true then parameter read
  logic           [NRD-1:0][ISIZE-1:0]          rd_b_hi;         // if true then read upper half parameter
  logic           [NRD-1:0][ACT_BREG_NUM-1:0]   rd_wad_oh;       // word parameter read operand address
  logic           [NRD-1:0]                     rd_b_oh_d;       // if true then parameter read, delayed on in0/in1
  logic           [NRD-1:0][ISIZE-1:0]          rd_b_hi_d;       // if true then read upper half parameter, delayed on in0/in1
  logic           [NRD-1:0][ACT_BREG_NUM-1:0]   rd_wad_oh_d;     // word parameter read operand address, delayed on in0/in1
  logic                                         rd_in0_oh_r;     // in0 read enable delayed
  logic           [ISIZE-1:0]                   rd_in0_hi_r;     // in0 read upper delayed
  logic           [ACT_BREG_NUM-1:0]            rd_in0_wad_r;    // in0 word parameter read operand address delayed
  logic                                         rd_in1_oh_r;     // in1 read enable delayed
  logic           [ISIZE-1:0]                   rd_in1_hi_r;     // in1 read upper delayed
  logic           [ACT_BREG_NUM-1:0]            rd_in1_wad_r;    // in1 word parameter read operand address delayed
  logic           [NRD-1:0][ACT_BREG_NUM-1:0]   rd_had_oh;       // half-word parameter read operand address
  logic           [NRD-1:0][ACT_BREG_NUM-1:0]   rd_bad_oh;       // byte parameter read operand address
  vyixacc_t       [NRD-1:0]                     rd_data;         // read data
  act_ot_t        [VSIZE-1:0][NWR-1:0]          wr_typ;          // write operand type
  logic           [VSIZE-1:0][NWR-1:0][2:0]     wr_ad;           // write operand address
  vyixacc_t       [NWR-1:0]                     wr_data;         // write data
  logic           [VSIZE-1:0]                   rf_trnsp;        // in register file transpose
  state_t                                       state_r;         // execution state
  state_t                                       state_nxt;       // execution state next
  logic                                         state_en;        // state enable
  tmask_t                                       io_en_r;         // input/output selectors
  logic                                         pcu_idle;        // true if PCU is idle and ready to accept new HLAPI
  ixacc_t         [VSIZE-1:0][NRD-2:0]          rd_datai;        // read data, transposed
  logic           [VSIZE-1:0][2:0]              ostalli;         // stall per vector lane
  logic           [VSIZE-1:0][1:0]              in_accepti;      // accept input data
  ixacc_t         [VSIZE-1:0][1:0]              in_datai;        // transposed input data stream
  logic           [VSIZE-1:0]                   out_validi;      // valid output data
  logic                                         out_accepti;     // accept output data
  vyixacc_t                                     out_datai;       // output data
  logic                                         pool_in_valid;   // pooling input valid
  logic                                         pool_in_accept;  // pooling input accept
  vyixacc_t                                     pool_in_data;    // pooling input data
  logic           [VSIZE-1:0]                   busyi;           // busy
  logic                                         busyp;           // pooling busy
  offset_t                                      gather_base_r;   // primary feature-map input base address
  offset_t                                      gather_base_mc2; // primary feature-map input base address multi cycle
  offset_t                                      prim_offs0_r;    // primary feature-map input offset 0
  offset_t                                      prim_offs0_mc2;  // primary feature-map input offset 0 multi cycle
  offset_t                                      prim_offs1_r;    // primary feature-map input offset 1
  offset_t                                      prim_offs1_mc2;  // primary feature-map input offset 1 multi cycle
  act_lut_t                                     lut_data_r;      // look-up table register
  act_lut_t                                     lut_data_mc2;    // look-up table register multi-cycle
  act_lutt_t                                    lut_data_trs;    // transposed LUT data
  ixacc_t         [VSIZE-1:0][NWR-1:0]          wr_datai;        // write data transpsoed
  vyixacc_t                                     shv_in;          // shv input
  logic                                         cf_in0fm_r;      // input 0 feature-map or accumulator attribute
  logic                                         cf_in0dbl_r;     // input 0 double wide (16b fm or 48b acc) attribute
  fmode_t                                       cf_in0fmode_r;   // input 0 float mode
  logic                                         cf_in1fm_r;      // input 1 feature-map or accumulator attribute
  logic                                         cf_in1dbl_r;     // input 1 double wide (16b fm or 48b acc) attribute
  fmode_t                                       cf_in1fmode_r;   // input 1 float mode
  logic                                         cf_outfm_r;      // output feature-map or accumulator attribute
  logic                                         cf_outsat_r;     // saturate output
  logic                                         cf_outdbl_r;     // double wide output (16b feature-map)
  fmode_t                                       cf_outfmode_r;   // output float mode
  logic                                         cf_in0fm_mc2;    // input 0 feature-map or accumulator attribute
  logic                                         cf_in0dbl_mc2;   // input 0 double wide (16b fm or 48b acc) attribute
  fmode_t                                       cf_in0fmode_mc2; // input 0 float mode
  logic                                         cf_in1fm_mc2;    // input 1 feature-map or accumulator attribute
  logic                                         cf_in1dbl_mc2;   // input 1 double wide (16b fm or 48b acc) attribute
  fmode_t                                       cf_in1fmode_mc2; // input 1 float mode
  logic                                         cf_outfm_mc2;    // output feature-map or accumulator attribute
  logic                                         cf_outsat_mc2;   // saturate output
  logic                                         cf_outdbl_mc2;   // double wide output (16b feature-map)
  fmode_t                                       cf_outfmode_mc2; // output float mode
  logic                                         pad_it_first;    // iterator first flags
  logic                                         padacc;          // accept padding
  logic                                         paden;           // enable padding
  pad_mode_t                                    padmode;         // padding mode: 0, -1, min, max
  pad_inc_t                                     padinc;          // padding increment mode: i16, v2i8, v4i4
  offset_t        [VSIZE-1:0][ISIZE/4-1:0]      padcpos;         // padding column position
  logic           [VSIZE-1:0][ISIZE/4-1:0]      padi4v;          // padding bit per i4 channels
  acc_t           [VSIZE-1:0]                   rd_vr7i0;        // fixed wire for vr7 i0 data read
  acc_t           [ISIZE-1:0]                   rd_vr7v0;        // fixed wire for vr7 v0 data read

  
  //
  // simple assignments
  //
  assign stall      = ostall != '0;
  assign ctrl_io_en = io_en_r;

  
  //
  // FSM
  //
  // outputs: state_nxt, state_en, iter_reqi, iter_ack, hlapi_o_valid, hlp_valid
  always_comb
  begin : state_nxt_PROC
    // default outputs
    state_en      = 1'b0;
    state_nxt     = state_idle_e;
    iter_reqi     = 1'b0;
    iter_ack      = 1'b0;
    hlp_valid     = 1'b0;
    hlapi_o_valid = 1'b0;
    case (state_r)
    state_req_e:
      begin
        // accept request
        iter_ack  = 1'b1;
        state_en  = 1'b1;
        iter_reqi = 1'b1;
        state_nxt = state_active_e;
      end
    state_active_e:
      begin
        if (pcu_idle & ~busy)
        begin
          // done with HLAPI, return response
          state_en  = 1'b1;
          state_nxt = state_resp_e;
        end
      end
    state_resp_e:
      begin
        hlapi_o_valid = 1'b1;
        if (hlapi_o_accept)
        begin
          // response done, go back to idle
          state_en  = 1'b1;
          state_nxt = state_idle_e;
        end
      end
    default: // idle
      begin
        if (lut_init)
        begin
          // initialize look-up table
          iter_ack  = 1'b1;
          state_en  = 1'b1;
          state_nxt = state_resp_e;
        end
        else if (iter_req)
        begin
          // start a new HLAPI
          state_en  = 1'b1;
          state_nxt = state_req_e;
          hlp_valid = 1'b1;
        end
      end
    endcase // case (state_r)
  end : state_nxt_PROC
  
  // state flops
  // outputs: state_r, io_en_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : fsm_reg_PROC
    if (rst_a == 1'b1)
    begin
      state_r     <= state_idle_e;
      io_en_r     <= '0;
      cf_in0fm_r  <= 1'b0;
      cf_in0dbl_r <= 1'b0;
      cf_in0fmode_r <= fmode_int32_e;
      cf_in1fm_r  <= 1'b0;
      cf_in1dbl_r <= 1'b0;
      cf_in1fmode_r <= fmode_int32_e;
      cf_outfm_r  <= 1'b0;
      cf_outsat_r <= 1'b0;
      cf_outdbl_r <= 1'b0;
      cf_outfmode_r <= fmode_int32_e;
    end
    else
    begin
      if (hlp_valid)
      begin
        io_en_r       <= cf_io_en;
        cf_in0fm_r    <= (cf_io_en & act_io_en_fm0_e) != '0 || (cf_io_en & act_io_en_gth_e) != 0;
        cf_in0dbl_r   <= cf_i0dbl;
        cf_in0fmode_r <= cf_i0fmode;
        cf_in1fm_r    <= (cf_io_en & act_io_en_fm1_e) != '0;
        cf_in1dbl_r   <= cf_i1dbl;
        cf_in1fmode_r <= cf_i1fmode;
        cf_outfm_r    <= (cf_io_en & act_io_en_ofm_e) != '0;
        cf_outsat_r   <= cf_osat;
        cf_outdbl_r   <= cf_odbl;
        cf_outfmode_r <= cf_ofmode;
      end
      if (state_en)
      begin
        state_r <= state_nxt;
      end
    end
  end : fsm_reg_PROC

  
  //
  // PCU Instance
  //
  npu_gtoa_pcu
    #(
      .PROG_LEN  ( ACT_PROG_LEN  ),
      .NUM_LOOPS ( ACT_NUM_LOOPS ),
      .ISS_SIZE  ( ISS_SIZE      ),   // issue table size
      .NUM_FU    ( NUM_FU        ),   // number of outputs to functional units
      .NRD       ( NRD           )    // number of read ports
      )
  u_pcu_inst
    (
     .clk       ( clk       ),
     .rst_a     ( rst_a     ),
     .iter_req  ( iter_reqi ),
     .iter_ack  ( pcu_idle  ),
     .iter_shp  ( iter_shp  ),
     .iter_prog ( iter_prog ),
     .iter_lay  ( iter_lay  ),
     .fu_valid  ( fu_valid  ),
     .fu_inst   ( fu_inst   ),
     .rd_ren    ( rd_ren    ),
     .rd_vad    ( rd_vad    ),
     .rd_sad_oh ( rd_sad_oh ),
     .rd_b_oh   ( rd_b_oh   ),
     .rd_b_hi   ( rd_b_hi   ),
     .rd_wad_oh ( rd_wad_oh ),
     .rd_had_oh ( rd_had_oh ),
     .rd_bad_oh ( rd_bad_oh ),
     .stall     ( stall     )
     );


  // 1 stage delay for in0/in1 BRW read
  always_ff @(posedge clk or
              posedge rst_a)
  begin : brw_reg_PROC
    if (rst_a == 1'b1)
    begin
      rd_in0_oh_r  <= 1'b0;
      rd_in0_hi_r  <= '0;
      rd_in0_wad_r <= '0;
      rd_in1_oh_r  <= 1'b0;
      rd_in1_hi_r  <= 1'b0;
      rd_in1_wad_r <= '0;
    end
    else
    begin
      if (~stall)
      begin
        rd_in0_oh_r  <= rd_b_oh[0];
        rd_in0_hi_r  <= rd_b_hi[0];
        rd_in0_wad_r <= rd_wad_oh[0];
        rd_in1_oh_r  <= rd_b_oh[2];
        rd_in1_hi_r  <= rd_b_hi[2];
        rd_in1_wad_r <= rd_wad_oh[2];
      end
    end
  end : brw_reg_PROC

  // use delayed wad for in0/in1 ports
  // b_oh/b_hi keep high for both stages
  always_comb
    begin : brw_rpl_PROC
      rd_b_oh_d      = rd_b_oh;
      rd_b_hi_d      = rd_b_hi;
      rd_wad_oh_d    = rd_wad_oh;
      // replace by delayed versions
      rd_b_oh_d[0]   = rd_in0_oh_r;
      rd_b_hi_d[0]   = rd_in0_hi_r;
      rd_wad_oh_d[0] = rd_in0_wad_r;
      rd_b_oh_d[2]   = rd_in1_oh_r;
      rd_b_hi_d[2]   = rd_in1_hi_r;
      rd_wad_oh_d[2] = rd_in1_wad_r;
    end : brw_rpl_PROC


  //
  // Register file
  //
  npu_gtoa_rf
    #(
      .NRD ( NRD ),
      .NWR ( NWR ),
      .VRD ( VRD ),
      .SRD ( SRD ),
      .WRD ( WRD ),
      .HRD ( HRD ),
      .BRD ( BRD ),
      .SWR ( SWR )
      )
  u_rf_inst
    (
     .clk         ( clk         ),
     .rst_a       ( rst_a       ),
     .hlp_valid   ( hlp_valid   ),
     .hlp_scalin  ( hlp_scalin  ),
     .hlp_scalout ( hlapi_o_res ),
     .bpar_we     ( bpar_we     ),
     .bpar_nxt    ( bpar_nxt    ),
     .rd_ren      ( rd_ren      ),
     .rd_vad      ( rd_vad      ),
     .rd_sad_oh   ( rd_sad_oh   ),
     .rd_b_oh     ( rd_b_oh_d   ),
     .rd_b_hi     ( rd_b_hi_d   ),
     .rd_wad_oh   ( rd_wad_oh_d ),
     .rd_had_oh   ( rd_had_oh   ),
     .rd_bad_oh   ( rd_bad_oh   ),
     .rd_data     ( rd_data     ),
     .rd_vr7i0    ( rd_vr7i0    ),
     .rd_vr7v0    ( rd_vr7v0    ),
     .wr_typ      ( wr_typ      ),
     .wr_ad       ( wr_ad       ),
     .wr_data     ( wr_data     ),
     .rf_trnsp    ( rf_trnsp    ),
     .stall       ( stall       )
     );


  logic [VSIZE-1:0][1:0][ISIZE-1:0][31:0]  lane_data_switch;
  always_comb 
  begin : red_sw_PROC
    lane_data_switch = '0;
    for (int i = 0; i < VSIZE; i++) 
    begin
      lane_data_switch[i/2][i&1] = rd_datai[i][6];
    end
    // eg. the above for loop results in the logic below
    //lane_data_switch[0][0] = rd_datai[0][6];
    //lane_data_switch[0][1] = rd_datai[1][6];
    //lane_data_switch[1][0] = rd_datai[2][6];
    //lane_data_switch[1][1] = rd_datai[3][6];
    //lane_data_switch[2][0] = rd_datai[4][6];
    //lane_data_switch[2][1] = rd_datai[5][6];
    //lane_data_switch[3][0] = rd_datai[6][6];
    //lane_data_switch[3][1] = rd_datai[7][6];
  end : red_sw_PROC  

  logic [VSIZE-1:0][ISIZE-1:0] lane_state_o;
  logic [VSIZE-1:0][ISIZE-1:0] lane_state_i;
  always_comb 
  begin : state_sw_PROC
    lane_state_i = '0;
    for (int i=0;i<VSIZE;i++) 
    begin
      lane_state_i[i] = (i%2==0) ? lane_state_o[i/2] : ~lane_state_o[i/2];
    end
    // eg. the above for loop results in the logic below
    //lane_state_i[0] = lane_state_o[0];
    //lane_state_i[1] = ~lane_state_o[0];
    //lane_state_i[2] = lane_state_o[1];
    //lane_state_i[3] = ~lane_state_o[1];
    //lane_state_i[4] = lane_state_o[2];
    //lane_state_i[5] = ~lane_state_o[2];
    //lane_state_i[6] = lane_state_o[3];
    //lane_state_i[7] = ~lane_state_o[3];
  end : state_sw_PROC

  // AGU offsets flops
  // outputs: prim_offs0_r, prim_offs1_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : offs_reg_PROC
    if (rst_a == 1'b1)
    begin
      prim_offs0_r  <= '0;
      prim_offs1_r  <= '0;
      gather_base_r <= '0;
    end
    else
    begin
      if (hlp_valid)
      begin
        prim_offs0_r  <= cf_prim_offsets[0];
        prim_offs1_r  <= cf_prim_offsets[1];
        gather_base_r <= cf_prim_base;
      end
    end
  end : offs_reg_PROC


  //
  // 2-cycle multi-cycle path on AGU offsets and base
  //
  npu_2cyc_checker
    #(
       .WIDTH ( $bits(offset_t) )
       )
  u_gather_base_mc2_inst
    (
     .clk      ( clk             ),
     .rst_a    ( rst_a           ),
     .valid    ( 1'b1            ),
     .data_in  ( gather_base_r   ),
     .data_out ( gather_base_mc2 )
     );

  npu_2cyc_checker
    #(
       .WIDTH ( $bits(offset_t) )
       )
  u_prim_offs0_mc2_inst
    (
     .clk      ( clk            ),
     .rst_a    ( rst_a          ),
     .valid    ( 1'b1           ),
     .data_in  ( prim_offs0_r   ),
     .data_out ( prim_offs0_mc2 )
     );

  npu_2cyc_checker
    #(
       .WIDTH ( $bits(offset_t) )
       )
  u_prim_offs1_mc2_inst
    (
     .clk      ( clk            ),
     .rst_a    ( rst_a          ),
     .valid    ( 1'b1           ),
     .data_in  ( prim_offs1_r   ),
     .data_out ( prim_offs1_mc2 )
     );
  
  //
  // Generate processing lanes
  //
  assign out_accepti = pool_in_accept;
  // reduction lane 0
  npu_gtoa_lane
  #(
      .VID    ( 0        ),
      .NUM_FU ( NUM_FU-1 ), // BPAR is not part of lane
      .NRD    ( NRD-1    ), // BPAR is not part of lane
      .NWR    ( NWR      )
      )
  u_lane_inst
    (
     .clk           ( clk                  ),
     .rst_a         ( rst_a                ),
     .slc_id        ( slc_id               ),
     .fu_valid      ( fu_valid[NUM_FU-2:0] ),
     .fu_inst       ( fu_inst[0][NUM_FU-2:0] ),
     .ostall        ( ostalli[0]           ),
     .stall         ( stall                ),
     .busy          ( busyi[0]             ),
     .rd_data       ( rd_datai[0]          ),
     .wr_typ        ( wr_typ[0]            ),
     .wr_ad         ( wr_ad[0]             ),
     .wr_data       ( wr_datai[0]          ),
     .rf_trnsp      ( rf_trnsp[0]          ),
     .lut_data      ( lut_data_trs         ),
     .red_inp       ( lane_data_switch[0]  ),
     .red_state_out ( lane_state_o[0]      ),
     .red_state_in  ( lane_state_i[0]      ),
`ifdef ACT_HAS_ALU1
     .bcv_in        ( rd_datai[0][8]       ),
`else
     .bcv_in        ( rd_datai[0][6]       ),
`endif
     .gather_base   ( gather_base_mc2      ),
     .in_offs0      ( prim_offs0_mc2       ),
     .in_offs1      ( prim_offs1_mc2       ),
     .rd_vr7i0      ( rd_vr7i0[0]          ),
     .rd_vr7i0v0    ( rd_vr7i0[0]          ),
     .rd_vr7v0l     ( rd_vr7v0[0]          ),
     .rd_vr7v0h     ( rd_vr7v0[0+ISIZE/2]  ),
     .gather_valid  ( gather_valid         ),
     .gather_accept ( gather_accept        ),
     .gather_prod   ( gather_prod[0]       ),
     .shv_in        ( shv_in[0]            ),
     .in_valid      ( in_valid             ),
     .in_accept     ( in_accepti[0]        ),
     .in_data       ( in_datai[0]          ),
     .it_first      ( pad_it_first         ),
     .padacc        ( padacc               ),
     .paden         ( paden                ),
     .padmode       ( padmode              ),
     .padinc        ( padinc               ),
     .padcpos       ( padcpos[0]           ),
     .padi4         ( padi4v[0]            ),
     .out_valid     ( out_validi[0]        ),
     .out_accept    ( out_accepti          ),
     .out_data      ( out_datai[0]         ),
     .cf_in0fm      ( cf_in0fm_mc2         ),
     .cf_in0dbl     ( cf_in0dbl_mc2        ),
     .cf_in0fmode   ( cf_in0fmode_mc2      ),
     .cf_in1fm      ( cf_in1fm_mc2         ),
     .cf_in1dbl     ( cf_in1dbl_mc2        ),
     .cf_in1fmode   ( cf_in1fmode_mc2      ),
     .cf_outfm      ( cf_outfm_mc2         ),
     .cf_outsat     ( cf_outsat_mc2        ),
     .cf_outdbl     ( cf_outdbl_mc2        ),
     .cf_outfmode   ( cf_outfmode_mc2      )
     );
  // lanes 1 and beyond
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :intentionally unconnected
  for (genvar gv = 1; gv < VSIZE; gv++)
    begin : lane_GEN
      npu_gtoa_lane
    #(
    .VID    ( gv       ),
    .NUM_FU ( NUM_FU-1 ), // BPAR is not part of lane
    .NRD    ( NRD-1    ), // BPAR is not part of lane
    .NWR    ( NWR      )
    )
    u_lane_inst
    (
     .clk           ( clk                  ),
     .rst_a         ( rst_a                ),
     .slc_id        ( slc_id               ),
     .fu_valid      ( fu_valid[NUM_FU-2:0] ),
     .fu_inst       ( fu_inst[gv][NUM_FU-2:0] ),
     .ostall        ( ostalli[gv]          ),
     .stall         ( stall                ),
     .busy          ( busyi[gv]            ),
     .rd_data       ( rd_datai[gv]         ),
     .wr_typ        ( wr_typ[gv]           ),
     .wr_ad         ( wr_ad[gv]            ),
     .wr_data       ( wr_datai[gv]         ),
     .rf_trnsp      ( rf_trnsp[gv]         ),
     .lut_data      ( lut_data_trs         ),
     .red_inp       ( lane_data_switch[gv] ),
     .red_state_out ( lane_state_o[gv]     ),
     .red_state_in  ( lane_state_i[gv]     ),
`ifdef ACT_HAS_ALU1
     .bcv_in        ( rd_datai[0][8]       ),
`else
     .bcv_in        ( rd_datai[0][6]       ),
`endif
     .gather_base   ( gather_base_mc2      ),
     .in_offs0      ( prim_offs0_mc2       ),
     .in_offs1      ( prim_offs1_mc2       ),
     .rd_vr7i0      ( rd_vr7i0[gv]         ),
     .rd_vr7i0v0    ( rd_vr7i0[0]          ),
     .rd_vr7v0l     ( rd_vr7v0[gv]         ),
     .rd_vr7v0h     ( rd_vr7v0[gv+ISIZE/2] ),
     .gather_valid  (                      ), // intentionally unconnected
     .gather_accept ( gather_accept        ),
     .gather_prod   ( gather_prod[gv]      ),
     .shv_in        ( shv_in[gv]           ),
     .in_valid      ( in_valid             ),
     .in_accept     ( in_accepti[gv]       ),
     .in_data       ( in_datai[gv]         ),
     .it_first      ( pad_it_first         ),
     .padacc        (                      ), // intentionally unconnected
     .paden         ( paden                ),
     .padmode       ( padmode              ),
     .padinc        ( padinc               ),
     .padcpos       ( padcpos[gv]          ),
     .padi4         ( padi4v[gv]           ),
     .out_valid     ( out_validi[gv]       ),
     .out_accept    ( out_accepti          ),
     .out_data      ( out_datai[gv]        ),
     .cf_in0fm      ( cf_in0fm_mc2         ),
     .cf_in0dbl     ( cf_in0dbl_mc2        ),
     .cf_in0fmode   ( cf_in0fmode_mc2      ),
     .cf_in1fm      ( cf_in1fm_mc2         ),
     .cf_in1dbl     ( cf_in1dbl_mc2        ),
     .cf_in1fmode   ( cf_in1fmode_mc2      ),
     .cf_outfm      ( cf_outfm_mc2         ),
     .cf_outsat     ( cf_outsat_mc2        ),
     .cf_outdbl     ( cf_outdbl_mc2        ),
     .cf_outfmode   ( cf_outfmode_mc2      )
     );
    end : lane_GEN
// spyglass enable_block W287b

  
  //
  // SHV: spatial dimension shift
  //
  // outputs: shv_in
  always_comb
  begin : shv_PROC
    shv_in = '0;
    for (int v = 0; v < VSIZE-1; v++)
    begin
`ifdef ACT_HAS_ALU1
      shv_in[v] = rd_datai[v+1][8];
`else
      shv_in[v] = rd_datai[v+1][6];
`endif
    end
  end : shv_PROC

  //
  // Padding unit
  //
  npu_gtoa_pad
  u_pad_inst
  (
   .clk          ( clk          ),
   .rst_a        ( rst_a        ),
   .cf_en        ( hlp_valid    ),
   .cf_paden     ( cf_paden     ),
   .cf_padmode   ( cf_padmode   ),
   .cf_padinc    ( cf_padinc    ),
   .cf_padlim    ( cf_padlim    ),
   .cf_padpos    ( cf_padpos    ),
   .cf_padoffs   ( cf_padoffs   ),
   .cf_paditer   ( cf_paditer   ),
   .cf_padstride ( cf_padstride ),
   .out_first    ( pad_it_first ),
   .padacc       ( padacc       ),
   .paden        ( paden        ),
   .padmode      ( padmode      ),
   .padinc       ( padinc       ),
   .padcpos      ( padcpos      ),
   .padi4v       ( padi4v       )
   );
  
  //
  // Common lane logic
  //
  assign ostall[2:0] = ostalli[0];
  assign in_accept   = in_accepti[0];
  assign busy        = busyi[0] | busyp | (~out_accept);

  //
  // Pooling on all lanes
  //
  assign pool_in_data    = out_datai;
  assign pool_in_valid   = out_validi[0];

  npu_gtoa_pool
  u_pool_inst
    (
     .clk                ( clk                ),
     .rst_a              ( rst_a              ),
     .in_valid           ( pool_in_valid      ),
     .in_accept          ( pool_in_accept     ),
     .in_data            ( pool_in_data       ),
     .hlp_valid          ( hlp_valid          ),
     .iter_req           ( iter_reqi          ),
     .pool_par_iter      ( pool_par.iter      ),
     .pool_par_mode      ( pool_par.mode      ),
     .pool_par_size      ( pool_par.size      ),
     .pool_par_dbl       ( cf_odbl            ),
     .pool_fmode         ( cf_ofmode          ),
     .padpos_col         ( cf_padpos[0]       ),
     .mpst_rd_valid      ( mpst_rd_valid      ),
     .mpst_rd_accept     ( mpst_rd_accept     ),
     .mpst_rd_data       ( mpst_rd_data       ),
     .mpst_wr_valid      ( mpst_wr_valid      ),
     .mpst_wr_accept     ( mpst_wr_accept     ),
     .mpst_wr_data       ( mpst_wr_data       ),
     .out_valid          ( out_valid          ),
     .out_accept         ( out_accept         ),
     .out_data           ( out_data           ),
     .busy               ( busyp              ),
     .ostall             ( ostall[3]          )
     );
  assign out_dbl = cf_outdbl_mc2;
  
  // transpose read data from [nr][v] to [v][nr]
  // outputs; rd_datai
  always_comb
  begin : rd_xpose_PROC
    for (int r = 0; r < NRD-1; r++)
    begin
      for (int v = 0; v < VSIZE; v++)
      begin
        rd_datai[v][r] = rd_data[r][v];
      end
    end
  end : rd_xpose_PROC

  // transpose write data from [v][nr] to [nr][v]
  // outputs; wr_data
  always_comb
  begin : wr_xpose_PROC
    for (int w = 0; w < NWR; w++)
    begin
      for (int v = 0; v < VSIZE; v++)
      begin
        wr_data[w][v] = wr_datai[v][w];
      end
    end
  end : wr_xpose_PROC

  // transpose input data streams
  // outputs; in_datai
  always_comb
  begin : in_xpose_PROC
    for (int r = 0; r < 2; r++)
    begin
      for (int v = 0; v < VSIZE; v++)
      begin
        in_datai[v][r] = in_data[r][v];
      end
    end
  end : in_xpose_PROC  

  // look-up fp table register
  // outputs: lut_data_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : lut_reg_PROC
    if (rst_a == 1'b1)
    begin
      lut_data_r <= '0;
    end
    else if (lut_init & (state_r == state_idle_e))
    begin
      lut_data_r <= lut_data;
    end
  end : lut_reg_PROC

  
  //
  // 2-cycle multi-cycle path on look-up table signals
  //
  npu_2cyc_checker 
  #( 
     .WIDTH ( $bits(act_lut_t) )
  )
  u_lut_data_mc2_inst
  (
   .clk      ( clk          ),
   .rst_a    ( rst_a        ),
   .valid    ( 1'b1         ),
   .data_in  ( lut_data_r   ),
   .data_out ( lut_data_mc2 )
  );

  // transpose LUT
  // outputs: lut_data_trs
  always_comb
  begin : trs_lut_PROC
    for (int j = 0; j < 2; j++)
    begin
      lut_data_trs.half[j].lim_offs  = lut_data_mc2.lim_offs[j];
      lut_data_trs.half[j].lim_deriv = lut_data_mc2.lim_deriv[j];
      for (int i = 0; i < ACT_LUT_SIZE/2; i++)
      begin
        // add bias differnce to lim
        lut_data_trs.half[j].entries[i].lim   = {4'd0,lut_data_mc2.lim[j*ACT_LUT_SIZE/2+i]}+{8'd120,4'd0};
        lut_data_trs.half[j].entries[i].coef0 = lut_data_mc2.coef0[j*ACT_LUT_SIZE/2+i];
        lut_data_trs.half[j].entries[i].coef1 = lut_data_mc2.coef1[j*ACT_LUT_SIZE/2+i];
        lut_data_trs.half[j].entries[i].coef2 = lut_data_mc2.coef2[j*ACT_LUT_SIZE/2+i];
      end
    end
  end : trs_lut_PROC


  //
  // 2-cycle multi-cycle path on config
  //
  npu_2cyc_checker 
    #( 
       .WIDTH ( 1 )
       )
  u_in0fm_mc2_inst
    (
     .clk      ( clk          ),
     .rst_a    ( rst_a        ),
     .valid    ( 1'b1         ),
     .data_in  ( cf_in0fm_r   ),
     .data_out ( cf_in0fm_mc2 )
     );

  npu_2cyc_checker 
    #( 
       .WIDTH ( $bits(fmode_t) )
       )
  u_in0fmode_mc2_inst
    (
     .clk      ( clk                                 ),
     .rst_a    ( rst_a                               ),
     .valid    ( 1'b1                                ),
     .data_in  ( cf_in0fmode_r[$bits(fmode_t)-1:0]   ),
     .data_out ( cf_in0fmode_mc2[$bits(fmode_t)-1:0] )
     );

  npu_2cyc_checker 
    #( 
       .WIDTH ( 1 )
       )
  u_in0dbl_mc2_inst
    (
     .clk      ( clk           ),
     .rst_a    ( rst_a         ),
     .valid    ( 1'b1          ),
     .data_in  ( cf_in0dbl_r   ),
     .data_out ( cf_in0dbl_mc2 )
     );

  npu_2cyc_checker 
    #( 
       .WIDTH ( 1 )
       )
  u_in1fm_mc2_inst
    (
     .clk      ( clk          ),
     .rst_a    ( rst_a        ),
     .valid    ( 1'b1         ),
     .data_in  ( cf_in1fm_r   ),
     .data_out ( cf_in1fm_mc2 )
     );

  npu_2cyc_checker 
    #( 
       .WIDTH ( $bits(fmode_t) )
       )
  u_in1fmode_mc2_inst
    (
     .clk      ( clk                                  ),
     .rst_a    ( rst_a                                ),
     .valid    ( 1'b1                                 ),
     .data_in  ( cf_in1fmode_r[$bits(fmode_t)-1:0]    ),
     .data_out ( cf_in1fmode_mc2[$bits(fmode_t)-1:0]  )
     );

  npu_2cyc_checker 
    #( 
       .WIDTH ( 1 )
       )
  u_in1dbl_mc2_inst
    (
     .clk      ( clk           ),
     .rst_a    ( rst_a         ),
     .valid    ( 1'b1          ),
     .data_in  ( cf_in1dbl_r   ),
     .data_out ( cf_in1dbl_mc2 )
     );

  npu_2cyc_checker 
    #( 
       .WIDTH ( 1 )
       )
  u_outfm_mc2_inst
    (
     .clk      ( clk          ),
     .rst_a    ( rst_a        ),
     .valid    ( 1'b1         ),
     .data_in  ( cf_outfm_r   ),
     .data_out ( cf_outfm_mc2 )
     );

  npu_2cyc_checker 
    #( 
       .WIDTH ( $bits(fmode_t) )
       )
  u_outfmode_mc2_inst
    (
     .clk      ( clk                                 ),
     .rst_a    ( rst_a                               ),
     .valid    ( 1'b1                                ),
     .data_in  ( cf_outfmode_r[$bits(fmode_t)-1:0]   ),
     .data_out ( cf_outfmode_mc2[$bits(fmode_t)-1:0] )
     );

  npu_2cyc_checker 
    #( 
       .WIDTH ( 1 )
       )
  u_outsat_mc2_inst
    (
     .clk      ( clk           ),
     .rst_a    ( rst_a         ),
     .valid    ( 1'b1          ),
     .data_in  ( cf_outsat_r   ),
     .data_out ( cf_outsat_mc2 )
     );

  npu_2cyc_checker 
    #( 
       .WIDTH ( 1 )
       )
  u_outdbl_mc2_inst
    (
     .clk      ( clk              ),
     .rst_a    ( rst_a            ),
     .valid    ( 1'b1             ),
     .data_in  ( cf_outdbl_r      ),
     .data_out ( cf_outdbl_mc2    )
     );


  //
  // Per channel parameter pop, input 0 from S
  //
  localparam int BPAR_RD_BASE = 11;
  npu_gtoa_fu_bpar
  u_bpar_inst
  (
   .clk         ( clk                             ),
   .rst_a       ( rst_a                           ),
   .fu_valid    ( fu_valid[fu_bpar]               ),
   .fu_inst     ( fu_inst[0][fu_bpar]             ),
   .rd_data     ( rd_data[BPAR_RD_BASE][0][0]     ),
   .par_q_lvl   ( bpar_q_lvl                      ),
   .pop_q       ( bpar_pop_q                      ),
   .pop_q_num   ( bpar_pop_q_num                  ),
   .bpar_we     ( bpar_we                         ),
   .ostall      ( ostall[4]                       ),
   .stall       ( stall                           )
   );
  
endmodule : npu_gtoa_core
