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
// vcs -sverilog  +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_iterator.sv ../../shared/RTL/npu_slice_int.sv ../../shared/RTL/npu_fifo.sv npu_gtoa_types.sv npu_gtoa_core.sv npu_gtoa_core_wrap.sv npu_gtoa_fu_alu.sv npu_gtoa_fu_bpar.sv npu_gtoa_fu_in.sv npu_gtoa_fu_mul.sv npu_gtoa_fu_out.sv npu_gtoa_pool.sv npu_gtoa_pcu_issue.sv npu_gtoa_pcu_iter.sv npu_gtoa_pcu.sv npu_gtoa_rf.sv npu_gtoa_lane.sv npu_gtoa_fu_alu_lut.sv -y $SYNOPSYS/dw/sim_ver +libext+.v
// analyze -format sverilog -vcs "+incdir+../../../shared/RTL ../../../shared/RTL/npu_types.sv ../../../shared/RTL/npu_iterator.sv ../../../shared/RTL/npu_skid.sv ../../../shared/RTL/npu_slice_int.sv ../../../shared/RTL/npu_fifo.sv ../npu_gtoa_types.sv ../npu_gtoa_core.sv ../npu_gtoa_fu_alu.sv ../npu_gtoa_fu_bpar.sv ../npu_gtoa_fu_in.sv ../npu_gtoa_fu_mul.sv ../npu_gtoa_fu_out.sv ../npu_gtoa_pool.sv ../npu_gtoa_pcu_issue.sv ../npu_gtoa_pcu_iter.sv ../npu_gtoa_pcu.sv ../npu_gtoa_rf.sv"
// set_app_var link_library "* $target_library dw_foundation.sldb"

`include "npu_vm_macros.svh"
`include "npu_am_macros.svh"

module npu_gtoa_core_wrap
  import npu_types::*;
  import npu_gtoa_types::*;
  // interface signals
  (
   // clock and reset
   input  logic                                    clk,                // GTOA main clock
   input  logic                                    clk_half,           // clock at half the frequency of the GTOA main clock
   input  logic           [1:0]                    cycle,              // signal indicating active clock cycle after rising edge
   input  logic                                    rst_a,              // asynchronous reset, active high, deassertion synchronous to clk_half
   input  logic                                    rst_half,           // asynchronous reset, active high, deassertion synchronous to clk_half
   // static inputs
   input  logic           [7:0]                    slc_id,             // unique slice ID
   // interface from HLAPI
   input  logic                                    iter_req,           // request start iterations
   output logic                                    iter_ack,           // acknowledge iteration start
   input  offset_t        [ACT_NUM_LOOPS-1:0]      iter_shp,           // shape of the iterator
   input  act_inst_t      [ACT_PROG_LEN-1:0]       iter_prog,          // iteration program
   input  logic                                    iter_lay,           // accumulator layout
   input  act_scalar_t    [ACT_SREG_INI-1:0]       hlp_scalin,         // scalar array from HLAPI
   input  logic                                    lut_init,           // lut initialization pulse
   input  act_lut_t                                lut_data,           // lut data
   // result to HLAPI struct
   output logic                                    hlapi_o_valid,      // HLAPI output is valid
   input  logic                                    hlapi_o_accept,     // HLAPI output is accepted
   output act_scalar_t                             hlapi_o_res,        // scalar to HLAPI
   // hlapi sat and pool parameters
   input  tmask_t                                  cf_io_en,           // input/output selection
   input  logic                                    cf_i0dbl,           // double width input 0
   input  fmode_t                                  cf_i0fmode,         // float mode input 0
   input  logic                                    cf_i1dbl,           // double width input 0
   input  fmode_t                                  cf_i1fmode,         // float mode input 1
   input  logic                                    cf_osat,            // saturation enable
   input  logic                                    cf_odbl,            // double width enable
   input  fmode_t                                  cf_ofmode,          // float mode output
   input  logic                                    cf_paden,           // enable padding
   input  pad_mode_t                               cf_padmode,         // pad mode
   input  pad_inc_t                                cf_padinc,          // pad increment mode
   input  offset_t        [1:0]                    cf_padlim,          // maxpooling and reduction window boundaries row&column
   input  offset_t        [1:0]                    cf_padpos,          // padding start row&column
   input  offset_t        [ACT_FM_LOOPS-1:0][1:0]  cf_padoffs,         // padding loop offset
   input  offset_t        [ACT_FM_LOOPS-1:0]       cf_paditer,         // padding loop iterator
   input  offset_t                                 cf_padstride,       // padding vector stride
   input  offset_t                                 cf_prim_base,       // base address of primary feature-map input
   input  offset_t        [ACT_FM_LOOPS-1:0]       cf_prim_offsets,    // offsets of primary feature-map input
   input  act_pool_t                               pool_par,           // pooling parameters
   // source&destination control
   output tmask_t                                  ctrl_io_en,         // input/output selection
   output logic                                    out_dbl,            // double output
   // per channel parameter loading
   input  logic           [5:0]                    bpar_q_lvl,         // parameter level
   output logic                                    bpar_pop_q,         // if true then pop parameters from the queue
   output logic           [3:0]                    bpar_pop_q_num,     // number of parameters to pop from queue -1
   input  ixacc_t         [ACT_BREG_NUM-1:0]       bpar_nxt,           // per channel parameters
   // gather interface
   output logic                                    gather_valid,       // gather valid
   input  logic                                    gather_accept,      // gather accept
   output offset_t        [VSIZE-1:0]              gather_prod,        // gather product
   // maxpool stash read/write
   input  logic                                    mpst_rd_valid,      // maxpool stash read data valid
   output logic                                    mpst_rd_accept,     // maxpool stash read data accept
   input  ixpix_t         [1:0]                    mpst_rd_data,       // maxpool stash read data
   output logic                                    mpst_wr_valid,      // maxpool stash write data valid
   input  logic                                    mpst_wr_accept,     // maxpool stash write accept
   output ixpix_t         [1:0]                    mpst_wr_data,       // maxpool stash write data
   // streaming inputs
   input  logic           [1:0]                    in_valid,           // input data valid
   output logic           [1:0]                    in_accept,          // accept input data
   input  vyixacc_t       [1:0]                    in_data,            // input data
   // streaming output
   output logic                                    out_valid,          // input data valid
   input  logic                                    out_accept,         // accept input data
   output vyixacc_t                                out_data            // input data
   ); 
  // internal wires
  logic                                    iter_acki;             // acknowledge iteration start
  logic                                    hlapi_o_validi;        // HLAPI output is valid
  logic                                    first_r;               // first cycle after reset
  logic           [7:0]                    slc_id_r;              // slice ID register
  logic           [5:0]                    bpar_q_lvl_r;          // delayed queue level
  logic                                    bpar_pop_q_i;
  // f2s multi-cycle handshake signals
  logic           [1:0]                    in_valid_mc2;
  logic                                    mpst_rd_valid_mc2;
  logic                                    out_accept_mc2;
  logic                                    mpst_wr_accept_mc2;
  logic                                    gather_accept_mc2;
  logic           [5:0]                    bpar_q_lvl_mc2;
  // f2s multi-cycle data
  vyixacc_t       [1:0]                    in_data_mc2;           // input data multi-cycle
  ixpix_t         [1:0]                    mpst_rd_data_mc2;      // stash input data multi-cycle
  // s2f multi-cycle handshake signals
  logic           [1:0]                    in_accept_mc2;
  logic                                    out_valid_mc2;
  logic                                    mpst_rd_accept_mc2;
  logic                                    mpst_wr_valid_mc2;
  logic                                    gather_valid_mc2;
  logic                                    bpar_pop_q_mc2;
  // s2f multi-cycle data
  logic                                    out_dbl_mc2;
  tmask_t                                  ctrl_io_en_mc2;
  vyixacc_t                                out_data_mc2;          // output data multi-cycle
  ixpix_t         [1:0]                    mpst_wr_data_mc2;      // stash output data multi-cycle
  offset_t        [VSIZE-1:0]              gather_prod_mc2;       // gather product
  logic           [3:0]                    bpar_pop_q_num_mc2;
 

  //
  // Gate external interfaces, so handshakes happen in second cycle only
  //
  assign iter_ack       = iter_acki      & cycle[1];
  assign hlapi_o_valid  = hlapi_o_validi & cycle[1];


  ////////////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Fast to slow domain crossing
  //
  ////////////////////////////////////////////////////////////////////////////////////////////////////
  for (genvar gi = 0; gi < 2; gi++)
  begin : in_GEN
    npu_gtoa_f2s_hs
      #(
        .W ( $bits(vyixacc_t) )
        )
    u_in_inst
      (
       .clk        ( clk               ),
       .rst_a      ( rst_a             ),
       .cycle1     ( cycle[1]          ),
       .valid      ( in_valid[gi]      ),
       .accept     ( in_accept[gi]     ),
       .data       ( in_data[gi]       ),
       .valid_mc2  ( in_valid_mc2[gi]  ),
       .accept_mc2 ( in_accept_mc2[gi] ),
       .data_mc2   ( in_data_mc2[gi]   )
       );
  end : in_GEN
  npu_gtoa_f2s_hs
    #(
      .W ( 2*$bits(ixpix_t) )
      )
  u_mprd_inst
      (
       .clk        ( clk                ),
       .rst_a      ( rst_a              ),
       .cycle1     ( cycle[1]           ),
       .valid      ( mpst_rd_valid      ),
       .accept     ( mpst_rd_accept     ),
       .data       ( mpst_rd_data       ),
       .valid_mc2  ( mpst_rd_valid_mc2  ),
       .accept_mc2 ( mpst_rd_accept_mc2 ),
       .data_mc2   ( mpst_rd_data_mc2   )
       );


  ////////////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Slow to fast domain paths
  //
  ////////////////////////////////////////////////////////////////////////////////////////////////////
  npu_gtoa_s2f_hs
    #(
      .W ( $bits(vyixacc_t) ),
      .V ( VSIZE            )
      )
  u_out_inst
    (
     .clk        ( clk            ),
     .rst_a      ( rst_a          ),
     .cycle1     ( cycle[1]       ),
     .valid_mc2  ( out_valid_mc2  ),
     .accept_mc2 ( out_accept_mc2 ),
     .data_mc2   ( out_data_mc2   ),
     .valid      ( out_valid      ),
     .accept     ( out_accept     ),
     .data       ( out_data       )
     );
  npu_gtoa_s2f_hs
    #(
      .W ( 2*$bits(ixpix_t) ),
      .V ( 2                )
      )
  u_mpwr_inst
    (
     .clk        ( clk                ),
     .rst_a      ( rst_a              ),
     .cycle1     ( cycle[1]           ),
     .valid_mc2  ( mpst_wr_valid_mc2  ),
     .accept_mc2 ( mpst_wr_accept_mc2 ),
     .data_mc2   ( mpst_wr_data_mc2   ),
     .valid      ( mpst_wr_valid      ),
     .accept     ( mpst_wr_accept     ),
     .data       ( mpst_wr_data       )
     );
  npu_gtoa_s2f_hs
    #(
      .W ( VSIZE*$bits(offset_t) )
      )
  u_gth_inst
    (
     .clk        ( clk               ),
     .rst_a      ( rst_a             ),
     .cycle1     ( cycle[1]          ),
     .valid_mc2  ( gather_valid_mc2  ),
     .accept_mc2 ( gather_accept_mc2 ),
     .data_mc2   ( gather_prod_mc2   ),
     .valid      ( gather_valid      ),
     .accept     ( gather_accept     ),
     .data       ( gather_prod       )
     );
  // pseudo-static signals
  npu_2cyc_checker 
    #( 
       .WIDTH ( 1+$bits(tmask_t) )
       )
  u_stat_mc2s2f_inst
    (
     .clk      ( clk                          ),
     .rst_a    ( rst_a                        ),
     .valid    ( 1'b1                         ),
     .data_in  ( {out_dbl_mc2,ctrl_io_en_mc2} ),
     .data_out ( {out_dbl    ,ctrl_io_en    } )
     );

  // bpar level delay
  always_ff @(posedge clk or
              posedge rst_a)
  begin : bpar_lvl_reg_PROC
    if (rst_a == 1'b1)
    begin
      bpar_q_lvl_r <= '0;
    end
    else if (cycle[1])
    begin
      bpar_q_lvl_r <= bpar_pop_q_i ? '0 : bpar_q_lvl;
    end
  end : bpar_lvl_reg_PROC
  npu_2cyc_checker 
    #( 
       .WIDTH          ( 6 ),
       .DISABLE_OPTION ( 1 )
       )
  u_data_mc2f2s_inst
    (
     .clk      ( clk            ),
     .rst_a    ( rst_a          ),
     .valid    ( 1'b1           ),
     .data_in  ( bpar_q_lvl_r   ),
     .data_out ( bpar_q_lvl_mc2 )
     );
  npu_2cyc_checker 
    #( 
       .WIDTH          ( 5 ),
       .DISABLE_OPTION ( 1 )
       )
  u_data_mc2s2f_inst
    (
     .clk      ( clk                                 ),
     .rst_a    ( rst_a                               ),
     .valid    ( 1'b1                                ),
     .data_in  ( {bpar_pop_q_mc2,bpar_pop_q_num_mc2} ),
     .data_out ( {bpar_pop_q_i,bpar_pop_q_num}       )
     );
  assign bpar_pop_q = bpar_pop_q_i & cycle[1];
  
  
  
  ////////////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Copy slice ID after reset
  //
  ////////////////////////////////////////////////////////////////////////////////////////////////////
  always_ff @(posedge clk_half or
              posedge rst_half)
  begin : slc_id_PROC
    if (rst_half == 1'b1)
    begin
      first_r  <= 1'b1;
      slc_id_r <= '0;
    end
    else if (first_r)
    begin
      first_r  <= 1'b0;
      slc_id_r <= slc_id;
    end
  end : slc_id_PROC

  

  ////////////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Core instance
  //
  ////////////////////////////////////////////////////////////////////////////////////////////////////

  npu_gtoa_core
  u_core_inst
  (
   .clk                ( clk_half            ),
   .rst_a              ( rst_half            ),
   .slc_id             ( slc_id_r            ),
   .iter_req           ( iter_req            ),
   .iter_ack           ( iter_acki           ),
   .iter_shp           ( iter_shp            ),
   .iter_prog          ( iter_prog           ),
   .iter_lay           ( iter_lay            ),
   .hlp_scalin         ( hlp_scalin          ),
   .lut_init           ( lut_init            ),
   .lut_data           ( lut_data            ),
   .hlapi_o_valid      ( hlapi_o_validi      ),
   .hlapi_o_accept     ( hlapi_o_accept      ),
   .hlapi_o_res        ( hlapi_o_res         ),
   .cf_io_en           ( cf_io_en            ),
   .cf_i0dbl           ( cf_i0dbl            ),
   .cf_i0fmode         ( cf_i0fmode          ),
   .cf_i1dbl           ( cf_i1dbl            ),
   .cf_i1fmode         ( cf_i1fmode          ),
   .cf_osat            ( cf_osat             ),
   .cf_odbl            ( cf_odbl             ),
   .cf_ofmode          ( cf_ofmode           ),
   .cf_paden           ( cf_paden            ),
   .cf_padmode         ( cf_padmode          ),
   .cf_padinc          ( cf_padinc           ),
   .cf_padlim          ( cf_padlim           ),
   .cf_padpos          ( cf_padpos           ),
   .cf_padoffs         ( cf_padoffs          ),
   .cf_paditer         ( cf_paditer          ),
   .cf_padstride       ( cf_padstride        ),
   .cf_prim_base       ( cf_prim_base        ),
   .cf_prim_offsets    ( cf_prim_offsets     ),
   .pool_par           ( pool_par            ),
   .ctrl_io_en         ( ctrl_io_en_mc2      ),
   .out_dbl            ( out_dbl_mc2         ),
   .bpar_q_lvl         ( bpar_q_lvl_mc2      ),
   .bpar_pop_q         ( bpar_pop_q_mc2      ),
   .bpar_pop_q_num     ( bpar_pop_q_num_mc2  ),
   .bpar_nxt           ( bpar_nxt            ),
   .gather_valid       ( gather_valid_mc2    ),
   .gather_accept      ( gather_accept_mc2   ),
   .gather_prod        ( gather_prod_mc2     ),
   .mpst_rd_valid      ( mpst_rd_valid_mc2   ),
   .mpst_rd_accept     ( mpst_rd_accept_mc2  ),
   .mpst_rd_data       ( mpst_rd_data_mc2    ),
   .mpst_wr_valid      ( mpst_wr_valid_mc2   ),
   .mpst_wr_accept     ( mpst_wr_accept_mc2  ),
   .mpst_wr_data       ( mpst_wr_data_mc2    ),
   .in_valid           ( in_valid_mc2        ),
   .in_accept          ( in_accept_mc2       ),
   .in_data            ( in_data_mc2         ),
   .out_valid          ( out_valid_mc2       ),
   .out_accept         ( out_accept_mc2      ),
   .out_data           ( out_data_mc2        )
   );
  
endmodule : npu_gtoa_core_wrap
