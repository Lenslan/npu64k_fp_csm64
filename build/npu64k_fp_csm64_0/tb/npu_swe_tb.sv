/*
 * Copyright (C) 2021-2022 Synopsys, Inc. All rights reserved.
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
`include "tb_defines.sv"


module npu_swe_tb();
   // trace SWE
  logic            rtt_swe_val;
  logic [40:0]     rtt_swe_data;
  logic [7:0]      rtt_swe_ext;
  logic [7:0]      ref_swe_ext;

  logic [`NPU_NUM_STU_PER_GRP + `NPU_NUM_SLC_PER_GRP-1:0]        trace_valid;
  logic [`NPU_NUM_STU_PER_GRP + `NPU_NUM_SLC_PER_GRP-1:0]        trace_valid_sync;
  logic [`NPU_NUM_STU_PER_GRP + `NPU_NUM_SLC_PER_GRP-1:0]        trace_accept;
  logic [`NPU_NUM_STU_PER_GRP + `NPU_NUM_SLC_PER_GRP-1:0][39:0]  trace_id;
  logic [`NPU_NUM_STU_PER_GRP + `NPU_NUM_SLC_PER_GRP-1:0][39:0]  trace_id_sync;
  logic [`NPU_NUM_STU_PER_GRP + `NPU_NUM_SLC_PER_GRP-1:0]        o_trace_valid;
  logic [`NPU_NUM_STU_PER_GRP + `NPU_NUM_SLC_PER_GRP-1:0][39:0]  o_trace_id;
  logic [`NPU_NUM_STU_PER_GRP + `NPU_NUM_SLC_PER_GRP-1:0]        swe_gen_en;
  logic                                                          host_sys_cfg_done;

  logic            sl0_rtt_swe_val;
  logic [32:0]     sl0_rtt_swe_data;
  logic [7:0]      sl0_rtt_swe_ext;
  logic [7:0]      sl0_ref_swe_ext;

  //temporary tie-off
  assign sl0_ref_swe_ext = {`NPU_TOP.clusternum[2:0],`NPU_SL0.arcnum[4:0]};

  logic [5-1:0]        sl0_trace_valid;
  logic [5-1:0]        sl0_trace_accept;
  logic [5-1:0][31:0]  sl0_trace_id;
  logic [5-1:0]        sl0_o_trace_valid;
  logic [5-1:0][31:0]  sl0_o_trace_id;
  logic [5-1:0]        sl0_swe_gen_en;
  logic            sl1_rtt_swe_val;
  logic [32:0]     sl1_rtt_swe_data;
  logic [7:0]      sl1_rtt_swe_ext;
  logic [7:0]      sl1_ref_swe_ext;

  //temporary tie-off
  assign sl1_ref_swe_ext = {`NPU_TOP.clusternum[2:0],`NPU_SL1.arcnum[4:0]};

  logic [5-1:0]        sl1_trace_valid;
  logic [5-1:0]        sl1_trace_accept;
  logic [5-1:0][31:0]  sl1_trace_id;
  logic [5-1:0]        sl1_o_trace_valid;
  logic [5-1:0][31:0]  sl1_o_trace_id;
  logic [5-1:0]        sl1_swe_gen_en;
  logic            sl2_rtt_swe_val;
  logic [32:0]     sl2_rtt_swe_data;
  logic [7:0]      sl2_rtt_swe_ext;
  logic [7:0]      sl2_ref_swe_ext;

  //temporary tie-off
  assign sl2_ref_swe_ext = {`NPU_TOP.clusternum[2:0],`NPU_SL2.arcnum[4:0]};

  logic [5-1:0]        sl2_trace_valid;
  logic [5-1:0]        sl2_trace_accept;
  logic [5-1:0][31:0]  sl2_trace_id;
  logic [5-1:0]        sl2_o_trace_valid;
  logic [5-1:0][31:0]  sl2_o_trace_id;
  logic [5-1:0]        sl2_swe_gen_en;
  logic            sl3_rtt_swe_val;
  logic [32:0]     sl3_rtt_swe_data;
  logic [7:0]      sl3_rtt_swe_ext;
  logic [7:0]      sl3_ref_swe_ext;

  //temporary tie-off
  assign sl3_ref_swe_ext = {`NPU_TOP.clusternum[2:0],`NPU_SL3.arcnum[4:0]};

  logic [5-1:0]        sl3_trace_valid;
  logic [5-1:0]        sl3_trace_accept;
  logic [5-1:0][31:0]  sl3_trace_id;
  logic [5-1:0]        sl3_o_trace_valid;
  logic [5-1:0][31:0]  sl3_o_trace_id;
  logic [5-1:0]        sl3_swe_gen_en;

  always @* begin
    if(sl0_swe_gen_en[0]) force `NPU_SL0.u_npu_idma.trace_valid = sl0_o_trace_valid[0];
    if(sl0_swe_gen_en[0]) force `NPU_SL0.u_npu_idma.trace_id    = sl0_o_trace_id[0];
    if(sl0_swe_gen_en[1]) force `NPU_SL0.u_npu_odma.trace_valid = sl0_o_trace_valid[1];
    if(sl0_swe_gen_en[1]) force `NPU_SL0.u_npu_odma.trace_id    = sl0_o_trace_id[1];
    if(sl0_swe_gen_en[2]) force `NPU_SL0.u_npu_conv.trace_valid = sl0_o_trace_valid[2];
    if(sl0_swe_gen_en[2]) force `NPU_SL0.u_npu_conv.trace_id    = sl0_o_trace_id[2];
    if(sl0_swe_gen_en[3]) force `NPU_SL0.u_npu_gtoa.trace_valid = sl0_o_trace_valid[3];
    if(sl0_swe_gen_en[3]) force `NPU_SL0.u_npu_gtoa.trace_id    = sl0_o_trace_id[3];
    if(sl0_swe_gen_en[4]) force `NPU_SL0.u_l1_swe_skid.out_valid = sl0_o_trace_valid[4];
    if(sl0_swe_gen_en[4]) force `NPU_SL0.u_l1_swe_skid.out_data = {sl0_o_trace_id[4]};
  end
  always @* begin
    if(sl1_swe_gen_en[0]) force `NPU_SL1.u_npu_idma.trace_valid = sl1_o_trace_valid[0];
    if(sl1_swe_gen_en[0]) force `NPU_SL1.u_npu_idma.trace_id    = sl1_o_trace_id[0];
    if(sl1_swe_gen_en[1]) force `NPU_SL1.u_npu_odma.trace_valid = sl1_o_trace_valid[1];
    if(sl1_swe_gen_en[1]) force `NPU_SL1.u_npu_odma.trace_id    = sl1_o_trace_id[1];
    if(sl1_swe_gen_en[2]) force `NPU_SL1.u_npu_conv.trace_valid = sl1_o_trace_valid[2];
    if(sl1_swe_gen_en[2]) force `NPU_SL1.u_npu_conv.trace_id    = sl1_o_trace_id[2];
    if(sl1_swe_gen_en[3]) force `NPU_SL1.u_npu_gtoa.trace_valid = sl1_o_trace_valid[3];
    if(sl1_swe_gen_en[3]) force `NPU_SL1.u_npu_gtoa.trace_id    = sl1_o_trace_id[3];
    if(sl1_swe_gen_en[4]) force `NPU_SL1.u_l1_swe_skid.out_valid = sl1_o_trace_valid[4];
    if(sl1_swe_gen_en[4]) force `NPU_SL1.u_l1_swe_skid.out_data = {sl1_o_trace_id[4]};
  end
  always @* begin
    if(sl2_swe_gen_en[0]) force `NPU_SL2.u_npu_idma.trace_valid = sl2_o_trace_valid[0];
    if(sl2_swe_gen_en[0]) force `NPU_SL2.u_npu_idma.trace_id    = sl2_o_trace_id[0];
    if(sl2_swe_gen_en[1]) force `NPU_SL2.u_npu_odma.trace_valid = sl2_o_trace_valid[1];
    if(sl2_swe_gen_en[1]) force `NPU_SL2.u_npu_odma.trace_id    = sl2_o_trace_id[1];
    if(sl2_swe_gen_en[2]) force `NPU_SL2.u_npu_conv.trace_valid = sl2_o_trace_valid[2];
    if(sl2_swe_gen_en[2]) force `NPU_SL2.u_npu_conv.trace_id    = sl2_o_trace_id[2];
    if(sl2_swe_gen_en[3]) force `NPU_SL2.u_npu_gtoa.trace_valid = sl2_o_trace_valid[3];
    if(sl2_swe_gen_en[3]) force `NPU_SL2.u_npu_gtoa.trace_id    = sl2_o_trace_id[3];
    if(sl2_swe_gen_en[4]) force `NPU_SL2.u_l1_swe_skid.out_valid = sl2_o_trace_valid[4];
    if(sl2_swe_gen_en[4]) force `NPU_SL2.u_l1_swe_skid.out_data = {sl2_o_trace_id[4]};
  end
  always @* begin
    if(sl3_swe_gen_en[0]) force `NPU_SL3.u_npu_idma.trace_valid = sl3_o_trace_valid[0];
    if(sl3_swe_gen_en[0]) force `NPU_SL3.u_npu_idma.trace_id    = sl3_o_trace_id[0];
    if(sl3_swe_gen_en[1]) force `NPU_SL3.u_npu_odma.trace_valid = sl3_o_trace_valid[1];
    if(sl3_swe_gen_en[1]) force `NPU_SL3.u_npu_odma.trace_id    = sl3_o_trace_id[1];
    if(sl3_swe_gen_en[2]) force `NPU_SL3.u_npu_conv.trace_valid = sl3_o_trace_valid[2];
    if(sl3_swe_gen_en[2]) force `NPU_SL3.u_npu_conv.trace_id    = sl3_o_trace_id[2];
    if(sl3_swe_gen_en[3]) force `NPU_SL3.u_npu_gtoa.trace_valid = sl3_o_trace_valid[3];
    if(sl3_swe_gen_en[3]) force `NPU_SL3.u_npu_gtoa.trace_id    = sl3_o_trace_id[3];
    if(sl3_swe_gen_en[4]) force `NPU_SL3.u_l1_swe_skid.out_valid = sl3_o_trace_valid[4];
    if(sl3_swe_gen_en[4]) force `NPU_SL3.u_l1_swe_skid.out_data = {sl3_o_trace_id[4]};
  end

  assign sl0_trace_valid[0]  =  `NPU_SL0.u_npu_idma.trace_valid ;
  assign sl0_trace_id[0]     =  `NPU_SL0.u_npu_idma.trace_id ;
  assign sl0_trace_accept[0] = `NPU_SL0.u_npu_idma.trace_accept;
  assign sl0_trace_valid[1]  =  `NPU_SL0.u_npu_odma.trace_valid ;
  assign sl0_trace_id[1]     =  `NPU_SL0.u_npu_odma.trace_id ;
  assign sl0_trace_accept[1] = `NPU_SL0.u_npu_odma.trace_accept;
  assign sl0_trace_valid[2]  =  `NPU_SL0.u_npu_conv.trace_valid ;
  assign sl0_trace_id[2]     =  `NPU_SL0.u_npu_conv.trace_id ;
  assign sl0_trace_accept[2] = `NPU_SL0.u_npu_conv.trace_accept;
  assign sl0_trace_valid[3]  =  `NPU_SL0.u_npu_gtoa.trace_valid ;
  assign sl0_trace_id[3]     =  `NPU_SL0.u_npu_gtoa.trace_id ;
  assign sl0_trace_accept[3] = `NPU_SL0.u_npu_gtoa.trace_accept;
  assign sl0_trace_valid[4]  =  `NPU_SL0.u_l1_swe_skid.out_valid;
  assign sl0_trace_id[4]     =  `NPU_SL0.u_l1_swe_skid.out_data;
  assign sl0_trace_accept[4] = `NPU_SL0.trace_accept[4];

  assign sl0_rtt_swe_ext     = `NPU_SL0.rtt_swe_ext;
  assign sl0_rtt_swe_val     = `NPU_SL0.rtt_swe_val;
  assign sl0_rtt_swe_data    = `NPU_SL0.rtt_swe_data;
  assign sl1_trace_valid[0]  =  `NPU_SL1.u_npu_idma.trace_valid ;
  assign sl1_trace_id[0]     =  `NPU_SL1.u_npu_idma.trace_id ;
  assign sl1_trace_accept[0] = `NPU_SL1.u_npu_idma.trace_accept;
  assign sl1_trace_valid[1]  =  `NPU_SL1.u_npu_odma.trace_valid ;
  assign sl1_trace_id[1]     =  `NPU_SL1.u_npu_odma.trace_id ;
  assign sl1_trace_accept[1] = `NPU_SL1.u_npu_odma.trace_accept;
  assign sl1_trace_valid[2]  =  `NPU_SL1.u_npu_conv.trace_valid ;
  assign sl1_trace_id[2]     =  `NPU_SL1.u_npu_conv.trace_id ;
  assign sl1_trace_accept[2] = `NPU_SL1.u_npu_conv.trace_accept;
  assign sl1_trace_valid[3]  =  `NPU_SL1.u_npu_gtoa.trace_valid ;
  assign sl1_trace_id[3]     =  `NPU_SL1.u_npu_gtoa.trace_id ;
  assign sl1_trace_accept[3] = `NPU_SL1.u_npu_gtoa.trace_accept;
  assign sl1_trace_valid[4]  =  `NPU_SL1.u_l1_swe_skid.out_valid;
  assign sl1_trace_id[4]     =  `NPU_SL1.u_l1_swe_skid.out_data;
  assign sl1_trace_accept[4] = `NPU_SL1.trace_accept[4];

  assign sl1_rtt_swe_ext     = `NPU_SL1.rtt_swe_ext;
  assign sl1_rtt_swe_val     = `NPU_SL1.rtt_swe_val;
  assign sl1_rtt_swe_data    = `NPU_SL1.rtt_swe_data;
  assign sl2_trace_valid[0]  =  `NPU_SL2.u_npu_idma.trace_valid ;
  assign sl2_trace_id[0]     =  `NPU_SL2.u_npu_idma.trace_id ;
  assign sl2_trace_accept[0] = `NPU_SL2.u_npu_idma.trace_accept;
  assign sl2_trace_valid[1]  =  `NPU_SL2.u_npu_odma.trace_valid ;
  assign sl2_trace_id[1]     =  `NPU_SL2.u_npu_odma.trace_id ;
  assign sl2_trace_accept[1] = `NPU_SL2.u_npu_odma.trace_accept;
  assign sl2_trace_valid[2]  =  `NPU_SL2.u_npu_conv.trace_valid ;
  assign sl2_trace_id[2]     =  `NPU_SL2.u_npu_conv.trace_id ;
  assign sl2_trace_accept[2] = `NPU_SL2.u_npu_conv.trace_accept;
  assign sl2_trace_valid[3]  =  `NPU_SL2.u_npu_gtoa.trace_valid ;
  assign sl2_trace_id[3]     =  `NPU_SL2.u_npu_gtoa.trace_id ;
  assign sl2_trace_accept[3] = `NPU_SL2.u_npu_gtoa.trace_accept;
  assign sl2_trace_valid[4]  =  `NPU_SL2.u_l1_swe_skid.out_valid;
  assign sl2_trace_id[4]     =  `NPU_SL2.u_l1_swe_skid.out_data;
  assign sl2_trace_accept[4] = `NPU_SL2.trace_accept[4];

  assign sl2_rtt_swe_ext     = `NPU_SL2.rtt_swe_ext;
  assign sl2_rtt_swe_val     = `NPU_SL2.rtt_swe_val;
  assign sl2_rtt_swe_data    = `NPU_SL2.rtt_swe_data;
  assign sl3_trace_valid[0]  =  `NPU_SL3.u_npu_idma.trace_valid ;
  assign sl3_trace_id[0]     =  `NPU_SL3.u_npu_idma.trace_id ;
  assign sl3_trace_accept[0] = `NPU_SL3.u_npu_idma.trace_accept;
  assign sl3_trace_valid[1]  =  `NPU_SL3.u_npu_odma.trace_valid ;
  assign sl3_trace_id[1]     =  `NPU_SL3.u_npu_odma.trace_id ;
  assign sl3_trace_accept[1] = `NPU_SL3.u_npu_odma.trace_accept;
  assign sl3_trace_valid[2]  =  `NPU_SL3.u_npu_conv.trace_valid ;
  assign sl3_trace_id[2]     =  `NPU_SL3.u_npu_conv.trace_id ;
  assign sl3_trace_accept[2] = `NPU_SL3.u_npu_conv.trace_accept;
  assign sl3_trace_valid[3]  =  `NPU_SL3.u_npu_gtoa.trace_valid ;
  assign sl3_trace_id[3]     =  `NPU_SL3.u_npu_gtoa.trace_id ;
  assign sl3_trace_accept[3] = `NPU_SL3.u_npu_gtoa.trace_accept;
  assign sl3_trace_valid[4]  =  `NPU_SL3.u_l1_swe_skid.out_valid;
  assign sl3_trace_id[4]     =  `NPU_SL3.u_l1_swe_skid.out_data;
  assign sl3_trace_accept[4] = `NPU_SL3.trace_accept[4];

  assign sl3_rtt_swe_ext     = `NPU_SL3.rtt_swe_ext;
  assign sl3_rtt_swe_val     = `NPU_SL3.rtt_swe_val;
  assign sl3_rtt_swe_data    = `NPU_SL3.rtt_swe_data;


  // TB output
  always @* begin
    if(swe_gen_en[`NPU_NUM_SLC_PER_GRP + 0]) force `NPU_GRP0.stu_trace_valid[0] = o_trace_valid[`NPU_NUM_SLC_PER_GRP + 0];
    if(swe_gen_en[`NPU_NUM_SLC_PER_GRP + 0]) force `NPU_GRP0.i_rtt_swe_data_comb[`NPU_NUM_SLC_PER_GRP + 0] = {8'h00,o_trace_id[`NPU_NUM_SLC_PER_GRP + 0][31],1'b0,o_trace_id[`NPU_NUM_SLC_PER_GRP + 0][30:0]};
    if(swe_gen_en[`NPU_NUM_SLC_PER_GRP + 1]) force `NPU_GRP0.stu_trace_valid[1] = o_trace_valid[`NPU_NUM_SLC_PER_GRP + 1];
    if(swe_gen_en[`NPU_NUM_SLC_PER_GRP + 1]) force `NPU_GRP0.i_rtt_swe_data_comb[`NPU_NUM_SLC_PER_GRP + 1] = {8'h00,o_trace_id[`NPU_NUM_SLC_PER_GRP + 1][31],1'b0,o_trace_id[`NPU_NUM_SLC_PER_GRP + 1][30:0]};
  end

  // RTL output
  assign rtt_swe_ext = `NPU_GRP0.rtt_swe_ext;
  assign rtt_swe_val = `NPU_GRP0.rtt_swe_val;
  assign rtt_swe_data = `NPU_GRP0.trace_arb_out_data;
  //temporary tie-off cause ext is combined with data to check in group
  assign ref_swe_ext = `NPU_GRP0.rtt_swe_ext;

  // TB input
  assign trace_valid[0]      = `NPU_SL0.rtt_swe_val;
  assign trace_id[0]         =  {`NPU_GRP0.i_rtt_swe_data_comb_mc2[0][40:32],`NPU_GRP0.i_rtt_swe_data_comb_mc2[0][30:0]} ;
  assign trace_valid[1]      = `NPU_SL1.rtt_swe_val;
  assign trace_id[1]         =  {`NPU_GRP0.i_rtt_swe_data_comb_mc2[1][40:32],`NPU_GRP0.i_rtt_swe_data_comb_mc2[1][30:0]} ;
  assign trace_valid[2]      = `NPU_SL2.rtt_swe_val;
  assign trace_id[2]         =  {`NPU_GRP0.i_rtt_swe_data_comb_mc2[2][40:32],`NPU_GRP0.i_rtt_swe_data_comb_mc2[2][30:0]} ;
  assign trace_valid[3]      = `NPU_SL3.rtt_swe_val;
  assign trace_id[3]         =  {`NPU_GRP0.i_rtt_swe_data_comb_mc2[3][40:32],`NPU_GRP0.i_rtt_swe_data_comb_mc2[3][30:0]} ;

  assign trace_valid[`NPU_NUM_SLC_PER_GRP+0] = `NPU_GRP0.stu_trace_valid[0] ;
  assign trace_id[`NPU_NUM_SLC_PER_GRP+0] =  {`NPU_GRP0.i_rtt_swe_data_comb_mc2[`NPU_NUM_SLC_PER_GRP+0][40:32],`NPU_GRP0.i_rtt_swe_data_comb_mc2[`NPU_NUM_SLC_PER_GRP+0][30:0]} ;
  assign trace_valid[`NPU_NUM_SLC_PER_GRP+1] = `NPU_GRP0.stu_trace_valid[1] ;
  assign trace_id[`NPU_NUM_SLC_PER_GRP+1] =  {`NPU_GRP0.i_rtt_swe_data_comb_mc2[`NPU_NUM_SLC_PER_GRP+1][40:32],`NPU_GRP0.i_rtt_swe_data_comb_mc2[`NPU_NUM_SLC_PER_GRP+1][30:0]} ;
  assign trace_id_sync[0] =  {`NPU_GRP0.trace_skid_data[0][40:32],`NPU_GRP0.trace_skid_data[0][30:0]};
  assign trace_valid_sync[0] = `NPU_GRP0.trace_skid_validi[0];
  assign trace_accept[0] = 1;
  assign trace_id_sync[1] =  {`NPU_GRP0.trace_skid_data[1][40:32],`NPU_GRP0.trace_skid_data[1][30:0]};
  assign trace_valid_sync[1] = `NPU_GRP0.trace_skid_validi[1];
  assign trace_accept[1] = 1;
  assign trace_id_sync[2] =  {`NPU_GRP0.trace_skid_data[2][40:32],`NPU_GRP0.trace_skid_data[2][30:0]};
  assign trace_valid_sync[2] = `NPU_GRP0.trace_skid_validi[2];
  assign trace_accept[2] = 1;
  assign trace_id_sync[3] =  {`NPU_GRP0.trace_skid_data[3][40:32],`NPU_GRP0.trace_skid_data[3][30:0]};
  assign trace_valid_sync[3] = `NPU_GRP0.trace_skid_validi[3];
  assign trace_accept[3] = 1;
  assign trace_id_sync[4] =  {`NPU_GRP0.trace_skid_data[4][40:32],`NPU_GRP0.trace_skid_data[4][30:0]};
  assign trace_valid_sync[4] = `NPU_GRP0.trace_skid_validi[4];
  assign trace_accept[4] = 1;
  assign trace_id_sync[5] =  {`NPU_GRP0.trace_skid_data[5][40:32],`NPU_GRP0.trace_skid_data[5][30:0]};
  assign trace_valid_sync[5] = `NPU_GRP0.trace_skid_validi[5];
  assign trace_accept[5] = 1;
  

  swe_arb_tb 
  #( 
    .NUM_TRACE_SRC(`NPU_NUM_STU_PER_GRP + `NPU_NUM_SLC_PER_GRP)
   ,.DW(40)
   ,.TB_GEN_TRACE_FLAG("TB_GEN_GRP_SWE")
  ) u_grp_swe_arb_tb (
   .clk  (`NPU_GRP0.grp_clk_gated),
   .rst_a(`NPU_GRP0.grp_rst_a),
   .trace_accept (`NPU_GRP0.u_grp_trace_arb.in_accept),
   .trace_cdc_valid (`NPU_GRP0.trace_valid_rise),
   .*
  );

generate
    genvar j;
    // checkers
    // slice swe output is unsyncronized with grp_clk_gated, use signal after sync
    // stu swe output is already sync with grp_clk_gated, directly check
      // check cycles of valid
      property trace_slc0_vld_grp_prop;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL0.rst_a !==0) $rose(trace_valid_sync[0]) |-> ##[1:4] !($fell(trace_valid_sync[0]));
      endproperty
      // check trace id
      property trace_slc0_data_grp_prop4;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL0.rst_a !==0) $rose(trace_valid_sync[0]) |-> ##4 (trace_id_sync[0] == $past(trace_id_sync[0], 4));
      endproperty
      property trace_slc0_data_grp_prop3;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL0.rst_a !==0) $rose(trace_valid_sync[0]) |-> ##3 (trace_id_sync[0] == $past(trace_id_sync[0], 3));
      endproperty
      property trace_slc0_data_grp_prop2;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL0.rst_a !==0) $rose(trace_valid_sync[0]) |-> ##2 (trace_id_sync[0] == $past(trace_id_sync[0], 2));
      endproperty
      property trace_slc0_data_grp_prop1;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL0.rst_a !==0) $rose(trace_valid_sync[0]) |-> ##1 (trace_id_sync[0] == $past(trace_id_sync[0], 1));
      endproperty

      ast_trc_slc0_vld_grp: assert property(trace_slc0_vld_grp_prop) else $error("trace_valid should keep 5 cycles");
      //ast_trc_acp: assert property(trace_acp_grp_prop) else $error("trace_accept should be asserted before trace_valid drop");
      ast_trc_slc0_dat_grp_cycle4: assert property(trace_slc0_data_grp_prop4) else $error("trace_id should keep 5 cycles when trace_valid is asserted");
      ast_trc_slc0_dat_grp_cycle3: assert property(trace_slc0_data_grp_prop3) else $error("trace_id should keep 5 cycles when trace_valid is asserted");
      ast_trc_slc0_dat_grp_cycle2: assert property(trace_slc0_data_grp_prop2) else $error("trace_id should keep 5 cycles when trace_valid is asserted");
      ast_trc_slc0_dat_grp_cycle1: assert property(trace_slc0_data_grp_prop1) else $error("trace_id should keep 5 cycles when trace_valid is asserted");
      // check cycles of valid
      property trace_slc1_vld_grp_prop;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL1.rst_a !==0) $rose(trace_valid_sync[1]) |-> ##[1:4] !($fell(trace_valid_sync[1]));
      endproperty
      // check trace id
      property trace_slc1_data_grp_prop4;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL1.rst_a !==0) $rose(trace_valid_sync[1]) |-> ##4 (trace_id_sync[1] == $past(trace_id_sync[1], 4));
      endproperty
      property trace_slc1_data_grp_prop3;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL1.rst_a !==0) $rose(trace_valid_sync[1]) |-> ##3 (trace_id_sync[1] == $past(trace_id_sync[1], 3));
      endproperty
      property trace_slc1_data_grp_prop2;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL1.rst_a !==0) $rose(trace_valid_sync[1]) |-> ##2 (trace_id_sync[1] == $past(trace_id_sync[1], 2));
      endproperty
      property trace_slc1_data_grp_prop1;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL1.rst_a !==0) $rose(trace_valid_sync[1]) |-> ##1 (trace_id_sync[1] == $past(trace_id_sync[1], 1));
      endproperty

      ast_trc_slc1_vld_grp: assert property(trace_slc1_vld_grp_prop) else $error("trace_valid should keep 5 cycles");
      //ast_trc_acp: assert property(trace_acp_grp_prop) else $error("trace_accept should be asserted before trace_valid drop");
      ast_trc_slc1_dat_grp_cycle4: assert property(trace_slc1_data_grp_prop4) else $error("trace_id should keep 5 cycles when trace_valid is asserted");
      ast_trc_slc1_dat_grp_cycle3: assert property(trace_slc1_data_grp_prop3) else $error("trace_id should keep 5 cycles when trace_valid is asserted");
      ast_trc_slc1_dat_grp_cycle2: assert property(trace_slc1_data_grp_prop2) else $error("trace_id should keep 5 cycles when trace_valid is asserted");
      ast_trc_slc1_dat_grp_cycle1: assert property(trace_slc1_data_grp_prop1) else $error("trace_id should keep 5 cycles when trace_valid is asserted");
      // check cycles of valid
      property trace_slc2_vld_grp_prop;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL2.rst_a !==0) $rose(trace_valid_sync[2]) |-> ##[1:4] !($fell(trace_valid_sync[2]));
      endproperty
      // check trace id
      property trace_slc2_data_grp_prop4;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL2.rst_a !==0) $rose(trace_valid_sync[2]) |-> ##4 (trace_id_sync[2] == $past(trace_id_sync[2], 4));
      endproperty
      property trace_slc2_data_grp_prop3;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL2.rst_a !==0) $rose(trace_valid_sync[2]) |-> ##3 (trace_id_sync[2] == $past(trace_id_sync[2], 3));
      endproperty
      property trace_slc2_data_grp_prop2;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL2.rst_a !==0) $rose(trace_valid_sync[2]) |-> ##2 (trace_id_sync[2] == $past(trace_id_sync[2], 2));
      endproperty
      property trace_slc2_data_grp_prop1;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL2.rst_a !==0) $rose(trace_valid_sync[2]) |-> ##1 (trace_id_sync[2] == $past(trace_id_sync[2], 1));
      endproperty

      ast_trc_slc2_vld_grp: assert property(trace_slc2_vld_grp_prop) else $error("trace_valid should keep 5 cycles");
      //ast_trc_acp: assert property(trace_acp_grp_prop) else $error("trace_accept should be asserted before trace_valid drop");
      ast_trc_slc2_dat_grp_cycle4: assert property(trace_slc2_data_grp_prop4) else $error("trace_id should keep 5 cycles when trace_valid is asserted");
      ast_trc_slc2_dat_grp_cycle3: assert property(trace_slc2_data_grp_prop3) else $error("trace_id should keep 5 cycles when trace_valid is asserted");
      ast_trc_slc2_dat_grp_cycle2: assert property(trace_slc2_data_grp_prop2) else $error("trace_id should keep 5 cycles when trace_valid is asserted");
      ast_trc_slc2_dat_grp_cycle1: assert property(trace_slc2_data_grp_prop1) else $error("trace_id should keep 5 cycles when trace_valid is asserted");
      // check cycles of valid
      property trace_slc3_vld_grp_prop;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL3.rst_a !==0) $rose(trace_valid_sync[3]) |-> ##[1:4] !($fell(trace_valid_sync[3]));
      endproperty
      // check trace id
      property trace_slc3_data_grp_prop4;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL3.rst_a !==0) $rose(trace_valid_sync[3]) |-> ##4 (trace_id_sync[3] == $past(trace_id_sync[3], 4));
      endproperty
      property trace_slc3_data_grp_prop3;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL3.rst_a !==0) $rose(trace_valid_sync[3]) |-> ##3 (trace_id_sync[3] == $past(trace_id_sync[3], 3));
      endproperty
      property trace_slc3_data_grp_prop2;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL3.rst_a !==0) $rose(trace_valid_sync[3]) |-> ##2 (trace_id_sync[3] == $past(trace_id_sync[3], 2));
      endproperty
      property trace_slc3_data_grp_prop1;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0 || `NPU_SL3.rst_a !==0) $rose(trace_valid_sync[3]) |-> ##1 (trace_id_sync[3] == $past(trace_id_sync[3], 1));
      endproperty

      ast_trc_slc3_vld_grp: assert property(trace_slc3_vld_grp_prop) else $error("trace_valid should keep 5 cycles");
      //ast_trc_acp: assert property(trace_acp_grp_prop) else $error("trace_accept should be asserted before trace_valid drop");
      ast_trc_slc3_dat_grp_cycle4: assert property(trace_slc3_data_grp_prop4) else $error("trace_id should keep 5 cycles when trace_valid is asserted");
      ast_trc_slc3_dat_grp_cycle3: assert property(trace_slc3_data_grp_prop3) else $error("trace_id should keep 5 cycles when trace_valid is asserted");
      ast_trc_slc3_dat_grp_cycle2: assert property(trace_slc3_data_grp_prop2) else $error("trace_id should keep 5 cycles when trace_valid is asserted");
      ast_trc_slc3_dat_grp_cycle1: assert property(trace_slc3_data_grp_prop1) else $error("trace_id should keep 5 cycles when trace_valid is asserted");

    for(j=`NPU_NUM_SLC_PER_GRP;j<(`NPU_NUM_STU_PER_GRP + `NPU_NUM_SLC_PER_GRP);j++)begin: grp_stu_assert_GEN
      // check cycles of valid
      property trace_stu_vld_grp_prop;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0) $rose(trace_valid_sync[j]) |-> ##[1:4] !($fell(trace_valid_sync[j]));
      endproperty
      // check trace id
      property trace_stu_data_grp_prop4;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0) $rose(trace_valid_sync[j]) |-> ##4 (trace_id_sync[j] == $past(trace_id_sync[j], 4));
      endproperty
      property trace_stu_data_grp_prop3;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0) $rose(trace_valid_sync[j]) |-> ##3 (trace_id_sync[j] == $past(trace_id_sync[j], 3));
      endproperty
      property trace_stu_data_grp_prop2;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0) $rose(trace_valid_sync[j]) |-> ##2 (trace_id_sync[j] == $past(trace_id_sync[j], 2));
      endproperty
      property trace_stu_data_grp_prop1;
         @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0) $rose(trace_valid_sync[j]) |-> ##1 (trace_id_sync[j] == $past(trace_id_sync[j], 1));
      endproperty

      ast_trc_stu_vld_grp: assert property(trace_stu_vld_grp_prop) else $error("trace_valid should keep 5 cycles");
      //ast_trc_acp: assert property(trace_acp_grp_prop) else $error("trace_accept should be asserted before trace_valid drop");
      ast_trc_stu_dat_grp_cycle4: assert property(trace_stu_data_grp_prop4) else $error("trace_id should keep 5 cycles when trace_valid is asserted");
      ast_trc_stu_dat_grp_cycle3: assert property(trace_stu_data_grp_prop3) else $error("trace_id should keep 5 cycles when trace_valid is asserted");
      ast_trc_stu_dat_grp_cycle2: assert property(trace_stu_data_grp_prop2) else $error("trace_id should keep 5 cycles when trace_valid is asserted");
      ast_trc_stu_dat_grp_cycle1: assert property(trace_stu_data_grp_prop1) else $error("trace_id should keep 5 cycles when trace_valid is asserted");

    end: grp_stu_assert_GEN
  endgenerate

  property rtt_swe_valid_cycles_grp_prop;
     @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0) $rose(rtt_swe_val) |-> ##5 $fell(rtt_swe_val);
  endproperty
  ast_rtt_valid_grp: assert property(rtt_swe_valid_cycles_grp_prop) else $fatal("rtt_swe_valid is not asserted 5 cycles");

  property rtt_swe_ext_grp_prop;
     @(posedge `NPU_GRP0.grp_clk_gated) disable iff(`NPU_GRP0.grp_rst_a !==0) (1) |-> (rtt_swe_ext == ref_swe_ext);
  endproperty
  ast_rtt_ext_grp: assert property(rtt_swe_ext_grp_prop) else $fatal("rtt_swe_ext is not expected");


  swe_arb_tb 
  #( 
    .NUM_TRACE_SRC(5)
   ,.DW(32)
   ,.TB_GEN_TRACE_FLAG("TB_GEN_GRP_SWE")
  ) u_slc0_swe_arb_tb (
     .clk              (`NPU_SL0.clk)
    ,.rst_a            (`NPU_SL0.rst_a)
    ,.trace_valid      (sl0_trace_valid     ) 
    ,.trace_id         (sl0_trace_id        )
    ,.trace_cdc_valid  (`NPU_SL0.trace_valid_rise)
    ,.trace_accept     (`NPU_SL0.u_slice_trace_arb.in_accept    )
    ,.rtt_swe_val      (sl0_rtt_swe_val     )
    ,.rtt_swe_data     (sl0_rtt_swe_data    )
    ,.rtt_swe_ext      (sl0_rtt_swe_ext     )
    ,.ref_swe_ext      (sl0_ref_swe_ext     )
    ,.o_trace_valid    (sl0_o_trace_valid   )
    ,.o_trace_id       (sl0_o_trace_id      )
    ,.swe_gen_en       (sl0_swe_gen_en      )
    ,.host_sys_cfg_done  ()
  );
  swe_arb_tb 
  #( 
    .NUM_TRACE_SRC(5)
   ,.DW(32)
   ,.TB_GEN_TRACE_FLAG("TB_GEN_GRP_SWE")
  ) u_slc1_swe_arb_tb (
     .clk              (`NPU_SL1.clk)
    ,.rst_a            (`NPU_SL1.rst_a)
    ,.trace_valid      (sl1_trace_valid     ) 
    ,.trace_id         (sl1_trace_id        )
    ,.trace_cdc_valid  (`NPU_SL1.trace_valid_rise)
    ,.trace_accept     (`NPU_SL1.u_slice_trace_arb.in_accept    )
    ,.rtt_swe_val      (sl1_rtt_swe_val     )
    ,.rtt_swe_data     (sl1_rtt_swe_data    )
    ,.rtt_swe_ext      (sl1_rtt_swe_ext     )
    ,.ref_swe_ext      (sl1_ref_swe_ext     )
    ,.o_trace_valid    (sl1_o_trace_valid   )
    ,.o_trace_id       (sl1_o_trace_id      )
    ,.swe_gen_en       (sl1_swe_gen_en      )
    ,.host_sys_cfg_done  ()
  );
  swe_arb_tb 
  #( 
    .NUM_TRACE_SRC(5)
   ,.DW(32)
   ,.TB_GEN_TRACE_FLAG("TB_GEN_GRP_SWE")
  ) u_slc2_swe_arb_tb (
     .clk              (`NPU_SL2.clk)
    ,.rst_a            (`NPU_SL2.rst_a)
    ,.trace_valid      (sl2_trace_valid     ) 
    ,.trace_id         (sl2_trace_id        )
    ,.trace_cdc_valid  (`NPU_SL2.trace_valid_rise)
    ,.trace_accept     (`NPU_SL2.u_slice_trace_arb.in_accept    )
    ,.rtt_swe_val      (sl2_rtt_swe_val     )
    ,.rtt_swe_data     (sl2_rtt_swe_data    )
    ,.rtt_swe_ext      (sl2_rtt_swe_ext     )
    ,.ref_swe_ext      (sl2_ref_swe_ext     )
    ,.o_trace_valid    (sl2_o_trace_valid   )
    ,.o_trace_id       (sl2_o_trace_id      )
    ,.swe_gen_en       (sl2_swe_gen_en      )
    ,.host_sys_cfg_done  ()
  );
  swe_arb_tb 
  #( 
    .NUM_TRACE_SRC(5)
   ,.DW(32)
   ,.TB_GEN_TRACE_FLAG("TB_GEN_GRP_SWE")
  ) u_slc3_swe_arb_tb (
     .clk              (`NPU_SL3.clk)
    ,.rst_a            (`NPU_SL3.rst_a)
    ,.trace_valid      (sl3_trace_valid     ) 
    ,.trace_id         (sl3_trace_id        )
    ,.trace_cdc_valid  (`NPU_SL3.trace_valid_rise)
    ,.trace_accept     (`NPU_SL3.u_slice_trace_arb.in_accept    )
    ,.rtt_swe_val      (sl3_rtt_swe_val     )
    ,.rtt_swe_data     (sl3_rtt_swe_data    )
    ,.rtt_swe_ext      (sl3_rtt_swe_ext     )
    ,.ref_swe_ext      (sl3_ref_swe_ext     )
    ,.o_trace_valid    (sl3_o_trace_valid   )
    ,.o_trace_id       (sl3_o_trace_id      )
    ,.swe_gen_en       (sl3_swe_gen_en      )
    ,.host_sys_cfg_done  ()
  );

  generate
    genvar i;
    // checkers
    for(i=0;i<5;i++)begin: assert_GEN
      // check cycles of valid
      property trace_vld_slc0_prop;
         @(posedge `NPU_SL0.clk) disable iff(`NPU_SL0.rst_a !==0) $rose(sl0_trace_valid[i]) |-> ##5 $fell(sl0_trace_valid[i]) ;
      endproperty
      // check trace id
      property trace_data_slc0_prop;
         @(posedge `NPU_SL0.clk) disable iff(`NPU_SL0.rst_a !==0) $rose(sl0_trace_valid[i]) |-> ##4 (sl0_trace_id[i] == $past(sl0_trace_id[i], 4));
      endproperty

      ast_trc_vld_slc0: assert property(trace_vld_slc0_prop) else $error("trace_valid should keep 5 cycles");
      //ast_trc_acp: assert property(trace_acp_slc0_prop) else $error("trace_accept should be asserted before trace_valid drop");
      ast_trc_dat_slc0: assert property(trace_data_slc0_prop) else $error("trace_id should keep 5 cycles when trace_valid is asserted");

      property trace_vld_slc1_prop;
         @(posedge `NPU_SL1.clk) disable iff(`NPU_SL1.rst_a !==0) $rose(sl1_trace_valid[i]) |-> ##5 $fell(sl1_trace_valid[i]) ;
      endproperty
      // check trace id
      property trace_data_slc1_prop;
         @(posedge `NPU_SL1.clk) disable iff(`NPU_SL1.rst_a !==0) $rose(sl1_trace_valid[i]) |-> ##4 (sl1_trace_id[i] == $past(sl1_trace_id[i], 4));
      endproperty

      ast_trc_vld_slc1: assert property(trace_vld_slc1_prop) else $error("trace_valid should keep 5 cycles");
      //ast_trc_acp: assert property(trace_acp_slc1_prop) else $error("trace_accept should be asserted before trace_valid drop");
      ast_trc_dat_slc1: assert property(trace_data_slc1_prop) else $error("trace_id should keep 5 cycles when trace_valid is asserted");

      property trace_vld_slc2_prop;
         @(posedge `NPU_SL2.clk) disable iff(`NPU_SL2.rst_a !==0) $rose(sl2_trace_valid[i]) |-> ##5 $fell(sl2_trace_valid[i]) ;
      endproperty
      // check trace id
      property trace_data_slc2_prop;
         @(posedge `NPU_SL2.clk) disable iff(`NPU_SL2.rst_a !==0) $rose(sl2_trace_valid[i]) |-> ##4 (sl2_trace_id[i] == $past(sl2_trace_id[i], 4));
      endproperty

      ast_trc_vld_slc2: assert property(trace_vld_slc2_prop) else $error("trace_valid should keep 5 cycles");
      //ast_trc_acp: assert property(trace_acp_slc2_prop) else $error("trace_accept should be asserted before trace_valid drop");
      ast_trc_dat_slc2: assert property(trace_data_slc2_prop) else $error("trace_id should keep 5 cycles when trace_valid is asserted");

      property trace_vld_slc3_prop;
         @(posedge `NPU_SL3.clk) disable iff(`NPU_SL3.rst_a !==0) $rose(sl3_trace_valid[i]) |-> ##5 $fell(sl3_trace_valid[i]) ;
      endproperty
      // check trace id
      property trace_data_slc3_prop;
         @(posedge `NPU_SL3.clk) disable iff(`NPU_SL3.rst_a !==0) $rose(sl3_trace_valid[i]) |-> ##4 (sl3_trace_id[i] == $past(sl3_trace_id[i], 4));
      endproperty

      ast_trc_vld_slc3: assert property(trace_vld_slc3_prop) else $error("trace_valid should keep 5 cycles");
      //ast_trc_acp: assert property(trace_acp_slc3_prop) else $error("trace_accept should be asserted before trace_valid drop");
      ast_trc_dat_slc3: assert property(trace_data_slc3_prop) else $error("trace_id should keep 5 cycles when trace_valid is asserted");

    end: assert_GEN
  endgenerate

  property rtt_swe_valid_cycles_slc0_prop;
     @(posedge `NPU_SL0.clk) disable iff(`NPU_SL0.rst_a !==0) $rose(sl0_rtt_swe_val) |-> ##5 $fell(sl0_rtt_swe_val);
  endproperty
  ast_rtt_valid_slc0: assert property(rtt_swe_valid_cycles_slc0_prop) else $fatal("rtt_swe_valid is not asserted 5 cycles");

  property rtt_swe_ext_slc0_prop;
     @(posedge `NPU_SL0.clk) disable iff(`NPU_SL0.rst_a !==0) (1) |-> (sl0_rtt_swe_ext == sl0_ref_swe_ext);
  endproperty
  ast_rtt_ext_slc0: assert property(rtt_swe_ext_slc0_prop) else $fatal("rtt_swe_ext is not expected");
  property rtt_swe_valid_cycles_slc1_prop;
     @(posedge `NPU_SL1.clk) disable iff(`NPU_SL1.rst_a !==0) $rose(sl1_rtt_swe_val) |-> ##5 $fell(sl1_rtt_swe_val);
  endproperty
  ast_rtt_valid_slc1: assert property(rtt_swe_valid_cycles_slc1_prop) else $fatal("rtt_swe_valid is not asserted 5 cycles");

  property rtt_swe_ext_slc1_prop;
     @(posedge `NPU_SL1.clk) disable iff(`NPU_SL1.rst_a !==0) (1) |-> (sl1_rtt_swe_ext == sl1_ref_swe_ext);
  endproperty
  ast_rtt_ext_slc1: assert property(rtt_swe_ext_slc1_prop) else $fatal("rtt_swe_ext is not expected");
  property rtt_swe_valid_cycles_slc2_prop;
     @(posedge `NPU_SL2.clk) disable iff(`NPU_SL2.rst_a !==0) $rose(sl2_rtt_swe_val) |-> ##5 $fell(sl2_rtt_swe_val);
  endproperty
  ast_rtt_valid_slc2: assert property(rtt_swe_valid_cycles_slc2_prop) else $fatal("rtt_swe_valid is not asserted 5 cycles");

  property rtt_swe_ext_slc2_prop;
     @(posedge `NPU_SL2.clk) disable iff(`NPU_SL2.rst_a !==0) (1) |-> (sl2_rtt_swe_ext == sl2_ref_swe_ext);
  endproperty
  ast_rtt_ext_slc2: assert property(rtt_swe_ext_slc2_prop) else $fatal("rtt_swe_ext is not expected");
  property rtt_swe_valid_cycles_slc3_prop;
     @(posedge `NPU_SL3.clk) disable iff(`NPU_SL3.rst_a !==0) $rose(sl3_rtt_swe_val) |-> ##5 $fell(sl3_rtt_swe_val);
  endproperty
  ast_rtt_valid_slc3: assert property(rtt_swe_valid_cycles_slc3_prop) else $fatal("rtt_swe_valid is not asserted 5 cycles");

  property rtt_swe_ext_slc3_prop;
     @(posedge `NPU_SL3.clk) disable iff(`NPU_SL3.rst_a !==0) (1) |-> (sl3_rtt_swe_ext == sl3_ref_swe_ext);
  endproperty
  ast_rtt_ext_slc3: assert property(rtt_swe_ext_slc3_prop) else $fatal("rtt_swe_ext is not expected");


endmodule
