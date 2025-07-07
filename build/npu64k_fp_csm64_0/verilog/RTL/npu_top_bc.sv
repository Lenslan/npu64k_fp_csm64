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


`include "npu_defines.v"
`include "npu_axi_macros.svh"


module npu_top_bc
  import npu_types::*;
  #(
    parameter int NUMMST  = 4,
    parameter int AXIIDW  = 4,
    parameter int AXIDW   = 128,
    parameter int AXIAWUW = 1,
    parameter int AXIWUW  = 1,
    parameter int AXIBUW  = 1,
    parameter int AXIARUW = 1,
    parameter int AXIRUW  = 1,
    // FIFO depth specification
    parameter int AWFIFO_DEPTH = 1,
    parameter int WFIFO_DEPTH  = 2,
    parameter int BFIFO_DEPTH  = 1,
    parameter int ARFIFO_DEPTH = 1,
    parameter int RFIFO_DEPTH  = 2
  )
  (
   // clock and reset
   input logic clk,
   input logic rst_a,
   // AXI slave interface
   `AXISLVN(NUMMST,AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_slv_),
   // AXI master interface
   `AXIMSTN(NUMMST,AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_mst_)
   );

  localparam int MAXID = 1<<AXIIDW;
  typedef  logic [AXIIDW-1:0] id_t;

    logic     [3:0][3:0]            axi_slv_arsyn_flg;
    assign    axi_slv_arsyn_flg[0]  = axi_slv_aruser[0][64+:4];
    assign    axi_slv_arsyn_flg[1]  = axi_slv_aruser[1][64+:4];
    assign    axi_slv_arsyn_flg[2]  = axi_slv_aruser[2][64+:4];
    assign    axi_slv_arsyn_flg[3]  = axi_slv_aruser[3][64+:4];


 `AXIWASG(axi_slv_,axi_mst_);

    // Put in AXI0
    assign     axi_mst_arid[0]     =   axi_slv_arid[0]      ; 
    assign     axi_mst_aruser[0]   =   axi_slv_aruser[0]    ; 
    assign     axi_mst_ar[0]       =   axi_slv_ar[0]        ; 
    assign     axi_slv_rid[0]      =   axi_mst_rid[0]       ; 
    assign     axi_slv_ruser[0]    =   axi_mst_ruser[0]     ; 
    assign     axi_slv_rdata[0]    =   axi_mst_rdata[0]     ; 
    assign     axi_slv_rresp[0]    =   axi_mst_rresp[0]     ;

    // AXI 0 master
    logic                 [3:0]               npu_si0_sync;
    logic      [MAXID-1:0][3:0]               sync_req_flag0;
    logic                 [3:0]               sync_req_flag0_arb;
    logic      [MAXID-1:0]                    mst0_cmd_wvld;

    assign     npu_si0_sync     = axi_slv_arsyn_flg[0];
    // AXI 1 master
    logic                 [3:0]               npu_si1_sync;
    logic      [MAXID-1:0][3:0]               sync_req_flag1;
    logic                 [3:0]               sync_req_flag1_arb;
    logic      [MAXID-1:0]                    mst1_cmd_wvld;

    assign     npu_si1_sync     = axi_slv_arsyn_flg[1];
    // AXI 2 master
    logic                 [3:0]               npu_si2_sync;
    logic      [MAXID-1:0][3:0]               sync_req_flag2;
    logic                 [3:0]               sync_req_flag2_arb;
    logic      [MAXID-1:0]                    mst2_cmd_wvld;

    assign     npu_si2_sync     = axi_slv_arsyn_flg[2];
    // AXI 3 master
    logic                 [3:0]               npu_si3_sync;
    logic      [MAXID-1:0][3:0]               sync_req_flag3;
    logic                 [3:0]               sync_req_flag3_arb;
    logic      [MAXID-1:0]                    mst3_cmd_wvld;

    assign     npu_si3_sync     = axi_slv_arsyn_flg[3];

// sync read channel for Port0
    logic                               axi_slv0_arvalid_mux ;
    logic                               axi_slv0_rready_mux  ;
    logic                               axi_mst0_arready_mux ;
    logic                               axi_mst0_rlast_mux   ;
    logic                               axi_mst0_rvalid_mux  ;
    logic                               axi_adr_isnot_ready0 ;
    id_t             [4-2:0]            axi0_arid            ;
    id_t  [MAXID-1:0][4-2:0]            axi0_rid             ;
    id_t             [4-2:0]            axi0_rid_arb         ;


    logic                               axi0_sync_axi1       ;
    logic                               axi0_sync_dat_axi1   ;
    logic                               axi0_sync_axi2       ;
    logic                               axi0_sync_dat_axi2   ;
    logic                               axi0_sync_axi3       ;
    logic                               axi0_sync_dat_axi3   ;

    always_comb 
    begin : mst0_cmd_fifo_PROC
      integer i;
      mst0_cmd_wvld      = {MAXID{1'b0}};
      axi0_rid_arb       = '0;
      sync_req_flag0_arb = '0;
      for (i=1; i<MAXID; i=i+2) begin
        if (axi_slv_arid[0] == i) begin
          mst0_cmd_wvld[i]   |= axi_slv_arvalid[0] && axi_slv_arready[0];
        end
        if ((axi_mst_rid[0] == i) && (axi_mst_rvalid[0] == 1'b1)) begin
          axi0_rid_arb       |= axi0_rid[i];
          sync_req_flag0_arb |= sync_req_flag0[i];
        end
      end
    end : mst0_cmd_fifo_PROC

    assign     axi0_arid            =  {
                                        axi_slv_arid[3],
                                        axi_slv_arid[2],
                                        axi_slv_arid[1]
                                       };


    assign     axi_mst_arvalid[0]   =   (npu_si0_sync    == 4'b0) ? axi_slv_arvalid[0] : axi_slv0_arvalid_mux ;   //addr request
    assign     axi_slv_arready[0]   =   (npu_si0_sync    == 4'b0) ? axi_mst_arready[0] : axi_mst0_arready_mux ;   //addr accept

    assign     axi_mst_rready[0]    =   (sync_req_flag0_arb  == 4'b0) ? axi_slv_rready[0]  : axi_slv0_rready_mux  ;   //data accept
    assign     axi_slv_rvalid[0]    =   (sync_req_flag0_arb  == 4'b0) ? axi_mst_rvalid[0]  : axi_mst0_rvalid_mux  ;   //data valid
    assign     axi_slv_rlast[0]     =   (sync_req_flag0_arb  == 4'b0) ? axi_mst_rlast[0]   : axi_mst0_rlast_mux   ;   //read last beat

    assign     axi_adr_isnot_ready0 =   1'b0
                                     || (npu_si0_sync[0] && (!axi_slv_arvalid[0]))
                                     || (npu_si0_sync[1] && (!axi_slv_arvalid[1]))
                                     || (npu_si0_sync[2] && (!axi_slv_arvalid[2]))
                                     || (npu_si0_sync[3] && (!axi_slv_arvalid[3]))
                                        ;

    assign       axi0_sync_axi1       =   npu_si0_sync[1] ? (npu_si0_sync == npu_si1_sync) : 1'b1;
    assign       axi0_sync_dat_axi1   =   sync_req_flag0_arb[1] ? (axi_slv_rready[1] && (sync_req_flag0_arb == sync_req_flag1_arb)) : 1'b1;
    assign       axi0_sync_axi2       =   npu_si0_sync[2] ? (npu_si0_sync == npu_si2_sync) : 1'b1;
    assign       axi0_sync_dat_axi2   =   sync_req_flag0_arb[2] ? (axi_slv_rready[2] && (sync_req_flag0_arb == sync_req_flag2_arb)) : 1'b1;
    assign       axi0_sync_axi3       =   npu_si0_sync[3] ? (npu_si0_sync == npu_si3_sync) : 1'b1;
    assign       axi0_sync_dat_axi3   =   sync_req_flag0_arb[3] ? (axi_slv_rready[3] && (sync_req_flag0_arb == sync_req_flag3_arb)) : 1'b1;

    always_comb
    begin
      axi_slv0_arvalid_mux  =  1'b0;
      axi_slv0_rready_mux   =  1'b0;
      axi_mst0_arready_mux  =  1'b0;
      axi_mst0_rvalid_mux   =  1'b0;
      axi_mst0_rlast_mux    =  1'b0;

      if ((!axi_adr_isnot_ready0)
        && axi0_sync_axi1
        && axi0_sync_axi2
        && axi0_sync_axi3
         ) begin
        axi_slv0_arvalid_mux  =  axi_slv_arvalid[0] ;
        axi_mst0_arready_mux  =  axi_mst_arready[0] ;
      end

      if (axi_slv_rready[0] 
        && axi0_sync_dat_axi1 
        && axi0_sync_dat_axi2 
        && axi0_sync_dat_axi3 
         ) begin
        axi_slv0_rready_mux   =  axi_slv_rready[0]  ;
        axi_mst0_rvalid_mux   =  axi_mst_rvalid[0]  ;
        axi_mst0_rlast_mux    =  axi_mst_rlast[0]   ;
      end
    end
    

// sync read channel for Port1

    npu_axi_cmd_t                       axi_slv1_ar_mux      ;
    logic  [AXIARUW-1:0]                axi_slv1_aruser_mux  ;
    logic  [AXIIDW-1:0]                 axi_slv1_arid_mux    ;
    logic                               axi_slv1_arvalid_mux ;
    logic                               axi_mst1_arready_mux ;
    logic  [AXIIDW-1:0]                 axi_mst1_rid_mux     ;
    logic  [AXIRUW-1:0]                 axi_mst1_ruser_mux   ;
    logic  [AXIDW-1:0]                  axi_mst1_rdata_mux   ;
    logic  [NPU_AXI_RESP_W-1:0]         axi_mst1_rresp_mux   ;
    logic                               axi_mst1_rlast_mux   ;
    logic                               axi_mst1_rvalid_mux  ;
    logic                               axi_slv1_rready_mux  ;
    logic                               axi_adr_isnot_ready1 ;
    id_t             [4-3:0]            axi1_arid            ;
    id_t  [MAXID-1:0][4-3:0]            axi1_rid             ;
    id_t             [4-3:0]            axi1_rid_arb         ;
      
  
    logic                               axi1_sync_axi2       ;
    logic                               axi1_sync_dat_axi2   ;
    logic                               axi1_sync_axi3       ;
    logic                               axi1_sync_dat_axi3   ;

    always_comb 
    begin : mst1_cmd_fifo_PROC
      integer i;
      mst1_cmd_wvld      = {MAXID{1'b0}};
      axi1_rid_arb       = '0;
      sync_req_flag1_arb = '0;
      for (i=1; i<MAXID; i=i+2) begin
        if (axi_slv_arid[1] == i) begin
          mst1_cmd_wvld[i]   |= axi_slv_arvalid[1] && axi_slv_arready[1];
        end
        // SYNC has highest priority
        if (axi_mst_rvalid[0] && sync_req_flag0_arb[1] && (axi0_rid_arb[0] == i)) begin
          axi1_rid_arb       |= axi1_rid[i];
          sync_req_flag1_arb |= sync_req_flag1[i];
        end
        else if ((axi_mst_rid[1] == i) && (axi_mst_rvalid[1] == 1'b1)) begin
          axi1_rid_arb       |= axi1_rid[i];
          sync_req_flag1_arb |= sync_req_flag1[i];
        end
      end
    end : mst1_cmd_fifo_PROC

    assign     axi1_arid            =  {axi_slv_arid[3], axi_slv_arid[2]};


    assign     axi_mst_aruser[1]    =   (npu_si1_sync == 4'b0) ? axi_slv_aruser[1]  : axi_slv1_aruser_mux  ; 
    assign     axi_mst_arid[1]      =   (npu_si1_sync == 4'b0) ? axi_slv_arid[1]    : axi_slv1_arid_mux    ; 
    assign     axi_mst_ar[1]        =   (npu_si1_sync == 4'b0) ? axi_slv_ar[1]      : axi_slv1_ar_mux      ; 
    assign     axi_mst_arvalid[1]   =   (npu_si1_sync == 4'b0) ? axi_slv_arvalid[1] : axi_slv1_arvalid_mux ; 
    assign     axi_slv_arready[1]   =   (npu_si1_sync == 4'b0) ? axi_mst_arready[1] : axi_mst1_arready_mux ; 

    assign     axi_slv_rid[1]       =   (sync_req_flag1_arb  == 4'b0) ? axi_mst_rid[1]     : axi_mst1_rid_mux     ;
    assign     axi_slv_ruser[1]     =   (sync_req_flag1_arb  == 4'b0) ? axi_mst_ruser[1]   : axi_mst1_ruser_mux   ;
    assign     axi_slv_rdata[1]     =   (sync_req_flag1_arb  == 4'b0) ? axi_mst_rdata[1]   : axi_mst1_rdata_mux   ;
    assign     axi_slv_rresp[1]     =   (sync_req_flag1_arb  == 4'b0) ? axi_mst_rresp[1]   : npu_axi_resp_t'(axi_mst1_rresp_mux)   ;
    assign     axi_slv_rvalid[1]    =   (sync_req_flag1_arb  == 4'b0) ? axi_mst_rvalid[1]  : axi_mst1_rvalid_mux  ;
    assign     axi_slv_rlast[1]     =   (sync_req_flag1_arb  == 4'b0) ? axi_mst_rlast[1]   : axi_mst1_rlast_mux   ;
    assign     axi_mst_rready[1]    =   (sync_req_flag1_arb  == 4'b0) ? axi_slv_rready[1]  : axi_slv1_rready_mux  ;

    assign     axi_adr_isnot_ready1 =   1'b0
                                     || (npu_si1_sync[0] && (!axi_slv_arvalid[0]))
                                     || (npu_si1_sync[1] && (!axi_slv_arvalid[1]))
                                     || (npu_si1_sync[2] && (!axi_slv_arvalid[2]))
                                     || (npu_si1_sync[3] && (!axi_slv_arvalid[3]))
                                        ;

    assign       axi1_sync_axi2       =   npu_si1_sync[2] ? (npu_si1_sync == npu_si2_sync) : 1'b1;
    assign       axi1_sync_dat_axi2   =   sync_req_flag1_arb[2] ? (axi_slv_rready[2] && (sync_req_flag1_arb == sync_req_flag2_arb)) : 1'b1;
    assign       axi1_sync_axi3       =   npu_si1_sync[3] ? (npu_si1_sync == npu_si3_sync) : 1'b1;
    assign       axi1_sync_dat_axi3   =   sync_req_flag1_arb[3] ? (axi_slv_rready[3] && (sync_req_flag1_arb == sync_req_flag3_arb)) : 1'b1;

    always_comb
    begin
      axi_slv1_aruser_mux   = '0;
      axi_slv1_arid_mux     = '0;
      axi_slv1_ar_mux       = '0;
      axi_slv1_arvalid_mux  = '0;
      axi_slv1_rready_mux   = '0;
      axi_mst1_arready_mux  = '0;
      axi_mst1_rid_mux      = '0;
      axi_mst1_ruser_mux    = '0;
      axi_mst1_rdata_mux    = '0;
      axi_mst1_rresp_mux    = '0;
      axi_mst1_rlast_mux    = '0;
      axi_mst1_rvalid_mux   = '0;

      if (npu_si1_sync[0]) begin
        if (npu_si1_sync == npu_si0_sync) begin
          axi_mst1_arready_mux  |= axi_mst0_arready_mux ;
        end
      end
      else if ((!axi_adr_isnot_ready1)
              && axi1_sync_axi2
              && axi1_sync_axi3
              )
      begin
        axi_slv1_aruser_mux   |= axi_slv_aruser[1]  ;
        axi_slv1_arid_mux     |= axi_slv_arid[1]    ;
        axi_slv1_ar_mux       |= axi_slv_ar[1]      ;
        axi_slv1_arvalid_mux  |= axi_slv_arvalid[1] ;
        axi_mst1_arready_mux  |= axi_mst_arready[1] ;
      end

      if (sync_req_flag1_arb[0]) begin
        axi_mst1_rid_mux      |= axi0_rid_arb[0]      ;
        axi_mst1_rdata_mux    |= axi_mst_rdata[0]     ;
        axi_mst1_rresp_mux    |= axi_mst_rresp[0]     ;
        axi_mst1_rlast_mux    |= axi_mst0_rlast_mux   ;
        axi_mst1_rvalid_mux   |= axi_mst0_rvalid_mux  ;
      end
      else if (axi_slv_rready[1] 
        && axi1_sync_dat_axi2 
        && axi1_sync_dat_axi3 
         ) begin
        axi_mst1_ruser_mux    |= axi_mst_ruser[1]   ;
        axi_mst1_rid_mux      |= axi_mst_rid[1]     ;
        axi_mst1_rdata_mux    |= axi_mst_rdata[1]   ;
        axi_mst1_rresp_mux    |= axi_mst_rresp[1]   ;
        axi_mst1_rlast_mux    |= axi_mst_rlast[1]   ;
        axi_mst1_rvalid_mux   |= axi_mst_rvalid[1]  ;
        axi_slv1_rready_mux   |= axi_slv_rready[1]  ;
      end
    end

// sync read channel for Port2

    npu_axi_cmd_t                       axi_slv2_ar_mux      ;
    logic  [AXIARUW-1:0]                axi_slv2_aruser_mux  ;
    logic  [AXIIDW-1:0]                 axi_slv2_arid_mux    ;
    logic                               axi_slv2_arvalid_mux ;
    logic                               axi_mst2_arready_mux ;
    logic  [AXIIDW-1:0]                 axi_mst2_rid_mux     ;
    logic  [AXIRUW-1:0]                 axi_mst2_ruser_mux   ;
    logic  [AXIDW-1:0]                  axi_mst2_rdata_mux   ;
    logic  [NPU_AXI_RESP_W-1:0]         axi_mst2_rresp_mux   ;
    logic                               axi_mst2_rlast_mux   ;
    logic                               axi_mst2_rvalid_mux  ;
    logic                               axi_slv2_rready_mux  ;
    logic                               axi_adr_isnot_ready2 ;
    id_t                                axi2_arid            ;
    id_t  [MAXID-1:0]                   axi2_rid             ;
    id_t                                axi2_rid_arb         ;
      

    logic                               axi2_sync_axi3       ;
    logic                               axi2_sync_dat_axi3   ;

    always_comb 
    begin : mst2_cmd_fifo_PROC
      integer i;
      mst2_cmd_wvld      = {MAXID{1'b0}};
      axi2_rid_arb       = '0;
      sync_req_flag2_arb = '0;
      for (i=1; i<MAXID; i=i+2) begin
        if (axi_slv_arid[2] == i) begin
          mst2_cmd_wvld[i]   |= axi_slv_arvalid[2] && axi_slv_arready[2];
        end
        // SYNC has highest priority
        if (axi_mst_rvalid[0] && sync_req_flag0_arb[2] && (axi0_rid_arb[1] == i)) begin
          axi2_rid_arb       |= axi2_rid[i];
          sync_req_flag2_arb |= sync_req_flag2[i];
        end
        else if (axi_mst_rvalid[1] && sync_req_flag1_arb[2] && (axi1_rid_arb[0] == i)) begin
          axi2_rid_arb       |= axi2_rid[i];
          sync_req_flag2_arb |= sync_req_flag2[i];
        end
        else if ((axi_mst_rid[2] == i) && (axi_mst_rvalid[2] == 1'b1)) begin
          axi2_rid_arb       |= axi2_rid[i];
          sync_req_flag2_arb |= sync_req_flag2[i];
        end
      end
    end : mst2_cmd_fifo_PROC

    assign     axi2_arid            =  axi_slv_arid[3];

    assign     axi_mst_aruser[2]    =   (npu_si2_sync == 4'b0) ? axi_slv_aruser[2]  : axi_slv2_aruser_mux  ; 
    assign     axi_mst_arid[2]      =   (npu_si2_sync == 4'b0) ? axi_slv_arid[2]    : axi_slv2_arid_mux    ; 
    assign     axi_mst_ar[2]        =   (npu_si2_sync == 4'b0) ? axi_slv_ar[2]      : axi_slv2_ar_mux      ; 
    assign     axi_mst_arvalid[2]   =   (npu_si2_sync == 4'b0) ? axi_slv_arvalid[2] : axi_slv2_arvalid_mux ; 
    assign     axi_slv_arready[2]   =   (npu_si2_sync == 4'b0) ? axi_mst_arready[2] : axi_mst2_arready_mux ; 

    assign     axi_slv_rid[2]       =   (sync_req_flag2_arb  == 4'b0) ? axi_mst_rid[2]     : axi_mst2_rid_mux     ;
    assign     axi_slv_ruser[2]     =   (sync_req_flag2_arb  == 4'b0) ? axi_mst_ruser[2]   : axi_mst2_ruser_mux   ;
    assign     axi_slv_rdata[2]     =   (sync_req_flag2_arb  == 4'b0) ? axi_mst_rdata[2]   : axi_mst2_rdata_mux   ;
    assign     axi_slv_rresp[2]     =   (sync_req_flag2_arb  == 4'b0) ? axi_mst_rresp[2]   : npu_axi_resp_t'(axi_mst2_rresp_mux)   ;
    assign     axi_slv_rvalid[2]    =   (sync_req_flag2_arb  == 4'b0) ? axi_mst_rvalid[2]  : axi_mst2_rvalid_mux  ;
    assign     axi_slv_rlast[2]     =   (sync_req_flag2_arb  == 4'b0) ? axi_mst_rlast[2]   : axi_mst2_rlast_mux   ;
    assign     axi_mst_rready[2]    =   (sync_req_flag2_arb  == 4'b0) ? axi_slv_rready[2]  : axi_slv2_rready_mux  ;

    assign     axi_adr_isnot_ready2 =   1'b0
                                     || (npu_si2_sync[0] && (!axi_slv_arvalid[0]))
                                     || (npu_si2_sync[1] && (!axi_slv_arvalid[1]))
                                     || (npu_si2_sync[2] && (!axi_slv_arvalid[2]))
                                     || (npu_si2_sync[3] && (!axi_slv_arvalid[3]))
                                        ;

    assign       axi2_sync_axi3       =   npu_si2_sync[3] ? (npu_si2_sync == npu_si3_sync) : 1'b1;
    assign       axi2_sync_dat_axi3   =   sync_req_flag2_arb[3] ? (axi_slv_rready[3] && (sync_req_flag2_arb == sync_req_flag3_arb)) : 1'b1;

    always_comb
    begin
      axi_slv2_aruser_mux   = '0;
      axi_slv2_arid_mux     = '0;
      axi_slv2_ar_mux       = '0;
      axi_slv2_arvalid_mux  = '0;
      axi_slv2_rready_mux   = '0;
      axi_mst2_arready_mux  = '0;
      axi_mst2_rid_mux      = '0;
      axi_mst2_ruser_mux    = '0;
      axi_mst2_rdata_mux    = '0;
      axi_mst2_rresp_mux    = '0;
      axi_mst2_rlast_mux    = '0;
      axi_mst2_rvalid_mux   = '0;

      if (npu_si2_sync[0]) begin
        if (npu_si2_sync == npu_si0_sync) begin
          axi_mst2_arready_mux  |= axi_mst0_arready_mux ;
        end
      end
      else if (npu_si2_sync[1]) begin
        if (npu_si2_sync == npu_si1_sync) begin
          axi_mst2_arready_mux  |= axi_mst1_arready_mux ;
        end
      end
      else if ((!axi_adr_isnot_ready2)
              && axi2_sync_axi3
              )
      begin
        axi_slv2_aruser_mux   |= axi_slv_aruser[2]  ;
        axi_slv2_arid_mux     |= axi_slv_arid[2]    ;
        axi_slv2_ar_mux       |= axi_slv_ar[2]      ;
        axi_slv2_arvalid_mux  |= axi_slv_arvalid[2] ;
        axi_mst2_arready_mux  |= axi_mst_arready[2] ;
      end

      if (sync_req_flag2_arb[0]) begin
        axi_mst2_rid_mux      |= axi0_rid_arb[1]      ;
        axi_mst2_rdata_mux    |= axi_mst_rdata[0]     ;
        axi_mst2_rresp_mux    |= axi_mst_rresp[0]     ;
        axi_mst2_rlast_mux    |= axi_mst0_rlast_mux   ;
        axi_mst2_rvalid_mux   |= axi_mst0_rvalid_mux  ;
      end
      else if (sync_req_flag2_arb[1]) begin
        axi_mst2_rid_mux      |= axi1_rid_arb[0]      ;
        axi_mst2_rdata_mux    |= axi_mst_rdata[1]     ;
        axi_mst2_rresp_mux    |= axi_mst_rresp[1]     ;
        axi_mst2_rlast_mux    |= axi_mst1_rlast_mux   ;
        axi_mst2_rvalid_mux   |= axi_mst1_rvalid_mux  ;
      end
      else if (axi_slv_rready[2] 
        && axi2_sync_dat_axi3 
         ) begin
        axi_mst2_ruser_mux    |= axi_mst_ruser[2]   ;
        axi_mst2_rid_mux      |= axi_mst_rid[2]     ;
        axi_mst2_rdata_mux    |= axi_mst_rdata[2]   ;
        axi_mst2_rresp_mux    |= axi_mst_rresp[2]   ;
        axi_mst2_rlast_mux    |= axi_mst_rlast[2]   ;
        axi_mst2_rvalid_mux   |= axi_mst_rvalid[2]  ;
        axi_slv2_rready_mux   |= axi_slv_rready[2]  ;
      end
    end

// sync read channel for Port3

    npu_axi_cmd_t                       axi_slv3_ar_mux      ;
    logic  [AXIARUW-1:0]                axi_slv3_aruser_mux  ;
    logic  [AXIIDW-1:0]                 axi_slv3_arid_mux    ;
    logic                               axi_slv3_arvalid_mux ;
    logic                               axi_mst3_arready_mux ;
    logic  [AXIIDW-1:0]                 axi_mst3_rid_mux     ;
    logic  [AXIRUW-1:0]                 axi_mst3_ruser_mux   ;
    logic  [AXIDW-1:0]                  axi_mst3_rdata_mux   ;
    logic  [NPU_AXI_RESP_W-1:0]         axi_mst3_rresp_mux   ;
    logic                               axi_mst3_rlast_mux   ;
    logic                               axi_mst3_rvalid_mux  ;
    logic                               axi_slv3_rready_mux  ;
    logic                               axi_adr_isnot_ready3 ;

    always_comb 
    begin : mst3_cmd_fifo_PROC
      integer i;
      mst3_cmd_wvld      = {MAXID{1'b0}};
      sync_req_flag3_arb = '0;
      for (i=1; i<MAXID; i=i+2) begin
        if (axi_slv_arid[3] == i) begin
          mst3_cmd_wvld[i]   |= axi_slv_arvalid[3] && axi_slv_arready[3];
        end
        // SYNC has highest priority
        if (axi_mst_rvalid[0] && sync_req_flag0_arb[3] && (axi0_rid_arb[2] == i)) begin
          sync_req_flag3_arb |= sync_req_flag3[i];
        end
        else if (axi_mst_rvalid[1] && sync_req_flag1_arb[3] && (axi1_rid_arb[1] == i)) begin
          sync_req_flag3_arb |= sync_req_flag3[i];
        end
        else if (axi_mst_rvalid[2] && sync_req_flag2_arb[3] && (axi2_rid_arb == i)) begin
          sync_req_flag3_arb |= sync_req_flag3[i];
        end
        else if ((axi_mst_rid[3] == i) && (axi_mst_rvalid[3] == 1'b1)) begin
          sync_req_flag3_arb |= sync_req_flag3[i];
        end
      end
    end : mst3_cmd_fifo_PROC


    assign     axi_mst_aruser[3]    =   (npu_si3_sync == 4'b0) ? axi_slv_aruser[3]  : axi_slv3_aruser_mux  ; 
    assign     axi_mst_arid[3]      =   (npu_si3_sync == 4'b0) ? axi_slv_arid[3]    : axi_slv3_arid_mux    ; 
    assign     axi_mst_ar[3]        =   (npu_si3_sync == 4'b0) ? axi_slv_ar[3]      : axi_slv3_ar_mux      ; 
    assign     axi_mst_arvalid[3]   =   (npu_si3_sync == 4'b0) ? axi_slv_arvalid[3] : axi_slv3_arvalid_mux ; 
    assign     axi_slv_arready[3]   =   (npu_si3_sync == 4'b0) ? axi_mst_arready[3] : axi_mst3_arready_mux ; 

    assign     axi_slv_rid[3]       =   (sync_req_flag3_arb  == 4'b0) ? axi_mst_rid[3]     : axi_mst3_rid_mux     ;
    assign     axi_slv_ruser[3]     =   (sync_req_flag3_arb  == 4'b0) ? axi_mst_ruser[3]   : axi_mst3_ruser_mux   ;
    assign     axi_slv_rdata[3]     =   (sync_req_flag3_arb  == 4'b0) ? axi_mst_rdata[3]   : axi_mst3_rdata_mux   ;
    assign     axi_slv_rresp[3]     =   (sync_req_flag3_arb  == 4'b0) ? axi_mst_rresp[3]   : npu_axi_resp_t'(axi_mst3_rresp_mux)   ;
    assign     axi_slv_rvalid[3]    =   (sync_req_flag3_arb  == 4'b0) ? axi_mst_rvalid[3]  : axi_mst3_rvalid_mux  ;
    assign     axi_slv_rlast[3]     =   (sync_req_flag3_arb  == 4'b0) ? axi_mst_rlast[3]   : axi_mst3_rlast_mux   ;
    assign     axi_mst_rready[3]    =   (sync_req_flag3_arb  == 4'b0) ? axi_slv_rready[3]  : axi_slv3_rready_mux  ;

    always_comb
    begin
      axi_slv3_aruser_mux   = '0;
      axi_slv3_arid_mux     = '0;
      axi_slv3_ar_mux       = '0;
      axi_slv3_arvalid_mux  = '0;
      axi_slv3_rready_mux   = '0;
      axi_mst3_arready_mux  = '0;
      axi_mst3_rid_mux      = '0;
      axi_mst3_ruser_mux    = '0;
      axi_mst3_rdata_mux    = '0;
      axi_mst3_rresp_mux    = '0;
      axi_mst3_rlast_mux    = '0;
      axi_mst3_rvalid_mux   = '0;

      if (npu_si3_sync[0]) begin
        if (npu_si3_sync == npu_si0_sync) begin
          axi_mst3_arready_mux  |= axi_mst0_arready_mux ;
        end
      end
      else if (npu_si3_sync[1]) begin
        if (npu_si3_sync == npu_si1_sync) begin
          axi_mst3_arready_mux  |= axi_mst1_arready_mux ;
        end
      end
      else if (npu_si3_sync[2]) begin
        if (npu_si3_sync == npu_si2_sync) begin
          axi_mst3_arready_mux  |= axi_mst2_arready_mux ;
        end
      end

      if (sync_req_flag3_arb[0]) begin
        axi_mst3_rid_mux      |= axi0_rid_arb[2]      ;
        axi_mst3_rdata_mux    |= axi_mst_rdata[0]     ;
        axi_mst3_rresp_mux    |= axi_mst_rresp[0]     ;
        axi_mst3_rlast_mux    |= axi_mst0_rlast_mux   ;
        axi_mst3_rvalid_mux   |= axi_mst0_rvalid_mux  ;
      end
      else if (sync_req_flag3_arb[1]) begin
        axi_mst3_rid_mux      |= axi1_rid_arb[1]      ;
        axi_mst3_rdata_mux    |= axi_mst_rdata[1]     ;
        axi_mst3_rresp_mux    |= axi_mst_rresp[1]     ;
        axi_mst3_rlast_mux    |= axi_mst1_rlast_mux   ;
        axi_mst3_rvalid_mux   |= axi_mst1_rvalid_mux  ;
      end
      else if (sync_req_flag3_arb[3]) begin
        axi_mst3_rid_mux      |= axi2_rid_arb         ;
        axi_mst3_rdata_mux    |= axi_mst_rdata[2]     ;
        axi_mst3_rresp_mux    |= axi_mst_rresp[2]     ;
        axi_mst3_rlast_mux    |= axi_mst2_rlast_mux   ;
        axi_mst3_rvalid_mux   |= axi_mst2_rvalid_mux  ;
      end
    end


    always @(posedge clk or posedge rst_a)
    begin: axi_mst0_sync_flags_PROC
       integer i;
       if (rst_a == 1)
       begin
         sync_req_flag0          <= '0;
         axi0_rid                <= '0;
       end
       else
       begin
         for (i=0; i<MAXID; i=i+1) begin
           if (mst0_cmd_wvld[i]) begin
             sync_req_flag0[i]   <= npu_si0_sync;
             axi0_rid[i]         <= axi0_arid;
           end
         end
       end
    end: axi_mst0_sync_flags_PROC

    always @(posedge clk or posedge rst_a)
    begin: axi_mst1_sync_flags_PROC
       integer i;
       if (rst_a == 1)
       begin
         sync_req_flag1          <= '0;
         axi1_rid                <= '0;
       end
       else
       begin
         for (i=0; i<MAXID; i=i+1) begin
           if (mst1_cmd_wvld[i]) begin
             sync_req_flag1[i]   <= npu_si1_sync;
             axi1_rid[i]         <= axi1_arid;
           end
         end
       end
    end: axi_mst1_sync_flags_PROC

    always @(posedge clk or posedge rst_a)
    begin: axi_mst2_sync_flags_PROC
       integer i;
       if (rst_a == 1)
       begin
         sync_req_flag2          <= '0;
         axi2_rid                <= '0;
       end
       else
       begin
         for (i=0; i<MAXID; i=i+1) begin
           if (mst2_cmd_wvld[i]) begin
             sync_req_flag2[i]   <= npu_si2_sync;
             axi2_rid[i]         <= axi2_arid;
           end
         end
       end
    end: axi_mst2_sync_flags_PROC

    always @(posedge clk or posedge rst_a)
    begin: axi_mst3_sync_flags_PROC
       integer i;
       if (rst_a == 1)
       begin
         sync_req_flag3          <= '0;
       end
       else
       begin
         for (i=0; i<MAXID; i=i+1) begin
           if (mst3_cmd_wvld[i]) begin
             sync_req_flag3[i]   <= npu_si3_sync;
           end
         end
       end
    end: axi_mst3_sync_flags_PROC
endmodule : npu_top_bc
