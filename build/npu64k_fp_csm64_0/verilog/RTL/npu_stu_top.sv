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
`include "npu_macros.svh"
`include "npu_axi_macros.svh"
`include "npu_macros.svh"


module npu_stu_top
  import npu_types::*;
  (
    input  logic    clk,           // Main clock and reset
    input  logic    rst,           // Synchronous reset
    output logic    done_evt,
    output logic    issue_evt,
    output logic    done_irq,
    output logic    err_irq,
    input  logic    test_mode,
   `TRCMST(stu_trace_,1),
    input  logic [64-1: 0]        vmid,
    `AXIMST(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,dev_axi_),
    `AXISLV(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,ccm_axi_)
  );

  // AXI wires
  `AXIWIRES(1,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,descr_nar_axi_);
  `AXIWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,descr_wid_axi_);
  `AXIWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,stu_fm_axi_);
  `AXIWIRESN(2,3,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_cslc_);
  `AXIWIRES(4,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,idev_axi_);


  // Unify STU Core
  npu_ustu_top
   #(.SAXIIDW     (1),
     .AXI_OST     (AXI_OST),
     .STU_D       (64*VSIZE),
     .SAXIAWUW    (SLICE_MMIO_AWUW),
     .SAXIWUW     (SLICE_MMIO_WUW ),
     .SAXIBUW     (SLICE_MMIO_BUW ),
     .SAXIARUW    (SLICE_MMIO_ARUW),
     .SAXIRUW     (SLICE_MMIO_RUW ),
     .MAXIAWUW    (SLICE_DMA_AWUW),
     .MAXIWUW     (SLICE_DMA_WUW ),
     .MAXIBUW     (SLICE_DMA_BUW ),
     .MAXIARUW    (SLICE_DMA_ARUW),
     .MAXIRUW     (SLICE_DMA_RUW ),
     .XM_BUF_SIZE2(XM_BUF_SIZE2),
     .XM_BUF_SIZE (XM_BUF_SIZE),
     .AXI_MST_IDW (1)
    ) u_npu_ustu
  (
    `AXIINST(mmio_axi_, ccm_axi_),
    `AXIINST(descr_axi_, descr_nar_axi_),
    `AXIINST(stu_fm_axi_,stu_fm_axi_),
    // interrupt and event
    //
    .irq                   (done_irq),        // level interrupt to processor
    .err_irq               (err_irq),         // level interrupt to processor
    .ievent                (issue_evt),       // event pulse to processor
    .devent                (done_evt),        // event pulse to processor
    // trace interface
    `TRCINST_B(trace_,stu_trace_),
    .vmid                  (vmid),
    .test_mode             (test_mode),
    .clk                   (clk),
    .rst_a                 (rst)
  );
 
  // Descriptor 64 to 128/512
  npu_axi_bridge
  #(
     .AXIIDW(1),
     .AXISAWUW(SLICE_DMA_AWUW),
     .AXISARUW(SLICE_DMA_ARUW),
     .AXIMAWUW(SLICE_DMA_AWUW),
     .AXIMARUW(SLICE_DMA_ARUW),
     .AXISDW(64),
     .AXIMDW(64*VSIZE)
  ) u_descr_upsize_bridge 
  (
    `AXIINST(axi_slv_,descr_nar_axi_),
    `AXIINST(axi_mst_,descr_wid_axi_),
    .clk            (clk),
    .rst_a          (rst)
  );

  `AXIASGNNID(0,axi_cslc_,descr_wid_axi_);
  `AXIASGNNID(1,axi_cslc_,stu_fm_axi_);
  npu_axi_matrix
  #(
   //As npu_stu_top will be protected by DCLS, npu_axi_matrix_ctrl don't need to be protected by DCLS
    .NUMSLV  ( 2               ),
    .NUMMST  ( 1               ),
    .NUMAP   ( 1               ),
    .AXIDW   ( 64*VSIZE        ),
    .AXISIDW ( 3               ),
    .AXIMIDW ( 4               ), 
    .AXIAWUW ( SLICE_DMA_AWUW  ),
    .AXIWUW  ( SLICE_DMA_WUW   ),
    .AXIBUW  ( SLICE_DMA_BUW   ),
    .AXIARUW ( SLICE_DMA_ARUW  ),
    .AXIRUW  ( SLICE_DMA_RUW   )
  )
  u_npu_unify_stu_data_mux_inst
  (
    .clk    ( clk      ),
    .rst_a  ( rst      ),
    .ptidx_a( 2'b00    ),
    .decslv ( '0       ),
    `AXIINST(axi_slv_,axi_cslc_),
    `AXIINST(axi_mst_,idev_axi_),
    .decbase('0                  ),
    .decsize('0                  ),
    .decmst ('0                  )
  );

  //
  // Output slices to L2 ARC NoC //
  npu_axi_idtrack
  #(
    .SIZE    ( AXI_OST       ),
    .AXISIDW ( 4             ),
    .AXIMIDW ( 1     ),
    .AXIDW   ( 64*VSIZE      ),
    .AXIAWUW ( SLICE_DMA_AWUW),
    .AXIWUW  ( SLICE_DMA_WUW ),
    .AXIBUW  ( SLICE_DMA_BUW ),
    .AXIARUW ( SLICE_DMA_ARUW),
    .AXIRUW  ( SLICE_DMA_RUW )
  )
  u_stu_idc_inst
  (
    .clk   ( clk      ),
    .rst_a ( rst      ),
    `AXIINST(axi_slv_,idev_axi_),
    `AXIINST(axi_mst_,dev_axi_)
  );


endmodule : npu_stu_top
