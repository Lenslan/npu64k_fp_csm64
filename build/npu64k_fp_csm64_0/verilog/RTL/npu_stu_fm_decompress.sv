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

 
`include "npu_vm_macros.svh"
`include "npu_axi_macros.svh"

module npu_stu_fm_decompress
  import npu_types::*;
  #(
    parameter DMA_VM_LANES_L = 4, //
    parameter AD_WID = $clog2(DMA_VM_LANES_L*ISIZE)
   )
  (
// spyglass disable_block W240
// SMD: Declare but Not used 
// SJ: Ignore 
   // Signals from MMIO register, controlled by valid/accept handshake
   input logic      hlapi_i_valid, // new HLAPI issue descriptor valid
   output logic     hlapi_i_accept, // new HLAPI issue descriptor accept
   input  hlapi_xm_agu_t hlapi_i_seq, // HLAPI input descriptor
   input  pix_t          hlapi_i_zero,
// spyglass enable_block W240
   
   // Compressed Data/Normal Data input
   input logic          buffer_wr_valid,
   input logic [AD_WID-1:0]     buffer_wr_num,
   input logic [AD_WID-1:0]     buffer_wr_alsb,
   input logic [DMA_VM_LANES_L*8*ISIZE-1:0]     buffer_wr_data,
   output logic         buffer_wr_accept,

   // Decompressed Data output
   output logic         fm_wr_valid,
   output logic [AD_WID-1:0]    fm_wr_num,
   output logic [AD_WID-1:0]    fm_wr_alsb,
   output logic [DMA_VM_LANES_L*8*ISIZE-1:0] fm_wr_data,
   input logic          fm_wr_accept,
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore
   input logic          fm_axi_idle,
   input logic          fm_agu_idle,
// spyglass enable_block W240
   output logic         idle,
// spyglass disable_block W240
//SMD:Declared input but not read
//SJ :Ignore rst_dp and clk because no compress in config NPU_DISABLE_DMA_CPS
   input logic          rst_dp, // reset compute datapath
   input logic          clk
// spyglass enable_block W240
   );

   assign buffer_wr_accept    =  fm_wr_accept;
   assign fm_wr_valid         =  buffer_wr_valid;
   assign fm_wr_num           =  buffer_wr_num;
   assign fm_wr_alsb          =  buffer_wr_alsb;
   assign fm_wr_data          =  buffer_wr_data;
   assign hlapi_i_accept      =  1'b1;
   assign idle                =  1'b1;
   
 
endmodule : npu_stu_fm_decompress
