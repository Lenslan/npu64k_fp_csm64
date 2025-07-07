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
// Top-level file for the oDMA XM Process
//


module npu_odma_xm_process
  import npu_types::*;
  #(
    // HLAPI type
    parameter int  S        = DMA_VM_LANES,
    parameter int  STU_D    = DMA_VM_LANES*8*ISIZE,
    parameter int  AD_WID   = $clog2(DMA_VM_LANES*ISIZE),  
    parameter int  DATA_LEN = AD_WID
  )
(
// spyglass disable_block W240
// SMD: Declare but Not used 
// SJ: Ignore 
  // Descr Input
  input  logic                  hlapi_i_valid, // new HLAPI issue descriptor valid
  input  dma_hlapi_i_t          hlapi_i,       // HLAPI input descriptor
  output logic                  hlapi_i_accept,// new HLAPI issue descriptor accept
// spyglass enable_block W240

  // FM Buffer Interface
  input  logic                  fm_buffer_wr_accept,
  output logic [AD_WID-1:0]     fm_buffer_wr_num,
  output logic [AD_WID-1:0]     fm_buffer_wr_alsb,
  output logic [STU_D-1:0]      fm_buffer_wr_data,
  output logic                  fm_buffer_wr_valid,

  // Output data
  input  logic                  out_valid,
  input  logic [STU_D-1:0]      out_data,
  input  logic [DATA_LEN:0]     out_len,
  output logic                  out_accept,
  output logic                  idle,

  // clock and reset
  //
  input  logic                  clk,         // clock, all logic clocked at posedge
  input  logic                  rst_dp       // reset, active high

);

  // Descr Information Buffer
  offset_t               planar_offset_r;   // pix_t channel offset in planar mode
  offset_t               planar_stride_r;   // VM pix_t channel stride for planar mode, log2 encoded; value 0 means no planar mode
  offset_t               xm_chnl_iter_r;    // XM Channel Iteration
  logic                  compress_r;        // Compresion Mode

  logic    [15:4]        xm_chnl_r;         // Current XM Channel Iteration
  logic    [15:4]        xm_chnl_nxt;       // Current XM Channel Iteration Next Value
  logic                  xm_chnl_en;        // Current XM Channel Iteration Enable

  // Data process
  logic                  fifo_valid;
  logic [STU_D-1:0]      fifo_data;
  logic [DATA_LEN:0]     fifo_len;
  logic                  fifo_accept;

  // WR FIFO connection
  logic                  fifo_buffer_wr_accept;
  logic [DATA_LEN-1:0]   fifo_buffer_wr_num;
  logic [STU_D-1:0]      fifo_buffer_wr_data;
  logic                  fifo_buffer_wr_valid;



// spyglass disable_block SelfDeterminedExpr-ML W116 W164a
// SMD: Self determined expression
// SJ: Intention implement 
  always_comb
  begin : buffer_store_PROC
    logic [S-1:0]          t_gte;
    logic [STU_D-1:0]      t_data;
    logic [DATA_LEN:0]     t_len;
    logic [DATA_LEN:0]     t_len1;
    logic [STU_D-1:0]      t_mask;
    logic [4:0]            t_plus;
    logic [4:0]            t_plus1;
    fifo_accept          = 'b0;
    fifo_buffer_wr_data  = 'b0;
    fifo_buffer_wr_num   = 'b0;
    fifo_buffer_wr_valid = 'b0;
    fm_buffer_wr_alsb    = 'b0;
    t_data               = 'b0;
    t_len                = '1;  // initialize to -1
    t_len1               = '0;
    t_mask               = '1;  // initialize mask to all ones
    t_plus               = '0;
    t_plus1              = '0;
    xm_chnl_en           = 1'b0;
    xm_chnl_nxt          = xm_chnl_r;
    
    // XM Padding Mode
    for (int i = 0; i < S; i++) begin // {
      t_gte[i] = fifo_len[DATA_LEN:4] >= unsigned'(i+1);
    end // }
    // Planar Mode check
        for (int i = 0; i < S; i++) begin // {
          t_data  = (t_data & (~t_mask)) | (fifo_data[128*i+:128] << {t_len1,3'b000});
          t_plus  = 5'd0;
          t_plus1 = 5'd0;
          if ((compress_r == 1'b0) && (xm_chnl_iter_r[3:0] != 4'b0) && (xm_chnl_nxt == 12'd0)) begin
            t_plus       |= t_gte[i] ? xm_chnl_iter_r[3:0] : '0;
            t_plus1      |= xm_chnl_iter_r[3:0];
            t_mask        = t_mask<<{xm_chnl_iter_r[3:0],3'b000};
            if (t_gte[i]) begin // {
              xm_chnl_nxt = xm_chnl_iter_r[15:4];
            end // }
          end
          else begin
            t_plus       |= t_gte[i] ? 'd16 : '0;
            t_plus1      |= 'd16;
            t_mask        = t_mask<<'d128;
            if (t_gte[i]) begin // {
              xm_chnl_nxt = xm_chnl_nxt - 'd1;
            end // }
          end
          t_len  = t_len  + t_plus;
          t_len1 = t_len1 + t_plus1;
        end
      
    fifo_buffer_wr_data    = t_data;
    fifo_buffer_wr_num     = t_len;
    fm_buffer_wr_alsb      = 'b0;
    // Set the XM chnl Iteration
    if (hlapi_i_valid && hlapi_i_accept) begin
      // Initialize channel counter
      xm_chnl_en           = 1'b1;
      xm_chnl_nxt          = hlapi_i.xm_seq.iter[NUM_FM_LOOPS-1][15:4];
    end
    else if (fifo_valid) begin      
      // Write to Buffer
      xm_chnl_en           = fifo_buffer_wr_accept;
      fifo_accept          = fifo_buffer_wr_accept;
      fifo_buffer_wr_valid = 1'b1;
    end
  end : buffer_store_PROC
// spyglass enable_block SelfDeterminedExpr-ML W116 W164a

 // Buffer Descr Information
  always_ff @(posedge clk or
              posedge rst_dp)
  begin : buf_descr_PROC
    if (rst_dp == 1'b1)
    begin
      planar_offset_r  <=  'b0;
      planar_stride_r  <=  'b0;
      xm_chnl_iter_r   <=  'b0;
      compress_r       <=  'b0;
    end
    else if (hlapi_i_valid & hlapi_i_accept)
    begin
      planar_offset_r  <=    0                       ;
      planar_stride_r  <=    0                       ;
      xm_chnl_iter_r   <=    hlapi_i.xm_seq.iter[NUM_FM_LOOPS-1];
      compress_r       <=    0                       ;
    end
  end : buf_descr_PROC

 // Iterate XM channel
  always_ff @(posedge clk or
              posedge rst_dp)
  begin : Iter_XM_chnl_PROC
    if (rst_dp == 1'b1)
    begin
      xm_chnl_r        <=  'b0;
    end
    else begin
      if (xm_chnl_en)
      begin
        xm_chnl_r        <=  xm_chnl_nxt;
      end
    end
  end : Iter_XM_chnl_PROC

  // FIFO to store command 
  npu_fifo 
  #(
    .SIZE   ( 2  ),
    .DWIDTH ( STU_D+DATA_LEN+1  )
  )
  u_vm_data_fifo_inst
  (           
     .clk          ( clk                  ),
     .rst_a        ( rst_dp               ),
     .valid_write  ( out_valid            ), 
     .accept_write ( out_accept           ),
     .data_write   ( {out_data, out_len}  ),
     .valid_read   ( fifo_valid           ),
     .accept_read  ( fifo_accept          ),
     .data_read    ( {fifo_data, fifo_len})
  );

  // FIX: opt on timing
  npu_fifo 
  #(
    .SIZE   ( 2  ),
    .DWIDTH ( STU_D+DATA_LEN  )
  )
  u_wbuffer_fifo_inst
  (           
     .clk          ( clk                  ),
     .rst_a        ( rst_dp               ),
     .valid_write  ( fifo_buffer_wr_valid ), 
     .accept_write ( fifo_buffer_wr_accept),
     .data_write   ( {fifo_buffer_wr_data, fifo_buffer_wr_num}),
     .valid_read   ( fm_buffer_wr_valid   ),
     .accept_read  ( fm_buffer_wr_accept  ),
     .data_read    ( {fm_buffer_wr_data, fm_buffer_wr_num})
  );

  assign    hlapi_i_accept        = 1'b1;
  assign    idle                  = ~fm_buffer_wr_valid && ~fifo_valid;

endmodule : npu_odma_xm_process
