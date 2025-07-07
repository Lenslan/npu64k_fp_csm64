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
// Top-level file for the iDMA XM process
//

//`include "npu_axi_macros.svh"
 
module npu_idma_xm_process
  import npu_types::*;
  #(
    // HLAPI type
    int S = DMA_VM_LANES,
    int STU_D = ISIZE*32 
    )
   (
// spyglass disable_block W240
// SMD: Declare but Not used 
// SJ: Ignore 
    // Descr Input
    input logic                hlapi_i_valid, // new HLAPI issue descriptor valid
    input dma_hlapi_i_t        hlapi_i, // HLAPI input descriptor
    output logic               hlapi_i_accept,// new HLAPI issue descriptor accept
// spyglass enable_block W240
    
    input logic [S-1:0]        vm_valid, // Enable each VM lanes
    
    // FM Buffer Interface
    output logic               fm_buffer_rd_accept,
    output logic [$clog2(DMA_VM_LANES*ISIZE)-1:0]         fm_buffer_rd_num,
    output logic [$clog2(DMA_VM_LANES*ISIZE)-1:0]         fm_buffer_rd_alsb,
    input logic [STU_D-1:0]    fm_buffer_rd_data,
    input logic [15:0]         fm_buffer_vld_size,
    
    // Output data
    output logic               out_valid,
    output logic [STU_D-1:0]   out_data,
    output logic [STU_D/8-1:0] out_wstrb,
    input logic                out_accept,
    
    // clock and reset
    //
    input logic                clk, // clock, all logic clocked at posedge
    input logic                rst_dp       // reset, active high
    
    );
  
  // Descr Information Buffer
  logic [15:0]                vm_wmsk_r;         // VM write mask in iDMA 
  offset_t                    planar_offset_r;   // pix_t channel offset in planar mode
  offset_t                    planar_stride_r;   // VM pix_t channel stride for planar mode, log2 encoded; value 0 means no planar mode
  logic                       gather_r;          // if true then use GTOA XM AGU input for "gather" support
  logic                       compress_mode_r;
  pix_t                       zero_point_r;      // zero point for channel padding for XM to VM copy: 8b
  dma_bc_t                    bc_r;              // broadcast flags for read data broadcast: 32b
  logic                       cnst_r;            // VM initialize mode
  offset_t                    xm_chnl_iter_r;    // XM Channel Iteration
  
  
  logic                       xm_chnl_en;        // Current XM Channel Iteration Enable

  // control logic
  logic [1:0]                 R_last_offset;
  logic [1:0]                 last_offset_next;
  logic [15:0]                R_bytes_left_to_send;
  logic [15:0]                new_bytes_left_to_send;
  logic [6:0]                 bytes_to_send_this_cycle;
  logic [3:0][3:0]            valid_bytes_per_beat;  // 0 means 16
  logic [3:0][5:0]            data_shift_per_beat;
 
generate  
  if(VSIZE==8) begin : V8_PROC
   always_comb
   begin : buffer_load_PROC
     logic [STU_D-1:0]        t_data;
     logic [STU_D/8-1:0]      t_wstrb;
     logic [6:0]              t_len;
     logic [3:0][15:0][7:0]   t_data_bytes;

     // default values
     out_valid            = '0;
     out_data             = '0;
     out_wstrb            = '0;
     fm_buffer_rd_accept  = '0;
     fm_buffer_rd_alsb    = '0;
     fm_buffer_rd_num     = '0;
     t_len                = '0;
     t_data               = '0;
     t_data_bytes         = '0;
     t_wstrb              = '0;
     xm_chnl_en           = 1'b0;

     new_bytes_left_to_send = '0;
     bytes_to_send_this_cycle = '0;
     valid_bytes_per_beat = '0;
     data_shift_per_beat = '0;
     last_offset_next = '0;
     
     
// spyglass disable_block SelfDeterminedExpr-ML W116 W164a W362 W486 W163
// SMD: Self determined expression
// SJ: Intention implement 
     //----------------------------------
     if (xm_chnl_iter_r <= 16) begin
       // simple case, 4 x beats per cycle
       bytes_to_send_this_cycle = xm_chnl_iter_r;
       valid_bytes_per_beat[0] = xm_chnl_iter_r;
       data_shift_per_beat[0] = 0;
       if (vm_valid[1]) begin
         bytes_to_send_this_cycle += xm_chnl_iter_r;
         valid_bytes_per_beat[1] = xm_chnl_iter_r;
         data_shift_per_beat[1] = xm_chnl_iter_r;
       end
       if (vm_valid[2]) begin
         bytes_to_send_this_cycle += xm_chnl_iter_r;
         valid_bytes_per_beat[2] = xm_chnl_iter_r;
         data_shift_per_beat[2] = 2 * xm_chnl_iter_r;
       end
       if (vm_valid[3]) begin
         bytes_to_send_this_cycle += xm_chnl_iter_r;
         valid_bytes_per_beat[3] = xm_chnl_iter_r;
         data_shift_per_beat[3] = 3 * xm_chnl_iter_r;
       end
     end
     //-------------------------------------
     else if (xm_chnl_iter_r <= 32) begin
       // simple case, 2 x beat per cycle
       bytes_to_send_this_cycle = xm_chnl_iter_r; 
       valid_bytes_per_beat[0] = 16;
       valid_bytes_per_beat[1] = xm_chnl_iter_r-16;
       data_shift_per_beat[0] = 0;
       data_shift_per_beat[1] = 16;
       if (vm_valid[2]) begin
         bytes_to_send_this_cycle += xm_chnl_iter_r;
         valid_bytes_per_beat[2] = 16;
         valid_bytes_per_beat[3] = xm_chnl_iter_r - 16;
         data_shift_per_beat[2] = xm_chnl_iter_r;
         data_shift_per_beat[3] = xm_chnl_iter_r+16;
       end
     end
     //------------------------------------------
     else if (xm_chnl_iter_r <= 48) begin
       // complex case, 1x/2x beat per cycle
       if (R_last_offset==0) begin
         // first alignment
         bytes_to_send_this_cycle = xm_chnl_iter_r;
         valid_bytes_per_beat[0] = 16;
         valid_bytes_per_beat[1] = 16;
         valid_bytes_per_beat[2] = xm_chnl_iter_r-32;
         data_shift_per_beat[0] = 0;
         data_shift_per_beat[1] = 16;
         data_shift_per_beat[2] = 32;
         if (vm_valid[3]) begin
           bytes_to_send_this_cycle += 16;
           valid_bytes_per_beat[3] = 16;
           data_shift_per_beat[3] = xm_chnl_iter_r;
         end
         last_offset_next = 1;
       end
       else if (R_last_offset==1) begin
         // second alignment
         bytes_to_send_this_cycle = xm_chnl_iter_r-16;
         valid_bytes_per_beat[0] = 16;
         valid_bytes_per_beat[1] = xm_chnl_iter_r-32;
         data_shift_per_beat[0] = 0;
         data_shift_per_beat[1] = 16;
         if (vm_valid[2]) begin
           bytes_to_send_this_cycle += 32;
           valid_bytes_per_beat[2] = 16;
           valid_bytes_per_beat[3] = 16;
           data_shift_per_beat[2] = xm_chnl_iter_r-16;
           data_shift_per_beat[3] = xm_chnl_iter_r;
         end
         last_offset_next = 2;
       end
       else begin
         // last alignment
         bytes_to_send_this_cycle = xm_chnl_iter_r-32;
         valid_bytes_per_beat[0] = xm_chnl_iter_r-32;
         data_shift_per_beat[0] = 0;
         if (vm_valid[1]) begin
           bytes_to_send_this_cycle += xm_chnl_iter_r;
           valid_bytes_per_beat[1] = 16;
           valid_bytes_per_beat[2] = 16;
           valid_bytes_per_beat[3] = xm_chnl_iter_r-32;
           data_shift_per_beat[1] = xm_chnl_iter_r-32;
           data_shift_per_beat[2] = xm_chnl_iter_r-16;
           data_shift_per_beat[3] = xm_chnl_iter_r;
         end
         last_offset_next = 0;              
       end
     end
     //-------------------------------------------
     else if (xm_chnl_iter_r <= 64) begin
       // simple case, 1 x beat per cycle
       bytes_to_send_this_cycle = xm_chnl_iter_r; 
       valid_bytes_per_beat[0] = 16;
       valid_bytes_per_beat[1] = 16;
       valid_bytes_per_beat[2] = 16;
       valid_bytes_per_beat[3] = xm_chnl_iter_r-48;
       data_shift_per_beat[0] = 0;
       data_shift_per_beat[1] = 16;
       data_shift_per_beat[2] = 32;
       data_shift_per_beat[3] = 48;
     end
     //-------------------------------------------
     else if (R_bytes_left_to_send > 64) begin
       // rolling count case
       // more to go, keep going
       bytes_to_send_this_cycle = 64;
       new_bytes_left_to_send = R_bytes_left_to_send - 64;
       valid_bytes_per_beat[0] = 16;
       valid_bytes_per_beat[1] = 16;
       valid_bytes_per_beat[2] = 16;
       valid_bytes_per_beat[3] = 16;
       data_shift_per_beat[0] = 0;
       data_shift_per_beat[1] = 16;
       data_shift_per_beat[2] = 32;
       data_shift_per_beat[3] = 48;
     end 
     else if (R_bytes_left_to_send<=16) begin
       // ending in this cycle, check vm_valid for more
       // 16 or less left
       if (vm_valid[1]) begin
         // another beat valid
         bytes_to_send_this_cycle = R_bytes_left_to_send+48;
         new_bytes_left_to_send = xm_chnl_iter_r-48;
         valid_bytes_per_beat[0] = R_bytes_left_to_send;
         valid_bytes_per_beat[1] = 16;
         valid_bytes_per_beat[2] = 16;
         valid_bytes_per_beat[3] = 16;
         data_shift_per_beat[0] = 0;
         data_shift_per_beat[1] = R_bytes_left_to_send;
         data_shift_per_beat[2] = R_bytes_left_to_send+16;
         data_shift_per_beat[3] = R_bytes_left_to_send+32;
       end    
       else begin
         // this is the last beat
         bytes_to_send_this_cycle = R_bytes_left_to_send;
         valid_bytes_per_beat[0] = R_bytes_left_to_send;
         data_shift_per_beat[0] = 0;
       end                   
     end
     else if (R_bytes_left_to_send<=32) begin
       // 17-32 left
       if (vm_valid[2]) begin
         // another beat valid
         bytes_to_send_this_cycle = R_bytes_left_to_send+32;
         new_bytes_left_to_send = xm_chnl_iter_r-32;
         valid_bytes_per_beat[0] = 16;
         valid_bytes_per_beat[1] = R_bytes_left_to_send-16;
         valid_bytes_per_beat[2] = 16;
         valid_bytes_per_beat[3] = 16;
         data_shift_per_beat[0] = 0;
         data_shift_per_beat[1] = 16;
         data_shift_per_beat[2] = R_bytes_left_to_send;
         data_shift_per_beat[3] = R_bytes_left_to_send+16;
       end    
       else begin
         // this is the last beat
         bytes_to_send_this_cycle = R_bytes_left_to_send;
         valid_bytes_per_beat[0] = 16;
         valid_bytes_per_beat[1] = R_bytes_left_to_send-16;
         data_shift_per_beat[0] = 0;
         data_shift_per_beat[1] = 16;
       end
     end
     else if (R_bytes_left_to_send<=48) begin
       // 33-48 left
       if (vm_valid[3]) begin
         // another beat valid
         bytes_to_send_this_cycle = R_bytes_left_to_send+16;
         new_bytes_left_to_send = xm_chnl_iter_r-16;
         valid_bytes_per_beat[0] = 16;
         valid_bytes_per_beat[1] = 16;
         valid_bytes_per_beat[2] = R_bytes_left_to_send-32;
         valid_bytes_per_beat[3] = 16;
         data_shift_per_beat[0] = 0;
         data_shift_per_beat[1] = 16;
         data_shift_per_beat[2] = 32;
         data_shift_per_beat[3] = R_bytes_left_to_send;
       end    
       else begin
         // this is the last beat
         bytes_to_send_this_cycle = R_bytes_left_to_send;
         valid_bytes_per_beat[0] = 16;
         valid_bytes_per_beat[1] = 16;
         valid_bytes_per_beat[2] = R_bytes_left_to_send-32;
         data_shift_per_beat[0] = 0;
         data_shift_per_beat[1] = 16;
         data_shift_per_beat[2] = 32;
       end                   
     end 
     else begin
       // 49-63 left
       bytes_to_send_this_cycle = R_bytes_left_to_send;
       new_bytes_left_to_send = xm_chnl_iter_r;
       valid_bytes_per_beat[0] = 16;
       valid_bytes_per_beat[1] = 16;
       valid_bytes_per_beat[2] = 16;
       valid_bytes_per_beat[3] = R_bytes_left_to_send-48;
       data_shift_per_beat[0] = 0;
       data_shift_per_beat[1] = 16;
       data_shift_per_beat[2] = 32;
       data_shift_per_beat[3] = 48;
       //----------------------------------------       
     end // else: !if(xm_chnl_iter_r <= 64)

           for (int i=0; i<S; i++)
           begin
             t_data_bytes[i] = cnst_r ? {16{zero_point_r}} : (fm_buffer_rd_data >> 8*data_shift_per_beat[i]);
             if (valid_bytes_per_beat[i]>0) begin
               // need to pad!
               for (int j=0;j<16;j++) begin
                 if (j>=valid_bytes_per_beat[i]) begin
                   t_data_bytes[i][j] = zero_point_r;
                 end
               end
             end
             t_wstrb[16*i+:16] |= vm_valid[i] ? (~vm_wmsk_r) : 16'h0000;
           end
           t_data             |= t_data_bytes;
           xm_chnl_en         = cnst_r ? 1'b0 : out_accept;
               
// spyglass enable_block SelfDeterminedExpr-ML W116 W164a W362 W486 W163

// spyglass disable_block W362
//SMD:Width mismatch
//SJ :No overflow
     // Set FM buffer read
     fm_buffer_rd_num     = bytes_to_send_this_cycle - 7'b1;
     
     if ((bytes_to_send_this_cycle>0 && fm_buffer_vld_size>=bytes_to_send_this_cycle && vm_valid!='0) || cnst_r) 
     begin
       out_valid            = 1'b1;
       out_data             = t_data;
       out_wstrb            = t_wstrb;
       fm_buffer_rd_accept  = cnst_r ? 1'b0 : out_accept;
     end

     // Set the XM chnl Iteration
     if (hlapi_i_valid) 
     begin
       xm_chnl_en             = 1'b1;
       new_bytes_left_to_send = hlapi_i.xm_seq.iter[NUM_FM_LOOPS-1];
       last_offset_next       = '0;
     end

   end : buffer_load_PROC
// spyglass enable_block W362
  end : V8_PROC
  else begin : V2_PROC
   always_comb
   begin : buffer_load_PROC
     logic [STU_D-1:0]         t_data;
     logic [STU_D/8-1:0]       t_wstrb;
     logic [6:0]               t_len;
     logic [3:0][15:0][7:0]    t_data_bytes;

     // default values
     out_valid            = '0;
     out_data             = '0;
     out_wstrb            = '0;
     fm_buffer_rd_accept  = '0;
     fm_buffer_rd_alsb    = '0;
     fm_buffer_rd_num     = '0;
     t_len                = '0;
     t_data               = '0;
     t_data_bytes         = '0;
     t_wstrb              = '0;
     xm_chnl_en           = 1'b0;

     new_bytes_left_to_send = '0;
     bytes_to_send_this_cycle = '0;
     valid_bytes_per_beat = '0;
     data_shift_per_beat = '0;
     last_offset_next = '0;
     
     
// spyglass disable_block SelfDeterminedExpr-ML W116 W164a W362 W486 W163
// SMD: Self determined expression
// SJ: Intention implement 
     //----------------------------------
     if (xm_chnl_iter_r <= 16) begin
       // simple case, 4 x beats per cycle
       bytes_to_send_this_cycle = xm_chnl_iter_r;
       valid_bytes_per_beat[0] = xm_chnl_iter_r;
       data_shift_per_beat[0] = 0;
     end
     else if (R_bytes_left_to_send > 16) begin
       bytes_to_send_this_cycle = 16;
       new_bytes_left_to_send = R_bytes_left_to_send - 16;
       valid_bytes_per_beat[0] = 16;
       data_shift_per_beat[0] = 0;
     end
     else begin
       // this is the last beat
       new_bytes_left_to_send = xm_chnl_iter_r;
       bytes_to_send_this_cycle = R_bytes_left_to_send;
       valid_bytes_per_beat[0] = R_bytes_left_to_send;
       data_shift_per_beat[0] = 0;
     end

     // select data
           for (int i=0; i<S; i++)
           begin
             t_data_bytes[i] = cnst_r ? {16{zero_point_r}} : (fm_buffer_rd_data >> 8*data_shift_per_beat[i]);
             if (valid_bytes_per_beat[i]>0) begin
               // need to pad!
               for (int j=0;j<16;j++) begin
                 if (j>=valid_bytes_per_beat[i]) begin
                   t_data_bytes[i][j] = zero_point_r;
                 end
               end
             end
             t_wstrb[16*i+:16] |= vm_valid[i] ? (~vm_wmsk_r) : 16'h0000;
           end
           t_data             |= t_data_bytes;
           xm_chnl_en         = cnst_r ? 1'b0 : out_accept;

               
// spyglass enable_block SelfDeterminedExpr-ML W116 W164a W362 W486 W163

// spyglass disable_block W362
//SMD:Width mismatch
//SJ :No overflow
     // Set FM buffer read
     fm_buffer_rd_num     = bytes_to_send_this_cycle - 7'b1;
     
     if ((bytes_to_send_this_cycle>0 && fm_buffer_vld_size>=bytes_to_send_this_cycle && vm_valid!='0) || cnst_r) 
     begin
       out_valid            = 1'b1;
       out_data             = t_data;
       out_wstrb            = t_wstrb;
       fm_buffer_rd_accept  = cnst_r ? 1'b0 : out_accept;
     end

     // Set the XM chnl Iteration
     if (hlapi_i_valid) 
     begin
       xm_chnl_en             = 1'b1;
       new_bytes_left_to_send = hlapi_i.xm_seq.iter[NUM_FM_LOOPS-1];
       last_offset_next       = '0;
     end

   end : buffer_load_PROC
// spyglass enable_block W362
  end : V2_PROC
endgenerate

   // Buffer Descr Information
  always_ff @(posedge clk or
              posedge rst_dp)
  begin : buf_descr_PROC
    if (rst_dp == 1'b1)
    begin
      vm_wmsk_r        <=  '0;
      planar_offset_r  <=  '0;
      planar_stride_r  <=  '0;
      zero_point_r     <=  '0;
      gather_r         <=  '0;
      compress_mode_r  <=  '0;
      bc_r             <=  '0;
      cnst_r           <=  '0;
      xm_chnl_iter_r   <=  '0;
    end
    else if (hlapi_i_valid)
    begin
      vm_wmsk_r        <=    hlapi_i.vm_wmsk         ;
      planar_offset_r  <=    '0                      ;
      planar_stride_r  <=    '0                      ;
      zero_point_r     <=    hlapi_i.zero_point      ;
      gather_r         <=    hlapi_i.gather          ;
      compress_mode_r  <=    '0                      ;
      bc_r             <=    hlapi_i.bc              ;
      cnst_r           <=    hlapi_i.cnst            ;
      xm_chnl_iter_r   <=    hlapi_i.xm_seq.iter[NUM_FM_LOOPS-1];
    end
  end : buf_descr_PROC

  // Iterate XM channel
  always_ff @(posedge clk or posedge rst_dp) 
  begin : Iter_XM_chnl_PROC
    if (rst_dp == 1'b1) begin
      R_last_offset        <= '0;
      R_bytes_left_to_send <= '0;
    end
    else if (xm_chnl_en) begin
      R_bytes_left_to_send <= new_bytes_left_to_send;
      R_last_offset        <= last_offset_next;
    end
  end : Iter_XM_chnl_PROC
  
  assign    hlapi_i_accept           = 1'b1;

endmodule : npu_idma_xm_process
