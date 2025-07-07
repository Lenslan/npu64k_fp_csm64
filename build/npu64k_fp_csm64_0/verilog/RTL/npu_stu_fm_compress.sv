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


//`include "npu_axi_macros.svh"
 
`include "npu_vm_macros.svh"
`include "npu_axi_macros.svh"

module npu_stu_fm_compress
  import npu_types::*;
#(
    parameter int  XM_BUF_SIZE2   = 5,
    parameter DMA_VM_LANES_L = 4, //
    parameter AD_WID = $clog2(DMA_VM_LANES_L*ISIZE)
 )
(
// spyglass disable_block W240
// SMD: Declare but Not used 
// SJ: Ignore 
   // Signals from MMIO register, controlled by valid/accept handshake
   input   logic               hlapi_i_valid,   // new HLAPI issue descriptor valid
   output  logic               hlapi_i_accept,  // new HLAPI issue descriptor accept
   input   hlapi_xm_agu_t      hlapi_i_seq,     // HLAPI input descriptor
   input   pix_t               hlapi_i_zero,    // VM ZP
// spyglass enable_block W240

   output  logic               buffer_rd_accept,
   output  logic [AD_WID-1:0]  buffer_rd_num,
   output  logic [AD_WID-1:0]  buffer_rd_alsb,
   input   logic [DMA_VM_LANES_L*8*ISIZE-1:0]       buffer_rd_data,
   input   logic [15:0]        buffer_vld_size,

   input   logic               fm_rd_accept,
   input   logic [AD_WID-1:0]  fm_rd_num,
   input   logic [AD_WID-1:0]  fm_rd_alsb,
   output  logic [DMA_VM_LANES_L*8*ISIZE-1:0]       fm_rd_data,
   output  logic [15:0]        fm_vld_size,

   output  logic               cps_len_valid,
   output  logic               cps_full,
   output  logic [13:0]        cps_blen,
   output  logic [13:0]        cps_len,
// spyglass disable_block W240
//SMD:Declared input but not read
//SJ :Ignore cps_len_accept and read_idle because no compress in config NPU_DISABLE_DMA_CPS
   input   logic               cps_len_accept,

   input   logic               read_idle,
// spyglass enable_block W240
   output  logic               idle,
   input   logic               rst_dp,          // reset compute datapath
   input   logic               clk

);

   localparam LIMIT_BUF = 2**(XM_BUF_SIZE2-1+6);
  // limited to almost full
  // also taking compressed sizei overhead into account

  typedef enum logic [1:0] { 
    fm_cps_status_idle_e,  // issue state is idle
    fm_cps_status_fm_e,    // compressed fm data
    fm_cps_status_fmsp_e,  // send split compressed data 
    fm_cps_status_meta_e   // write metadata 
  } fm_cps_state_t;

   logic       compress_r;

   
  // Internal signals
  fm_cps_state_t             fm_cps_state_r;
  fm_cps_state_t             fm_cps_state_nxt;
  logic                      fm_cps_state_en;

   // Transfer Mode
   pix_t                      zp_r;
   offset_t                   cblen_r;



   logic                     buffer_rd_accept__comp;
   logic [6:0]               buffer_rd_num__comp;
   logic                     buffer_rd_accept__nocomp;
   logic [5:0]               buffer_rd_num__nocomp;
   // mux outputs based on what mode the HLAPI is indicating
   // comp(ress) mode has an extra buffer to help with timing
   // non compress mode doesn't need to make use of this
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :1K config will be narrow but no overflow
   always_comb begin
      buffer_rd_alsb = '0;

      if (compress_r) begin
         buffer_rd_accept = buffer_rd_accept__comp;
         buffer_rd_num = buffer_rd_num__comp-1;  // subtract 1 for the output (it's an actual number)
      end
      else begin
         buffer_rd_accept = buffer_rd_accept__nocomp;
         buffer_rd_num = buffer_rd_num__nocomp; // no subtract 1, it's the same -1 formate already
      end
   end
// spyglass enable_block W164a

   // this is the extra compress shift buffer used for storing
   // data to be compressed.
   logic [7:0]               R_compress_buf_vld_size;
   logic [127:0][7:0]        R_compress_buf_data;
   logic [127:0]             R_compress_buf_data_compare;            
   logic [1023:0]            compress_buf_data_wire;
   // create a bit wire for use later 
   assign compress_buf_data_wire = R_compress_buf_data;

   // valid when data is consumed from the compress shift buffer
   logic                     compress_buf_data_consume;
   logic [6:0]               compress_buf_data_consume_num;

   // adjust the size and shift the contents of the shift buffer
   // when we're consuming some bytes
   logic [7:0]               compress_buf_vld_size_w_consume;
   logic [127:0][7:0]        compress_buf_data_w_consume;
   always_comb begin
      compress_buf_vld_size_w_consume = R_compress_buf_vld_size;
      compress_buf_data_w_consume = R_compress_buf_data;
      if (compress_buf_data_consume) begin
         compress_buf_vld_size_w_consume = R_compress_buf_vld_size - compress_buf_data_consume_num;
         compress_buf_data_w_consume = R_compress_buf_data >> (8*compress_buf_data_consume_num);
      end
   end

   // shift the incoming rd data left to align with the number
   // of bytes already in the compress shift buffer (take consumption into account)
   logic [127:0][7:0] buffer_rd_data_shift_left;
   always_comb begin
// spyglass disable_block W164b
// SMD: LHS large than RHS
// SJ: Not used all the bit in this config
      buffer_rd_data_shift_left = buffer_rd_data << (8*compress_buf_vld_size_w_consume);
// spyglass enable_block W164b
   end

   // create a load bit mask to take either existing data, or new incoming data
   logic [127:0] compress_buf_data_vld_mask;
   always_comb begin
      compress_buf_data_vld_mask = ~({128{1'b1}}<<compress_buf_vld_size_w_consume);
   end


// spyglass disable_block W164a
// SMD: Width Mismatch 
// SJ: Calculation will wrap, range limited 
   logic [127:0][7:0]        compress_buf_data_combined;
   logic [127:0]             compress_buf_data_compared;
   always_comb begin
      for (int i=0;i<128;i++) begin
         if (compress_buf_data_vld_mask[i]) begin
            compress_buf_data_combined[i] = compress_buf_data_w_consume[i];
            compress_buf_data_compared[i] = (compress_buf_data_w_consume[i]==zp_r);
         end
         else begin
            compress_buf_data_combined[i] = buffer_rd_data_shift_left[i];
            compress_buf_data_compared[i] = (buffer_rd_data_shift_left[i]==zp_r);
         end    
      end
   end    
      
   
   // logic to control when the shift buffer is updated
   logic compress_buf_upd;
   always_comb begin
      compress_buf_upd = 0;
      buffer_rd_accept__comp = 0;
      buffer_rd_num__comp = 0;
         // update when we're consuming data
         if (compress_buf_data_consume) begin
            compress_buf_upd = 1;
         end
         // and/or update when we're adding new data
         // also consume from the input rd data bus here
         // only go ahead when there's room in the compress shift buffer (<=64 existing)   
      if (compress_r) begin
         if (R_compress_buf_vld_size<=64 && buffer_vld_size>0) begin
            buffer_rd_accept__comp = 1;
            buffer_rd_num__comp = buffer_vld_size>64 ? 64 : buffer_vld_size;
            compress_buf_upd = 1;
         end
      end
   end
// spyglass enable_block W164a
   

   // update the shift buffer flops
   always_ff @(posedge clk or posedge rst_dp) begin
      if (rst_dp) begin
         R_compress_buf_vld_size <= '0;
         R_compress_buf_data <= '0;
         R_compress_buf_data_compare <= '0;
      end
      else begin
         // only capture when there are changes needed
         if (compress_buf_upd) begin
            R_compress_buf_data <= compress_buf_data_combined;
            R_compress_buf_data_compare <= compress_buf_data_compared;
            // update the size of what's held in shift buffer
// spyglass disable_block W164a
//SMD:Width missmatch
//SJ :no overflow and ignore
            R_compress_buf_vld_size <= compress_buf_vld_size_w_consume + buffer_rd_num__comp;
// spyglass enable_block W164a
         end
      end

   end

   // the 'read' data is the lowest 64B of the shift buffer.
   logic [511:0] comp_rd_data;
   logic [63:0] comp_rd_data_compare;
   always_comb begin
      comp_rd_data = compress_buf_data_wire[511:0];
      comp_rd_data_compare = R_compress_buf_data_compare[63:0];
   end
   
   

   // output buffer
  logic                              fifo_wr_valid;
  logic [AD_WID-1:0]                 fifo_wr_num;
  logic [AD_WID-1:0]                 fifo_wr_alsb;
  logic [DMA_VM_LANES_L*8*ISIZE-1:0] fifo_wr_data;
  logic                              fifo_wr_accept;

  logic                              ifm_wr_valid;
  logic [AD_WID-1:0]                 ifm_wr_num;
  logic [AD_WID-1:0]                 ifm_wr_alsb;
  logic [DMA_VM_LANES_L*8*ISIZE-1:0] ifm_wr_data;
  logic                              ifm_wr_accept;

   // rd data from output buffer
  logic                              ifm_rd_accept;
  logic [AD_WID-1:0]                 ifm_rd_num;
  logic [AD_WID-1:0]                 ifm_rd_alsb;
  logic [DMA_VM_LANES_L*8*ISIZE-1:0] ifm_rd_data;
  logic [15:0]                       ifm_vld_size;

  // compressed Counter in Sub-conatainer
  offset_t                   encode_num_r;
  offset_t                   encode_num_nxt;
  logic                      encode_num_en;

  // Compressed Block Lenth (Calculate Meta)
  logic [13:0]               cps_len_r;
  logic [13:0]               cps_len_nxt;
  logic                      cps_len_en;

  logic [13:0]               cps_blen_r;
  logic [13:0]               cps_blen_nxt;
  logic                      cps_blen_en;

  logic [3:0][15:0]               grp_hhd;   // Group x Huffman Head

  logic [3:0][127:0]              grp_data;  // Compressed Data

  logic [3:0][4:0]                grp_len;  // Compressed Data in bytes

  logic [3:0][6:0]                running_size;  // Cumulative size for each item in group
  logic [2:1][6:0]                shift_size;    // Cumulative size for each item in group

   // fully compressed output data (needs to be 64B + 8B of mask + 3B of len metadata
   logic [(75*8)-1:0]             full_wr_data;              
   logic [6:0]                    full_wr_num; // can be 0-75B
   // this holds the residue for the rare case that the compressed
   // data is > the incoming data
   logic [10:0][7:0]              full_wr_residue_r;
   logic [3:0]                    full_wr_residue_bytes_r;                        
   logic [3:0]                    full_wr_residue_bytes_nxt;                      
   logic                          full_wr_residue_bytes_en;                       
   
  logic                      finish_cps_blk;
  logic                      finish_cps_blk_pend;
  logic                      split_cps_blk;
  always_comb
  begin : fm_cps_PROC // {
    //Buffer Operation
    fifo_wr_valid        = 'b0;
    fifo_wr_num          = '0;
    fifo_wr_alsb         = '0;
    fifo_wr_data         = '0;

    ifm_rd_accept        = 'b0;
    ifm_rd_num           = '0;
    ifm_rd_alsb          = '0;

     buffer_rd_accept__nocomp   = '0;
     buffer_rd_num__nocomp      = '0;

     compress_buf_data_consume = 0;
     compress_buf_data_consume_num = '0;
     
    fm_rd_data           = '0;
    fm_vld_size          = '0;

    //Registers
    encode_num_en        = 1'b0;
    encode_num_nxt       = encode_num_r;
    cps_len_en           = 1'b0;
    cps_len_nxt          = cps_len_r;
    cps_blen_en          = 1'b0;
    cps_blen_nxt         = cps_blen_r;

    //Temporary flags
    finish_cps_blk       = 'b0;
    split_cps_blk        = 'b0;
    finish_cps_blk_pend  = 'b0;
    grp_hhd              = '0;
    grp_data             = '0;
    grp_len              = '0;
    running_size         = '0;
    shift_size           = '0;

     full_wr_data         = '0;
     full_wr_num = '0;
     full_wr_residue_bytes_nxt = '0;
     full_wr_residue_bytes_en = '0;
     


// spyglass disable_block SelfDeterminedExpr-ML W116
// SMD: Self determined expression
// SJ: Intention implement 
      // no compresion
      if (buffer_vld_size > 0) begin
        buffer_rd_accept__nocomp    =  fifo_wr_accept;
        buffer_rd_num__nocomp       =  buffer_vld_size - 1;

        fifo_wr_valid               =  1'b1;
        fifo_wr_data                =  buffer_rd_data;
        fifo_wr_num                 =  buffer_vld_size - 1;
      end
    ifm_rd_accept      = fm_rd_accept    ;
    ifm_rd_num         = fm_rd_num       ;
    ifm_rd_alsb        = fm_rd_alsb      ;
    fm_rd_data         = ifm_rd_data     ;
    fm_vld_size        = ifm_vld_size    ;
// spyglass enable_block SelfDeterminedExpr-ML W116

  end : fm_cps_PROC // }

  //
  // FM Compress next state
  //
  always_comb
  begin : fm_cps_nxt_PROC
    fm_cps_state_en     = 1'b0;
    fm_cps_state_nxt    = fm_cps_state_r;
    cps_len_valid       = 1'b0;
    cps_full            = 1'b0;
    hlapi_i_accept      = 1'b0;

    hlapi_i_accept   = 1'b1;
          
  end : fm_cps_nxt_PROC

   npu_dma_buffer
   #(.SIZEL2 (XM_BUF_SIZE2),
     .DMA_VM_LANES_L (DMA_VM_LANES_L)
    )
   u_npu_stu_fm_buffer (
    .buffer_wr_valid  (ifm_wr_valid    ),
    .buffer_wr_num    (ifm_wr_num      ),
    .buffer_wr_alsb   (ifm_wr_alsb     ),
    .buffer_wr_data   (ifm_wr_data     ),
    .buffer_wr_accept (ifm_wr_accept   ),

    .buffer_rd_num    (ifm_rd_num      ),
    .buffer_rd_alsb   (ifm_rd_alsb     ),
    .buffer_rd_data   (ifm_rd_data     ),
    .buffer_rd_accept (ifm_rd_accept   ),

    .buffer_vld_size  (ifm_vld_size    ),
    .buffer_clr       (1'b0            ),
    .rst_a            (rst_dp          ),
    .clk              (clk             )
   );

  //
  // FSM 
  //
  always_ff @(posedge clk or
              posedge rst_dp)
  begin : fsm_PROC
    if (rst_dp == 1'b1)
    begin
      fm_cps_state_r   <= fm_cps_status_idle_e;
    end
    else if (fm_cps_state_en)
    begin
// spyglass disable_block FlopEConst
//SMD:tie to constant
//SJ :Ignore fm_cps_state_r[0] because no compress
      fm_cps_state_r   <= fm_cps_state_nxt;
// spyglass enable_block FlopEConst
    end
  end : fsm_PROC

  //
  // Register assign
  //

  always_ff @(posedge clk or
              posedge rst_dp)
  begin : reg_pipe_PROC
    if (rst_dp == 1'b1)
    begin
      compress_r       <=  'b0;
      zp_r             <=  'b0;
      cblen_r          <=  'b0;
      encode_num_r   <=  'b0;
      cps_len_r      <=  'b0;
      cps_blen_r     <=  'b0;
       full_wr_residue_bytes_r <= '0;
       full_wr_residue_r <= '0; 
    end
    else 
    begin
      if (hlapi_i_valid && (fm_cps_state_r == fm_cps_status_idle_e)) begin
        compress_r       <= 1'b0;
        zp_r             <= hlapi_i_zero;
        cblen_r          <= hlapi_i_seq.cblen;
      end
// spyglass disable_block FlopEConst
//SMD:tie to constant
//SJ :Ignore encode_num_r[0], cps_len_r[0], cps_blen_r[0], full_wr_residue_bytes_r[0] because no compress
      if (encode_num_en) begin
        encode_num_r   <= encode_num_nxt;
      end
      if (cps_len_en) begin
        cps_len_r      <= cps_len_nxt;
      end
      if (cps_blen_en) begin
        cps_blen_r     <= cps_blen_nxt;
      end
       // capture the upper 11B of residue into flops
       // to write out at next opportunity
       if (full_wr_residue_bytes_en) begin
          full_wr_residue_bytes_r <= full_wr_residue_bytes_nxt;
          full_wr_residue_r <= full_wr_data[599:512];
       end
// spyglass enable_block FlopEConst
    end
  end


  // FIX: opt on timing
  npu_fifo
  #(
    .SIZE   ( 2  ),
    .DWIDTH ( DMA_VM_LANES_L*8*ISIZE+AD_WID+AD_WID )
  )
  u_wbuffer_fifo_inst
  (
     .clk          ( clk                  ),
     .rst_a        ( rst_dp               ),
     .valid_write  ( fifo_wr_valid        ),
     .accept_write ( fifo_wr_accept       ),
     .data_write   ( {fifo_wr_data, fifo_wr_num, fifo_wr_alsb}),
     .valid_read   ( ifm_wr_valid   ),
     .accept_read  ( ifm_wr_accept  ),
     .data_read    ( {ifm_wr_data,  ifm_wr_num,  ifm_wr_alsb })
  );

  // Output Assign
  assign cps_len     =  cps_len_r;
  assign cps_blen    =  cps_blen_r;
  assign idle        =  (fm_cps_state_r == fm_cps_status_idle_e);

endmodule : npu_stu_fm_compress
