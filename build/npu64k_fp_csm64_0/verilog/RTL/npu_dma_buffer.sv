//----------------------------------------------------------------------------
//
// Copyright 2010-2019 Synopsys, Inc. All rights reserved.
//
// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
///////////////////////////////////////////////////////////////////////////////
//
//                       ######  #     #    #
//                       #     # ##   ##   # #
//                       #     # # # # #  #   #
//                       #     # #  #  # #     #
//                       #     # #     # #######
//                       #     # #     # #     #
//                       ######  #     # #     #
//
///////////////////////////////////////////////////////////////////////////////

module npu_dma_buffer
  import npu_types::*;
  #(
    parameter SIZEL2 = 8,         // log2 of buffer size, in 512b elements
    parameter DMA_VM_LANES_L = 4, //
    parameter AD_WID = $clog2(DMA_VM_LANES_L*ISIZE)
    )
   (
    input logic                             buffer_wr_valid,
    input logic [AD_WID-1:0]                buffer_wr_num,
    input logic [AD_WID-1:0]                buffer_wr_alsb,
    input logic [DMA_VM_LANES_L*8*ISIZE-1:0]  buffer_wr_data,
    output logic                            buffer_wr_accept,

    input logic                             buffer_rd_accept,
    input logic  [AD_WID-1:0]               buffer_rd_num,
    input logic  [AD_WID-1:0]               buffer_rd_alsb,
    output logic [DMA_VM_LANES_L*8*ISIZE-1:0] buffer_rd_data,
    output logic [15:0]                     buffer_vld_size,
    input logic                             buffer_clr,
    input logic                             clk,
    input logic                             rst_a
    );

   localparam NUM_WORDS = 1<<SIZEL2;
   localparam NUM_BYTES = DMA_VM_LANES_L*ISIZE<<SIZEL2;
   

   // the actual byte buffers
   logic [NUM_WORDS-1:0][DMA_VM_LANES_L*ISIZE-1:0][7:0] buffer_r;        

   // write and read byte pointers
   logic [SIZEL2+AD_WID-1:0]       wr_ptr_r;
   logic [SIZEL2+AD_WID-1:0]       rd_ptr_r;

   // aggregate size of the bytes held in the buffer
   logic [15:0]             buffer_vld_size_r;
   assign buffer_vld_size = buffer_vld_size_r;
   
   

   // gather incoming wr data into bytes
   logic [DMA_VM_LANES_L*ISIZE-1:0][7:0] buffer_wr_bytes;
   assign buffer_wr_bytes = buffer_wr_data;

   // what's the new write ptr?
   logic [SIZEL2+AD_WID-1:0] new_wr_ptr;
   assign new_wr_ptr = wr_ptr_r + buffer_wr_num+1;

   // what's the new read ptr?
   logic [SIZEL2+AD_WID-1:0] new_rd_ptr;
   assign new_rd_ptr = rd_ptr_r + buffer_rd_num+1;


   // update the vld_size on a read and/or a write
   always_ff @(posedge clk or posedge rst_a) begin
      if (rst_a) begin
         buffer_vld_size_r <= '0;
      end
      else if (buffer_clr) begin
         buffer_vld_size_r <= '0;
      end
      else begin
         // there's a read and a write in the same cycle
         if (buffer_wr_valid && buffer_wr_accept && buffer_rd_accept) begin
            buffer_vld_size_r <= buffer_vld_size_r + (buffer_wr_num+1) - (buffer_rd_num+1);
         end
         // there's just a read
         else if (buffer_rd_accept) begin
            buffer_vld_size_r <= buffer_vld_size_r - (buffer_rd_num+1);
         end
         // there's just a write
         else if (buffer_wr_valid && buffer_wr_accept) begin
            buffer_vld_size_r <= buffer_vld_size_r + (buffer_wr_num+1);
         end
      end
      // TODO add assertion for underflow and overflow!
   end

   // calculate the byte offset within the current word
   // also calculate the current word plus 1 (with wrap)
   logic [AD_WID-1:0] current_wr_byte_offset;
   assign current_wr_byte_offset = wr_ptr_r[AD_WID-1:0];
   logic [SIZEL2-1:0] current_wr_word;
   assign current_wr_word = wr_ptr_r[SIZEL2+AD_WID-1:AD_WID];
   logic [SIZEL2-1:0] current_wr_word_plus1;
   assign current_wr_word_plus1 = wr_ptr_r[SIZEL2+AD_WID-1:AD_WID]+1;


   // shift the incoming bytes down by alsb
   logic [DMA_VM_LANES_L*ISIZE-1:0][7:0] buffer_wr_bytes_alsb_shift_right;
   always_comb begin
      buffer_wr_bytes_alsb_shift_right = buffer_wr_bytes >> 8*buffer_wr_alsb;
   end

   // shift that up by the current write byte offset 
   logic [DMA_VM_LANES_L*ISIZE*2-1:0][7:0] buffer_wr_bytes_ptr_shift_left;
   always_comb begin
// spyglass disable_block W164b
// SMD: LHS large than RHS
// SJ: Not used all the bit in this config
      buffer_wr_bytes_ptr_shift_left = {{(DMA_VM_LANES_L*ISIZE){1'b0}},buffer_wr_bytes_alsb_shift_right} << 8*current_wr_byte_offset;
// spyglass enable_block W164b
   end

   // create a write mask for the current word and the next word
   logic [DMA_VM_LANES_L*ISIZE*2-1:0] buffer_wr_bytes_write_mask;
   logic [DMA_VM_LANES_L*ISIZE-1:0] buffer_wr_bytes_write_mask_upper;
   logic [DMA_VM_LANES_L*ISIZE-1:0] buffer_wr_bytes_write_mask_lower;
   always_comb begin
      buffer_wr_bytes_write_mask = {{(DMA_VM_LANES_L*ISIZE){1'b0}},{(DMA_VM_LANES_L*ISIZE){1'b1}}} << current_wr_byte_offset;
      buffer_wr_bytes_write_mask_upper = buffer_wr_bytes_write_mask[DMA_VM_LANES_L*ISIZE*2-1:DMA_VM_LANES_L*ISIZE];
      buffer_wr_bytes_write_mask_lower = buffer_wr_bytes_write_mask[DMA_VM_LANES_L*ISIZE-1:0];
   end

   
   // capture the wr ptr and buffer on a write
   always_ff @(posedge clk or posedge rst_a) begin
      if (rst_a) begin
         buffer_r <= '0;
         wr_ptr_r <= '0;
      end
      else if (buffer_clr) begin
         buffer_r <= '0;
         wr_ptr_r <= '0;
      end
      else begin
         // write is happening
         if (buffer_wr_valid && buffer_wr_accept) begin

            // update write ptr
            wr_ptr_r <= new_wr_ptr;

            // cycle through all words in the buffer
            for (int i=0;i<NUM_WORDS;i++) begin
               // we have one current word
               if (i==current_wr_word) begin
                  for (int j=0;j<DMA_VM_LANES_L*ISIZE;j++) begin
                     // only update bytes that are masked on
                     if (buffer_wr_bytes_write_mask_lower[j]) begin
                        buffer_r[i][j] <= buffer_wr_bytes_ptr_shift_left[j];
                     end
                  end
               end
               // now do the current word plus 1
               else if (i==current_wr_word_plus1) begin
// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self determined expression
// SJ: Intention implement 
                  for (int j=0;j<DMA_VM_LANES_L*ISIZE;j++) begin
                     // update the masked bytes here too
                     // handles the overflow of bytes from current word
                     // to next
                     if (buffer_wr_bytes_write_mask_upper[j]) begin
                        buffer_r[i][j] <= buffer_wr_bytes_ptr_shift_left[DMA_VM_LANES_L*ISIZE+j];
                     end
                  end
// spyglass enable_block SelfDeterminedExpr-ML
               end
            end           
         end
         
      end
   end

   
   // only accept a write if there's room for a full worst case 64B write
   always_comb begin
      buffer_wr_accept = (NUM_BYTES-buffer_vld_size)>=DMA_VM_LANES_L*ISIZE;
   end


   // calculate the byte offset within the current word
   // also calculate the current word plus 1 (with wrap)   
   logic [AD_WID-1:0] current_rd_byte_offset;
   assign current_rd_byte_offset = rd_ptr_r[AD_WID-1:0];
   logic [SIZEL2-1:0] current_rd_word;
   assign current_rd_word = rd_ptr_r[SIZEL2+AD_WID-1:AD_WID];
   logic [SIZEL2-1:0] current_rd_word_plus1;
   assign current_rd_word_plus1 = rd_ptr_r[SIZEL2+AD_WID-1:AD_WID]+1;


   // join the current and next words together
   logic [DMA_VM_LANES_L*ISIZE*2-1:0][7:0] buffer_rd_bytes_join;
   always_comb begin
      buffer_rd_bytes_join = {buffer_r[current_rd_word_plus1],buffer_r[current_rd_word]};
   end

   // shift this right to line up with the current read byte offset
// spyglass disable_block W486 W164a W164b
// SMD:No overflow
// SJ :buffer_rd_bytes_ptr_shift_right shift operation will not overflow 
   logic [63:0][7:0] buffer_rd_bytes_ptr_shift_right;
   always_comb begin
      buffer_rd_bytes_ptr_shift_right = buffer_rd_bytes_join >> 8*current_rd_byte_offset;
   end
// spyglass enable_block W486 W164a W164b

   // shift this left by the requested alsb
   logic [DMA_VM_LANES_L*ISIZE-1:0][7:0] buffer_rd_bytes_alsb_shift_left;
   always_comb begin
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
      buffer_rd_bytes_alsb_shift_left = buffer_rd_bytes_ptr_shift_right << 8*buffer_rd_alsb;
// spyglass enable_block W164a
   end

   // this is our output
   assign buffer_rd_data = buffer_rd_bytes_alsb_shift_left;
 
   // update read ptr on a read accept
   always_ff @(posedge clk or posedge rst_a) begin
      if (rst_a) begin
         rd_ptr_r <= '0;
      end
      else if (buffer_clr) begin
         rd_ptr_r <= '0;
      end
      else if (buffer_rd_accept) begin
         rd_ptr_r <= new_rd_ptr;
      end
   end





   
   

   /*


    // old dma buffer code
    
   
  localparam SIZE = (1 << SIZEL2) - 1; // subtract 1 because wbuf also stores an element
  logic  [511:0]        wbuf_r;              // write data buffer
  logic  [5:0]          wbuf_tail_r;         // write buffer tail, if msb set then full
  logic  [511:0]        wbuf_nxt;            // next write data buffer
  logic                 wbuf_tail_msb;       // next write buffer tail
  logic  [5:0]          wbuf_tail_nxt;       // next write buffer tail
  logic                 wbuf_tail_en;        // write buffer tail register enable
  logic  [511:0]        buffer_r[SIZE-1:0];  // main buffer
  logic  [SIZEL2:0]     wptr_r;              // buffer write pointer + msb sign
  logic  [SIZEL2:0]     rptr_r;              // buffer write pointer + msb sign
  logic  [SIZEL2:0]     wptr_nxt;            // buffer write pointer + msb sign
  logic  [SIZEL2:0]     rptr_nxt;            // buffer write pointer + msb sign
  logic                 wptr_en;             // buffer write pointer enable
  logic                 rptr_en;             // buffer read pointer enable
  logic  [511:0]        rbuf_r;              // read data buffer
  logic  [6:0]          rbuf_head_r;         // read buffer head, if msb set then empty
  logic  [6:0]          rbuf_head_nxt;       // read buffer head
  logic                 rbuf_en;             // read buffer enable
  logic                 rbuf_head_en;        // read buffer head enable
  logic                 wbuf_valid;          // valid data from write buffer to buffer
  logic                 wbuf_accept;         // accept data from write buffer to buffer
  logic  [511:0]        wbuf_data;           // data from write buffer into buffer
  logic                 buf_wr_valid;        // main buffer write valid
  logic                 buf_wr_accept;       // main buffer write accept
  logic                 buf_rd_valid;        // main buffer read valid
  logic                 buf_rd_accept;       // main buffer read accept
  logic  [511:0]        buf_rd_data;         // main buffer read data  
  logic  [SIZEL2-1:0]   wptr;                // buffer write pointer
  logic  [SIZEL2-1:0]   rptr;                // buffer write pointer
  logic                 rbuf_valid;          // valid data to read buffer from buffer
  logic                 rbuf_accept;         // accept data to read buffer from buffer
  logic  [511:0]        rbuf_data;           // data from buffer to read buffer
  logic  [511:0]        rbuf_nxt;            // fast data from buffer to read buffer
  logic  [15:0]         buffer_vld_size_nxt; // Current Valid Bytes in Buffer
  logic                 force_upd_wbuf;
  logic  [5:0]          wbuf_sft;            

  
  ///////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Control data flows
  //
  ///////////////////////////////////////////////////////////////////////////////////////////////

  // outputs: wbuf_accept, rbuf_valid, buf_wr_valid, buf_rd_accept, rbuf_data, rbuf_nxt
  assign wbuf_accept    = buf_wr_accept;
  assign rbuf_valid     = buf_rd_valid | wbuf_valid;
  assign buf_wr_valid   = wbuf_valid & (buf_rd_valid | ~rbuf_accept);
  assign buf_rd_accept  = rbuf_accept;
  assign rbuf_data      = buf_rd_valid ? buf_rd_data : wbuf_r;
  assign rbuf_nxt       = buf_rd_valid ? buf_rd_data : wbuf_data;
  
  ///////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Buffer Size calculation 
  //
  ///////////////////////////////////////////////////////////////////////////////////////////////

  always @*
    begin : buffer_vld_size_nxt_PROC
      buffer_vld_size_nxt = buffer_vld_size;

      if (buffer_clr) begin
        buffer_vld_size_nxt = 16'b0;
      end
      else begin
        if (buffer_wr_valid && buffer_wr_accept) begin
          buffer_vld_size_nxt = buffer_vld_size_nxt + buffer_wr_num + 1;
        end
        if (buffer_rd_accept) begin
          buffer_vld_size_nxt = buffer_vld_size_nxt - buffer_rd_num - 1;
        end
      end
    end
  
  ///////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Write buffer for aligning input data
  //
  ///////////////////////////////////////////////////////////////////////////////////////////////

  // align and buffer incoming write data
  // outputs: wbuf_nxt, wbuf_tail_msb, wbuf_tail_nxt, wbuf_tail_en, wbuf_valid, wbuf_data
  always @*
    begin : wbuf_nxt_PROC
      logic [2047:0] dn;
      logic [6:0]    sh;
      logic [127:0]  m;
      integer      i;
      // align write data and create a mask by shifting based on:
      //  - the position of data in the input word
      //  - the buffer fill level
      //  - the size of the data
      m                       = 128'd0;
      dn                      = 2048'd0;
      dn[511:0]               = buffer_wr_data;
      force_upd_wbuf          = 1'b0;
      case (buffer_wr_num)
        6'b000000:  m[63:0]      = 64'h0000000000000001;
        6'b000001:  m[63:0]      = 64'h0000000000000003;
        6'b000010:  m[63:0]      = 64'h0000000000000007;
        6'b000011:  m[63:0]      = 64'h000000000000000f;
        6'b000100:  m[63:0]      = 64'h000000000000001f;
        6'b000101:  m[63:0]      = 64'h000000000000003f;
        6'b000110:  m[63:0]      = 64'h000000000000007f;
        6'b000111:  m[63:0]      = 64'h00000000000000ff;
        6'b001000:  m[63:0]      = 64'h00000000000001ff;
        6'b001001:  m[63:0]      = 64'h00000000000003ff;
        6'b001010:  m[63:0]      = 64'h00000000000007ff;
        6'b001011:  m[63:0]      = 64'h0000000000000fff;
        6'b001100:  m[63:0]      = 64'h0000000000001fff;
        6'b001101:  m[63:0]      = 64'h0000000000003fff;
        6'b001110:  m[63:0]      = 64'h0000000000007fff;
        6'b001111:  m[63:0]      = 64'h000000000000ffff;
        6'b010000:  m[63:0]      = 64'h000000000001ffff;
        6'b010001:  m[63:0]      = 64'h000000000003ffff;
        6'b010010:  m[63:0]      = 64'h000000000007ffff;
        6'b010011:  m[63:0]      = 64'h00000000000fffff;
        6'b010100:  m[63:0]      = 64'h00000000001fffff;
        6'b010101:  m[63:0]      = 64'h00000000003fffff;
        6'b010110:  m[63:0]      = 64'h00000000007fffff;
        6'b010111:  m[63:0]      = 64'h0000000000ffffff;
        6'b011000:  m[63:0]      = 64'h0000000001ffffff;
        6'b011001:  m[63:0]      = 64'h0000000003ffffff;
        6'b011010:  m[63:0]      = 64'h0000000007ffffff;
        6'b011011:  m[63:0]      = 64'h000000000fffffff;
        6'b011100:  m[63:0]      = 64'h000000001fffffff;
        6'b011101:  m[63:0]      = 64'h000000003fffffff;
        6'b011110:  m[63:0]      = 64'h000000007fffffff;
        6'b011111:  m[63:0]      = 64'h00000000ffffffff;
        6'b100000:  m[63:0]      = 64'h00000001ffffffff;
        6'b100001:  m[63:0]      = 64'h00000003ffffffff;
        6'b100010:  m[63:0]      = 64'h00000007ffffffff;
        6'b100011:  m[63:0]      = 64'h0000000fffffffff;
        6'b100100:  m[63:0]      = 64'h0000001fffffffff;
        6'b100101:  m[63:0]      = 64'h0000003fffffffff;
        6'b100110:  m[63:0]      = 64'h0000007fffffffff;
        6'b100111:  m[63:0]      = 64'h000000ffffffffff;
        6'b101000:  m[63:0]      = 64'h000001ffffffffff;
        6'b101001:  m[63:0]      = 64'h000003ffffffffff;
        6'b101010:  m[63:0]      = 64'h000007ffffffffff;
        6'b101011:  m[63:0]      = 64'h00000fffffffffff;
        6'b101100:  m[63:0]      = 64'h00001fffffffffff;
        6'b101101:  m[63:0]      = 64'h00003fffffffffff;
        6'b101110:  m[63:0]      = 64'h00007fffffffffff;
        6'b101111:  m[63:0]      = 64'h0000ffffffffffff;
        6'b110000:  m[63:0]      = 64'h0001ffffffffffff;
        6'b110001:  m[63:0]      = 64'h0003ffffffffffff;
        6'b110010:  m[63:0]      = 64'h0007ffffffffffff;
        6'b110011:  m[63:0]      = 64'h000fffffffffffff;
        6'b110100:  m[63:0]      = 64'h001fffffffffffff;
        6'b110101:  m[63:0]      = 64'h003fffffffffffff;
        6'b110110:  m[63:0]      = 64'h007fffffffffffff;
        6'b110111:  m[63:0]      = 64'h00ffffffffffffff;
        6'b111000:  m[63:0]      = 64'h01ffffffffffffff;
        6'b111001:  m[63:0]      = 64'h03ffffffffffffff;
        6'b111010:  m[63:0]      = 64'h07ffffffffffffff;
        6'b111011:  m[63:0]      = 64'h0fffffffffffffff;
        6'b111100:  m[63:0]      = 64'h1fffffffffffffff;
        6'b111101:  m[63:0]      = 64'h3fffffffffffffff;
        6'b111110:  m[63:0]      = 64'h7fffffffffffffff;
        //6'b111111:  m[63:0]      = 64'hffffffffffffffff;
        default: //6'b111111
                    m[63:0]      = 64'hffffffffffffffff;
      endcase // case (buffer_wr_num)
      sh                      = {1'b0, wbuf_tail_r} - {1'b0,buffer_wr_alsb};
      dn                      = dn << {sh, 3'b000};
      m                       = m  << wbuf_tail_r;
      dn[1023:0]              = dn[1023:0] | dn[2047:1024];
      // add new data to existing data
      {wbuf_tail_msb, wbuf_tail_nxt} = {1'b0, wbuf_tail_r} + (buffer_wr_valid ? ({1'b0, buffer_wr_num} + 1) : 0);
      // update state if accepts
      wbuf_tail_en            = buffer_wr_valid & buffer_wr_accept;
      wbuf_sft                = wbuf_tail_nxt - buffer_vld_size_nxt[5:0];
      if (buffer_rd_accept && (buffer_vld_size_nxt < wbuf_tail_nxt)) begin
        wbuf_tail_nxt = buffer_vld_size_nxt;
        wbuf_tail_en  = 1'b1;
        force_upd_wbuf= 1'b1;
      end
      for (i = 0; i < 64; i = i + 1) begin
// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self determined expression (i * 8) found in module
// SJ: OK for vector range select
        wbuf_nxt[i*8+:8]      = m[i] ? dn[i*8+:8] : wbuf_r[i*8+:8];
// spyglass enable_block SelfDeterminedExpr-ML
      end
      // output to buffer if more than 16 bytes collected
      wbuf_valid              = wbuf_tail_msb;
      wbuf_data               = buffer_wr_valid ? wbuf_nxt : wbuf_r;
      if (wbuf_tail_msb) begin
        // pop 16 bytes from register
        wbuf_nxt              = dn[1023:512];
      end
      if (force_upd_wbuf) begin
        wbuf_nxt              = (wbuf_nxt >> {wbuf_sft,3'b000});
      end
      // soft reset
      if (buffer_clr) begin
        wbuf_tail_en          = 1'b1;
        wbuf_tail_nxt         = 6'd0;
      end
    end // wbuf_nxt_PROC

  // write buffer registers
  // outputs: wbuf_r, wbuf_tail_r
  always @(posedge clk or posedge rst_a)
    begin : wbuf_reg_PROC
      if (rst_a == 1'b1) begin
        wbuf_r               <= 512'd0;
        wbuf_tail_r          <= 6'd0;
      end
      else begin // !`if(rst_a == 1'b1)
        if ((buffer_wr_valid && buffer_wr_accept) || force_upd_wbuf) begin
          wbuf_r             <= wbuf_nxt;
        end
        if (wbuf_tail_en) begin
          wbuf_tail_r        <= wbuf_tail_nxt;
        end
      end // end !`if(rst_a   == 1'b1)
    end // block:wbuf_ reg_PROC


  ///////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Main buffer two port register file
  //
  ///////////////////////////////////////////////////////////////////////////////////////////////

  // main buffer
  assign wptr                 = wptr_r[SIZEL2-1:0];
  assign rptr                 = rptr_r[SIZEL2-1:0];
  assign wptr_en              = (buf_wr_valid & buf_wr_accept) | buffer_clr;
  assign rptr_en              = (buf_rd_valid & buf_rd_accept) | buffer_clr;
  assign buf_wr_accept        = (wptr != rptr) || (wptr_r[SIZEL2] == rptr_r[SIZEL2]) || buf_rd_accept;
  assign buf_rd_valid         = wptr_r != rptr_r;
  assign buf_rd_data          = buffer_r[rptr];
  
  // next state for buffer
  always @*
    begin : buf_nxt_PROC
      // update write pointer
      if (wptr == $unsigned(SIZE - 1)) begin
        // wrap and flip msb
        wptr_nxt              = {~wptr_r[SIZEL2], {SIZEL2{1'b0}}};
      end
      else begin
        wptr_nxt[SIZEL2]      = wptr_r[SIZEL2];
        wptr_nxt[SIZEL2-1:0]  = wptr + 1'b1;
      end
      // update read pointer
      if (rptr == $unsigned(SIZE - 1)) begin
        // wrap and flip msb
        rptr_nxt              = {~rptr_r[SIZEL2], {SIZEL2{1'b0}}};
      end
      else begin
        rptr_nxt[SIZEL2]      = rptr_r[SIZEL2];
        rptr_nxt[SIZEL2-1:0]  = rptr + 1'b1;
      end
      // soft reset
      if (buffer_clr) begin
        wptr_nxt              = {(SIZEL2+1){1'b0}};
        rptr_nxt              = {(SIZEL2+1){1'b0}};
      end
    end // buf_nxt_PROC

  // main buffer state
  always @(posedge clk or posedge rst_a)
    begin : buf_reg_PROC
      integer i;
      if (rst_a == 1'b1) begin
        for (i = 0; i < SIZE; i = i + 1) begin
          buffer_r[i]    <= 512'd0;
        end
        wptr_r           <= {(SIZEL2+1){1'b0}};
        rptr_r           <= {(SIZEL2+1){1'b0}};
      end
      else begin
        if (wptr_en) begin
          buffer_r[wptr] <= wbuf_data;
          wptr_r         <= wptr_nxt;
        end
        if (rptr_en) begin
          rptr_r         <= rptr_nxt;
        end
      end
    end // buf_reg_PROC


  ///////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Read buffer for aligning input data
  //
  ///////////////////////////////////////////////////////////////////////////////////////////////

  assign rbuf_en          = (rbuf_valid) & rbuf_accept;

  // read data from buffer and align
  // outputs: rbuf_head_nxt, rbuf_head_en, rbuf_accept, buffer_rd_data
  always @*
    begin : rbuf_nxt_PROC
      logic [2047:0] dn;
      logic [6:0]    sh;
      // defaults
      rbuf_head_en          = 1'b0;
      rbuf_accept           = 1'b0;
      rbuf_head_nxt         = rbuf_head_r;
      // output data by shifting data from register and next data
      sh                    = rbuf_head_r - {1'b0,buffer_rd_alsb};
      dn                    = {rbuf_data, rbuf_r, rbuf_data, rbuf_r} >> {sh, 3'b000};
      buffer_rd_data        = dn[511:0];
      if (buffer_rd_accept) begin
        // update tail pointer when data gets popped
        rbuf_head_en        = 1'b1;
        rbuf_head_nxt       = rbuf_head_r + buffer_rd_num + 1;
      end
      if (rbuf_head_nxt[6]) begin
        // all 16 consumed, buffer empty, so accept next input
        rbuf_accept         = 1'b1;
        if (rbuf_valid) begin
          rbuf_head_en      = 1'b1;
          rbuf_head_nxt[6]  = 1'b0;
        end
        else if (buffer_rd_accept) begin
          rbuf_head_en      = 1'b1;
          rbuf_head_nxt     = 7'd64;
        end
      end
      // soft reset
      if (buffer_clr) begin
        // invalidate
        rbuf_head_en        = 1'b1;
        rbuf_head_nxt       = 7'd64;            
      end
    end // rbuf_nxt_PROC

  // read buffer registers
  // outputs: rbuf_r, rbuf_head_r
  always @(posedge clk or posedge rst_a)
    begin : rbuf_reg_PROC
      if (rst_a == 1'b1) begin
        rbuf_r               <= 512'd0;
        rbuf_head_r          <= 7'd64;
      end
      else begin // !`if(rst_a == 1'b1)
        if (rbuf_en) begin
          rbuf_r             <= rbuf_nxt;
        end
        if (rbuf_head_en) begin
          rbuf_head_r        <= rbuf_head_nxt;
        end
      end // end !`if(rst_a   == 1'b1)
    end // block: rbuf_reg_PROC

  always @(posedge clk or posedge rst_a)
    begin : buffer_vld_size_PROC
      if (rst_a == 1'b1) begin
        buffer_vld_size      <= 16'd0;
      end
      else begin // !`if(rst_a == 1'b1)
        if (buffer_wr_valid || buffer_rd_accept) begin
          buffer_vld_size    <= buffer_vld_size_nxt;
        end
      end // end !`if(rst_a   == 1'b1)
    end // block: rbuf_reg_PROC

  assign buffer_wr_accept = ((wbuf_valid && wbuf_accept) || (!wbuf_valid));

    
    */
endmodule // xdma_buffer
