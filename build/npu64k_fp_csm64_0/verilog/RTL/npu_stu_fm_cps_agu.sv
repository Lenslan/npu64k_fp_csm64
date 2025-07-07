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
// Top-level file for the FM AGU
//

 
`include "npu_vm_macros.svh"
`include "npu_axi_macros.svh"


module npu_stu_fm_cps_agu
  import npu_types::*;
  #(
    parameter DMA_VM_LANES_L = 4,
    parameter AD_WID = $clog2(DMA_VM_LANES_L*ISIZE)
   )

(
   input  logic            clk,             // clock
   input  logic            rst_a,           // asynchronous reset, active high
   // New descr issue
   input  logic            hlapi_i_valid,   // start new iteration
   output logic            hlapi_i_accept,  // acknowledge start
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore packed signal
   input  hlapi_xm_agu_t   hlapi_i_seq,     // AGU params 
// spyglass enable_block W240

   // Iterations
   output logic            fm_in_req,       // start new iteration
   input  logic            fm_in_ack,       // acknowledge start
   output offset_t [5:0]   fm_in_shp,       // shape of the iterator
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore
   input  logic            fm_it_req,       // iterator valid
   output logic            fm_it_ack,       // iterator accept
   input  logic    [5:0]   fm_it_first,     // first bits
// spyglass enable_block W240
   input  logic    [5:0]   fm_it_last,      // last bits

   // Meta Load
   input  logic            cps_len_valid,   // CPS block len valid
   input  logic            cps_full,        // CPS block full
   input  logic    [13:0]  cps_blen,        // Burst Length
   input  logic    [13:0]  cps_len,         // Container Length
   output logic            cps_len_accept,  // CPS block len accept

   output logic            meta_wr_valid,
   output logic    [AD_WID-1:0]   meta_wr_num,
   output logic    [AD_WID-1:0]   meta_wr_alsb,
   output logic    [DMA_VM_LANES_L*8*ISIZE-1:0] meta_wr_data,
   input  logic            meta_wr_accept,

   // fm status
   output logic    [31:0]  fm_len_trans,
   // fm request
   output logic            fm_valid,
// spyglass disable_block W241
//SMD:Output never set
//SJ :padm[63:40] is unused and ignore
   output xm_buf_t         fm_request,
// spyglass enable_block W241
   input  logic            fm_accept,
   output logic            boost,
   output logic [1:0]      wr_ost,

   //IDLE
   output logic            idle
);

  // Local parameters
  typedef enum logic [2:0] { 
    fm_agu_state_idle_e,     // issue state is idle
    fm_agu_state_cal_e,      // calculation ful burst & alternative iteration
    fm_agu_state_req_e,      // request iteration 
    fm_agu_state_gen_e,      // generate fm command seq 
    fm_agu_state_issue_e,    // issue the fm seq 
    fm_agu_state_sp_issue_e  // issue the fm seq 
  } fm_agu_state_t;

  // Internal signals
  fm_agu_state_t           fm_agu_state_r;
  fm_agu_state_t           fm_agu_state_nxt;
  logic                    fm_agu_state_en;

  // Iteration Check Flag
  logic       [2:0]        fm_it_check_r;
  logic       [2:0]        fm_it_check_nxt;
  // Continue Flag
  logic                    cont_r;
  logic                    cont_nxt;
  logic                    fm_it_check_en;

  // burst ptr
  xm_ptr_t                 fm_ptr_r;
  xm_ptr_t                 fm_ptr_nxt;
  logic                    fm_ptr_en;

  xm_ptr_t                 base_fm_ptr_r;
  xm_ptr_t                 base_fm_ptr_nxt;
  logic                    base_fm_ptr_en;

  logic                    fm_compress_r;
  logic                    fm_compress_nxt;

  logic                    fm_boost_r;
  logic                    fm_boost_nxt;

  logic [1:0]              fm_wr_ost_r;
  logic [1:0]              fm_wr_ost_nxt;

  // buffer ptr
  xm_buf_t                 fm_buffer_r;
  xm_buf_t                 fm_buffer_nxt;
  logic       [ASIZE:0]    fm_bufend_r;
  logic       [ASIZE:0]    fm_bufend_nxt;
  // Offsets
  xm_offset_t [5:0]        fm_offsets_r;
  xm_offset_t [5:0]        fm_offsets_nxt;
  logic                    fm_buffoffs_en;

  // repack iters to skip continuely burst
  offset_t    [5:0]        packed_iters_r;
  offset_t    [5:0]        packed_iters_nxt;
  logic       [5:0]        packed_iters_en;


  // full burst length
  logic       [31:0]       full_burst_r;
  logic                    full_burst_en;

  // rest burst length
  logic       [31:0]       rest_burst_r;
  logic       [31:0]       rest_burst_nxt;
  logic                    rest_burst_en;

  // burst length
  logic       [31:0]       len_r;
  logic       [31:0]       len_nxt;
  logic                    len_en;

  // total size
  logic       [31:0]       total_size_r;
  logic       [31:0]       total_size_nxt;
  logic                    total_size_en;

  // Iteration Next Flag
  logic                    nxt_iter_r;
  logic                    nxt_iter_nxt;
  logic                    nxt_iter_en;

  // Iter Next Offsets
  xm_offset_t              nxt_iter_oft_r;
  xm_offset_t              nxt_iter_oft_nxt;
  xm_offset_t              nxt_iter_oftb_r;
  xm_offset_t              nxt_iter_oftb_nxt;
  logic                    nxt_iter_oft_en;

  logic                    lst_issued;
  logic                    f;


  function automatic logic gen_axi_cmd(
                                       input  logic    [31:0]    ful_len,  // full burst length
                                       input  logic    [31:0]    cur_len,  // remaining burst length
                                       input  logic    [ASIZE:0] bufend,   // end of buffer + 1
                                       input  xm_ptr_t           ptr,      // running pointer
                                       output logic    [31:0]    len,      // length of current burst
                                       output logic    [31:0]    nxt_len   // length of next burst
                                      );
    // check fm request length hit wrap-back 
    // check for burst length and remaining burst
    logic              sf;
    sf = (({1'b0,ptr} + {1'b0,cur_len}) >= bufend) ? 1'b0 : 1'b1;
    if (sf) 
    begin
      len     = cur_len;
      nxt_len = ful_len;
    end
// spyglass disable_block W164a
//SMD:Width missmatch
//SJ :no overflow and ignore
    else 
    begin
      len     = bufend[ASIZE-1:0] - ptr - 1'b1;
      nxt_len = cur_len - len;
    end
// spyglass enable_block W164a
    return sf;
  endfunction : gen_axi_cmd


  // simple assignments
  assign fm_buffer_nxt   = hlapi_i_seq.buffer;
  assign fm_bufend_nxt   = {1'b0,hlapi_i_seq.buffer.base} + {1'b0,hlapi_i_seq.buffer.len} + 'd1;
  assign fm_offsets_nxt  = hlapi_i_seq.offsets;
  assign fm_boost_nxt    = hlapi_i_seq.boost[1];
  assign fm_wr_ost_nxt   = hlapi_i_seq.wr_ost;
  assign fm_compress_nxt = 1'b0;
  assign fm_request.base = fm_ptr_r;
  assign fm_request.padm = '0;
  assign fm_request.len  = len_r;
  assign fm_in_shp       = packed_iters_r;
  assign fm_it_check_nxt = fm_it_check_r == '0 ? 'd5 : fm_it_check_r - 'd1;


  always_comb
  begin : fm_ptr_upd_PROC
    xm_offset_t o;
    xm_ptr_t p;
    o = '0;
    p = '0;
    fm_ptr_nxt = '0;
      casez ({fm_compress_r,nxt_iter_r})
      2'b1?:
        begin
          // next compression container
          o |= nxt_iter_oft_r;
          p |= base_fm_ptr_r[NPU_AXI_ADDR_W-1:0];
        end
      2'b01:
        begin
          // next dimension
          o |= nxt_iter_oftb_r; // len_r + nxt_iter_oft_r - 'd1;
          p |= fm_ptr_r[NPU_AXI_ADDR_W-1:0];
        end
      default:
        begin
          // continue current burst
          o |= len_r;
          p |= fm_ptr_r[NPU_AXI_ADDR_W-1:0];
        end
      endcase // casez ({fm_compress_r,nxt_iter_r})
    if (fm_agu_state_r == fm_agu_state_idle_e)
    begin
      // new transaction
      fm_ptr_nxt |= hlapi_i_seq.ptr[ASIZE-1:0];
    end
    else
    begin
      // continue existing transaction
      fm_ptr_nxt |= incr_xm(p[NPU_AXI_ADDR_W-1:0], o, fm_buffer_r);
    end
  end : fm_ptr_upd_PROC
  

// spyglass disable_block W164a
//SMD:Width missmatch
//SJ :no overflow and ignore
  // update AGU
  always_comb
  begin : fm_agu_issue_PROC // {
    logic [31:0] lenn;
    logic [31:0] rbn;
    base_fm_ptr_nxt   =   '0;
    base_fm_ptr_en    = 1'b0;
    fm_ptr_en         = 1'b0;
    fm_buffoffs_en    = 1'b0;
    cont_nxt          = 1'b0;
    fm_it_check_en    = 1'b0;
    packed_iters_nxt  =   '0;
    packed_iters_en   = 6'd0;
    fm_valid          = 1'b0;
    full_burst_en     = 1'b0;
    rest_burst_nxt    =   '0;
    rest_burst_en     = 1'b0;
    len_nxt           =   '0;
    len_en            = 1'b0;
    nxt_iter_en       = 1'b0;
    nxt_iter_oft_nxt  =   '0;
    nxt_iter_oft_en   = 1'b0;
    total_size_nxt    =   '0;
    total_size_en     = 1'b0;
    cps_len_accept    = 1'b0;
    lst_issued        = 1'b0;
    f                 = 1'b0;
    fm_it_ack         = 1'b0;
    // precompute next address
    nxt_iter_nxt      = fm_compress_r | gen_axi_cmd(full_burst_r, rest_burst_r, fm_bufend_r, fm_ptr_r, lenn, rbn);
    // precompute next iteration offset
    for (int n = 5; n >= 0; n--)
    begin
      // looking for offsets
      if ((~fm_it_last[n]) & (~f)) 
      begin
        nxt_iter_oft_nxt |= fm_offsets_r[n];
        f                 = 1'b1;
      end
    end
    nxt_iter_oftb_nxt = nxt_iter_oft_nxt + rest_burst_r - 'd1;

    // Execute iteration
    case (fm_agu_state_r)
    fm_agu_state_idle_e:
      begin // {
        // accept new command
        base_fm_ptr_nxt  |= hlapi_i_seq.ptr[ASIZE-1:0];
        total_size_nxt   |= hlapi_i_seq.compress ? 'd0 : 'd1;
        packed_iters_nxt |= hlapi_i_seq.iter;
        base_fm_ptr_en    = hlapi_i_valid;
        fm_ptr_en         = hlapi_i_valid;
        fm_buffoffs_en    = hlapi_i_valid;
        packed_iters_en   = {6{hlapi_i_valid}};
        total_size_en     = hlapi_i_valid;
        full_burst_en     = hlapi_i_valid;
      end // }
    fm_agu_state_cal_e:
      begin // {
        logic [15:0] m;
// spyglass disable_block W164a W486 W164b
//SMD:RHS shift output is more than LHS Width
//SJ :intentional, msb need to be dropped
        m                 = packed_iters_r >> {fm_it_check_r,4'h0};
// spyglass enable_block W164a W164b W486
        fm_it_check_en    =  1'b1;
        packed_iters_nxt |= {6{16'd1}};
        // extend burst if offset is 1
        cont_nxt         |= cont_r & (((fm_offsets_r>>{fm_it_check_r,5'b0}) & 32'hFFFFFFFF) == 'd1);
        full_burst_en     = cont_nxt;
        // update iterators if burst is extended
        packed_iters_en  |= {5'd0,cont_nxt}<<fm_it_check_r;
        cont_nxt         |= fm_it_check_r == 3'd0;
        total_size_en     = 1'b1;
        total_size_nxt   |= total_size_r * m;
      end // case: fm_agu_state_cal_e // }
    fm_agu_state_req_e:
      begin // {
        // Set Remaining Burst Length to Full burst
        rest_burst_nxt      |=  full_burst_r;
        rest_burst_en        =  fm_in_ack;
      end // }
    fm_agu_state_gen_e:
      begin // {
        nxt_iter_en       =  1'b1;
        nxt_iter_oft_en   = nxt_iter_nxt;
        rest_burst_nxt   |=  rbn;
        if (fm_compress_r)
        begin
          // Generate CPS Command
          len_nxt          |=  {18'd0,cps_blen};
          len_en           |=  cps_len_valid;
          cps_len_accept    =  cps_full ? meta_wr_accept : 1'b1;
        end
        else 
        begin
          // Generate Normal Command
          len_nxt          |= lenn;
          len_en            =  1'b1;
          rest_burst_en     =  1'b1;
        end
      end // }
    default: // fm_agu_state_issue_e:
      begin // {
        fm_valid         = 1'b1;
        total_size_nxt  |= total_size_r + len_r;
        base_fm_ptr_nxt |= incr_xm(base_fm_ptr_r[NPU_AXI_ADDR_W-1:0], nxt_iter_oft_r, fm_buffer_r);
        if (fm_accept) 
        begin // {
          if (fm_compress_r == 1'b1) 
          begin
            fm_it_ack      = 1'b1;
            total_size_en  = 1'b1;
            base_fm_ptr_en = 1'b1;
          end
          else 
          begin
            fm_it_ack    = nxt_iter_r;
          end
          fm_ptr_en      = 1'b1;
          lst_issued     = nxt_iter_r & (&fm_it_last);
        end // }
      end // }
    endcase // case (fm_agu_state_r)
  end : fm_agu_issue_PROC // }
// spyglass enable_block W164a


  //
  // fm AGU next state
  //
  // fm AGU state and AXI master outputs
  // outputs: 
  always_comb
  begin : fm_agu_nxt_PROC
    hlapi_i_accept      = 1'b0;
    fm_in_req           = 1'b0;
    meta_wr_valid       = 1'b0;
    fm_agu_state_en     = 1'b0;
    fm_agu_state_nxt    = fm_agu_state_idle_e;
    case (fm_agu_state_r)
    fm_agu_state_cal_e:
      begin
        // compute max burst length
        fm_agu_state_nxt = fm_agu_state_req_e;
        fm_agu_state_en  = fm_it_check_r == 3'h0;
      end
    fm_agu_state_req_e:
      begin
        // Keep assert Iteration issue
        fm_in_req        = 1'b1;
        fm_agu_state_nxt = fm_agu_state_gen_e;
        fm_agu_state_en  = fm_in_ack;
      end
    fm_agu_state_gen_e:
      begin
        // generate new command
          // Jump to Issue when Metadata is valid or non-compress mode
          fm_agu_state_en  = 1'b1;
          fm_agu_state_nxt = fm_agu_state_issue_e;
      end
    fm_agu_state_issue_e:
      begin
        if (lst_issued) 
        begin
          fm_agu_state_en  = 1'b1;
          fm_agu_state_nxt = fm_agu_state_idle_e;
        end
        else if (fm_accept) 
        begin
          fm_agu_state_en  = 1'b1;
          fm_agu_state_nxt = fm_agu_state_gen_e;
        end
      end
    default: // fm_agu_state_idle_e
      begin
        // idle, wait for next request
        hlapi_i_accept   = 1'b1;
        fm_agu_state_en  = hlapi_i_valid;
        if (hlapi_i_seq.compress) 
        begin
          // Compress Enabled, Skip Iteration Alter 
          fm_agu_state_nxt = fm_agu_state_req_e;
        end
        else
        begin
          // Normal Enabled, Calculate FM Iter
          fm_agu_state_nxt = fm_agu_state_cal_e;
        end
      end
    endcase // casez (fm_agu_state_r)
  end : fm_agu_nxt_PROC

  
  //
  // FSM 
  //
  always_ff @(posedge clk or
              posedge rst_a)
  begin : fsm_PROC
    if (rst_a == 1'b1)
    begin
      fm_agu_state_r <= fm_agu_state_idle_e;
    end
    else if (fm_agu_state_en)
    begin
      fm_agu_state_r <= fm_agu_state_nxt;
    end
  end : fsm_PROC

  
  //
  // Register assign
  //
  always_ff @(posedge clk or
              posedge rst_a)
  begin : reg_pipe_PROC
    if (rst_a == 1'b1)
    begin
      fm_ptr_r         <= 'b0;
      base_fm_ptr_r    <= 'b0;
      fm_buffer_r      <= 'b0;
      fm_bufend_r      <= 'b0;
      fm_offsets_r     <= 'b0;
      packed_iters_r   <= 'b0;
      full_burst_r     <= 'b0;
      rest_burst_r     <= 'b0;
      cont_r           <= 'b1;
      len_r            <= 'b0;
      nxt_iter_r       <= 'b0;
      nxt_iter_oft_r   <= 'b0;
      nxt_iter_oftb_r  <= 'b0;
      total_size_r     <= 'b0;
      fm_it_check_r    <= 'h5;
      fm_compress_r    <= 'b0;
      fm_boost_r       <= 'b0;
      fm_wr_ost_r      <= 'b0;
    end
    else 
    begin
      if (fm_ptr_en)
      begin
        fm_ptr_r       <= fm_ptr_nxt;
      end
      if (base_fm_ptr_en)
      begin
        base_fm_ptr_r  <= base_fm_ptr_nxt;
      end
      if (fm_buffoffs_en)
      begin
        fm_buffer_r    <= fm_buffer_nxt;
        fm_bufend_r    <= fm_bufend_nxt;
        fm_offsets_r   <= fm_offsets_nxt;
        fm_compress_r  <= fm_compress_nxt;
        fm_boost_r     <= fm_boost_nxt;
        fm_wr_ost_r    <= fm_wr_ost_nxt;
      end
      if (len_en)
      begin
        len_r          <= len_nxt;
      end
      for (int i = 0; i < 6; i++)
      begin     
        if (packed_iters_en[i])
        begin
          packed_iters_r[i] <= packed_iters_nxt[i];
        end
      end
      if (total_size_en)
      begin
        total_size_r   <= total_size_nxt;
      end
      if (full_burst_en)
      begin
        full_burst_r   <= total_size_nxt;
      end
      if (rest_burst_en)
      begin
        rest_burst_r   <= rest_burst_nxt;
      end
      if (nxt_iter_en)
      begin
        nxt_iter_r     <= nxt_iter_nxt;
      end
      if (nxt_iter_oft_en)
      begin
        nxt_iter_oft_r  <= nxt_iter_oft_nxt;
        nxt_iter_oftb_r <= nxt_iter_oftb_nxt;
      end
      if (fm_it_check_en)
      begin
        fm_it_check_r  <= fm_it_check_nxt;
        cont_r         <= cont_nxt;
      end
    end
  end : reg_pipe_PROC
  
  // Output assign
  assign idle          = (fm_agu_state_r == fm_agu_state_idle_e);
  assign fm_len_trans  = total_size_r;

  assign meta_wr_num   = 6'h0;
  assign meta_wr_alsb  = 6'h0;
  assign meta_wr_data  = (cps_len[5:0] == 6'h0) ? ({504'b0,cps_len[13:6]} - 512'h1) : {504'b0,cps_len[13:6]};

  assign boost         = fm_boost_r;
  assign wr_ost        = fm_wr_ost_r;

endmodule : npu_stu_fm_cps_agu
