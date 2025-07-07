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
module npu_shared_hl_ctrl_dma_res
  import npu_types::*;
  #(
    parameter int NR = 4
    )
  (
   // System interface
   input  logic                    clk,             // always-on clock
   input  logic                    rst_a,           // asynchronous reset, active high, synchronous deassertion


   // From MMIO 
   input  logic                    out_rvalid,      // pending transaction
   output logic                    out_raccept,     // pending transaction done
   input  logic                    out_rlst,        // llist based descriptor
   input  npu_axi_addr_t           out_raddr,       // abse address of list descriptor

   input  logic                    hlapi_o_valid,   // new HLAPI issue descriptor valid
   output logic                    hlapi_o_accept,  // new HLAPI issue descriptor accept
   input  logic          [31:0]    hlapi_o_res,     // result from datapath to HLAPI
   input  logic          [31:0]    hlapi_o_stat,    // status 0=sucess, 1=err

   // Read IO and write IO&O
   output logic                    io_rd_req,       // request IO read
   input  logic                    io_rd_ack,       // acknowledge IO read
   input  hlapi_io_t               io_rd,           // IO write data
   output logic                    io_wr_req,       // request IO write
   input  logic                    io_wr_ack,       // acknowledge IO write
   output npu_axi_addr_t           io_addr,         // IO address
   output hlapi_io_t               io_wr,           // IO write data
   output hlapi_o_t                o_wr,            // O write data

   // Results to MMIO
   output logic                    hlapi_io_en,     // Enable IO registers
   output hlapi_io_t               hlapi_io_nxt,    // IO fields next
   input  hlapi_io_t               hlapi_io,        // IO fields
   output logic                    hlapi_o_en,      // Enable O registers
   output hlapi_o_t                hlapi_o_nxt,     // O fields next
   input  hlapi_o_t                hlapi_o          // O fields    
   );
  // local types
  typedef enum logic [3:0] { 
                             out_state_idle_e     = 4'b0001, // IDLE
                             out_state_readio_e   = 4'b0010, // Need to read IO section od descriptor
                             out_state_waitdone_e = 4'b0100, // Wait for HLAPI to complete
                             out_state_writeoio_e = 4'b1000  // Write o&io sections of desciptor&trace
                             } out_state_t;
                           
  // local wires
  logic        out_state_en;     // state register
  out_state_t  out_state_r;
  out_state_t  out_state_nxt;
  logic        cycles_en;        // cycle counter
  logic [31:0] cycles_r;
  logic [31:0] cycles_nxt;
  
  // simple assignments
  assign io_addr  = out_raddr + (((NR+'d1)>>'d1)<<'d3);
  assign io_wr    = hlapi_io;
  assign o_wr     = hlapi_o;

  // outputs: out_state_nxt, out_state_en, cycles_en, cycles_nxt, out_raccept, io_wr_req, io_rd_req, hlapi*
  always_comb
  begin : out_nxt_PROC
    // defaults
    cycles_en          = 1'b0;
    cycles_nxt         = cycles_r + 'd1;
    out_state_en       = 1'b0;
    out_state_nxt      = out_state_idle_e;
    hlapi_io_en        = 1'b0;
    hlapi_io_nxt       = io_rd;
    hlapi_o_accept     = 1'b0;
    hlapi_o_en         = 1'b0;
    hlapi_o_nxt.status = hlapi_o_stat;
    hlapi_o_nxt.res    = hlapi_o_res;
    out_raccept        = 1'b0;
    io_rd_req          = 1'b0;
    io_wr_req          = 1'b0;
    case (out_state_r)
    out_state_readio_e:
      begin
        // Need to read IO section of descriptor
        io_rd_req     = 1'b1;
        out_state_nxt = out_state_waitdone_e;
        cycles_en     = 1'b1;
        if (io_rd_ack)
        begin
          out_state_en = 1'b1;
          hlapi_io_en  = 1'b1;
        end
      end
// spyglass disable_block W164a
//SMD:Width mismatch
//SJ :No overflow
    out_state_waitdone_e:
      begin
        // Wait for HLAPI to complete
        hlapi_o_accept = 1'b1;
        hlapi_io_nxt.count   = hlapi_io.count+'d1;
        hlapi_io_nxt.cycles  = hlapi_io.cycles+cycles_r;
        cycles_en            = 1'b1;
        if (hlapi_o_valid)
        begin
          out_state_en = 1'b1;
          hlapi_io_en  = 1'b1;
          hlapi_o_en   = 1'b1;
          if (out_rlst)
          begin
            // list mode write result descriptor
            out_state_nxt = out_state_writeoio_e;
          end
          else
          begin
            // single mode skip write
            out_state_nxt = out_state_idle_e;
            out_raccept   = 1'b1;
          end
        end
      end
// spyglass enable_block W164a
    out_state_writeoio_e:
      begin
        // Write o&io sections of descriptor
        io_wr_req = 1'b1;
        out_state_nxt = out_state_idle_e;
        if (io_wr_ack)
        begin
          out_state_en = 1'b1;
          out_raccept  = 1'b1;
        end
      end
    out_state_idle_e:
      begin
        // idle
        if (out_rvalid)
        begin
          // new descriptor in FIFO
          cycles_en    = 1'b1;
          cycles_nxt   = '0;
          out_state_en = 1'b1;
          if (out_rlst)
          begin
            // list descriptor, need to read IO section
            out_state_nxt = out_state_readio_e;
          end
          else
          begin
            // single issue, skip IO read
            out_state_nxt = out_state_waitdone_e;
          end
        end
      end
    default:
      begin
        out_state_nxt = out_state_r;
        cycles_nxt    = cycles_r;
      end
    endcase // case (out_state_r)
  end : out_nxt_PROC
  
  // registers
  // outputs: out_state_r, cycles_r
  always_ff @(posedge clk or posedge rst_a)
  begin : out_reg_PROC
    if (rst_a)
    begin
      cycles_r    <= '0;
      out_state_r <= out_state_idle_e;
    end
    else
    begin
      if (out_state_en)
      begin
        out_state_r <= out_state_nxt;
      end
      if (cycles_en)
      begin
        cycles_r <= cycles_nxt;
      end      
    end
  end : out_reg_PROC
  
endmodule : npu_shared_hl_ctrl_dma_res
