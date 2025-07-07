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
// File defining the AXI master interface for controlling accelerators


`include "npu_defines.v"
`include "npu_macros.svh"
`include "npu_axi_macros.svh"

module npu_shared_hl_ctrl_dma_mst
  import npu_types::*;
  #(
    parameter int  NR       = 4,             // Number of 32b registers
    parameter int  MAXIAWUW = 1,             // AXI MMIO slave AW user width
    parameter int  MAXIWUW  = 1,             // AXI MMIO slave W user width
    parameter int  MAXIBUW  = 1,             // AXI MMIO slave B user width
    parameter int  MAXIARUW = 1,             // AXI MMIO slave AR user width
    parameter int  MAXIRUW  = 1              // AXI MMIO slave R user width
    )
  (
   // System interface
   input  logic                    clk,             // always-on clock
   input  logic                    rst_a,           // asynchronous reset, active high, synchronous deassertion
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore
   // AXI DMA master interface for reading/writing descriptors 64b wide data
   `AXIMST(1,64,MAXIAWUW,MAXIWUW,MAXIBUW,MAXIARUW,MAXIRUW,mst_axi_),
// spyglass enable_block W240
   // Descriptor read
   input  logic                    rd_descr_req,    // read a new descriptor
   output logic                    rd_descr_ack,    // finish descriptor read
   input  npu_axi_addr_t           rd_descr_addr,   // address of descriptor to read
   output logic          [NR-1:0]  rd_descr_i_en,   // I register enable
   output logic          [63:0]    rd_descr_data,   // descriptor read data

   // Descriptor append
   input  logic                    append_req,      // append a new descriptor
   output logic                    append_ack,      // acknowledge descriptor append
   input  npu_axi_addr_t           append_tail,     // address of tail
   input  npu_axi_addr_t           append_new,      // new descriptor pointer

   // Read IO and write IO&O
   input  logic                    io_rd_req,       // request IO read
   output logic                    io_rd_ack,       // acknowledge IO read
   output hlapi_io_t               io_rd,           // IO write data
   input  logic                    io_wr_req,       // request IO write
   output logic                    io_wr_ack,       // acknowledge IO write
   input  npu_axi_addr_t           io_addr,         // IO address
   input  hlapi_io_t               io_wr,           // IO write data
   input  hlapi_o_t                o_wr,            // O write data

   // common error output
   output logic                    err              // error
   );
  // local types
  typedef enum logic [11:0] { 
    dma_state_idle_e  = 12'b0000_0000_0001,  // AXI master is idle
    dma_state_dcmd_e  = 12'b0000_0000_0010,  // AXI master issues descriptor input field read command
    dma_state_drd_e   = 12'b0000_0000_0100,  // AXI master accepts descriptor input field read data
    dma_state_iocmd_e = 12'b0000_0000_1000,  // AXI master issues descriptor input&output field read command
    dma_state_iord_e  = 12'b0000_0001_0000,  // AXI master accepts descriptor input&output field read data
    dma_state_wcmd_e  = 12'b0000_0010_0000,  // AXI master issue descriptor input&output and output field write command
    dma_state_wd0_e   = 12'b0000_0100_0000,  // AXI master transfers descriptor input&output field write data
    dma_state_wd1_e   = 12'b0000_1000_0000,  // AXI master transfers descriptor output field write data
    dma_state_wb_e    = 12'b0001_0000_0000,  // AXI master waits for input&output and output field write response
    dma_state_ncmd_e  = 12'b0010_0000_0000,  // AXI master issues write command to update descriptor next field
    dma_state_nd_e    = 12'b0100_0000_0000,  // AXI master transfers write data to update descriptor next field
    dma_state_nb_e    = 12'b1000_0000_0000   // AXI master waits for write response to update descriptor next field
  } dma_state_t;
 
  // local wires
  logic                dma_state_en;    // FSM state transition enable
  dma_state_t          dma_state_r;     // FSM state register
  dma_state_t          dma_state_nxt;   // FSM state register next 
  logic                dma_cnt_en;      // Counter enable
  logic          [7:0] dma_cnt_r;       // Counter register
  logic          [7:0] dma_cnt_nxt;     // Counter register next
  logic                err_r;           // Error bit
  logic                err_nxt;         // Next error
  logic                len_en;          // command burst counter enable
  logic          [7:0] len_nxt;         // next command burst counter
  npu_axi_addr_t       addr_nxt;        // next address
  logic          [7:0] len_r;           // read command burst counter
  npu_axi_addr_t       addr_r;          // command address register


  //
  // Simple assignments
  //
  assign mst_axi_arid     = '0;
  assign mst_axi_awid     = '0;
  assign mst_axi_aruser   = '0;
  assign mst_axi_awuser   = '0;
  assign mst_axi_wuser    = '0;
  assign rd_descr_data    = mst_axi_rdata;
  assign io_rd            = mst_axi_rdata;
  assign err              = err_r;
  

  //
  // AXI FSM next state and outputs
  //
  // outputs: dma_state_en, dma_cnt_en, dma_state_nxt, dma_cnt_nxt, len_nxt, len_en, addr_nxt
  // mst_axi_arvalid, mst_axi_ar, mst_axi_rready,
  // mst_axi_awvalid, mst_axi_aw, mst_axi_wvalid, mst_axi_wdata, mst_axi_wstrb, mst_axi_wlast, mst_axi_bready
  // rd_descr_ack, append_ack, io_rd_ack, io_wr_ack, rd_descr_i_en
  always_comb
  begin : dma_nxt_PROC
    logic [7:0] len;
    // default outputs
    dma_state_en     = 1'b0;
    dma_cnt_en       = 1'b0;
    dma_state_nxt    = dma_state_idle_e;
    dma_cnt_nxt      = dma_cnt_r + 'd1;
    err_nxt          = err_r;
    len_en           = 1'b0;
    len_nxt          = '0;
    addr_nxt         = '0;
    // AXI default outputs
    mst_axi_arvalid  = 1'b0;
    mst_axi_rready   = 1'b1;
    mst_axi_awvalid  = 1'b0;
    mst_axi_wvalid   = 1'b0;
    mst_axi_wdata    = '0;
    mst_axi_wlast    = 1'b0;
    mst_axi_bready   = 1'b1;
    mst_axi_ar       = '0;
    mst_axi_ar.cache = 4'h0;   // device non-bufferable
    mst_axi_ar.prot  = 3'b010; // unprivileged, non-secure, data access
    mst_axi_ar.lock  = npu_axi_lock_normal_e;
    mst_axi_ar.burst = npu_axi_burst_incr_e;
    mst_axi_ar.len   = 8'h00;
    mst_axi_ar.size  = 3'd3;   // 64b data
    mst_axi_aw       = '0;
    mst_axi_aw.cache = 4'h0;   // device non-bufferable
    mst_axi_aw.prot  = 3'b010; // unprivileged, non-secure, data access
    mst_axi_aw.lock  = npu_axi_lock_normal_e;
    mst_axi_aw.burst = npu_axi_burst_incr_e;
    mst_axi_aw.len   = 8'h00;
    mst_axi_aw.size  = 3'd3;   // 64b data
    mst_axi_wstrb    = '1;     // all-1 write mask
    // handshake acknowledge
    rd_descr_ack     = 1'b0;
    append_ack       = 1'b0;
    io_rd_ack        = 1'b0;
    io_wr_ack        = 1'b0;
    rd_descr_i_en    = 1'b0;
    // length computation in 64b units
    len = (NR>>'d1)-1;
    case (dma_state_r)
    dma_state_dcmd_e:
      begin
        // issue a descriptor i read command
        mst_axi_arvalid = 1'b1;
        mst_axi_ar.addr |= rd_descr_addr;
        mst_axi_ar.len   = ~rd_descr_addr[3+:4];
// spyglass disable_block W164a
// spyglass disable_block W362
        if (mst_axi_ar.len >= len)
        begin
          // limit burst length
          mst_axi_ar.len = len;
        end
// spyglass enable_block W164a
// spyglass enable_block W362
        if (mst_axi_arready)
        begin
          // command accepted, so start transferring read data
          dma_state_en  = 1'b1;
          dma_state_nxt = dma_state_drd_e;
          // reset register counter
          dma_cnt_en    = 1'b1;
          dma_cnt_nxt   = 8'h00;
          // update comamnd state
          len_en   = 1'b1;
          len_nxt  = len - mst_axi_ar.len - 1'b1;
          addr_nxt = mst_axi_ar.addr + {mst_axi_ar.len,3'b000} + 'd8;
        end
      end
    dma_state_drd_e:
      begin
        // check if more commands required
        if (len_r != '1)
        begin
          mst_axi_arvalid = 1'b1;
          mst_axi_ar.addr |= addr_r;
          mst_axi_ar.len  |= len_r < 'd16 ? len_r : 'd15;
          if (mst_axi_arready)
          begin
            len_en   = 1'b1;
            len_nxt  = len_r - mst_axi_ar.len - 1'b1;
            addr_nxt = mst_axi_ar.addr + {mst_axi_ar.len,3'b000} + 'd8;
          end
        end
        // accept descriptor i read data
        mst_axi_rready = 1'b1;
        if (mst_axi_rvalid)
        begin
          // set error interrupt if not ok
          err_nxt |= mst_axi_rresp != npu_axi_resp_okay_e;
          // read descriptor data into a register pair
          for (int i = 0; i < NR/2; i++)
          begin
            if (i == dma_cnt_r)
            begin
              rd_descr_i_en[2*i+:2] = 2'b11;
            end
          end
          // increment register counter
          dma_cnt_en    = 1'b1;
          if (dma_cnt_r == len)
          begin
            // data transfers done, return to idle
            dma_state_en  = 1'b1;
            dma_state_nxt = dma_state_idle_e;
            // notify MMIO that descriptor read has finished
            rd_descr_ack = 1'b1;
          end
        end
      end
    dma_state_iocmd_e:
      begin
        // issue and descriptor io read command
        mst_axi_arvalid = 1'b1;
        mst_axi_ar.addr |= io_addr;
        mst_axi_ar.len  |= '0; // IO fields has one 64 bits register
        if (mst_axi_arready)
        begin
          // command accepted, so start transferring read data
          dma_state_en  = 1'b1;
          dma_state_nxt = dma_state_iord_e;
        end
      end
    dma_state_iord_e:
      begin
        // accept descriptor io read data
        mst_axi_rready = 1'b1;
        if (mst_axi_rvalid)
        begin
          // set error interrupt if not ok
          err_nxt |= mst_axi_rresp != npu_axi_resp_okay_e;
          if (mst_axi_rlast)
          begin
            // data transfers done, return to idle
            dma_state_en  = 1'b1;
            dma_state_nxt = dma_state_idle_e;
            io_rd_ack     = 1'b1;
          end
        end
      end
    dma_state_wcmd_e:
      begin
        // issue a descriptor io&o write command
        mst_axi_awvalid = 1'b1;
        mst_axi_aw.addr |= io_addr;
        mst_axi_aw.len  |= 'd1; // IO fields has 64bits register, O fields has 64bits register
        if (mst_axi_awready)
        begin
          // command accepted, so start transferring write data
          dma_state_en  = 1'b1;
          dma_state_nxt = dma_state_wd0_e;
        end
      end
    dma_state_wd0_e:
      begin
        // transfer io write data
        mst_axi_wvalid = 1'b1;
        mst_axi_wdata  |= io_wr;
        if (mst_axi_wready)
        begin
          dma_state_en   = 1'b1;
          dma_state_nxt  = dma_state_wd1_e;
        end
      end
    dma_state_wd1_e:
      begin
        // transfer io write data
        mst_axi_wvalid = 1'b1;
        mst_axi_wdata  |= o_wr;
        mst_axi_wlast  = 1'b1;
        if (mst_axi_wready)
        begin
          dma_state_en   = 1'b1;
          dma_state_nxt  = dma_state_wb_e;
        end
      end
    dma_state_wb_e:
      begin
        // accept io&o write response
        mst_axi_bready = 1'b1;
        if (mst_axi_bvalid)
        begin
          err_nxt       |= mst_axi_bresp != npu_axi_resp_okay_e;
          dma_state_en   = 1'b1;
          dma_state_nxt  = dma_state_idle_e;
          io_wr_ack      = 1'b1;
        end
      end
    dma_state_ncmd_e:
      begin
        // issue a descripor append command
        mst_axi_awvalid = 1'b1;
        mst_axi_aw.addr |= append_tail;
        mst_axi_aw.len  |= 'd0;
        if (mst_axi_awready)
        begin
          // write data accepted, accept next
          dma_state_en  = 1'b1;
          dma_state_nxt = dma_state_nd_e;
        end
      end
    dma_state_nd_e:
      begin
        // transfer next pointer update write data
        mst_axi_wvalid = 1'b1;
        mst_axi_wlast  = 1'b1;
        mst_axi_wdata  |= {{(64-NPU_AXI_ADDR_W){1'b0}},append_new};
        if (mst_axi_wready)
        begin
          // write data, wait for response
          dma_state_en  = 1'b1;
          dma_state_nxt = dma_state_nb_e;
        end
      end
    dma_state_nb_e:
      begin
        // transfer next pointer response
        mst_axi_bready = 1'b1;
        if (mst_axi_bvalid)
        begin
          // set error interrupt if not ok
          err_nxt      |= mst_axi_bresp != npu_axi_resp_okay_e;
          // response accepted, go back to idle
          dma_state_en  = 1'b1;
          dma_state_nxt = dma_state_idle_e;
          append_ack    = 1'b1;
        end
      end
    dma_state_idle_e:
      begin
        // idle, wait for next request
        err_nxt       = 1'b0;
        casez ({io_wr_req,io_rd_req,append_req,rd_descr_req})
        4'b1???:
          begin
            // compute is done, timestamp has been read, write-back result
            dma_state_en  = 1'b1;
            dma_state_nxt = dma_state_wcmd_e;
          end
        4'b01??:
          begin
            // compute has been issued but IO cycle/time not read yet
            dma_state_en  = 1'b1;
            dma_state_nxt = dma_state_iocmd_e;
          end
        4'b001?:
          begin
            // append a new descriptor to the list
            dma_state_en  = 1'b1;
            dma_state_nxt = dma_state_ncmd_e;
          end
        4'b0001:
          begin
            // need to read the descriptor
            dma_state_en    = 1'b1;
            dma_state_nxt   = dma_state_dcmd_e;
          end
        endcase // casez ({io_wr_req,io_rd_req,append_req,rd_descr_req})
      end
    default:
    begin
      dma_state_nxt = dma_state_r;
      dma_cnt_nxt   = dma_cnt_r;
      mst_axi_rready = 1'b0;
      mst_axi_bready = 1'b0;
    end
    endcase // casez (dma_state_r)
  end : dma_nxt_PROC


  // AXI master registers
  // outputs: dma_state_r, dma_cnt_r, err_r, len_r, addr_R
  always_ff @(posedge clk or
              posedge rst_a)
  begin : dma_reg_PROC
    if (rst_a == 1'b1)
    begin
      dma_state_r <= dma_state_idle_e;
      dma_cnt_r   <= 8'h00;
      err_r       <= 1'b0;
      addr_r      <= '0;
      len_r       <= '0;
    end
    else 
    begin
      err_r <= err_nxt;
      if (dma_state_en)
      begin
        dma_state_r <= dma_state_nxt;
      end
      if (dma_cnt_en)
      begin
        dma_cnt_r   <= dma_cnt_nxt;
      end
      if (len_en)
      begin
        addr_r      <= addr_nxt;
        len_r       <= len_nxt;
      end
    end
  end : dma_reg_PROC

endmodule : npu_shared_hl_ctrl_dma_mst
