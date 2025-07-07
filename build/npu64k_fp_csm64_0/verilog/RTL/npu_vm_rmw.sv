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
// VM read modify write
//
 
`include "npu_defines.v"
`include "npu_vm_macros.svh"

module npu_vm_rmw
  import npu_types::*;
(
  //
  // VM Request Interface
  //
  `VMWSLV(1,in_wr_),      // VM write from source
  `VMWMST(1,out_wr_),     // VM write to vm_mux
  `VMRMST(1,rd_),         // VM read
  //
  // clock and reset
  //
  input  logic     clk,
  input  logic     rst_a
);

// VMWSLV                                   // VMWMST                                  
// input  logic       in_wr_cmd_valid       // output logic       out_wr_cmd_valid  
// output logic       in_wr_cmd_accept      // input  logic       out_wr_cmd_accept 
// input  vm_addr_t   in_wr_cmd_addr        // output vm_addr_t   out_wr_cmd_addr   
// input ixpix_t      in_wr_wdata           // output ixpix_t     out_wr_wdata      
// input ixbit_t      in_wr_wstrb           // output ixbit_t     out_wr_wstrb      
                                            // output vm_ecc_c_t  out_wr_ecc        

// VMRMST                               
// output logic       rd_cmd_valid   
// input  logic       rd_cmd_accept  
// output vm_addr_t   rd_cmd_addr    
// input  logic       rd_rvalid      
// input  ixpix_t     rd_rdata       
// input  vm_ecc_c_t  rd_ecc         

  // Local parameter 
  typedef enum logic [2:0] {
    IDLE = 3'b001, // idle state
    RD   = 3'b010, // read state
    WR   = 3'b100  // write state
  } state_t;

  state_t state_r, state_nxt;  // R-M-W fsm state
  logic state_en;              // state gating
  logic full_write;            // write 128b/64b/0b
  logic full_write_r;            
  logic rd_nxt;          // 1 cycle delay for ecc decoder processing read data

  // internal transaction and buffer signal  
  ixpix_t    int_wdata;          // latch in_wr_wdata   
  ixpix_t    int_wdata_r;        // store int_wdata  
  ixbit_t    int_wstrb;          // latch in_wr_wstrb 
  ixbit_t    int_wstrb_r;        // store int_wstrb
  logic      int_rd_cmd_valid;   // generate for rd cmd
  logic      int_rd_cmd_valid_r; // store int_rd_cmd_valid
  vm_addr_t  int_cmd_addr;       // latch in_wr_cmd_addr
  vm_addr_t  int_cmd_addr_r;     // store int_cmd_addr
  ixpix_t    bff_rdata_r;        // buffered rd_rdata
  logic      int_wr_cmd_valid;   // generate for wr cmd
  logic      int_wr_cmd_valid_r;
  ixpix_t    int_rmw_wdata;      // post r-m-w data
  
  assign state_en = |(state_r ^ state_nxt);
  always_ff @(posedge clk or posedge rst_a)
  begin : rmw_state_reg_PROC
    if(rst_a == 1'b1)
      state_r <= IDLE;
    else if (state_en)
      state_r <= state_nxt;  
  end : rmw_state_reg_PROC

  assign full_write = ((in_wr_wstrb == 'hffff) // 128b full write
                    || (in_wr_wstrb == 'h00ff) // low 64b write   
                    || (in_wr_wstrb == 'hff00) // high 64b write   
                    || (in_wr_wstrb == 'h0));  // 0b write  
  
  always_comb
  begin : rmw_state_nxt_PROC
    state_nxt = state_r;
    rd_nxt           = '0;
    in_wr_cmd_accept = '0;  
    int_rd_cmd_valid = int_rd_cmd_valid_r;
    int_wdata        = int_wdata_r;
    int_wstrb        = int_wstrb_r;
    int_cmd_addr     = int_cmd_addr_r;
    int_wr_cmd_valid = int_wr_cmd_valid_r;
    int_rmw_wdata    = bff_rdata_r;
    case(state_r)
    IDLE:
    begin
      int_rd_cmd_valid = 1'b0;
      int_wr_cmd_valid = 1'b0;
      if (in_wr_cmd_valid)
      begin
        in_wr_cmd_accept = 1'b1;  
        int_wdata = in_wr_wdata/*`upd::*/;
        int_wstrb = in_wr_wstrb;
        int_cmd_addr = in_wr_cmd_addr;
        if (full_write)
        begin
          state_nxt = WR;
          int_wr_cmd_valid = 1'b1;
        end
        else
        begin
          state_nxt = RD;
          int_rd_cmd_valid = 1'b1;
        end    
      end    
    end    
    RD:
    begin
      rd_nxt = rd_rvalid;
      if (rd_cmd_valid & rd_cmd_accept)
      begin
        int_rd_cmd_valid = 1'b0;
      end
      else if (rd_nxt)
      begin
        state_nxt = WR;
        int_wr_cmd_valid = 1'b1;
      end    
    end    
    WR:
    begin
      if (out_wr_cmd_valid & out_wr_cmd_accept)
      begin
      state_nxt = IDLE;
      int_wr_cmd_valid = 1'b0;
        if (!full_write_r)
        begin    
          for(int i=0; i < ISIZE; i++)
          begin
            if(int_wstrb_r[i])
            int_rmw_wdata[i] = int_wdata_r[i]; 
          end
        end
        else
        begin
          int_rmw_wdata = int_wdata_r; 
        end    
      end    
    end    
    default:
    begin
      state_nxt = IDLE; 
      in_wr_cmd_accept = '0;  
      int_rd_cmd_valid = '0;
      int_wr_cmd_valid = '0;
    end    
    endcase
  end : rmw_state_nxt_PROC   

  always_ff @(posedge clk or posedge rst_a)
  begin : ctrl_reg_PROC
    if(rst_a == 1'b1)
    begin
      int_rd_cmd_valid_r <= '0;
      int_wr_cmd_valid_r <= '0;
    end    
    else
    begin
      int_rd_cmd_valid_r <= int_rd_cmd_valid;
      int_wr_cmd_valid_r <= int_wr_cmd_valid;
    end    
  end : ctrl_reg_PROC   

  always_ff @(posedge clk or posedge rst_a)
  begin : bff_reg_PROC
    if (rst_a)
    begin
      int_cmd_addr_r     <= '0;
      int_wdata_r        <= '0;
      int_wstrb_r        <= '0;
      full_write_r       <= '0;
    end
    else 
    begin
      if (in_wr_cmd_valid & in_wr_cmd_accept)
      begin
        int_cmd_addr_r     <= int_cmd_addr;
        int_wdata_r        <= int_wdata;
        int_wstrb_r        <= int_wstrb;
        full_write_r       <= full_write;
      end 
      if(rd_rvalid)
      begin
        bff_rdata_r        <= rd_rdata;
      end
    end
  end : bff_reg_PROC
  

  //
  // output signal
  //
  assign rd_cmd_valid     = int_rd_cmd_valid_r;
  assign rd_cmd_addr      = int_cmd_addr_r;
  assign out_wr_cmd_valid = int_wr_cmd_valid_r;
  assign out_wr_cmd_addr  = int_cmd_addr_r;
  assign out_wr_wdata     = full_write_r? int_wdata_r : int_rmw_wdata;
  assign out_wr_wstrb     = full_write_r? int_wstrb_r : 'hffff; 
endmodule
