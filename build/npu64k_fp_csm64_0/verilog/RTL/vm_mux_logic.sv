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
// Top-level demo file for the VM BUS 
//
 
`include "npu_defines.v"
`include "npu_vm_macros.svh"
`include "npu_vm_ecc_macros.sv"

`ifndef NPU_ECC_TYPES_IMPORTED
`define NPU_ECC_TYPES_IMPORTED
import npu_ecc_types::*;
`endif  

module vm_mux_logic
  import npu_types::*;
#(
    parameter VM_RPORTS=(((NUM_FM_QUEUE+NUM_COEF_QUEUE+CONV_PAD_LD_LANES+VSIZE+GTOA_BPAR_LD_LANES+GTOA_MPST_LANES+DMA_VM_LANES)+1)+1),
    parameter VM_WPORTS=((VSIZE+GTOA_MPST_LANES+DMA_VM_LANES)+1),
    parameter NUM_VM_BANKS=((VSIZE==8)?32:16),
    parameter int WWID = 16-$clog2(NUM_VM_BANKS)+ISIZE*9
   )
  (

   input  logic     [VM_WPORTS-1:0]     nn_vm_wr_cmd_valid,  // write command valid
   output logic     [VM_WPORTS-1:0]     nn_vm_wr_cmd_accept, // write command accept
   input  vm_addr_t [VM_WPORTS-1:0]     nn_vm_wr_cmd_addr,   // write command address
   // write data channel
   input  ixpix_t   [VM_WPORTS-1:0]     nn_vm_wr_wdata,      // write data
   input  ixbit_t   [VM_WPORTS-1:0]     nn_vm_wr_wstrb,      // write strobe
   // read request
   input  logic     [VM_RPORTS-1:0]     nn_vm_rd_cmd_valid,  // read command valid
   output logic     [VM_RPORTS-1:0]     nn_vm_rd_cmd_accept, // read command accept
   input  vm_addr_t [VM_RPORTS-1:0]     nn_vm_rd_cmd_addr,   // read command address
   // read data channel
   output logic     [VM_RPORTS-1:0]     nn_vm_rd_rvalid,     // read data valid
   
   // muxed request
   input  logic     [NUM_VM_BANKS-1:0]  vm_mem_en,  // load enable

   //
   // vm ecc
   //
   input  logic                      vm_prot_en,
   
   output logic       [NUM_VM_BANKS-1:0] [VM_NUM_ECC-1:0]    nn_vm_wr_ecc_wstrb_nxt,  // port2bank write ecc msk

// input signals
   input  logic       [VM_RPORTS-1:0][2:0][NUM_VM_BANKS-1:0] bank_r,
   input  logic       [NUM_VM_BANKS-1:0]                     wfifo_waccept,
   input  logic       [NUM_VM_BANKS-1:0]                     wfifo_rvalid,
   input  logic       [NUM_VM_BANKS-1:0][WWID-1:0]           wfifo_rdata,
   input  logic       [NUM_VM_BANKS-1:0]                     wfifo_prio,

// output signals
   output logic       [VM_RPORTS-1:0][2:0]                   bank_en,            
   output logic       [VM_RPORTS-1:0][2:0][NUM_VM_BANKS-1:0] bank_nxt,           
   output logic       [NUM_VM_BANKS-1:0]                     vm_mem_en_nxt,      
   output logic       [NUM_VM_BANKS-1:0]                     vm_cmd_en,          
   output logic       [NUM_VM_BANKS-1:0]                     vm_ldst_en_nxt,      
   output ixbit_t     [NUM_VM_BANKS-1:0]                     nn_vm_wr_wstrb_nxt, 
   output logic       [NUM_VM_BANKS-1:0]                     nn_vm_wr_en,
   output logic       [NUM_VM_BANKS-1:0]                     ren,
   output logic       [NUM_VM_BANKS-1:0]                     vm_ls_nxt,
   output logic       [NUM_VM_BANKS-1:0]                     wfifo_wvalid,
   output logic       [NUM_VM_BANKS-1:0][WWID-1:0]           wfifo_wdata,
   output logic       [NUM_VM_BANKS-1:0]                     wfifo_raccept,
   // vm initialization
   input logic      vm_init,
   //
   // clock and rst_a
   //
   input logic      clk,                   // clock, all logic clocked at posedge
   input logic      rst_a                  // asynchronous rst_a, active high


  );

  localparam VM_PORTS_WIDTH=$clog2(NUM_VM_BANKS);
  
  logic mem_ecc_en;
  assign mem_ecc_en = vm_prot_en;
  logic       [VM_WPORTS-1:0]                     mpst_wr_cmd_accept;

  // light sleep when memory access is done
  assign vm_ls_nxt = ~(vm_mem_en_nxt | vm_mem_en);

// spyglass disable_block W362
//SMD:Width mismatch for operation ==
//SJ :32 bits unsigned'(i) can be used for operation (==)
  // write arbitration
  always_comb
  begin : vm_wbus_ack_PROC
    // default
    wfifo_wvalid                    = '0;
    wfifo_wdata                     = '0;
    nn_vm_wr_cmd_accept             = mpst_wr_cmd_accept;
    for (int i=0; i<NUM_VM_BANKS; i++) 
    begin //{
      // write arbitration per bank
      for (int m=0; m<VSIZE; m++)
      begin //{
        // GTOA main ports
        if ((nn_vm_wr_cmd_addr[m][VM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_vm_wr_cmd_valid[m]) 
        begin // select write operation
          if (~wfifo_wvalid[i])
          begin
            nn_vm_wr_cmd_accept[m]  = wfifo_waccept[i];
            wfifo_wdata[i]         |= {nn_vm_wr_cmd_addr[m][15:VM_PORTS_WIDTH], nn_vm_wr_wdata[m], nn_vm_wr_wstrb[m]};
          end
          wfifo_wvalid[i]          |= 1'b1;
        end
      end //}
      // no arbitration on GTOA MPST_WR
      for (int m=VSIZE+GTOA_MPST_LANES; m<VM_WPORTS; m++)
      begin //{
        // iDMA ports
        if ((nn_vm_wr_cmd_addr[m][VM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_vm_wr_cmd_valid[m]) 
        begin // select write operation
          if (~wfifo_wvalid[i])
          begin
            nn_vm_wr_cmd_accept[m]  = wfifo_waccept[i];
            wfifo_wdata[i]         |= {nn_vm_wr_cmd_addr[m][15:VM_PORTS_WIDTH], nn_vm_wr_wdata[m], nn_vm_wr_wstrb[m]};
          end
          wfifo_wvalid[i]          |= 1'b1;
        end
      end //}
    end //}
  end : vm_wbus_ack_PROC
// spyglass enable_block W362

 // arbitration per bank
  logic [$bits(ixbit_t)-1:0] vm_wr_wstrb_tmp; 
  always_comb
  begin : vm_bus_ack_PROC
    logic f;
    bank_en             = '0;
    bank_nxt            = '0;
    vm_mem_en_nxt       = '0;
    vm_cmd_en           = '0;
    vm_ldst_en_nxt      = '0;
    nn_vm_rd_cmd_accept = '0;
    nn_vm_wr_wstrb_nxt  = '0;
    nn_vm_wr_en         = '0;
    vm_wr_wstrb_tmp     = '1;
    wfifo_raccept       = '0;
    mpst_wr_cmd_accept  = '0;
    // shift bank next
    for (int r = 0; r < VM_RPORTS; r++)
    begin
      bank_nxt[r][2:1] = bank_r[r][1:0];
      bank_en[r][2]    = bank_r[r][2:1] != '0;
      bank_en[r][1]    = bank_r[r][1:0] != '0;
      bank_en[r][0]    = bank_r[r][0]   != '0;
    end

// spyglass disable_block W362
// SMD: an arithmetic comparison operator with unequal length
// SJ: it's compare to the int type, no side effects
    for (int i=0; i<NUM_VM_BANKS; i++) 
    begin //{
      if (vm_init) begin
        vm_mem_en_nxt[i]       |= 1'b1;
        vm_cmd_en[i]           |= 1'b1;                       //enable memory
        vm_ldst_en_nxt[i]      |= 1;
        nn_vm_wr_en[i]         |= 1;
        nn_vm_wr_wstrb_nxt[i]  |= vm_wr_wstrb_tmp;
      end
      f = wfifo_prio[i];
      // conv and gtoa read have highest priority
      for (int n=0; n<NUM_FM_QUEUE+NUM_COEF_QUEUE+CONV_PAD_LD_LANES+VSIZE+GTOA_BPAR_LD_LANES+GTOA_MPST_LANES; n++)
      begin //{
        if ((nn_vm_rd_cmd_addr[n][VM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_vm_rd_cmd_valid[n]) 
        begin    //select read operation
          nn_vm_rd_cmd_accept[n] |= ~f;                         //accept read
          bank_en[n][0]          |= ~f;
          bank_nxt[n][0][i]      |= ~f;                         //record port info for data return
          vm_mem_en_nxt[i]       |= 1'b1;                       //enable memory
          vm_cmd_en[i]           |= 1'b1;
          f                      |= 1'b1;
        end
      end //}

      // pool write ports
      for (int n=VSIZE; n<VSIZE+GTOA_MPST_LANES; n++) 
      begin //{
        if ((nn_vm_wr_cmd_addr[n][VM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_vm_wr_cmd_valid[n]) 
        begin    //select read operation
          mpst_wr_cmd_accept[n]  |= ~f;                         //accept write
          vm_mem_en_nxt[i]       |= 1'b1;                       //enable memory
          vm_cmd_en[i]           |= 1'b1;
          vm_ldst_en_nxt[i]      |= ~f;
          nn_vm_wr_en[i]         |= ~f;
          nn_vm_wr_wstrb_nxt[i]  |= f ? '0 : nn_vm_wr_wstrb[n];
          f                      |= 1'b1;
        end
      end //}
      
      // write ports have second highest priority and highest if priority inverted
      f &= ~wfifo_prio[i];
      if (wfifo_rvalid[i]) 
      begin // select write operation
        wfifo_raccept[i]       |= ~f;                         //accept write
        vm_mem_en_nxt[i]       |= 1'b1;
        vm_cmd_en[i]           |= 1'b1;                       //enable memory
        vm_ldst_en_nxt[i]      |= ~f;
        nn_vm_wr_en[i]         |= ~f;
        nn_vm_wr_wstrb_nxt[i]  |= f ? '0 : wfifo_rdata[i][0+:ISIZE];
        f                      |= 1'b1;
      end //}

      // rest
      for (int n=NUM_FM_QUEUE+NUM_COEF_QUEUE+CONV_PAD_LD_LANES+VSIZE+GTOA_BPAR_LD_LANES+GTOA_MPST_LANES; n<VM_RPORTS; n++)
      begin //{
        if ((nn_vm_rd_cmd_addr[n][VM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_vm_rd_cmd_valid[n])
        begin    //select read operation
          nn_vm_rd_cmd_accept[n] |= ~f;                         //accept read
          bank_en[n][0]          |= ~f;
          bank_nxt[n][0][i]      |= ~f;                         //record port info for data return
          vm_mem_en_nxt[i]       |= 1'b1;                       //enable memory
          vm_cmd_en[i]           |= 1'b1;
          f                      |= 1'b1;
        end
      end //}

    end //}
// spyglass enable_block W362
  end : vm_bus_ack_PROC

  localparam CFG_NPU_MEM_ECC = 1;
  always_comb
  begin : vm_ecc_PROC
    logic f;
    nn_vm_wr_ecc_wstrb_nxt  = '0;

// spyglass disable_block W362
// SMD: an arithmetic comparison operator with unequal length
// SJ: it's compare to the int type, no side effects
    for (int i=0; i<NUM_VM_BANKS; i++) 
    begin //{
      if (vm_init)
      begin 
          nn_vm_wr_ecc_wstrb_nxt[i][0] |= mem_ecc_en;
          nn_vm_wr_ecc_wstrb_nxt[i][1] |= mem_ecc_en;
      end
      f = wfifo_prio[i];
      // conv and gtoa read have highest priority
      for (int n=0; n<NUM_FM_QUEUE+NUM_COEF_QUEUE+CONV_PAD_LD_LANES+VSIZE+GTOA_BPAR_LD_LANES+GTOA_MPST_LANES; n++)
      begin //{
        if ((nn_vm_rd_cmd_addr[n][VM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_vm_rd_cmd_valid[n]) 
        begin    //select read operation
          f                      |= 1'b1;
        end
      end //}
      // pool write ports
      for (int n=VSIZE; n<VSIZE+GTOA_MPST_LANES; n++) 
      begin //{
        if ((nn_vm_wr_cmd_addr[n][VM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_vm_wr_cmd_valid[n]) 
        begin    //select read operation
// spyglass disable_block SelfDeterminedExpr-ML
//SMD:Self determined expression (j + (ISIZE / VM_NUM_ECC))
//SJ :Ignore
          for (int j=0; j<ISIZE/VM_NUM_ECC; j++)
          begin    
            nn_vm_wr_ecc_wstrb_nxt[i][0] |= mem_ecc_en & nn_vm_wr_wstrb[n][j];
            nn_vm_wr_ecc_wstrb_nxt[i][1] |= mem_ecc_en & nn_vm_wr_wstrb[n][j+(ISIZE/VM_NUM_ECC)];
          end 
// spyglass enable_block SelfDeterminedExpr-ML
          f                      |= 1'b1;
        end
      end //}
      // write ports have second highest priority and highest if priority inverted
      f &= ~wfifo_prio[i];
      if (wfifo_rvalid[i]) 
      begin // select write operation
// spyglass disable_block SelfDeterminedExpr-ML
//SMD:Self determined expression (j + (ISIZE / VM_NUM_ECC))
//SJ :Ignore
        for (int j=0; j<ISIZE/VM_NUM_ECC; j++)
        begin    
          nn_vm_wr_ecc_wstrb_nxt[i][0] |= mem_ecc_en & wfifo_rdata[i][j];
          nn_vm_wr_ecc_wstrb_nxt[i][1] |= mem_ecc_en & wfifo_rdata[i][j+(ISIZE/VM_NUM_ECC)];
        end 
// spyglass enable_block SelfDeterminedExpr-ML
        f                        |= 1'b1;
      end //}

      // rest
      for (int n=NUM_FM_QUEUE+NUM_COEF_QUEUE+CONV_PAD_LD_LANES+VSIZE+GTOA_BPAR_LD_LANES+GTOA_MPST_LANES; n<VM_RPORTS; n++)
      begin //{
        if ((nn_vm_rd_cmd_addr[n][VM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_vm_rd_cmd_valid[n])
        begin    //select read operation
          f                      |= 1'b1;
        end
      end //}
    end //}
// spyglass enable_block W362
  end : vm_ecc_PROC  

  ///////////////////get load data and data valid/////////////////////////////
  always_comb
  begin: vm_bus_rdata_PROC
    ren             = '0;
    nn_vm_rd_rvalid = '0;
    
    for (int n=0; n<VM_RPORTS; n++) // {
    begin
      nn_vm_rd_rvalid[n] = bank_r[n][2] != '0;
      for (int i=0; i<NUM_VM_BANKS; i++) //{
      begin
        ren[i] |= bank_r[n][1][i];         // enable read data register
      end //}
    end //}
  end : vm_bus_rdata_PROC

  

endmodule : vm_mux_logic
