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
// spyglass disable_block W240
// SMD: Declared but not read
// SJ: Reviewed
module vm_mux
  import npu_types::*;
  #(
    parameter VM_RPORTS=(((NUM_FM_QUEUE+NUM_COEF_QUEUE+CONV_PAD_LD_LANES+VSIZE+GTOA_BPAR_LD_LANES+GTOA_MPST_LANES+DMA_VM_LANES)+1)+1),
    parameter VM_WPORTS=((VSIZE+GTOA_MPST_LANES+DMA_VM_LANES)+1),
    parameter NUM_VM_BANKS=((VSIZE==8)?32:16),
    parameter int WWID = 16-$clog2(NUM_VM_BANKS)+ISIZE*9
   )
  (
   //
   // interfaces
   //
   // write request
   `VMWSLV(VM_WPORTS,nn_vm_wr_),
   // read request
   `VMRSLV(VM_RPORTS,nn_vm_rd_),
   
   // muxed request
   `VMMST(NUM_VM_BANKS,vm_),

   //
   // vm ecc
   //
   input  logic          vm_prot_en,
   // vm mem access interface
   `VMMST_ECC(NUM_VM_BANKS,vm_),
   
   // vm port access interface
//TBD remove//   `VMRSLV_ECC_RPT(NUM_VM_BANKS,nn_vm_rd_),
   output logic                      vm_sb_err,
   output logic                      vm_db_err,

   // vm initialization
   input logic      vm_init,
   output logic     vm_init_end,

   // vm write fifo
   output logic       [NUM_VM_BANKS-1:0]           wfifo_wvalid,
   input  logic       [NUM_VM_BANKS-1:0]           wfifo_waccept,
   output logic       [NUM_VM_BANKS-1:0][WWID-1:0] wfifo_wdata,
   input  logic       [NUM_VM_BANKS-1:0]           wfifo_rvalid,
   output logic       [NUM_VM_BANKS-1:0]           wfifo_raccept,
   input  logic       [NUM_VM_BANKS-1:0][WWID-1:0] wfifo_rdata,
   input  logic       [NUM_VM_BANKS-1:0]           wfifo_prio,

   //test mode
   input logic      test_mode,
   //
   // clock and rst_a
   //
   input logic      clk,                   // clock, all logic clocked at posedge
   input logic      rst_a                  // asynchronous rst_a, active high
  );
// spyglass enable_block W240
  localparam VM_PORTS_WIDTH=$clog2(NUM_VM_BANKS);

  // 3-stage delay line type onehot0 on inner dimension
  typedef logic [VM_RPORTS-1:0][2:0][NUM_VM_BANKS-1:0] bank_t;

  // command wires  
  logic       [NUM_VM_BANKS-1:0]     vm_mem_en_r;
  logic       [NUM_VM_BANKS-1:0]     vm_mem_en_nxt;
  logic       [NUM_VM_BANKS-1:0]     vm_ls_r;
  logic       [NUM_VM_BANKS-1:0]     vm_ls_nxt;
  logic       [NUM_VM_BANKS-1:0]     vm_cmd_en;
  logic       [NUM_VM_BANKS-1:0]     vm_ldst_en_r;
  logic       [NUM_VM_BANKS-1:0]     vm_ldst_en_nxt;
  vm_addr_t   [NUM_VM_BANKS-1:0]     vm_addr_r;
  vm_addr_t   [NUM_VM_BANKS-1:0]     vm_addr_nxt;
  // write data wires
  ixpix_t     [NUM_VM_BANKS-1:0]     nn_vm_wr_wdata_nxt;
  ixbit_t     [NUM_VM_BANKS-1:0]     nn_vm_wr_wstrb_nxt;
  ixpix_t     [NUM_VM_BANKS-1:0]     nn_vm_wr_wdata_r;
  ixbit_t     [NUM_VM_BANKS-1:0]     nn_vm_wr_wstrb_r;
  logic       [NUM_VM_BANKS-1:0]     nn_vm_wr_en;
  
  // Read data buffer
  logic       [NUM_VM_BANKS-1:0]     ren;
  ixpix_t     [NUM_VM_BANKS-1:0]     nn_vm_rd_rdata_r;

  // vm initialization
  vm_addr_t  vm_init_wr_cmd_addr; // vm init write command address
  logic vm_init_busy;
  // mem ecc
  logic       [NUM_VM_BANKS-1:0] [VM_NUM_ECC-1:0] nn_vm_wr_ecc_wstrb_nxt;  // port2bank write ecc msk
  vm_ecc_c_t  [NUM_VM_BANKS-1:0]                  nn_vm_wr_ecc_r;          // write buffered wr_ecc, to vm_wecc
  logic       [NUM_VM_BANKS-1:0] [VM_NUM_ECC-1:0] nn_vm_wr_ecc_wstrb_r;    // write buffered wr_ecc msk, to vm_ecc_wstrb
  vm_ecc_c_t  [NUM_VM_BANKS-1:0]                  nn_vm_rd_ecc_r;          // read buffered rd_ecc,  from vm_recc
  vm_ecc_c_t  [NUM_VM_BANKS-1:0]                  nn_vm_wr_ecc_nxt;
  logic                                           db_err_aggr;
  logic                                           sb_err_aggr;
  logic                                           db_err_aggr_r;
  logic                                           sb_err_aggr_r;

  // bank delay line
  logic       [VM_RPORTS-1:0][2:0]   bank_en;
  bank_t                             bank_r;
  bank_t                             bank_nxt;

  vm_mux_reg
  #(
    .NUM_VM_BANKS(NUM_VM_BANKS),
    .VM_RPORTS(VM_RPORTS)
  )
  u_vm_mux_reg
  (
    
    .vm_mem_en_nxt             (vm_mem_en_nxt         ),
    .vm_ls_nxt                 (vm_ls_nxt             ),
    .vm_ldst_en_nxt            (vm_ldst_en_nxt        ),
    .vm_addr_nxt               (vm_addr_nxt           ),
    .nn_vm_wr_wdata_nxt        (nn_vm_wr_wdata_nxt    ),
    .nn_vm_wr_wstrb_nxt        (nn_vm_wr_wstrb_nxt    ),
    .vm_rdata                  (vm_rdata              ),
    .bank_nxt                  (bank_nxt              ),

    .nn_vm_wr_ecc_nxt          (nn_vm_wr_ecc_nxt      ),
    .nn_vm_wr_ecc_wstrb_nxt    (nn_vm_wr_ecc_wstrb_nxt),
    .vm_recc                   (vm_recc               ),
    .db_err_aggr               (db_err_aggr),
    .sb_err_aggr               (sb_err_aggr),

    .vm_cmd_en                 (vm_cmd_en             ),
    .nn_vm_wr_en               (nn_vm_wr_en           ),
    .ren                       (ren                   ),
    .bank_en                   (bank_en               ),
                             
    .vm_mem_en_r_out           (vm_mem_en_r           ),
    .vm_ls_r_out               (vm_ls_r               ),
    .vm_ldst_en_r_out          (vm_ldst_en_r          ),
    .vm_addr_r_out             (vm_addr_r             ),
    .nn_vm_wr_wdata_r_out      (nn_vm_wr_wdata_r      ),
    .nn_vm_wr_wstrb_r_out      (nn_vm_wr_wstrb_r      ),
    .nn_vm_rd_rdata_r_out      (nn_vm_rd_rdata_r      ),
  
    .bank_r_out                (bank_r                ),

    .nn_vm_wr_ecc_r_out        (nn_vm_wr_ecc_r        ),
    .nn_vm_wr_ecc_wstrb_r_out  (nn_vm_wr_ecc_wstrb_r  ),
    .nn_vm_rd_ecc_r_out        (nn_vm_rd_ecc_r        ),
    .db_err_aggr_r_out         (vm_db_err),
    .sb_err_aggr_r_out         (vm_sb_err),
    
    .clk                       (clk                   ),
    .rst_a                     (rst_a                 )
  
  );

   vm_mux_logic
   #(
    .VM_RPORTS(VM_RPORTS),
    .VM_WPORTS(VM_WPORTS),
    .NUM_VM_BANKS(NUM_VM_BANKS),
    .WWID(WWID)
   )
   u_vm_mux_logic
   (
    .nn_vm_wr_cmd_valid  (nn_vm_wr_cmd_valid      ),
    .nn_vm_wr_cmd_accept (nn_vm_wr_cmd_accept     ),
    .nn_vm_wr_cmd_addr   (nn_vm_wr_cmd_addr       ),
    .nn_vm_wr_wdata      (nn_vm_wr_wdata          ),
    .nn_vm_wr_wstrb      (nn_vm_wr_wstrb          ),
    .nn_vm_rd_cmd_valid  (nn_vm_rd_cmd_valid      ),
    .nn_vm_rd_cmd_accept (nn_vm_rd_cmd_accept     ),
    .nn_vm_rd_cmd_addr   (nn_vm_rd_cmd_addr       ),
    .nn_vm_rd_rvalid     (nn_vm_rd_rvalid         ),
                                            
    .vm_mem_en           (vm_mem_en               ),

    .vm_prot_en          (vm_prot_en),
   .nn_vm_wr_ecc_wstrb_nxt (nn_vm_wr_ecc_wstrb_nxt),  // port2bank write ecc msk
  
// input signals
   .bank_r                 (bank_r                ),
   .wfifo_waccept          (wfifo_waccept         ),
   .wfifo_rvalid           (wfifo_rvalid          ),
   .wfifo_rdata            (wfifo_rdata           ),
   .wfifo_prio             (wfifo_prio            ),

// output signals
   .bank_en                (bank_en               ), 
   .bank_nxt               (bank_nxt              ),
   .vm_mem_en_nxt          (vm_mem_en_nxt         ),
   .vm_cmd_en              (vm_cmd_en             ),
   .vm_ldst_en_nxt         (vm_ldst_en_nxt        ),
   .nn_vm_wr_wstrb_nxt     (nn_vm_wr_wstrb_nxt    ),
   .vm_ls_nxt              (vm_ls_nxt             ),
   .nn_vm_wr_en            (nn_vm_wr_en           ),
   .ren                    (ren                   ),
   .wfifo_wvalid           (wfifo_wvalid          ),
   .wfifo_wdata            (wfifo_wdata           ),
   .wfifo_raccept          (wfifo_raccept         ),

   // vm initialization
   .vm_init                (vm_init_busy          ),
   //
   // clock and rst_a
   //
   .clk                    (clk                   ),  // clock, all logic clocked at posedge
   .rst_a                  (rst_a                 )   // asynchronous rst_a, active high


  ); 

   vm_mux_logic_data_addr#(
    .VM_RPORTS(VM_RPORTS),
    .VM_WPORTS(VM_WPORTS),
    .NUM_VM_BANKS(NUM_VM_BANKS),
    .WWID(WWID)
   )
   u_vm_mux_logic_data_addr
   (

    .nn_vm_wr_cmd_valid  (nn_vm_wr_cmd_valid      ),
    .nn_vm_wr_cmd_addr   (nn_vm_wr_cmd_addr       ),
    .nn_vm_wr_wdata      (nn_vm_wr_wdata          ),
    .nn_vm_rd_cmd_valid  (nn_vm_rd_cmd_valid      ),
    .nn_vm_rd_cmd_addr   (nn_vm_rd_cmd_addr       ),
    .nn_vm_rd_rdata      (nn_vm_rd_rdata          ),
    .vm_addr             (vm_addr                 ),
    .vm_wdata            (vm_wdata                ),
    .vm_rdata            (vm_rdata                ),

    .vm_mem_en           (vm_mem_en               ),
    .vm_ls               (vm_ls                   ),
    .vm_ds               (vm_ds                   ),
    .vm_ldst_en          (vm_ldst_en              ),
    .vm_wstrb            (vm_wstrb                ),

    .vm_mem_en_r         (vm_mem_en_r             ),
    .vm_ls_r             (vm_ls_r                 ),
    .vm_ldst_en_r        (vm_ldst_en_r            ),
    .nn_vm_wr_wstrb_r    (nn_vm_wr_wstrb_r        ),

    .vm_prot_en          (vm_prot_en),
    .nn_vm_wr_ecc_r        (nn_vm_wr_ecc_r        ),
    .nn_vm_wr_ecc_wstrb_r  (nn_vm_wr_ecc_wstrb_r  ),
    .vm_wecc               (vm_wecc               ),
    .vm_ecc_wstrb          (vm_ecc_wstrb          ),
  
// input signals
   .vm_addr_r              (vm_addr_r             ),
   .nn_vm_wr_wdata_r       (nn_vm_wr_wdata_r      ),
   .nn_vm_rd_rdata_r       (nn_vm_rd_rdata_r      ),
   .nn_vm_rd_ecc_r         (nn_vm_rd_ecc_r        ),
   .bank_r                 (bank_r                ),
   .wfifo_rvalid           (wfifo_rvalid          ),
   .wfifo_rdata            (wfifo_rdata           ),
   .wfifo_prio             (wfifo_prio            ),

// output signals
   .vm_addr_nxt            (vm_addr_nxt           ),
   .nn_vm_wr_wdata_nxt     (nn_vm_wr_wdata_nxt    ),

  // mem ecc
   .nn_vm_wr_ecc_nxt       (nn_vm_wr_ecc_nxt      ),
   .sb_err_aggr            (sb_err_aggr           ),
   .db_err_aggr            (db_err_aggr           ),
   // vm initialization
   .vm_init                (vm_init_busy          ),
   .vm_init_wr_cmd_addr    (vm_init_wr_cmd_addr   ),
   //
   // clock and rst_a
   //
   .clk                    (clk                   ),  // clock, all logic clocked at posedge
   .rst_a                  (rst_a                 )   // asynchronous rst_a, active high


  );

  //
  // VM init instance
  //
  assign vm_init_busy = vm_init & !vm_init_end;
  npu_sram_init
   #(
     .ADDR_W($bits(vm_addr_t)),
     .NUM_BANKS(NUM_VM_BANKS),
     .MEM_MODE(0) //1:AM, 0:VM    
    )
    u_npu_vm_init(
   .clk            (clk        ),
   .rst_a          (rst_a      ),
   .sram_init      (vm_init),
   .sram_init_end  (vm_init_end),
   .cmd_addr       (vm_init_wr_cmd_addr)
   );

endmodule : vm_mux
