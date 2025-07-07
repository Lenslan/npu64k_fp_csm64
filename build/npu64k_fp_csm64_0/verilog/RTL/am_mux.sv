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
// Top-level demo file for the AM BUS 
//
`include "npu_defines.v"
 
`include "npu_defines.v"
`include "npu_am_macros.svh"

`include "npu_am_ecc_macros.sv"

`ifndef NPU_ECC_TYPES_IMPORTED
`define NPU_ECC_TYPES_IMPORTED
import npu_ecc_types::*;
`endif  
// spyglass disable_block W240
// SMD: Declared but not read
// SJ: Reviewed
module am_mux
  import npu_types::*;
  import npu_ecc_types::*;
  #(
    parameter int AM_RPORTS=5+1,
    parameter int AM_WPORTS=4+1,
    parameter int NUM_AM_BANKS=2
   )
  (
   //
   // interfaces
   //
   // write request
   `AMWSLV_MSK(nn_am_wr_,AM_WPORTS),
   // read request
   `AMRSLV(nn_am_rd_,AM_RPORTS),
   
   // muxed request
   `AMMST_MSK(NUM_AM_BANKS,am_),

   //
   // am ecc
   //
   input  logic                     am_prot_en,
   // am mem access interface
   `AMMST_ECC(NUM_AM_BANKS,am_),
   
   // am port access interface
   output logic                     am_sb_err,
   output logic                     am_db_err,
   // am initialization
   input logic      am_init,
   output logic     am_init_end,
   //test mode
   input logic      test_mode,
   //
   // clock and rst_a
   //
   input logic      clk,                     // clock, all logic clocked at posedge
   input logic      rst_a                  // asynchronous rst_a, active high
  );
// spyglass enable_block W240

  localparam AM_PORTS_WIDTH=$clog2(NUM_AM_BANKS);

  // 3-stage delay line type onehot0 on inner dimension
  typedef logic [AM_RPORTS-1:0][2:0][NUM_AM_BANKS-1:0] bank_t;

  ////////////////////////////////////////////////////////////
  
  logic       [NUM_AM_BANKS-1:0]     am_mem_en_r;
  logic       [NUM_AM_BANKS-1:0]     am_mem_en_nxt;
  logic       [NUM_AM_BANKS-1:0]     am_ls_r;
  logic       [NUM_AM_BANKS-1:0]     am_ls_nxt;
  logic       [NUM_AM_BANKS-1:0]     am_cmd_en;
  logic       [NUM_AM_BANKS-1:0]     am_ldst_en_r;
  logic       [NUM_AM_BANKS-1:0]     am_ldst_en_nxt;
  am_addr_t   [NUM_AM_BANKS-1:0]     am_addr_r;
  am_addr_t   [NUM_AM_BANKS-1:0]     am_addr_nxt;

  vyixacc_t   [NUM_AM_BANKS-1:0]     nn_am_wr_wdata_nxt;
  vyixacc_t   [NUM_AM_BANKS-1:0]     nn_am_wr_wdata_r;
  ixambit_t   [NUM_AM_BANKS-1:0]     nn_am_wr_wstrb_nxt;
  ixambit_t   [NUM_AM_BANKS-1:0]     nn_am_wr_wstrb_r;
  logic       [NUM_AM_BANKS-1:0]     nn_am_wr_en;

  // Read data buffer
  logic       [NUM_AM_BANKS-1:0]     ren;
  vyixacc_t   [NUM_AM_BANKS-1:0]     nn_am_rd_rdata_r;
  // am initialization
  am_addr_t  am_init_wr_cmd_addr; // am init write command address
  logic      am_init_busy;
  // mem ecc
  localparam CFG_NPU_MEM_ECC = 1;
  logic       [NUM_AM_BANKS-1:0] [AM_NUM_ECC-1:0] nn_am_wr_ecc_wstrb_nxt;
  logic       [NUM_AM_BANKS-1:0] [AM_NUM_ECC-1:0] nn_am_wr_ecc_wstrb_r;
  am_ecc_c_t  [NUM_AM_BANKS-1:0]                  nn_am_wr_ecc_r;
  am_ecc_c_t  [NUM_AM_BANKS-1:0]                  nn_am_rd_ecc_r;
  am_ecc_c_t  [NUM_AM_BANKS-1:0]                  nn_am_wr_ecc_nxt;
  logic                                           db_err_aggr;
  logic                                           sb_err_aggr;
  logic                                           db_err_aggr_r;
  logic                                           sb_err_aggr_r;

  // bank delay line
  logic       [AM_RPORTS-1:0][2:0]   bank_en;
  bank_t                             bank_r;
  bank_t                             bank_nxt;

  am_mux_reg
  #(
    .NUM_AM_BANKS(NUM_AM_BANKS),
    .AM_RPORTS(AM_RPORTS)
  )
  u_am_mux_reg
  (
    
    .am_mem_en_nxt             (am_mem_en_nxt     ),
    .am_ls_nxt                 (am_ls_nxt         ),
    .am_ldst_en_nxt            (am_ldst_en_nxt    ),
    .am_addr_nxt               (am_addr_nxt       ),
    .nn_am_wr_wdata_nxt        (nn_am_wr_wdata_nxt),
    .nn_am_wr_wstrb_nxt        (nn_am_wr_wstrb_nxt),
    .am_rdata                  (am_rdata          ),
    .bank_nxt                  (bank_nxt          ),

    .nn_am_wr_ecc_nxt          (nn_am_wr_ecc_nxt      ),
    .nn_am_wr_ecc_wstrb_nxt    (nn_am_wr_ecc_wstrb_nxt),
    .am_recc                   (am_recc               ),
    .db_err_aggr               (db_err_aggr),
    .sb_err_aggr               (sb_err_aggr),

    .am_cmd_en                 (am_cmd_en         ),
    .nn_am_wr_en               (nn_am_wr_en       ),
    .ren                       (ren               ),
    .bank_en                   (bank_en           ),
                             
    .am_mem_en_r_out           (am_mem_en_r     ),
    .am_ls_r_out               (am_ls_r         ),
    .am_ldst_en_r_out          (am_ldst_en_r    ),
    .am_addr_r_out             (am_addr_r       ),
    .nn_am_wr_wdata_r_out      (nn_am_wr_wdata_r),
    .nn_am_wr_wstrb_r_out      (nn_am_wr_wstrb_r),
    .nn_am_rd_rdata_r_out      (nn_am_rd_rdata_r),
  
    .bank_r_out                (bank_r          ),

    .nn_am_wr_ecc_r_out        (nn_am_wr_ecc_r      ),
    .nn_am_wr_ecc_wstrb_r_out  (nn_am_wr_ecc_wstrb_r),
    .nn_am_rd_ecc_r_out        (nn_am_rd_ecc_r      ),
    .db_err_aggr_r_out         (am_db_err),
    .sb_err_aggr_r_out         (am_sb_err),
    
    .clk                 (clk),
    .rst_a               (rst_a)
  
  );

   am_mux_logic
  #(
    .AM_RPORTS(AM_RPORTS),
    .AM_WPORTS(AM_WPORTS),
    .NUM_AM_BANKS(NUM_AM_BANKS)
   )
   u_am_mux_logic
   (
    .nn_am_wr_cmd_valid  (nn_am_wr_cmd_valid      ),
    .nn_am_wr_cmd_accept (nn_am_wr_cmd_accept     ),
    .nn_am_wr_cmd_addr   (nn_am_wr_cmd_addr       ),                                            
    .nn_am_wr_wstrb      (nn_am_wr_wstrb          ),                                            
    .nn_am_rd_cmd_valid  (nn_am_rd_cmd_valid      ),
    .nn_am_rd_cmd_accept (nn_am_rd_cmd_accept     ),
    .nn_am_rd_cmd_addr   (nn_am_rd_cmd_addr       ),                                          
    .nn_am_rd_rvalid     (nn_am_rd_rvalid         ),                                           
                                            
    .am_mem_en           (am_mem_en               ),

    .am_prot_en          (am_prot_en),
   .nn_am_wr_ecc_wstrb_nxt (nn_am_wr_ecc_wstrb_nxt),
  
// input signals
   .bank_r                 (bank_r                ),

// output signals
   .bank_en                (bank_en               ), 
   .bank_nxt               (bank_nxt              ),
   .am_mem_en_nxt          (am_mem_en_nxt         ),
   .am_cmd_en              (am_cmd_en             ),
   .am_ldst_en_nxt         (am_ldst_en_nxt        ),
   .nn_am_wr_wstrb_nxt     (nn_am_wr_wstrb_nxt    ),
   .nn_am_wr_en            (nn_am_wr_en           ),
   .ren                    (ren                   ),
   .am_ls_nxt              (am_ls_nxt             ),

   // am initialization
   .am_init                (am_init_busy          ),
   //
   // clock and rst_a
   //
   .clk                    (clk                   ),  // clock, all logic clocked at posedge
   .rst_a                  (rst_a                 )   // asynchronous rst_a, active high


  );

   am_mux_logic_data_addr#(
    .AM_RPORTS(AM_RPORTS),
    .AM_WPORTS(AM_WPORTS),
    .NUM_AM_BANKS(NUM_AM_BANKS)
   )
   u_am_mux_logic_data_addr
   (

    .nn_am_wr_cmd_valid  (nn_am_wr_cmd_valid      ),
    .nn_am_wr_cmd_addr   (nn_am_wr_cmd_addr       ),
    .nn_am_wr_wdata      (nn_am_wr_wdata          ),
    .nn_am_rd_cmd_valid  (nn_am_rd_cmd_valid      ),
    .nn_am_rd_cmd_addr   (nn_am_rd_cmd_addr       ),
    .nn_am_rd_rdata      (nn_am_rd_rdata          ),
    .am_addr             (am_addr                 ),
    .am_wdata            (am_wdata                ),
    .am_rdata            (am_rdata                ),

    .am_mem_en_r         (am_mem_en_r             ),
    .am_ls_r             (am_ls_r                 ),
    .am_ldst_en_r        (am_ldst_en_r            ),
    .nn_am_wr_wstrb_r    (nn_am_wr_wstrb_r        ),

    .am_mem_en           (am_mem_en               ),
    .am_ls               (am_ls                   ),
    .am_ds               (am_ds                   ),
    .am_ldst_en          (am_ldst_en              ),
    .am_wstrb            (am_wstrb                ),

    .am_prot_en            (am_prot_en            ),
    .am_wecc               (am_wecc               ),
    .am_ecc_wstrb          (am_ecc_wstrb          ),
    .nn_am_wr_ecc_r        (nn_am_wr_ecc_r        ),
    .nn_am_wr_ecc_wstrb_r  (nn_am_wr_ecc_wstrb_r  ),
  
// input signals
   .am_addr_r              (am_addr_r             ),
   .nn_am_wr_wdata_r       (nn_am_wr_wdata_r      ),
   .nn_am_rd_rdata_r       (nn_am_rd_rdata_r      ),
   .nn_am_rd_ecc_r         (nn_am_rd_ecc_r        ),
   .bank_r                 (bank_r                ),

// output signals
   .am_addr_nxt            (am_addr_nxt           ),
   .nn_am_wr_wdata_nxt     (nn_am_wr_wdata_nxt    ),

  // mem ecc
   .nn_am_wr_ecc_nxt       (nn_am_wr_ecc_nxt      ),
   .sb_err_aggr            (sb_err_aggr           ),
   .db_err_aggr            (db_err_aggr           ),
   // am initialization
   .am_init                (am_init_busy          ),
   .am_init_wr_cmd_addr    (am_init_wr_cmd_addr   ),
   //
   // clock and rst_a
   //
   .clk                    (clk                   ),  // clock, all logic clocked at posedge
   .rst_a                  (rst_a                 )   // asynchronous rst_a, active high


  );

  //
  // AM init instance
  //    
  assign am_init_busy = am_init & !am_init_end;
  npu_sram_init
   #(
     .ADDR_W($bits(am_addr_t)),
     .NUM_BANKS(NUM_AM_BANKS),
     .MEM_MODE(1) //1:AM, 0:VM    
    )
    u_npu_am_init(
   .clk            (clk        ),
   .rst_a          (rst_a      ),
   .sram_init      (am_init),
   .sram_init_end  (am_init_end),
   .cmd_addr       (am_init_wr_cmd_addr)
   );

endmodule : am_mux
