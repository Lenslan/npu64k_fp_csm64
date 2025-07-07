/*
 * Copyright (C) 2022 Synopsys, Inc. All rights reserved.
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
`include "npu_axi_macros.svh"

`include "npu_vm_ecc_macros.sv"
`include "npu_am_ecc_macros.sv"
module npu_sfty_top
  import npu_types::*;
  import npu_ecc_types::*;
  #(
    parameter int  SAXIIDW  = 1,             // AXI MMIO slave ID width
    parameter int  SAXIAWUW = 1,             // AXI MMIO slave AW user width
    parameter int  SAXIWUW  = 1,             // AXI MMIO slave W user width
    parameter int  SAXIBUW  = 1,             // AXI MMIO slave B user width
    parameter int  SAXIARUW = 1,             // AXI MMIO slave AR user width
    parameter int  SAXIRUW  = 1,             // AXI MMIO slave R user width
    parameter int  VM_RPORTS = 45 + 2,
    parameter int  AM_RPORTS = 3 + 1,
    parameter int  NUM_VM_BANKS = 32,
    parameter int  NUM_AM_BANKS = 2  
   ,localparam int  NUM_VM_ERR_PORT = NUM_VM_BANKS,
    localparam int  NUM_AM_ERR_PORT = NUM_AM_BANKS
  )
  (
   // AXI MMIO interface 64b wide data
   `AXISLV(SAXIIDW,64,SAXIAWUW,SAXIWUW,SAXIBUW,SAXIARUW,SAXIRUW,mmio_axi_),
   
   // input interface
   input  logic                           vm_init_end,// vm initialization done status
   input  logic                           am_init_end,// am initialization done status
   input  logic                   vm_sb_err,
   input  logic                   am_sb_err,
   input  logic                   vm_db_err,
   input  logic                   am_db_err,

   // output interface  
   output logic                           vm_init,    // vm initialization enable control
   output logic                           am_init,    // am initialization enable control
   output logic                   vm_prot_en, // vm ecc protection enable control
   output logic                   am_prot_en, // am ecc protection enable control
   output logic                           mem_ecc_irq,    
   output logic                           vm_ecc_dbe,
   output logic                           am_ecc_dbe,
   output logic                           vm_ecc_sbe,
   output logic                           am_ecc_sbe,
   // System interface
   input  logic                           clk,       // always-on clock
   input  logic                           rst_a,     // asynchronous reset, active high, synchronous deassertion
   input  logic                           test_mode
  );


logic            rst;
   //
   // Reset synchronizer
   //
   npu_reset_ctrl
   u_reset_ctrl_inst
     (
     .clk        ( clk       ),
     .rst_a      ( rst_a     ),
     .test_mode  ( test_mode ),
     .rst        ( rst       )
     );
   //
   // NPU safety mmio control
   //
   npu_sfty_ctrl_mmio #(
       .SAXIIDW        (SAXIIDW        ),
       .SAXIAWUW       (SAXIAWUW       ),
       .SAXIWUW        (SAXIWUW        ),
       .SAXIBUW        (SAXIBUW        ),
       .SAXIARUW       (SAXIARUW       ),
       .SAXIRUW        (SAXIRUW        ),
       .VM_RPORTS      (VM_RPORTS      ),
       .AM_RPORTS      (AM_RPORTS      ),
       .NUM_VM_BANKS   (NUM_VM_BANKS   ),
       .NUM_AM_BANKS   (NUM_AM_BANKS   )
   ) u_npu_sfty_ctrl_mmio (
   // System interface
       `AXIINST(mmio_axi_,mmio_axi_),
   // ECC result input interface
       .vm_sb_err               (vm_sb_err),
       .am_sb_err               (am_sb_err),
       .vm_db_err               (vm_db_err),
       .am_db_err               (am_db_err),    

   // mmio ctrl interface
       .vm_init                       (vm_init    ),
       .am_init                       (am_init    ),
       .vm_init_end                   (vm_init_end),
       .am_init_end                   (am_init_end),
       .vm_prot_en                    (vm_prot_en ),
       .am_prot_en                    (am_prot_en ),
   // irq
       .mem_ecc_irq                   (mem_ecc_irq),
   // report to sfty aggregator     
       .vm_ecc_dbe                     (vm_ecc_dbe),
       .am_ecc_dbe                     (am_ecc_dbe),
       .vm_ecc_sbe                     (vm_ecc_sbe),
       .am_ecc_sbe                     (am_ecc_sbe),
       // Clock, Reset
       .rst_a                          (rst            ),
       .clk                            (clk            )
   );



endmodule
