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
// convolution stash module
// vcs -sverilog +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_iterator.sv ../../shared/RTL/npu_fifo.sv ../../shared/RTL/npu_vm_read.sv ../../shared/RTL/npu_hs_broadcast.sv npu_conv_types.sv npu_conv_stash_quad_load.sv  npu_conv_stash_scalar.sv npu_conv_stash_vector.sv npu_conv_stash_pad_load.sv npu_conv_stash_pad_data.sv npu_conv_stash.sv 
// analyze -format sverilog -vcs "+incdir+../../../shared/RTL ../../../shared/RTL/npu_types.sv ../../../shared/RTL/npu_iterator.sv ../../../shared/RTL/npu_fifo.sv ../../../shared/RTL/npu_vm_read.sv ../../../shared/RTL/npu_hs_broadcast.sv ../npu_conv_types.sv ../npu_conv_stash_quad_load.sv ../npu_conv_stash_scalar.sv ../npu_conv_stash_vector.sv ../npu_conv_stash_pad_load.sv ../npu_conv_stash_pad_data.sv ../npu_conv_stash.sv"
 
`include "npu_defines.v"
`include "npu_axi_macros.svh"
`include "npu_vm_macros.svh"


module npu_conv_stash
  import npu_types::*;
  import npu_conv_types::*;
  (
   //
   // Clock and reset
   //
   input  logic                clk,                          // Clock, all logic clocked at posedge
   input  logic                rst_a,                        // Asynchronous reset, active high
   // HLAPI interface
   input  logic                hlapi_valid,                  // Request new HLAPI start
   output logic                hlapi_accept,                 // Acknowledge new HLAPI start
   input  conv_hlapi_i_t       hlapi_i,                      // HLAPI parameters
   //
   // External interfaces
   //
   `VMRMST(NUM_FM_QUEUE+1,vm_rd_),                           // FM_QUEUE+1 bank VM feature-map and padding read
   //
   // Interface to MAC array
   //
   output logic                stash_valid,                  // Stash output to multipliers is valid
   input  logic                stash_accept,                 // Multiplier accetps stash output
   output stash_data_t         stash_data                    // Data from stash to multiplier
   );
  localparam int NUM = 5;
  // local handshakes
  logic   [NUM-1:0] hso_valid;            // handshake is valid
  logic   [NUM-1:0] hso_accept;           // handshake is accepted
  // quadrant information
  logic             quad_valid;           // quadrant information valid
  logic             quad_accept;          // quadrant information accepted
  quadrant_t        quad_data;            // quadrant information
  // scalar information
  logic             scalar_valid;         // scalar information valid
  logic             scalar_accept;        // scalar information accepted
  vm_scalar_t       scalar_data;          // scalar information
  // VM vector load output
  logic             vector_valid;         // Load data is valid
  logic             vector_accept;        // Load data is accepted
  vm_vector_t       vector_data;          // Load data
  // padding
  logic             pad_valid;            // pad load data is valid
  logic             pad_accept;           // pad load data is accepted
  ixpix_t [3:0]     pad_data;             // i64 padding values
 

  //
  // Replicate handshakes
  //
  npu_hs_broadcast
  #(
    .NUM ( NUM )
    )
  u_hs_inst
  (
   .clk        ( clk          ),
   .rst_a      ( rst_a        ),
   .hsi_valid  ( hlapi_valid  ),
   .hsi_accept ( hlapi_accept ),
   .hso_valid  ( hso_valid    ),
   .hso_accept ( hso_accept   )
   );

  
  //
  // Generate Quadrant Sequence
  //
  npu_conv_stash_quad_load
  u_quad_load_inst
    (
   .clk          ( clk           ),
   .rst_a        ( rst_a         ),
   .hlapi_valid  ( hso_valid[0]  ),
   .hlapi_accept ( hso_accept[0] ),
   .hlapi_i      ( hlapi_i       ),
   .quad_valid   ( quad_valid    ),
   .quad_accept  ( quad_accept   ),
   .quad_data    ( quad_data     )
     );

  
  //
  // Scalar VM AGU, compute the start address of the column
  //
  npu_conv_stash_scalar
  u_scalar_inst
    (
   .clk           ( clk           ),
   .rst_a         ( rst_a         ),
   .hlapi_valid   ( hso_valid[1]  ),
   .hlapi_accept  ( hso_accept[1] ),
   .hlapi_i       ( hlapi_i       ),
   .quad_valid    ( quad_valid    ),
   .quad_accept   ( quad_accept   ),
   .quad_data     ( quad_data     ),
   .scalar_valid  ( scalar_valid  ),
   .scalar_accept ( scalar_accept ),
   .scalar_data   ( scalar_data   )
     );
     

  //
  // Vector VM AGU
  //
  npu_conv_stash_vector
  u_vector_inst
    (
   .clk           ( clk           ),
   .rst_a         ( rst_a         ),
   .hlapi_valid   ( hso_valid[2]  ),
   .hlapi_accept  ( hso_accept[2] ),
   .hlapi_i       ( hlapi_i       ),
   .scalar_valid  ( scalar_valid  ),
   .scalar_accept ( scalar_accept ),
   .scalar_data   ( scalar_data   ),
   `VMRINST_S(NUM_FM_QUEUE,vm_rd_,vm_rd_,0),
   .vector_valid  ( vector_valid  ),
   .vector_accept ( vector_accept ),
   .vector_data   ( vector_data   )
     );
     

  //
  // Pad loading
  //
  npu_conv_stash_pad_load 
  u_pad_load_inst
    (
     .clk          ( clk           ),
     .rst_a        ( rst_a         ),
     .hlapi_valid  ( hso_valid[3]  ),
     .hlapi_accept ( hso_accept[3] ),
     .hlapi_i      ( hlapi_i       ),
     `VMRINST_S(1,vm_rd_,vm_rd_,NUM_FM_QUEUE),
     .pad_valid    ( pad_valid     ),
     .pad_accept   ( pad_accept    ),
     .pad_data     ( pad_data      )
     );

  
  //
  // Padding
  //
  npu_conv_stash_pad_data
  u_pad_data_inst
    (
     .clk           ( clk           ),
     .rst_a         ( rst_a         ),
     .hlapi_valid   ( hso_valid[4]  ),
     .hlapi_accept  ( hso_accept[4] ),
     .hlapi_i       ( hlapi_i       ),
     .vector_valid  ( vector_valid  ),
     .vector_accept ( vector_accept ),
     .vector_data   ( vector_data   ),
     .pad_valid     ( pad_valid     ),
     .pad_accept    ( pad_accept    ),
     .pad_data      ( pad_data      ),
     .stash_valid   ( stash_valid   ),
     .stash_accept  ( stash_accept  ),
     .stash_data    ( stash_data    )
     );
  
endmodule : npu_conv_stash
