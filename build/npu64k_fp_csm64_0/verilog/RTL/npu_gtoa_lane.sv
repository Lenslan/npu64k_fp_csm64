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

/*
 * NPU lane logic
 */
// vcs -sverilog  +incdir+$NPU_HOME/build/verilog/RTL $NPU_HOME/build/verilog/RTL/npu_types.sv $NPU_HOME/build/verilog/RTL/npu_fifo.sv $NPU_HOME/arch/shared/RTL/npu_fp*.sv npu_gtoa_types.sv npu_gtoa_lane.sv npu_gtoa_fu_alu.sv npu_gtoa_fu_in.sv npu_gtoa_fu_pad.sv npu_gtoa_fu_mul.sv npu_gtoa_fu_out.sv npu_gtoa_fu_alu_lut.sv
// analyze -format sverilog -vcs "+incdir+../../../shared/RTL ../../../shared/RTL/npu_types.sv ../../../shared/RTL/npu_fifo.sv ../../../shared/RTL/npu_2cyc_checker.sv ../npu_gtoa_types.sv ../npu_gtoa_lane.sv ../npu_gtoa_fu_alu.sv ../npu_gtoa_fu_alu_multi4.sv ../npu_gtoa_fu_in.sv ../npu_gtoa_fu_mul.sv ../npu_gtoa_fu_out.sv"
// set_app_var link_library "* $target_library dw_foundation.sldb"

`include "npu_vm_macros.svh"
`include "npu_am_macros.svh"

module npu_gtoa_lane
  import npu_types::*;
  import npu_gtoa_types::*;
  #(
    parameter int VID    = 0,  // vector lane ID
    parameter int NUM_FU = 6,  // number of functional units in lane: 2*IN, OUT, 2*ALU, 1*MUL
    parameter int NRD    = 12, // number of register file read ports
    parameter int NWR    = 4   // number of regiser file write ports
    )
  (
   // clock and reset
   input  logic                                      clk,             // clock
   input  logic                                      rst_a,           // asynchronous reset, active high
   // static inputs
   input  logic             [7:0]                    slc_id,          // unique slice ID
   // input flow
   input  logic             [NUM_FU-1:0]             fu_valid,        // instruction valid per functional unit
   input  act_dec_inst_t    [NUM_FU-1:0]             fu_inst,         // instruction to be executed per functional units
   output logic             [2:0]                    ostall,          // stall per block
   input  logic                                      stall,           // global stall
   output logic                                      busy,            // datapath is busy
   // input operands
   input  ixacc_t           [NRD-1:0]                rd_data,         // read data
   // output result
   output act_ot_t          [NWR-1:0]                wr_typ,          // write operand type
   output logic             [NWR-1:0][2:0]           wr_ad,           // write operand address
   output ixacc_t           [NWR-1:0]                wr_data,         // write data
   // transpose to register file
   output logic                                      rf_trnsp,        // transpose data in regfile
   // LUT table
   input  act_lutt_t                                 lut_data,
   // reduction input, incoming rd_data from another lane!
   input  ixacc_t           [1:0]                    red_inp,
   output logic             [ISIZE-1:0]              red_state_out,
   input  logic             [ISIZE-1:0]              red_state_in,
   input  ixacc_t                                    bcv_in,          // spatial broadcast input
   // interface for gather
   input  offset_t                                   gather_base,     // gather base address
   input  offset_t                                   in_offs0,        // input feature-map AGU offset 0
   input  offset_t                                   in_offs1,        // input feature-map AGU offset 1
   input  acc_t                                      rd_vr7i0,        // read data from vr7 i0
   input  acc_t                                      rd_vr7i0v0,      // read data from vr7 i0 v0
   input  acc_t                                      rd_vr7v0l,       // read data from vr7 v0 low
   input  acc_t                                      rd_vr7v0h,       // read data from vr7 v0 high
   output logic                                      gather_valid,    // gather product is valid
   input  logic                                      gather_accept,   // gather product is accepted
   output offset_t                                   gather_prod,     // gather product 0 to AGU
   // shv interface
   input  ixacc_t                                    shv_in,          // shv input
   // streaming inputs
   input  logic             [1:0]                    in_valid,        // input data valid
   output logic             [1:0]                    in_accept,       // accept input data
   input  ixacc_t           [1:0]                    in_data,         // input data
   // padding iterator interface
   input  logic                                      it_first,        // iterator first flags
   output logic                                      padacc,          // accept padding
   input  logic                                      paden,           // enable padding
   input  pad_mode_t                                 padmode,         // pad 0, -1, min, max
   input  pad_inc_t                                  padinc,          // pad increment mode: i16, v2i8, v4i4
   input  offset_t          [ISIZE/4-1:0]            padcpos,         // padding column position
   input  logic             [ISIZE/4-1:0]            padi4,           // padding per i4 channels
   // streaming output
   output logic                                      out_valid,       // input data valid
   input  logic                                      out_accept,      // accept input data
   output ixacc_t                                    out_data,        // input data
   // hlapi sat and pool parameters
   input  logic                                      cf_in0fm,        // input 0 is feature-map
   input  logic                                      cf_in0dbl,       // input 0 is double wide
   input  fmode_t                                    cf_in0fmode,     // input 0 float mode
   input  logic                                      cf_in1fm,        // input 1 is feature-map
   input  logic                                      cf_in1dbl,       // input 1 is double wide
   input  fmode_t                                    cf_in1fmode,     // input 1 float mode
   input  logic                                      cf_outfm,        // output is feature-map
   input  logic                                      cf_outsat,       // saturation enable
   input  logic                                      cf_outdbl,        // double width enable
   input  fmode_t                                    cf_outfmode     // output float mode
   );
  // local wires
  logic            [1:0]                 q_in_valid;       // lut queue valid
  ix_fplut_queue_t [1:0]                 q_in_data;        // queue from LUT
  logic            [1:0]                 q_lut_accept;     // lut queue accept
  ix_fplut_queue_t [1:0]                 q_lut_data;       // buffered lut queue to MUL
  logic                                  out_dbl;          // double output, not used
  ixacc_t                                in0_data;         // unpadded input data
  logic                                  fu_in_state_en;   // alu state enable from fu_in
  logic            [ISIZE-1:0]           fu_in_state;      // alu state from fu_in
  logic            [ISIZE/4-1:0]         padflag;          // fu_in0 data is padded
  logic                                  padval;           // valid padding instruction
`ifdef ACT_HAS_ALU1
  logic            [ISIZE-1:0]           alu_state;        // ALU state from ALU0 to ALU1
`endif 
 

  //
  // Input 0 functional unit, inputs are from BW+BB, output to V
  //
  localparam int IN0_RD_BASE = 0;
  localparam int IN0_WR_BASE = 0;
  npu_gtoa_fu_in
  #
  (
   .ID     ( 0   ),
   .VID    ( VID ),
   .GATHEN ( 1   )
  )
  u_in0_inst
  (
   .clk         ( clk                     ),
   .rst_a       ( rst_a                   ),
   .attr_fm     ( cf_in0fm                ),
   .attr_dbl    ( cf_in0dbl               ),
   .attr_fmode  ( cf_in0fmode             ),
   .fu_valid    ( fu_valid[fu_in0]        ),
   .fu_inst     ( fu_inst[fu_in0]         ),
   .rd_data     ( rd_data[IN0_RD_BASE+:2] ),
   .wr_typ      ( wr_typ[IN0_WR_BASE]     ),
   .wr_ad       ( wr_ad[IN0_WR_BASE]      ),
   .wr_data     ( in0_data                ),
   .cidx        ( '0                      ), // intentionally tied to 0
   .in_valid    ( in_valid[0]             ),
   .in_accept   ( in_accept[0]            ),
   .in_data     ( in_data[0]              ),
   .gather_base ( gather_base             ),
   .in_offs0    ( in_offs0                ),
   .in_offs1    ( in_offs1                ),
   .rd_vr7i0    ( rd_vr7i0v0              ),
   .rd_vr7v0l   ( rd_vr7v0l               ),
   .rd_vr7v0h   ( rd_vr7v0h               ),
   .gather_val  ( gather_valid            ),
   .gather_acc  ( gather_accept           ),
   .gather_prod ( gather_prod             ),
   .state_en    ( fu_in_state_en          ),
   .state       (                         ),
   .padval      ( padval                  ),
   .padflag     ( padflag                 ),
   .padacc      ( padacc                  ),
   .it_first    ( it_first                ),
   .ostall      ( ostall[0]               ),
   .stall       ( stall                   )
  );


  //
  // Padding on input 0
  //
  npu_gtoa_fu_pad
  u_pad_inst
  (
   .paden   ( paden                ),
   .padval  ( padval               ),
   .padmode ( padmode              ),
   .padinc  ( padinc               ),
   .padi4   ( padi4                ),
   .in_acc  ( in0_data             ),
   .padflag ( padflag              ),
   .out_acc ( wr_data[IN0_WR_BASE] )
  );
  always_comb
  begin : state_PROC
    for (int i = 0; i < ISIZE; i++)
    begin
      fu_in_state[i] = ~wr_data[IN0_WR_BASE][i][31];
    end
  end : state_PROC
  
  
  //
  // Input 1 functional unit, inputs are from BW+BB, output to V
  //
  localparam int IN1_RD_BASE = 2;
  localparam int IN1_WR_BASE = 1;
  npu_gtoa_fu_in
  #
  (
   .ID     ( 1   ),
   .VID    ( VID ),
   .GATHEN ( 0   )
  )
  u_in1_inst
  (
   .clk         ( clk                       ),
   .rst_a       ( rst_a                     ),
   .attr_fm     ( cf_in1fm                  ),
   .attr_dbl    ( cf_in1dbl                 ),
   .attr_fmode  ( cf_in1fmode               ),
   .fu_valid    ( fu_valid[fu_in1]          ),
   .fu_inst     ( fu_inst[fu_in1]           ),
   .rd_data     ( rd_data[IN1_RD_BASE+:2]   ),
   .wr_typ      ( wr_typ[IN1_WR_BASE]       ),
   .wr_ad       ( wr_ad[IN1_WR_BASE]        ),
   .wr_data     ( wr_data[IN1_WR_BASE]      ),
   .cidx        ( padcpos                   ),
   .in_valid    ( in_valid[1]               ),
   .in_accept   ( in_accept[1]              ),
   .in_data     ( in_data[1]                ),
   .gather_base ( '0                        ),  // intentionally tied
   .in_offs0    ( '0                        ),  // intentionally tied
   .in_offs1    ( '0                        ),  // intentionally tied
   .rd_vr7i0    ( '0                        ),  // intentionally tied
   .rd_vr7v0l   ( '0                        ),  // intentionally tied
   .rd_vr7v0h   ( '0                        ),  // intentionally tied
   .gather_val  (                           ),  // intentionally unconnected
   .gather_acc  ( 1'b1                      ),  // intentionally tied
   .gather_prod (                           ),  // intentionally unconnected
   .state_en    (                           ),  // intentionally unconnected 
   .state       (                           ),  // intentionally unconnected
   .padval      (                           ),  // intentionally unconnected
   .padflag     ( padflag                   ),
   .padacc      (                           ),  // intentionally unconnected
   .it_first    ( '0                        ),  // intentionally tied
   .ostall      ( ostall[1]                 ),
   .stall       ( stall                     )
  );

  
  //
  // Output functional unit, input 0 from V, 1 from BB
  //
  localparam int OUT_RD_BASE = 4;
  npu_gtoa_fu_out
  u_out_inst
  (
   .clk          ( clk                       ),
   .rst_a        ( rst_a                     ),
   .fu_valid     ( fu_valid[fu_out]          ),
   .fu_inst      ( fu_inst[fu_out]           ),
   .rd_data      ( rd_data[OUT_RD_BASE+:2]   ),
   .cf_fm        ( cf_outfm                  ),
   .cf_sat       ( cf_outsat                 ),
   .cf_dbl       ( cf_outdbl                 ),
   .cf_fmode     ( cf_outfmode               ),
   .out_valid    ( out_valid                 ),
   .out_accept   ( out_accept                ),
   .out_data     ( out_data                  ),
   .out_dbl      ( out_dbl                   ),
   .busy         ( busy                      ),
   .ostall       ( ostall[2]                 ),
   .stall        ( stall                     )
  );

  
  //
  // ALU0 functional unit, input 0 from V or S, 1 from B or V, output to V or S
  //
  localparam int ALU0_RD_BASE = 6;
  localparam int ALU0_WR_BASE = 2;
  npu_gtoa_fu_alu
  #(
    .ID  ( 0   ),
    .VID ( VID )
  )
  u_alu0_inst
  (
   .clk           ( clk                      ),
   .rst_a         ( rst_a                    ),
   .slc_id        ( slc_id                   ),
   .fu_valid      ( fu_valid[fu_alu0]        ),
   .fu_inst       ( fu_inst[fu_alu0]         ),
   .rd_data       ( rd_data[ALU0_RD_BASE+:2] ),
   .wr_typ        ( wr_typ[ALU0_WR_BASE]     ),
   .wr_ad         ( wr_ad[ALU0_WR_BASE]      ),
   .wr_data       ( wr_data[ALU0_WR_BASE]    ),
   .rf_trnsp      ( rf_trnsp                 ),
   .in_state_en   ( fu_in_state_en           ),
   .in_state      ( fu_in_state              ),
   .red_inp       ( red_inp                  ),
   .red_state_out ( red_state_out            ),
   .red_state_in  ( red_state_in             ),
   .rd_vr7i0      ( rd_vr7i0                 ),
`ifdef ACT_HAS_ALU1
   .alu_state     ( alu_state                ),
`else  // ACT_HAS_ALU1
   .bcv_in        ( bcv_in                   ), 
   .shv_in        ( shv_in                   ),
   .lut_data      ( lut_data                 ),
   .q_in_valid    ( q_in_valid               ),
   .q_in_data     ( q_in_data                ),
`endif  // ACT_HAS_ALU1
   .stall         ( stall                    )
  );


`ifdef ACT_HAS_ALU1
  //
  // ALU1 functional unit, input 0 from V or W, output to V
  //
  localparam int ALU1_RD_BASE = 8;
  localparam int ALU1_WR_BASE = 3;
  npu_gtoa_fu_alu1
  u_alu1_inst
  (
   .clk           ( clk                      ),
   .rst_a         ( rst_a                    ),
   .fu_valid      ( fu_valid[fu_alu1]        ),
   .fu_inst       ( fu_inst[fu_alu1]         ),
   .rd_data       ( rd_data[ALU1_RD_BASE+:1] ),
   .bcv_in        ( bcv_in                   ), 
   .shv_in        ( shv_in                   ),
   .wr_typ        ( wr_typ[ALU1_WR_BASE]     ),
   .wr_ad         ( wr_ad[ALU1_WR_BASE]      ),
   .wr_data       ( wr_data[ALU1_WR_BASE]    ),
   .alu_state     ( alu_state                ),
   .lut_data      ( lut_data                 ),
   .q_in_valid    ( q_in_valid               ),
   .q_in_data     ( q_in_data                ),
   .stall         ( stall                    )
  );
`else  // ACT_HAS_ALU1
  localparam int ALU1_WR_BASE = 3;
  assign wr_typ[ALU1_WR_BASE]  = ot_no;
  assign wr_ad[ALU1_WR_BASE]   = '0;
  assign wr_data[ALU1_WR_BASE] = '0;
`endif  // ACT_HAS_ALU1


  //
  // LUT->MUL queues
  //
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :intentionally open
  npu_fifo
  #(
    .SIZE   ( 1                ),   // size 1, MUL follows directly after LUT
    .DWIDTH ( $bits(ix_fplut_queue_t) ),
    .FRCVAL ( 1'b1             ),
    .FRCACC ( 1'b1             )
  )
  u_q0_inst
  (
   .clk          ( clk             ),
   .rst_a        ( rst_a           ),
   .valid_write  ( q_in_valid[0]   ),
   .accept_write (                 ), // intentionally open, forced accept
   .data_write   ( q_in_data[0]   ),
   .valid_read   (                 ), // intentionally open, forced valid
   .accept_read  ( q_lut_accept[0] ),
   .data_read    ( q_lut_data[0]  )
  );
  npu_fifo
  #(
    .SIZE   ( 2                ),   // size 2, second MUL has latency 2 after first
    .DWIDTH ( $bits(ix_fplut_queue_t) ),
    .FRCVAL ( 1'b1             ),
    .FRCACC ( 1'b1             )
  )
  u_q1_inst
  (
   .clk          ( clk             ),
   .rst_a        ( rst_a           ),
   .valid_write  ( q_in_valid[1]   ),
   .accept_write (                 ), // intentionally open, forced accept
   .data_write   ( q_in_data[1]   ),
   .valid_read   (                 ), // intentionally open, forced valid
   .accept_read  ( q_lut_accept[1] ),
   .data_read    ( q_lut_data[1]  )
  );
// spyglass enable_block W287b  

  
  //
  // Multiplier 0 functional unit, input 0 from V, 1 from BH or V, output to V
  //
  localparam int MUL0_RD_BASE = 9;
  localparam int MUL0_WR_BASE = 4;
  npu_gtoa_fu_mul
  #(
    .ID ( 0 )
  )
  u_mul0_inst
  (
   .clk          ( clk                      ),
   .rst_a        ( rst_a                    ),
   .fu_valid     ( fu_valid[fu_mul0]        ),
   .fu_inst      ( fu_inst[fu_mul0]         ),
   .rd_data      ( rd_data[MUL0_RD_BASE+:2] ),
   .q_in_accept  ( q_lut_accept             ),
   .q_in_data    ( q_lut_data              ),
   .wr_typ       ( wr_typ[MUL0_WR_BASE]     ),
   .wr_ad        ( wr_ad[MUL0_WR_BASE]      ),
   .wr_data      ( wr_data[MUL0_WR_BASE]    ),
   .stall        ( stall                    )
  );
  
endmodule : npu_gtoa_lane
