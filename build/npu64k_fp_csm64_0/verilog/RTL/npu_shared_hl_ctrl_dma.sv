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
// File defining the MMIO and control interface for controlling accelerators
//
// MMIO registers accessible over AXI:
//
// name            aoffset    roffset rd/wr width Description
// ID              0x000       0       R     32b  Identification and version
// CTRL            0x004       1       RW    32b  Clock, halt, reset control
// STATUS          0x008       2       R     32b  Busy status
// ENABLE          0x00c       3       RW    32b  Enable interrupt output
// INT_STATUS      0x010       4       R     32b  Interrupt status
// INT_SET         0x014       5       R0W   32b  Interrupt flag set, read as 0
// INT_CLR         0x018       6       R0W   32b  Interrupt flag clear, read as 0
// reserved        0x01c
// CNT_ISSUE       0x020       8       RW    32b  Count issued HLAPIs
// CNT_FINISH      0x024       9       RW    32b  Count finished HLAPIs
// reserved        0x028-0x02f
// ISSUE           0x030       12      R0W   32b  Trigger HLAPI execution
// reserved        0x034
// TAIL            0x038       14      R     64b  Pointer to tail of HLAPI descriptor list
// SINGLE          0x040       16      R0W   64b  Pointer to descriptor for appending a single descriptor to the list, read as 0
// CONCAT_HEAD     0x048       18      RW    64b  Pointer to head of a list of descriptors to be appended to the list
// CONCAT_TAIL     0x050       20      RW    64b  Pointer to tail of a list of descriptors to be appended to the list
// PREFETCH        0x58        22      RW    64b  Pointer for prefetching next descriptor
// HLAPI_I_*       0x060       24      RW    32b  Block of HLAPI specific input parameters
//                -0x05c+NR*4  20+NR
// HLAPI_IO_CYCLES 0x070+NR*4  24+NR   RW    32b  HLAPI aggregate cycle count
// HLAPI_IO_COUNT  0x074+NR*4  25+NR   RW    32b  HLAPI aggregate invokation count
// HLAPI_O_RES     0x078+NR*4  26+NR   RW    32b  HLAPI result, output only
// HLAPI_O_STATUS  0x07c+NR*4  27+NR   RW    32b  HLAPI status, output only

// vcs -sverilog npu_types.sv npu_fifo.sv npu_shared_hl_ctrl_dma_mmio.sv npu_shared_hl_ctrl_dma_res.sv npu_shared_hl_ctrl_dma_mst.sv npu_shared_hl_ctrl_dma.sv
// analyze -format sverilog "../npu_types.sv ../npu_fifo.sv ../npu_shared_hl_ctrl_dma_mmio.sv ../npu_shared_hl_ctrl_dma_res.sv ../npu_shared_hl_ctrl_dma_mst.sv ../npu_shared_hl_ctrl_dma.sv"


`include "npu_defines.v"
`include "npu_macros.svh"
`include "npu_axi_macros.svh"

module npu_shared_hl_ctrl_dma
  import npu_types::*;
  #(
    parameter int  NC       = 1,             // Number of Cores
    parameter int  ID       = -1,            // module ID
    parameter int  MAJ      = -1,            // module major version
    parameter int  MIN      = -1,            // module minor version
    parameter int  SAXIIDW  = 1,             // AXI MMIO slave ID width
    parameter int  SAXIAWUW = 1,             // AXI MMIO slave AW user width
    parameter int  SAXIWUW  = 1,             // AXI MMIO slave W user width
    parameter int  SAXIBUW  = 1,             // AXI MMIO slave B user width
    parameter int  SAXIARUW = 1,             // AXI MMIO slave AR user width
    parameter int  SAXIRUW  = 1,             // AXI MMIO slave R user width
    parameter int  MAXIAWUW = 1,             // AXI MMIO slave AW user width
    parameter int  MAXIWUW  = 1,             // AXI MMIO slave W user width
    parameter int  MAXIBUW  = 1,             // AXI MMIO slave B user width
    parameter int  MAXIARUW = 1,             // AXI MMIO slave AR user width
    parameter int  MAXIRUW  = 1,             // AXI MMIO slave R user width
    parameter type T        = dummy_hlapi_i_t // HLAPI input descriptor type
  ) 
  (
   // System interface
   input  logic          clk,             // always-on clock
   input  logic          rst_a,           // asynchronous reset, active high, synchronous deassertion
   input  logic          test_mode,       // block datapath reset in testmode
   output logic          clk_en,          // clock enable for the accelerator compute core
   output logic          rst_dp,          // reset compute datapath
   output logic [NC-1:0] err_irq,         // common error interrupt
   output logic [NC-1:0] irq,             // interrupt request output, level sensitive
   output logic [NC-1:0] ievent,          // issue event output, pulse with duration of a minimum of 5 cycles
   output logic [NC-1:0] devent,          // done event output, pulse with duration of a minimum of 5 cycles
   
   // AXI MMIO interface 64b wide data
   `AXISLV(SAXIIDW,64,SAXIAWUW,SAXIWUW,SAXIBUW,SAXIARUW,SAXIRUW,mmio_axi_),

   // AXI DMA master interface for reading/writing descriptors 64b wide data
   `AXIMST(1,64,MAXIAWUW,MAXIWUW,MAXIBUW,MAXIARUW,MAXIRUW,mst_axi_),

   // Signals to accelerator datapath, controlled by valid/accept handshake
   output logic          hlapi_i_valid,   // new HLAPI issue descriptor valid
   input  logic          hlapi_i_accept,  // new HLAPI issue descriptor accept
   output T              hlapi_i,         // HLAPI input descriptor
   input  logic          hlapi_o_valid,   // new HLAPI output descriptor valid
   output logic          hlapi_o_accept,  // new HLAPI output descriptor accept
   input  logic [31:0]   hlapi_o_res,     // result from datapath to HLAPI
   input  logic [31:0]   hlapi_o_stat,    // result from datapath to HLAPI
   
   // trace interface
   `TRCMST(trace_,1)
   );
  //
  // local parameters
  //
  // number of 32b register in HLAPI,
  localparam int NR = $bits(T)/32; // number of 32b register in input HLAPI

  //
  // Local wires
  //
  // Descriptor append
  logic                    append_req;      // append a new descriptor
  logic                    append_ack;      // acknowledge descriptor append
  npu_axi_addr_t           append_tail;     // address of tail
  npu_axi_addr_t           append_new;      // new descriptor pointer
  // Descriptor read
  logic                    rd_descr_req;    // read a new descriptor
  logic                    rd_descr_ack;    // accept read command
  npu_axi_addr_t           rd_descr_addr;   // address of descriptor to read
  logic          [NR-1:0]  rd_descr_i_en;   // I register enable
  logic          [63:0]    rd_descr_data;   // descriptor read data
  // From MMIO to result pipeline
  logic                    out_rvalid;      // pending transaction
  logic                    out_raccept;     // pending transaction done
  logic                    out_rlst;        // llist based descriptor
  npu_axi_addr_t           out_raddr;       // abse address of list descriptor
  // Result handshake
  logic                    hlapi_io_en;     // Enable IO registers
  hlapi_io_t               hlapi_io_nxt;    // IO fields next
  hlapi_io_t               hlapi_io;        // IO fields
  logic                    hlapi_o_en;      // Enable O registers
  hlapi_o_t                hlapi_o_nxt;     // O fields next
  hlapi_o_t                hlapi_o;         // O fields
  // IO&O read/write
  logic                    io_rd_req;       // request IO read
  logic                    io_rd_ack;       // acknowledge IO read
  hlapi_io_t               io_rd;           // IO write data
  logic                    io_wr_req;       // request IO write
  logic                    io_wr_ack;       // acknowledge IO write
  npu_axi_addr_t           io_addr;         // IO address
  hlapi_io_t               io_wr;           // IO write data
  hlapi_o_t                o_wr;            // O write data
  logic                    err;             // If true then error

  
  //
  // MMIO registers and descriptor read
  //
  npu_shared_hl_ctrl_dma_mmio
  #(
    .NR       ( NR       ),
    .NC       ( NC       ),
    .ID       ( ID       ),
    .MAJ      ( MAJ      ),
    .MIN      ( MIN      ),
    .SAXIIDW  ( SAXIIDW  ),
    .SAXIAWUW ( SAXIAWUW ),
    .SAXIWUW  ( SAXIWUW  ),
    .SAXIBUW  ( SAXIBUW  ),
    .SAXIARUW ( SAXIARUW ),
    .SAXIRUW  ( SAXIRUW  ),
    .T        ( T        )
    )
  u_mmio_inst
    (
   .clk            ( clk            ),
   .rst_a          ( rst_a          ),
   .test_mode      ( test_mode      ),
   .clk_en         ( clk_en         ),
   .rst_dp         ( rst_dp         ),
   .err_irq        ( err_irq        ),
   .irq            ( irq            ),
   .ievent         ( ievent         ),
   .devent         ( devent         ),
   `AXIINST(mmio_axi_,mmio_axi_),
   .append_req     ( append_req     ),
   .append_ack     ( append_ack     ),
   .append_tail    ( append_tail    ),
   .append_new     ( append_new     ),
   .rd_descr_req   ( rd_descr_req   ),
   .rd_descr_ack   ( rd_descr_ack   ),
   .rd_descr_addr  ( rd_descr_addr  ),
   .rd_descr_i_en  ( rd_descr_i_en  ),
   .rd_descr_data  ( rd_descr_data  ),
   .hlapi_i_valid  ( hlapi_i_valid  ),
   .hlapi_i_accept ( hlapi_i_accept ),
   .hlapi_i        ( hlapi_i        ),
   .out_rvalid     ( out_rvalid     ),
   .out_raccept    ( out_raccept    ),
   .out_rlst       ( out_rlst       ),
   .out_raddr      ( out_raddr      ),
   .hlapi_io_en    ( hlapi_io_en    ),
   .hlapi_io_nxt   ( hlapi_io_nxt   ),
   .hlapi_io       ( hlapi_io       ),
   .hlapi_o_en     ( hlapi_o_en     ),
   .hlapi_o_nxt    ( hlapi_o_nxt    ),
   .hlapi_o        ( hlapi_o        ),
   .err            ( err            ),
   `TRCINST_S(trace_,trace_,0)
     );

  
  //
  // Processing and response handling
  //
  npu_shared_hl_ctrl_dma_res
    #(
      .NR ( NR )
      )
  u_res_inst
    (
   .clk            ( clk            ),
   .rst_a          ( rst_a          ),
   .out_rvalid     ( out_rvalid     ),
   .out_raccept    ( out_raccept    ),
   .out_rlst       ( out_rlst       ),
   .out_raddr      ( out_raddr      ),
   .hlapi_o_valid  ( hlapi_o_valid  ),
   .hlapi_o_accept ( hlapi_o_accept ),
   .hlapi_o_res    ( hlapi_o_res    ),
   .hlapi_o_stat   ( hlapi_o_stat   ),
   .io_rd_req      ( io_rd_req      ),
   .io_rd_ack      ( io_rd_ack      ),
   .io_rd          ( io_rd          ),
   .io_wr_req      ( io_wr_req      ),
   .io_wr_ack      ( io_wr_ack      ),
   .io_addr        ( io_addr        ),
   .io_wr          ( io_wr          ),
   .o_wr           ( o_wr           ),
   .hlapi_io_en    ( hlapi_io_en    ),
   .hlapi_io_nxt   ( hlapi_io_nxt   ),
   .hlapi_io       ( hlapi_io       ),
   .hlapi_o_en     ( hlapi_o_en     ),
   .hlapi_o_nxt    ( hlapi_o_nxt    ),
   .hlapi_o        ( hlapi_o        )
   );

  //
  // AXI descriptor read/write
  //
npu_shared_hl_ctrl_dma_mst
  #(
   .NR       ( NR       ),
   .MAXIAWUW ( MAXIAWUW ),
   .MAXIWUW  ( MAXIWUW  ),
   .MAXIBUW  ( MAXIBUW  ),
   .MAXIARUW ( MAXIARUW ),
   .MAXIRUW  ( MAXIRUW  )
    )
  u_mst_inst
  (
   .clk ( clk ),
   .rst_a ( rst_a ),
   `AXIINST(mst_axi_,mst_axi_),
   .rd_descr_req  ( rd_descr_req  ),
   .rd_descr_ack  ( rd_descr_ack  ),
   .rd_descr_addr ( rd_descr_addr ),
   .rd_descr_i_en ( rd_descr_i_en ),
   .rd_descr_data ( rd_descr_data ),
   .append_req    ( append_req    ),
   .append_ack    ( append_ack    ),
   .append_tail   ( append_tail   ),
   .append_new    ( append_new    ),
   .io_rd_req     ( io_rd_req     ),
   .io_rd_ack     ( io_rd_ack     ),
   .io_rd         ( io_rd         ),
   .io_wr_req     ( io_wr_req     ),
   .io_wr_ack     ( io_wr_ack     ),
   .io_addr       ( io_addr       ),
   .io_wr         ( io_wr         ),
   .o_wr          ( o_wr          ),
   .err           ( err           )
   );
  

`ifdef ABV_ON
  property pmul64;
  @(rst_a)  $bits(T)%64 == 0;
  endproperty : pmul64
  assert property (pmul64) else $fatal(1, "Error: HLAPI bits need to be multiple of 64");  
`endif
  
endmodule : npu_shared_hl_ctrl_dma
