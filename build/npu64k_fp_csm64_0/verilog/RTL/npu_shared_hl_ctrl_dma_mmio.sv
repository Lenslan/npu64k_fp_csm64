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
// PREFETCH        0x058       22      RW    64b  Pointer to descriptor to prefetch
// HLAPI_I_*       0x060       24      RW    32b  Block of HLAPI specific input parameters
//                -0x05c+NR*4  20+NR
// HLAPI_IO_CYCLES 0x070+NR*4  28+NR   RW    32b  HLAPI aggregate cycle count
// HLAPI_IO_COUNT  0x064+NR*4  29+NR   RW    32b  HLAPI aggregate invokation count
// HLAPI_O_RES     0x068+NR*4  30+NR   RW    32b  HLAPI result, output only
// HLAPI_O_STATUS  0x06c+NR*4  31+NR   RW    32b  HLAPI status, output only


`include "npu_defines.v"
`include "npu_macros.svh"
`include "npu_axi_macros.svh"

module npu_shared_hl_ctrl_dma_mmio
  import npu_types::*;
  #(
    parameter int  NR       = 4,             // Number of 32b registers
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
    parameter type T        = dummy_hlapi_i_t // HLAPI input descriptor type
  )
  (
   // System interface
   input  logic                    clk,             // always-on clock
   input  logic                    rst_a,           // asynchronous reset, active high, synchronous deassertion
   input  logic                    test_mode,       // block datapath reset in testmode
   output logic                    clk_en,          // clock enable for the accelerator compute core
   output logic                    rst_dp,          // reset compute datapath
   output logic          [NC-1:0]  err_irq,         // error interrrupt
   output logic          [NC-1:0]  irq,             // interrupt request output, level sensitive
   output logic          [NC-1:0]  ievent,          // issue event output, pulse with duration of a minimum of 5 cycles
   output logic          [NC-1:0]  devent,          // done event output, pulse with duration of a minimum of 5 cycles
   
   // AXI MMIO interface 64b wide data
// spyglass disable_block W240
// SMD: Declare but not read 
// SJ: Not used signals 
   `AXISLV(SAXIIDW,64,SAXIAWUW,SAXIWUW,SAXIBUW,SAXIARUW,SAXIRUW,mmio_axi_),
// spyglass enable_block W240

   // Descriptor append
   output logic                    append_req,      // append a new descriptor
   input  logic                    append_ack,      // acknowledge descriptor append
   output npu_axi_addr_t           append_tail,     // address of tail
   output npu_axi_addr_t           append_new,      // new descriptor pointer

   // Descriptor read
   output logic                    rd_descr_req,    // read a new descriptor
   input  logic                    rd_descr_ack,    // accept read command
   output npu_axi_addr_t           rd_descr_addr,   // address of descriptor to read
   input  logic          [NR-1:0]  rd_descr_i_en,   // I register enable
   input  logic          [63:0]    rd_descr_data,   // descriptor read data
   
   // Input HLAPI handshake
   output logic                    hlapi_i_valid,   // new HLAPI issue descriptor valid
   input  logic                    hlapi_i_accept,  // new HLAPI issue descriptor accept
   output T                        hlapi_i,         // HLAPI input descriptor

   // To result pipeline
   output logic                    out_rvalid,      // pending transaction
   input  logic                    out_raccept,     // pending transaction done
   output logic                    out_rlst,        // llist based descriptor
   output npu_axi_addr_t           out_raddr,       // abse address of list descriptor

   // Result handshake
   input  logic                    hlapi_io_en,     // Enable IO registers
   input  hlapi_io_t               hlapi_io_nxt,    // IO fields next
   output hlapi_io_t               hlapi_io,        // IO fields
   input  logic                    hlapi_o_en,      // Enable O registers
   input  hlapi_o_t                hlapi_o_nxt,     // O fields next
   output hlapi_o_t                hlapi_o,         // O fields

   // descriptor error pulse
   input  logic                    err,             // bus error

   // trace interface
   `TRCMST(trace_,1)
   );

  //
  // local parameters
  //
  // number of 32b register in HLAPI, add two for read/write regs at the end of the SW view
  localparam int HLAPI_I_BASE        = 24;          // 32b offset of input HLAPI registers
  localparam int HLAPI_IW_BASE       = 24;          // 32b offset of input HLAPI registers
  localparam int HLAPI_IO_BASE       = 24+NR;       // 32b offset of i/o registers, at the end of the input registers
  localparam int HLAPI_O_BASE        = 26+NR;       // 32b offset of output registers at the end of the input/output registers
  localparam int NUM_RGS             = 28+NR;       // total number of MMIO registers
  // MMIO register offsets, see table at head of the file
  localparam int MMIO_OS_ID          = 0;
  localparam int MMIO_OS_CTRL        = 1;
  localparam int MMIO_OS_STATUS      = 2;
  localparam int MMIO_OS_ENABLE      = 3;
  localparam int MMIO_OS_INT_STATUS  = 4;
  localparam int MMIO_OS_INT_SET     = 5;
  localparam int MMIO_OS_INT_CLR     = 6;
  localparam int MMIO_OS_CNT_ISSUE   = 8;
  localparam int MMIO_OS_CNT_FINISH  = 9;
  localparam int MMIO_OS_ISSUE       = 12;
  localparam int MMIO_OS_TAIL        = 14; // 64b!
  localparam int MMIO_OS_SINGLE      = 16; // 64b!
  localparam int MMIO_OS_CONCAT_HEAD = 18; // 64b!
  localparam int MMIO_OS_CONCAT_TAIL = 20; // 64b!
  localparam int MMIO_OS_PREFETCH    = 22; // 64b!

  localparam int MMIO_REG_ID                = 12'h000;
  localparam int MMIO_REG_CTRL              = 12'h004;
  localparam int MMIO_REG_STATUS            = 12'h008;
  localparam int MMIO_REG_INT_ENABLE        = 12'h00c;
  localparam int MMIO_REG_INT_STATUS        = 12'h010;
  localparam int MMIO_REG_INT_SET           = 12'h014;
  localparam int MMIO_REG_INT_CLR           = 12'h018;
  localparam int MMIO_REG_CNT_ISSUE         = 12'h020;
  localparam int MMIO_REG_CNT_FINISH        = 12'h024;
  localparam int MMIO_REG_ISSUE             = 12'h030;
  localparam int MMIO_REG_TAIL              = 12'h038;
  localparam int MMIO_REG_SINGLE_L          = 12'h040;
  localparam int MMIO_REG_SINGLE_H          = 12'h044;
  localparam int MMIO_REG_CONCAT_HEAD_L     = 12'h048;
  localparam int MMIO_REG_CONCAT_HEAD_H     = 12'h04c;
  localparam int MMIO_REG_CONCAT_TAIL_L     = 12'h050;
  localparam int MMIO_REG_CONCAT_TAIL_H     = 12'h054;
  localparam int MMIO_REG_PREFETCH_L        = 12'h058;
  localparam int MMIO_REG_PREFETCH_H        = 12'h05c;
  localparam int MMIO_REG_HLAPI_I_NEXT      = 12'h060;
  localparam int MMIO_REG_HLAPI_I_CTRL      = 12'h068;
  localparam int MMIO_REG_HLAPI_I_ID        = 12'h06c;
  localparam int MMIO_REG_HLAPI_IO_CYCLES   = 12'h060+NR*4; //"NR" include HLAPI_I regs
  localparam int MMIO_REG_HLAPI_IO_COUNT    = 12'h064+NR*4;
  localparam int MMIO_REG_HLAPI_O_RES       = 12'h068+NR*4;
  localparam int MMIO_REG_HLAPI_O_STATUS    = 12'h06c+NR*4;
  
  //
  // local types
  //
  // Control register
  typedef struct packed {
    logic clkfrc;        // force clock enable
    logic srst;          // softreset datapath
    logic halt;          // stop descriptor issue
  } mmio_ctrl_t;
  // MMIO issue state
  typedef enum logic [2:0] {
    mmio_state_idle_e         = 3'b000, // issue state is idle
    mmio_state_drd_e          = 3'b001, // reading the descriptor input fields into the MMIO registers
    mmio_state_issue_e        = 3'b010, // issue the descriptor from the MMIO registers
    mmio_state_append_e       = 3'b011, // append a new list to the list of descriptors
    mmio_state_issue_append_e = 3'b100  // issue the descriptor and append a new list to the list of descriptors
  } mmio_state_t;

  typedef struct packed {
    mmio_state_t state;  // MMIO read state
    logic        prefd;  // if true then prefetch complete
    logic        pref;   // if true then do prefetch
    logic        rst;    // if true then in reset
    logic        issued; // if true then computing is pending
    logic        append; // if true then need to append a new list
    logic        busy;   // if true then busy
    logic        lst;    // if true then active in list mode
    logic        sngl;   // if true then active in single mode
  } mmio_status_t;
  // AXI MMIO slave interface state
  typedef enum logic [8:0] { 
    saxi_rst_e   = 9'b0_0000_0001,          // reset state
    saxi_rcmd_e  = 9'b0_0000_0010,         // accept MMIO read command
    saxi_wcmd_e  = 9'b0_0000_0100,         // accept MMIO write command
    saxi_wdata_e = 9'b0_0000_1000,        // accept MMIO write data
    saxi_rdata_e = 9'b0_0001_0000,        // return MMIO read data
    saxi_bresp_e = 9'b0_0010_0000,        // return MMIO write OK response
    saxi_werr_e  = 9'b0_0100_0000,         // ignore remaining writes after error on MMIO
    saxi_berr_e  = 9'b0_1000_0000,         // return write error on MMIO
    saxi_rerr_e  = 9'b1_0000_0000         // ignore remaining reads after error on MMIO
  } saxi_state_t;

  
  //
  // local functions
  //
// spyglass disable_block W263 
// SMD: OutOfRangeIndex
// SJ: Index selection is limited 
  function automatic logic check_write(input logic [11:2] addr, input logic dual, input logic hir, input logic [7:0] wstrb);
    check_write = 1'b0;
    // check if an MMIO register is writable
    if ((addr[2] == 1'b1) && (wstrb[7:4] != 4'b0))
    begin
      casez (addr)
        // writeable regs
        MMIO_OS_CTRL,
        MMIO_OS_ENABLE,
        MMIO_OS_INT_SET,
        MMIO_OS_CNT_FINISH,
        MMIO_OS_SINGLE+1,
        MMIO_OS_CONCAT_HEAD+1,
        MMIO_OS_CONCAT_TAIL+1,
        MMIO_OS_PREFETCH+1,
        HLAPI_IO_BASE+1:
          // in range of single registers
          check_write = 1'b1;
        default:
          // in input HLAPI range
          check_write = hir;
      endcase
    end

    if ((addr[2] == 1'b0) && (wstrb[3:0] != 4'b0))
    begin
      casez (addr)
        MMIO_OS_INT_CLR,
        MMIO_OS_CNT_ISSUE,
        MMIO_OS_ISSUE,
        MMIO_OS_SINGLE,
        MMIO_OS_CONCAT_HEAD,
        MMIO_OS_CONCAT_TAIL,
        MMIO_OS_PREFETCH,
        HLAPI_IO_BASE:
          // in range of single registers
          check_write = 1'b1;
        default:
          // in input HLAPI range
          check_write = hir;
      endcase // casez (addr)
    end

    // second 32b
    if (dual && (wstrb[7:4] != 4'b0))
    begin
      casez ({addr[11:3],1'b1})
        // writeable regs
        MMIO_OS_CTRL,
        MMIO_OS_ENABLE,
        MMIO_OS_INT_SET,
        MMIO_OS_CNT_FINISH,
        MMIO_OS_SINGLE+1,
        MMIO_OS_CONCAT_HEAD+1,
        MMIO_OS_CONCAT_TAIL+1,
        MMIO_OS_PREFETCH+1,
        HLAPI_IO_BASE+1:
          // in range of single registers
          check_write = check_write;
      default:
          // in input HLAPI range
          check_write = hir;
      endcase // casez (addr)
    end
  endfunction : check_write
// spyglass enable_block W263 
  

  //
  // registers and wires
  //
  // MMIO registers and wires
  logic                        mmio_wen;             // register enables: true if register is written
  logic                        mmio_prefetch_l_en;
  logic                        mmio_prefetch_h_en;
  logic                        mmio_concat_tail_en;
  logic                        mmio_concat_head_en;
  logic                        mmio_tail_en;
  logic                        mmio_cnt_finish_en;
  logic                        mmio_cnt_issue_en;
  logic                        mmio_int_status_en;
  logic                        mmio_int_enable_en;
  logic                        mmio_status_en;
  logic                        mmio_ctrl_en;
  logic                        mmio_hlapi_o_en;
  logic                        mmio_hlapi_io_en;
  logic         [NR-1:0]       mmio_hlapi_i_en;
  logic         [63:0]         mmio_concat_tail_nxt;
  logic         [63:0]         mmio_concat_head_nxt;
  logic         [63:0]         mmio_prefetch_nxt;
  logic         [63:0]         mmio_tail_nxt;
  logic         [31:0]         mmio_cnt_finish_nxt;
  logic         [31:0]         mmio_cnt_issue_nxt;
  logic         [2*NC-1:0]     mmio_int_status_nxt; //Status: [NC-1:0] done; [NC+&:8] error
  logic         [2*NC-1:0]     mmio_int_enable_nxt; //Enable: [NC-1:0] done; [NC+7:8] error
  mmio_status_t                mmio_status_nxt;
  mmio_ctrl_t                  mmio_ctrl_nxt;
  hlapi_o_t                    mmio_hlapi_o_nxt;
  hlapi_io_t                   mmio_hlapi_io_nxt;
  logic         [NR-1:0][31:0] mmio_hlapi_i_nxt;
  logic         [NC-1:0]       err_irq_nxt;
  logic         [NC-1:0]       irq_nxt;
  logic         [63:0]         mmio_concat_tail_r;   // tail of concat list
  logic         [63:0]         mmio_concat_head_r;   // head of concat list
  logic         [63:0]         mmio_prefetch_r;      // prefetch register
  logic         [63:0]         mmio_tail_r;          // tail of descriptor list
  logic         [31:0]         mmio_cnt_finish_r;    // finish counter
  logic         [31:0]         mmio_cnt_issue_r;     // issue counter
  logic         [2*NC-1:0]     mmio_int_status_r;    // interrupt status
  logic         [2*NC-1:0]     mmio_int_enable_r;    // interrupt enable
  mmio_status_t                mmio_status_r;        // status bits
  logic                        mmio_issue_r;         // issue bit
  mmio_ctrl_t                  mmio_ctrl_r;          // halt, clock and reset control
  hlapi_io_t                   mmio_hlapi_io_r;      // HLAPI input/output registers
  hlapi_o_t                    mmio_hlapi_o_r;       // HLAPI output registers
  logic         [NR-1:0][31:0] mmio_hlapi_i_r;       // HLAPI input registers
  T                            hlapi_int;            // HLAPI struct
  logic         [NC-1:0]       err_irq_r;            // Error interrupt
  logic         [NC-1:0]       irq_r;                // interrupt request output
  // AXI slave state registers and wires
  logic                        saxi_state_en;        // AXI slave state register enable
  logic                        saxi_id_en;           // AXI slave update ID register
  saxi_state_t                 saxi_state_r;         // AXI slave state register
  saxi_state_t                 saxi_state_nxt;       // AXI slave state next
  logic                        saxi_size_r;          // AXI slave data size
  logic                        saxi_size_nxt;        // AXI slave data size
  logic                        saxi_cnt_en;          // AXI slave burst count register enable
  npu_axi_len_t                saxi_cnt_r;           // AXI slave burst count register
  logic         [11:2]         saxi_addr_r;          // AXI slave address register
  logic         [11:2]         saxi_addr_nxt;        // AXI slave address next
  npu_axi_len_t                saxi_cnt_nxt;         // AXI slave burst count register
  logic         [SAXIIDW-1:0]  saxi_id_r;            // AXI response ID
  logic         [SAXIIDW-1:0]  saxi_id_nxt;          // AXI response ID
  logic                        clken_r;              // registered clock enable clock for compute
  logic                        clken_nxt;
  logic                        rst_dp_r;             // reset datapath
  logic         [2*NC-1:0]     set_irq;              // set done and error interrupt
  logic                        hlapi_i_r_range;      // if true then MMIO in HLAPI input range
  logic                        hlapi_i_w_range;      // if true then MMIO in HLAPI input range
  logic         [11:2]         mmio_ridx;            // index of 32b HLAPI register
  logic                        out_wvalid;           // hadnshakes into fIFO
  logic                        out_waccept;
  logic                        out1_wvalid;
  logic         [3*NC-1:0]     out_wevt;             // output event bits
  logic         [3*NC-1:0]     out_revt;             // output event bits
  logic         [NC-1:0]       ievent_en;            // event outputs
  logic         [NC-1:0]       devent_en;
  logic         [NC-1:0][4:0]  ievent_nxt;
  logic         [NC-1:0][4:0]  devent_nxt;
  logic         [NC-1:0]       ievent_sw;
  logic         [NC-1:0]       devent_sw;
  logic         [NC-1:0][4:0]  ievent_r;
  logic         [NC-1:0][4:0]  devent_r;
  // trace signals
  logic                        trace_en;
  logic                        trace_ien;
  logic                        trace_den;
  logic                        trace_valid_r;
  logic                        trace_ivalid_r;
  logic                        trace_dvalid_r;
  logic                        trace_valid_d1;
  trace_id_t                   trace_id_r;
  trace_id_t                   trace_did_r;
  trace_id_t                   trace_iid_r;
  trace_id_t                   trace_id_nxt;
  logic                        trace_valid_nxt;
  logic                        trace_ivalid_nxt;
  logic                        trace_dvalid_nxt;
  
  logic                        mmio_rdata_hld;
  logic         [63:0]         mmio_rdata_shadow_r;  // shadow register of AXI rdata 
  logic         [63:0]         i_mmio_axi_rdata;     // Internal AXI rdata 
  logic                        rd_descr_prefetch;

  logic  [NPU_AXI_ADDR_W-1:0]  wb_next;              // MUX to select prefetch head to write-back 
  logic                        lock_perf_en;
  logic                        lock_perf_nxt;
  logic                        lock_perf_r;
  

  //
  // Clock enable for the compute core if busy or forced clock enable
  //
  // outputs: clken_r, rst_dp_r
// spyglass disable_block W402b
//SMD:Self generated reset
//SJ :Ignore
  assign clken_nxt = (mmio_status_r != {mmio_state_idle_e,8'b0}) || mmio_ctrl_r.clkfrc;
  always_ff @(posedge clk or
              posedge rst_a)
  begin : clkenrst_reg_PROC
    if (rst_a == 1'b1) 
    begin
      clken_r  <= 1'b1;
      rst_dp_r <= 1'b1;
    end
    else 
    begin
      clken_r  <= clken_nxt;
      rst_dp_r <= mmio_ctrl_r.srst;
    end
  end : clkenrst_reg_PROC
  assign clk_en = clken_r;
  assign rst_dp = test_mode ? rst_a : rst_dp_r;
// spyglass enable_block W402b
 

  //
  // Interrupt output
  //
  assign irq_nxt     = mmio_int_status_r[0+:NC]  & mmio_int_enable_r[0+:NC];
  assign err_irq_nxt = mmio_int_status_r[NC+:NC] & mmio_int_enable_r[NC+:NC];
  assign irq         = irq_r;
  assign err_irq     = err_irq_r;
  

  //
  // AXI MMIO interface, supports 32b and 64b linear bursts or single
  //
  // tied user signals
  assign mmio_axi_buser = '0;
  assign mmio_axi_ruser = '0;

  /// output ID
  assign mmio_axi_bid = saxi_id_r;
  assign mmio_axi_rid = saxi_id_r;

  // check if MMIO access is in MMIO input range
  assign hlapi_i_w_range = (saxi_addr_r[11:3] >= $unsigned(HLAPI_IW_BASE/2)) && (saxi_addr_r[11:3] < $unsigned(HLAPI_IO_BASE/2));
  assign hlapi_i_r_range = (saxi_addr_r[11:3] >= $unsigned(HLAPI_I_BASE/2)) && (saxi_addr_r[11:3] < $unsigned(HLAPI_IO_BASE/2));

  // compute index of HLAPI register
  assign mmio_ridx = saxi_addr_r - HLAPI_I_BASE;

  // output HLAPI
  assign hlapi_int = mmio_hlapi_i_r;
  always_comb
  begin : ho_PROC
    hlapi_i  = mmio_hlapi_i_r;
    // avoid glitch on next field when appending descriptor
    hlapi_i.common.next = '0;
  end : ho_PROC
  assign hlapi_io = mmio_hlapi_io_r;
  assign hlapi_o = mmio_hlapi_o_r;

  
  // AXI slave state dependent outputs and next state
  // outputs: saxi_state_en, saxi_id_en, saxi_cnt_en, saxi_state_nxt, saxi_cnt_nxt, saxi_id_nxt, saxi_addr_nxt,
  // mmio_wen, mmio_axi_awready, mmio_axi_wready, mmio_axi_bvalid, mmio_axi_bresp, mmio_axi_arready, mmio_axi_rvalid, mmio_axi_rresp, mmio_axi_rlast
  always_comb
  begin : saxi_next_PROC
    logic canwrite;
    canwrite = check_write(saxi_addr_r, saxi_size_r, hlapi_i_w_range, mmio_axi_wstrb);
    // defaults
    saxi_state_en    = 1'b0;
    saxi_id_en       = 1'b0;
    saxi_cnt_en      = 1'b0;
    saxi_state_nxt   = saxi_rcmd_e;
    saxi_size_nxt    = mmio_axi_ar.size == 3'd3;
    saxi_cnt_nxt     = saxi_cnt_r - 1'b1;
    saxi_addr_nxt    = saxi_addr_r + (saxi_size_r ? 10'd2 : 10'd1);
    saxi_id_nxt      = mmio_axi_arid;
    // default AXI outputs
    mmio_wen         = 1'b0;
    mmio_axi_awready = 1'b0;
    mmio_axi_wready  = 1'b0;
    mmio_axi_bvalid  = 1'b0;
    mmio_axi_bresp   = npu_axi_resp_okay_e;
    mmio_axi_arready = 1'b0;
    mmio_axi_rvalid  = 1'b0;
    mmio_axi_rresp   = npu_axi_resp_okay_e;
    mmio_axi_rlast   = saxi_cnt_r == 8'h00;
    // state dependent outputs
    casez (saxi_state_r)
    saxi_rst_e: 
      begin
        saxi_state_en  = 1'b1;
        saxi_state_nxt = saxi_rcmd_e;
      end
    saxi_rcmd_e: 
      begin
        // accept read command
        mmio_axi_arready = 1'b1;
        if (mmio_axi_arvalid) 
        begin
          saxi_state_en  = 1'b1;
          saxi_id_en     = 1'b1;
          saxi_cnt_en    = 1'b1;
          saxi_cnt_nxt   = mmio_axi_ar.len;
          saxi_addr_nxt  = {mmio_axi_ar.addr[11:3], mmio_axi_ar.addr[2] & (mmio_axi_ar.size == 3'd2)};
          // new read command accepted
          if ((mmio_axi_ar.size == 3'd2 || mmio_axi_ar.size == 3'd3) && (mmio_axi_ar.burst == npu_axi_burst_incr_e || mmio_axi_ar.len == 8'h00))
          begin
            // command is OK, start read data burst
            saxi_state_nxt  = saxi_rdata_e;
          end
          else
          begin
            // command is not OK, return errors
            saxi_state_nxt = saxi_rerr_e;
          end
        end
        else if (mmio_axi_awvalid) 
        begin
          // accept write command in next cycle
          saxi_state_en  = 1'b1;
          saxi_state_nxt = saxi_wcmd_e;
        end
      end
    saxi_rdata_e: 
      begin
        // return read data
        mmio_axi_rvalid = 1'b1;
        if (mmio_axi_rready)
        begin
          saxi_cnt_en    = 1'b1;
          if (saxi_cnt_r == 8'h00)
          begin
            saxi_state_en  = 1'b1;
            saxi_state_nxt = saxi_wcmd_e;
          end
        end
      end
    saxi_rerr_e: 
      begin
        // return read ERR response
        mmio_axi_rvalid = 1'b1;
        mmio_axi_rresp  = npu_axi_resp_slverr_e;
        if (mmio_axi_rready) 
        begin
          // done, accept next command
          saxi_cnt_en = 1'b1;
          if (saxi_cnt_r == 8'h00)
          begin
            saxi_state_en  = 1'b1;
            saxi_state_nxt = saxi_wcmd_e;
          end
        end
      end        
    saxi_wcmd_e: 
      begin
        // accept write command
        mmio_axi_awready = 1'b1;
        saxi_size_nxt  = mmio_axi_aw.size == 3'd3;
        saxi_id_nxt    = mmio_axi_awid;
        if (mmio_axi_awvalid) 
        begin
          saxi_state_en  = 1'b1;
          saxi_id_en     = 1'b1;
          saxi_cnt_en    = 1'b1;
          saxi_addr_nxt  = {mmio_axi_aw.addr[11:3], mmio_axi_aw.addr[2] & (mmio_axi_aw.size == 3'd2)};
          // new write command accepted
          if ((mmio_axi_aw.size == 2 || mmio_axi_aw.size == 3) && (mmio_axi_aw.burst == npu_axi_burst_incr_e || mmio_axi_aw.len == 8'h00))
          begin
            // command is OK, start write data burst
            saxi_state_nxt = saxi_wdata_e;
          end
          else
          begin
            // command is not OK, return errors
            saxi_state_nxt = saxi_werr_e;
          end
        end
        else if (mmio_axi_arvalid) 
        begin
          // accept read command in next cycle
          saxi_state_en  = 1'b1;
          saxi_state_nxt = saxi_rcmd_e;
        end
      end
    saxi_wdata_e:
      begin
        // stall as long as list append is pending
        if (!mmio_status_r.append)
        begin
          // accept write data
          mmio_axi_wready = 1'b1;
          if (mmio_axi_wvalid) 
          begin
            // new write data, update address
            saxi_cnt_en    = 1'b1;
            if (mmio_axi_wlast) 
            begin
              // done accepting write data
              saxi_state_en  = 1'b1;
              if (!canwrite && (mmio_axi_wstrb != '0))
              begin
                // not a writeable register, error response
                saxi_state_nxt = saxi_berr_e;
              end
              else
              begin
                // return OK
                saxi_state_nxt = saxi_bresp_e;
                mmio_wen = (mmio_axi_wstrb != '0) ? 1'b1 : 1'b0;
              end
            end
            else if (!canwrite && (mmio_axi_wstrb != '0))
            begin
              // not a writeable register, terminate remainder of burst
              saxi_state_en  = 1'b1;
              saxi_state_nxt = saxi_werr_e;
            end
            else
            begin
              mmio_wen = (mmio_axi_wstrb != '0) ? 1'b1 : 1'b0;
            end
          end
        end
      end // case: saxi_wdata_e
    saxi_bresp_e: 
      begin
        // return write OK response
        mmio_axi_bvalid = 1'b1;
        if (mmio_axi_bready) begin
          // done, accept next command
          saxi_state_en  = 1'b1;
          saxi_state_nxt = saxi_rcmd_e;
        end
      end 
    saxi_werr_e: 
      begin
        // terminate remainder of burst by accept write data
        mmio_axi_wready = 1'b1;
        if (mmio_axi_wlast && mmio_axi_wvalid) begin
          saxi_state_en  = 1'b1;
          saxi_state_nxt = saxi_berr_e;
        end
      end
    saxi_berr_e: 
      begin
        // return write ERR response
        mmio_axi_bvalid = 1'b1;
        mmio_axi_bresp  = npu_axi_resp_slverr_e;
        if (mmio_axi_bready) 
        begin
          // done, accept next command
          saxi_state_en  = 1'b1;
          saxi_state_nxt = saxi_rcmd_e;
        end
      end
    default:
      begin
        saxi_state_nxt = saxi_state_r;
        saxi_cnt_nxt   = saxi_cnt_r;
        saxi_addr_nxt  = saxi_addr_r;
      end    
    endcase // casez (saxi_state_r)
  end : saxi_next_PROC

  // AXI MMIO slave interface state registers
  always_ff @(posedge clk or
              posedge rst_a)
  begin : saxi_state_reg_PROC
    if (rst_a == 1'b1) 
    begin
      // reset
      saxi_state_r   <= saxi_rst_e;
      saxi_size_r    <= 1'b0;
      saxi_cnt_r     <= 8'h0;
      saxi_addr_r    <= 10'h0;
      saxi_id_r      <= {SAXIIDW{1'b0}};
      irq_r          <=  'b0;
      err_irq_r      <=  'b0;
    end
    else
    begin
      if (saxi_state_en)
      begin
        saxi_state_r <= saxi_state_nxt;
        saxi_size_r  <= saxi_size_nxt;
      end
      if (saxi_id_en)
      begin
        saxi_id_r    <= saxi_id_nxt;
      end
      if (saxi_cnt_en)
      begin
        saxi_addr_r  <= saxi_addr_nxt;
        saxi_cnt_r   <= saxi_cnt_nxt;
      end
      irq_r          <= irq_nxt;
      err_irq_r      <= err_irq_nxt;
    end
  end : saxi_state_reg_PROC

  
  //
  // MMIO register values
  //

// spyglass disable_block W263 
// SMD: OutOfRangeIndex
// SJ: Index selection is limited 
  // AXI MMIO read data
  // outputs: i_mmio_axi_rdata
  always_comb
  begin : saxi_rd_PROC
    // default
    i_mmio_axi_rdata = '0;
    casez (saxi_addr_r)
      MMIO_OS_ID,
      MMIO_OS_CTRL: // ID&control register
        begin 
          i_mmio_axi_rdata[7:0]                    = $unsigned(MIN);
          i_mmio_axi_rdata[15:8]                   = $unsigned(MAJ);
          i_mmio_axi_rdata[31:16]                  = $unsigned(ID);
          i_mmio_axi_rdata[32+:$bits(mmio_ctrl_t)] = mmio_ctrl_r;
        end
      MMIO_OS_STATUS,
      MMIO_OS_ENABLE: // status&enable
        // Always use copy of status regsiter to avoid value change during AXI transfer
        begin
          i_mmio_axi_rdata[$bits(mmio_status_t)-1:0] = mmio_status_r;
          i_mmio_axi_rdata[32+:NC] = mmio_int_enable_r[0+:NC];
          i_mmio_axi_rdata[40+:NC] = mmio_int_enable_r[NC+:NC];
        end
      MMIO_OS_INT_STATUS: // intstatus&intset
        begin
          i_mmio_axi_rdata[0+:NC] = mmio_int_status_r[0+:NC];
          i_mmio_axi_rdata[8+:NC] = mmio_int_status_r[NC+:NC];
        end
      // 3: intclr&reserved
      MMIO_OS_CNT_ISSUE,
      MMIO_OS_CNT_FINISH: // cntissue&cntfinish
        begin
          i_mmio_axi_rdata[31:0]  = mmio_cnt_issue_r;
          i_mmio_axi_rdata[63:32] = mmio_cnt_finish_r;
        end
      // 5 reserved
      // 6 issue&reserved
      MMIO_OS_TAIL: // tail
        begin
          i_mmio_axi_rdata        = mmio_tail_r;
        end
      // 8 single
      MMIO_OS_CONCAT_HEAD: // concathead
        begin
          i_mmio_axi_rdata        = mmio_concat_head_r;
        end
      MMIO_OS_CONCAT_TAIL: // concattail
        begin
          i_mmio_axi_rdata        = mmio_concat_tail_r;
        end
      MMIO_OS_PREFETCH: // prefetch
        begin
          i_mmio_axi_rdata        = '0;
        end
      HLAPI_IO_BASE,
      HLAPI_IO_BASE+1: // IO regs
        begin
          i_mmio_axi_rdata        = mmio_hlapi_io_r;
        end
      HLAPI_O_BASE,
      HLAPI_O_BASE+1: // O regs
        begin
          i_mmio_axi_rdata        = mmio_hlapi_o_r;
        end
      default:
        if (hlapi_i_r_range)
        begin
          // input HLAPI
// spyglass disable_block ImproperRangeIndex-ML WRN_1024 W164b
// SMD: OutOfRangeIndex
// SJ: Index selection is limited 
          int idx0, idx1;
          idx0 = $unsigned({mmio_ridx[11:3], 1'b0});
          i_mmio_axi_rdata[31:0] = mmio_hlapi_i_r[idx0];
          idx1 = $unsigned({mmio_ridx[11:3], 1'b1});
          i_mmio_axi_rdata[63:32] = mmio_hlapi_i_r[idx1];
        end
    endcase // casez (saxi_addr_r)
  end : saxi_rd_PROC
// spyglass enable_block ImproperRangeIndex-ML WRN_1024 W164b
// spyglass enable_block W263 
  
  // update MMIO registers and issue descriptor
  assign rd_descr_addr = rd_descr_prefetch ? mmio_prefetch_r[NPU_AXI_ADDR_W-1:0] : hlapi_int.common.next;
  assign append_tail   = mmio_tail_r[NPU_AXI_ADDR_W-1:0];
  assign append_new    = mmio_concat_head_r[NPU_AXI_ADDR_W-1:0];
  assign hlapi_i_valid = mmio_issue_r;
  // outputs: mmio*en, mmio*nxt, rd_descr_valid, out_wvalid, out1_wvalid, append_req
  always_comb
  begin : saxi_mmio_wr_PROC
    // default values
    mmio_hlapi_i_en       = rd_descr_i_en;
    mmio_hlapi_io_en      = hlapi_io_en;
    mmio_hlapi_o_en       = hlapi_o_en;
    mmio_tail_en          = 1'b0;
    mmio_concat_tail_en   = 1'b0;
    mmio_concat_head_en   = 1'b0;
    mmio_prefetch_l_en    = 1'b0;
    mmio_prefetch_h_en    = 1'b0;
    mmio_cnt_finish_en    = 1'b0;
    mmio_cnt_issue_en     = 1'b0;
    mmio_int_status_en    = 1'b0;
    mmio_int_enable_en    = 1'b0;
    mmio_status_en        = 1'b0;
    mmio_ctrl_en          = 1'b0;
    mmio_hlapi_i_nxt      = {(NR/2){rd_descr_data}};
    if (hlapi_io_en)
    begin
      mmio_hlapi_io_nxt   = hlapi_io_nxt;
    end
    else
    begin
      mmio_hlapi_io_nxt   = mmio_hlapi_io_r;
    end
    mmio_hlapi_o_nxt      = hlapi_o_nxt;
    mmio_tail_nxt         = mmio_tail_r;
    mmio_concat_tail_nxt  = mmio_concat_tail_r;
    mmio_concat_head_nxt  = mmio_concat_head_r;
    mmio_prefetch_nxt     = mmio_prefetch_r;
    mmio_cnt_finish_nxt   = mmio_cnt_finish_r + 'd1;
    mmio_cnt_issue_nxt    = mmio_cnt_issue_r + 'd1;
    mmio_int_status_nxt   = mmio_int_status_r;
    mmio_int_enable_nxt   = mmio_int_enable_r;
    mmio_status_nxt       = mmio_status_r;
    mmio_ctrl_nxt         = mmio_ctrl_r;
    append_req            = 1'b0;
    rd_descr_req          = 1'b0;
    out_wvalid            = 1'b0;
    out1_wvalid           = 1'b0;
    rd_descr_prefetch     = 1'b0;
    ievent_sw             = '0;
    devent_sw             = '0;
    // Updates from datapath
    mmio_int_status_en   |= (set_irq != 0);
    mmio_int_status_nxt  |=  set_irq;
    lock_perf_nxt         = lock_perf_r;
    lock_perf_en          = 1'b0;

    // AXI write
    if (mmio_wen) 
    begin
      // MMIO write operation
      if ((!saxi_addr_r[2]) && (mmio_axi_wstrb[3:0] != '0))
      begin
        // write even registers
        casez ({saxi_addr_r[11:3],3'b000})
          MMIO_REG_PREFETCH_L: 
            begin
              // lower concat tail
              mmio_prefetch_l_en          = 1'b1;
              mmio_prefetch_nxt[31:0]     = mmio_axi_wdata[31:0];
            end
          MMIO_REG_CONCAT_TAIL_L: 
            begin
              // lower concat tail
              mmio_concat_tail_en         = 1'b1;
              mmio_concat_tail_nxt[31:0]  = mmio_axi_wdata[31:0];
            end
          MMIO_REG_CONCAT_HEAD_L: 
            begin
              // lower concat head
              mmio_concat_head_en         = 1'b1;
              mmio_concat_head_nxt[31:0]  = mmio_axi_wdata[31:0];
            end
          MMIO_REG_SINGLE_L: 
            begin
              // issue a single descriptor low
              mmio_concat_head_en         = 1'b1;
              mmio_concat_tail_en         = 1'b1;
              mmio_concat_head_nxt[31:0]  = mmio_axi_wdata[31:0];
              mmio_concat_tail_nxt[31:0]  = mmio_axi_wdata[31:0];
            end
          MMIO_REG_ISSUE: 
            begin
              // issue register
              mmio_status_en              = 1'b1;
              mmio_status_nxt.sngl        = mmio_axi_wdata[0]; 
              mmio_status_nxt.append      = mmio_axi_wdata[1];
            end
          MMIO_REG_CNT_ISSUE: 
            begin
              // cnt_issue register
              mmio_cnt_issue_en           = 1'b1;
              mmio_cnt_issue_nxt          = mmio_axi_wdata[31:0];
            end
          MMIO_REG_INT_CLR: 
            begin
              // clear interrrupt
              mmio_int_status_en          = 1'b1;
              mmio_int_status_nxt         = mmio_int_status_r & {~mmio_axi_wdata[8], ~mmio_axi_wdata[NC-1:0]};
            end
// spyglass disable_block W263 
// SMD: OutOfRangeIndex
// SJ: Index selection is limited 
          MMIO_REG_HLAPI_IO_CYCLES:
            begin
              // write cycles
              mmio_hlapi_io_en            = 1'b1;
              mmio_hlapi_io_nxt.cycles    = mmio_axi_wdata[31:0];
            end
// spyglass enable_block W263 
          default:
            begin
              if (hlapi_i_w_range)
              begin
// spyglass disable_block ImproperRangeIndex-ML WRN_1024
// SMD: OutOfRangeIndex
// SJ: Index selection is limited 
                // hlapi input register
                mmio_hlapi_i_en[mmio_ridx]  = 1'b1; 
                mmio_hlapi_i_nxt[mmio_ridx] = mmio_axi_wdata[31:0];
// spyglass enable_block ImproperRangeIndex-ML WRN_1024
              end
            end
        endcase // casez ({saxi_addr_r[11:3],3'b000})
      end // if (!saxi_addr_r[2])
      if ((saxi_addr_r[2] || saxi_size_r) && (mmio_axi_wstrb[7:4] != '0))
      begin
        // write odd registers
        casez ({saxi_addr_r[11:3],3'b100})
          MMIO_REG_PREFETCH_H: 
            begin
              // lower concat tail
              mmio_prefetch_h_en           = 1'b1;
              mmio_prefetch_nxt[63:32]     = mmio_axi_wdata[63:32];
              mmio_status_en               = 1'b1;
              mmio_status_nxt.pref         = 1'b1;
              mmio_status_nxt.prefd        = 1'b0;
            end
          MMIO_REG_CONCAT_TAIL_H: 
            begin
              // upper concat tail
              mmio_concat_tail_en = 1'b1;
              mmio_concat_tail_nxt[63:32] = mmio_axi_wdata[63:32];
            end
          MMIO_REG_CONCAT_HEAD_H: 
            begin
              // upper concat head
              mmio_concat_head_en = 1'b1;
              mmio_concat_head_nxt[63:32] = mmio_axi_wdata[63:32];
            end
          MMIO_REG_SINGLE_H: 
            begin
              // issue a single descriptor high, auto trigger issue list
              mmio_status_en              = 1'b1;
              mmio_status_nxt.lst         = 1'b1;
              mmio_status_nxt.append      = 1'b1;
              mmio_concat_head_en         = 1'b1;
              mmio_concat_tail_en         = 1'b1;
              mmio_concat_head_nxt[63:32] = mmio_axi_wdata[63:32];
              mmio_concat_tail_nxt[63:32] = mmio_axi_wdata[63:32];
            end
          MMIO_REG_CNT_FINISH: 
            begin
              // cnt_finish register
              mmio_cnt_finish_en          = 1'b1;
              mmio_cnt_finish_nxt         = mmio_axi_wdata[63:32];
            end
          MMIO_REG_INT_SET: 
            begin
              // set interrupt
              mmio_int_status_en          = 1'b1;
              mmio_int_status_nxt         = mmio_int_status_r | {mmio_axi_wdata[NC+39:40], mmio_axi_wdata[NC+31:32]};
              // software triggers events
              devent_sw                   = mmio_axi_wdata[NC+47:48];
              ievent_sw                   = mmio_axi_wdata[NC+55:56];
            end
          MMIO_REG_INT_ENABLE: 
            begin
              // enable interrupt
              mmio_int_enable_en          = 1'b1;
              mmio_int_enable_nxt         = {mmio_axi_wdata[40+:NC] , mmio_axi_wdata[32+:NC]};
            end
          MMIO_REG_CTRL: 
            begin
              // control register
              mmio_ctrl_en                = 1'b1;
              mmio_ctrl_nxt               = mmio_axi_wdata[32+:$bits(mmio_ctrl_t)];
            end
// spyglass disable_block W263 
// SMD: OutOfRangeIndex
// SJ: Index selection is limited 
          MMIO_REG_HLAPI_IO_COUNT:
            begin
              // write count
              mmio_hlapi_io_en            = 1'b1;
              mmio_hlapi_io_nxt.count     = mmio_axi_wdata[63:32];
            end
// spyglass enable_block W263 
          default:
            begin
              if (hlapi_i_w_range)
              begin
                // hlapi input register
// spyglass disable_block ImproperRangeIndex-ML WRN_1024
// SMD: OutOfRangeIndex
// SJ: Index selection is limited 
                logic [11:2] idx1;
                idx1 = $unsigned({mmio_ridx[11:3], 1'b1});
                mmio_hlapi_i_en[idx1]  = 1'b1; 
                mmio_hlapi_i_nxt[idx1] = mmio_axi_wdata[63:32];
// spyglass enable_block ImproperRangeIndex-ML WRN_1024
              end
            end
        endcase // casez ({saxi_addr_r[11:3],3'b100})
      end // if (saxi_addr_r[2] || saxi_size_r)
    end // if (mmio_wen)

    // check if we can issue a new descriptor
    case (mmio_status_r.state)
    mmio_state_drd_e:
      begin
        // read a descriptor
        rd_descr_req            = 1'b1;
        if (mmio_status_r.lst && (lock_perf_r == 1'b0))
        begin
          // issue descriptor
          if (rd_descr_ack)
          begin
            // done reading, now issue the descriptor
            mmio_status_en        = 1'b1;
            mmio_status_nxt.prefd = 1'b0;
            mmio_status_nxt.state = mmio_state_issue_e;
            mmio_status_nxt.lst   = mmio_status_r.lst & (hlapi_int.common.next != '0);
          end
        end
        else //if (mmio_status_r.pref)
        begin
          // prefetch
          rd_descr_prefetch       = 1'b1;
          if (rd_descr_ack)
          begin
            lock_perf_nxt         = 1'b0;
            lock_perf_en          = 1'b1;
            // done reading, now back to idle 
            mmio_status_en        = 1'b1;
            mmio_status_nxt.pref  = 1'b0;
            mmio_status_nxt.prefd = 1'b1;
            mmio_status_nxt.state = mmio_state_idle_e;
          end
        end
      end
    mmio_state_issue_e:
      begin
        // issue the descriptor from the registers
        if (hlapi_i_accept) 
        begin
          out1_wvalid           = 1'b1;
          mmio_status_en        = 1'b1;
          mmio_status_nxt.state = mmio_state_idle_e;
          mmio_status_nxt.sngl  = 1'b0;
        end
        else if (mmio_status_r.append)
        begin
          mmio_status_en        = 1'b1;
          mmio_status_nxt.state = mmio_state_issue_append_e;
        end
      end
    mmio_state_issue_append_e:
      begin
        logic apdone;
        // issue the descriptor from the registers
        apdone        = 1'b0;
        if (hlapi_i_accept) 
        begin
          out1_wvalid           = 1'b1;
          mmio_status_en        = 1'b1;
          mmio_status_nxt.sngl  = 1'b0;
        end
        // append a list
        if (hlapi_int.common.next == 0)
        begin
          // append a list to an empty list
          mmio_status_en         = 1'b1;
          mmio_status_nxt.lst    = 1'b1;
          mmio_status_nxt.append = 1'b0;
          apdone                 = 1'b1;
          mmio_hlapi_i_en[0]     = 1'b1;
          mmio_hlapi_i_en[1]     = 1'b1;
          mmio_hlapi_i_nxt[0]    = mmio_concat_head_r[31:0];
          mmio_hlapi_i_nxt[1]    = mmio_concat_head_r[63:32];
          mmio_tail_en           = 1'b1;
          mmio_tail_nxt          = mmio_concat_tail_r;
        end
        else
        begin
          // append to a non-empty list
          append_req = 1'b1;
          if (append_ack)
          begin
            mmio_status_en         = 1'b1;
            mmio_status_nxt.lst    = 1'b1;
            mmio_status_nxt.append = 1'b0;
            apdone                 = 1'b1;
            // Update Tail to New Concate tail register
            mmio_tail_en           = 1'b1;
            mmio_tail_nxt          = mmio_concat_tail_r;
          end
        end
        case ({hlapi_i_accept, apdone}) 
        2'b11:
          begin
            // append and issue done
            mmio_status_nxt.state = mmio_state_idle_e;
          end
        2'b01:
          begin
            // append done and issue not done
            mmio_status_nxt.state = mmio_state_issue_e;
          end
        2'b10:
          begin
            // append not done and issue done
            mmio_status_nxt.state = mmio_state_append_e;
          end
        default:
          begin
            mmio_status_nxt.state = mmio_state_issue_append_e;
          end
        endcase // case ({hlapi_i_accept, apdone})
      end // case: mmio_state_issue_append_e
    mmio_state_append_e:
      begin
        // append a list
        if (hlapi_int.common.next == 0)
        begin
          // append a list to an empty list
          mmio_status_en         = 1'b1;
          mmio_status_nxt.lst    = 1'b1;
          mmio_status_nxt.append = 1'b0;
          mmio_status_nxt.state  = mmio_state_idle_e;    
          mmio_hlapi_i_en[0]     = 1'b1;
          mmio_hlapi_i_en[1]     = 1'b1;
          mmio_hlapi_i_nxt[0]    = mmio_concat_head_r[31:0];
          mmio_hlapi_i_nxt[1]    = mmio_concat_head_r[63:32];
          mmio_tail_en           = 1'b1;
          mmio_tail_nxt          = mmio_concat_tail_r;
        end
        else
        begin
          // append to a non-empty list
          append_req = 1'b1;
          if (append_ack)
          begin
            mmio_status_en         = 1'b1;
            mmio_status_nxt.lst    = 1'b1;
            mmio_status_nxt.append = 1'b0;
            mmio_status_nxt.state  = mmio_state_idle_e;    
            // Update Tail to New Concate tail register
            mmio_tail_en           = 1'b1;
            mmio_tail_nxt          = mmio_concat_tail_r;
          end
        end
      end
    mmio_state_idle_e:
      begin 
        if (mmio_ctrl_r.halt == 1'b0) begin
          // mmio_state_idle_e, issue state is idle
          if (mmio_status_r.sngl)
          begin
            // issue a single descriptor from the registers
            out_wvalid              = 1'b1;
            mmio_status_nxt.pref    = 1'b0;
            mmio_status_nxt.prefd   = 1'b0;
            if (out_waccept)
            begin
              mmio_status_en        = 1'b1;
              mmio_status_nxt.state = mmio_state_issue_e;
            end
          end
          else if (mmio_status_r.append)
          begin
            if (mmio_status_r.prefd && hlapi_int.common.next == '0 && mmio_concat_head_r == mmio_prefetch_r && mmio_concat_tail_r == mmio_prefetch_r)
            begin
              // try to issue a prefetched descriptor
              out_wvalid              = 1'b1;
              if (out_waccept)
              begin
                // issue prefetched descriptor
                mmio_status_en         = 1'b1;
                mmio_status_nxt.state  = mmio_state_issue_e;
                mmio_status_nxt.prefd  = 1'b0;
                mmio_status_nxt.append = 1'b0;
                mmio_status_nxt.lst    = 1'b0;
                mmio_tail_en           = 1'b1;
                mmio_tail_nxt          = mmio_concat_tail_r;
              end
            end
            else
            begin
              // append a list to the list
              mmio_status_en          = 1'b1;
              mmio_status_nxt.state   = mmio_state_append_e;   
            end
          end
          else if (mmio_status_r.lst)
          begin
            // try issue a list descriptor
            out_wvalid              = 1'b1;
            if (out_waccept)
            begin
              // read new descriptor
              mmio_status_en        = 1'b1;
              mmio_status_nxt.state = mmio_state_drd_e;
            end
          end
          else if (mmio_status_r.pref)
          begin
            // prefetch a descriptor
            mmio_status_en        = 1'b1;
            mmio_status_nxt.state = mmio_state_drd_e;
            lock_perf_nxt         = 1'b1;
            lock_perf_en          = 1'b1;
          end
        end // if (mmio_ctrl_r.halt == 1'b0)
      end // case: default
      default:
      begin
        mmio_cnt_finish_nxt = mmio_cnt_finish_r;
        mmio_cnt_issue_nxt  = mmio_cnt_issue_r;
      end
    endcase // case (mmio_status_r.state)
    // status busy bit
    mmio_status_nxt.busy   = (mmio_status_nxt.state != mmio_state_idle_e) || mmio_status_nxt.append || mmio_status_nxt.sngl || mmio_status_nxt.lst || out1_wvalid || out_rvalid;
    mmio_status_nxt.issued = (mmio_status_nxt.state != mmio_state_idle_e) || mmio_status_nxt.append || mmio_status_nxt.sngl || mmio_status_nxt.lst;
    mmio_status_nxt.rst    = mmio_ctrl_r.srst && (rst_dp_r == 1'b0);
    if ((mmio_status_nxt.busy   != mmio_status_r.busy) ||
        (mmio_status_nxt.rst    != mmio_status_r.rst)  ||
        (mmio_status_nxt.issued != mmio_status_r.issued)
       )
    begin
      mmio_status_en        = 1'b1;
    end
    mmio_cnt_finish_en    |= out_rvalid & out_raccept;
    mmio_cnt_issue_en     |= out1_wvalid;
  end : saxi_mmio_wr_PROC
  
  // MMIO registers
  // outputs: mmio*_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : saxi_mmio_reg_PROC
    if (rst_a == 1'b1) 
    begin
      mmio_hlapi_i_r      <= '0;
      mmio_hlapi_io_r     <= '0;
      mmio_hlapi_o_r      <= '0;
      mmio_concat_tail_r  <= '0;
      mmio_concat_head_r  <= '0;
      mmio_tail_r         <= '0;
      mmio_status_r       <= {mmio_state_idle_e,8'b0};
      mmio_issue_r        <= '0;
      mmio_cnt_finish_r   <= '0;
      mmio_cnt_issue_r    <= '0;
      mmio_int_status_r   <= '0;
      mmio_int_enable_r   <= '0;
`ifdef NPU_ENABLE_DP_CLOCK_GATE
      mmio_ctrl_r         <= 3'b000;
`else
      mmio_ctrl_r         <= 3'b100;
`endif
      mmio_prefetch_r     <= '0;
      lock_perf_r         <= '0;
    end
    else
    begin
      if (mmio_prefetch_h_en)
      begin
        mmio_prefetch_r[63:32] <= mmio_prefetch_nxt[63:32];
      end
      if (mmio_prefetch_l_en)
      begin
        mmio_prefetch_r[31:0]  <= mmio_prefetch_nxt[31:0];
      end
      if (mmio_concat_tail_en)
      begin
        mmio_concat_tail_r <= mmio_concat_tail_nxt;
      end
      if (mmio_concat_head_en)
      begin
        mmio_concat_head_r <= mmio_concat_head_nxt;
      end
      if (mmio_tail_en)
      begin
        mmio_tail_r        <= mmio_tail_nxt;
      end
      if (mmio_cnt_finish_en)
      begin
        mmio_cnt_finish_r  <= mmio_cnt_finish_nxt;
      end
      if (mmio_cnt_issue_en)
      begin
        mmio_cnt_issue_r   <= mmio_cnt_issue_nxt;
      end
      if (mmio_int_status_en)
      begin
        mmio_int_status_r  <= mmio_int_status_nxt;
      end
      if (mmio_int_enable_en)
      begin
        mmio_int_enable_r  <= mmio_int_enable_nxt;
      end
// spyglass disable_block Ar_converge02
//SMD:Async reset signal other use
//SJ :Ignore
      if (mmio_status_en)
      begin
        mmio_status_r      <= mmio_status_nxt;
        mmio_issue_r       <= mmio_status_nxt.state == mmio_state_issue_e || mmio_status_nxt.state == mmio_state_issue_append_e;
      end
// spyglass enable_block Ar_converge02
      if (lock_perf_en)
      begin
        lock_perf_r        <= lock_perf_nxt;
      end
      if (mmio_ctrl_en)
      begin
        mmio_ctrl_r        <= mmio_ctrl_nxt;
      end
      if (mmio_hlapi_o_en)
      begin
        mmio_hlapi_o_r     <= mmio_hlapi_o_nxt;
      end
      if (mmio_hlapi_io_en)
      begin
        mmio_hlapi_io_r    <= mmio_hlapi_io_nxt;
      end
      for (int i = 0; i < NR; i++)
      begin
        if (mmio_hlapi_i_en[i])
        begin
          mmio_hlapi_i_r[i] <= mmio_hlapi_i_nxt[i];
        end
      end
    end // else: !if(rst_a == 1'b1)
  end : saxi_mmio_reg_PROC

// spyglass disable_block W164a
//SMD:Width mismatch
//SJ :Ignore
  assign wb_next  = (hlapi_int.common.next == 'b0) ? (mmio_status_r.prefd ? mmio_concat_tail_r : mmio_tail_r[NPU_AXI_ADDR_W-1:0]) : hlapi_int.common.next;
// spyglass enable_block W164a
// spyglass disable_block W287b
// SMD: disconnect signal 
// SJ: Intended open 
  //
  // FIFOs for tracking pending HLAPI operations
  //
  npu_fifo 
  #(
    .SIZE          ( 2                    ),
    .DWIDTH        ( NPU_AXI_ADDR_W+1     ),
    .FRCVAL        ( 1                    ),
    .FRCACC        ( 0                    )
  )
  u_fifo_inst
  (           
     .clk          ( clk                  ),
     .rst_a        ( rst_a                ),
     .valid_write  ( out_wvalid           ), 
     .accept_write ( out_waccept          ),
     .data_write   ( {mmio_status_r.lst, wb_next} ),
     .valid_read   (                      ), // intentionally open
     .accept_read  ( out_raccept          ),
     .data_read    ( {out_rlst,out_raddr} )
  );
  logic [31:0] out_wid;
  logic [31:0] out_rid;
  assign out_wid  = hlapi_int.common.id;
  assign out_wevt = {hlapi_int.common.ctrl.interrupt[NC-1:0], hlapi_int.common.ctrl.ievent[NC-1:0], hlapi_int.common.ctrl.devent[NC-1:0]};
  npu_fifo 
  #(
    .SIZE          ( 2                   ),
    .DWIDTH        ( 32+3*NC             ),
    .FRCVAL        ( 0                   ),
    .FRCACC        ( 1                   )
    )
  u_fifo1_inst
  (           
     .clk          ( clk                 ),
     .rst_a        ( rst_a               ),
     .valid_write  ( out1_wvalid         ),
     .accept_write (                     ), // intentionally open
     .data_write   ( {out_wid,out_wevt}  ),
     .valid_read   ( out_rvalid          ),
     .accept_read  ( out_raccept         ),
     .data_read    ( {out_rid,out_revt}  )
  );
// spyglass enable_block W287b


  //
  // Events, interrupts and tracing
  //
  
  // set interrupt bits
  assign set_irq[0+:NC]   = out_rvalid & out_raccept       ? out_revt[2*NC+:NC] : '0;
  assign set_irq[NC+:NC]  = {NC{err}};
  
// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self determined expression
// SJ: Intended used
  // event outputs next state
  // outputs: ievent, devent, ievent_nxt, devent_nxt, ievent_en, devent_en
  always_comb
    begin : evt_nxt_PROC
      for (int i = 0; i < NC; i++)
      begin
        // event outputs
        ievent[i] = ievent_r[i][0];
        devent[i] = devent_r[i][0];
        // update state
        if ((hlapi_i_valid & hlapi_i_accept & out_wevt[NC+i]) | ievent_sw[i])
        begin
          // new issue event
          ievent_nxt[i] = '1;
          ievent_en[i]  = 1'b1;
        end
        else
        begin
          // shift issue delay line by 1
          ievent_nxt[i] = { 1'b0, ievent_r[i][4:1] };
          ievent_en[i]  = ievent[i];
        end
        if ((out_rvalid & out_raccept & out_revt[i]) | devent_sw[i])
        begin
          // new done event
          devent_nxt[i] = '1;
          devent_en[i]  = 1'b1;   
        end
        else
        begin
          // shift done delay line by 1
          devent_nxt[i] = { 1'b0, devent_r[i][4:1] };
          devent_en[i]  = devent[i];
        end
      end
    end : evt_nxt_PROC
// spyglass enable_block SelfDeterminedExpr-ML
  
  // event state
  // outputs: ievent_r, devent_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : evt_reg_PROC
    if (rst_a == 1'b1)
    begin
      ievent_r <= '0;
      devent_r <= '0;
    end
    else 
    begin
      for (int i = 0; i < NC; i++) 
      begin
        if (ievent_en[i])
        begin
          ievent_r[i] <= ievent_nxt[i];
        end
        if (devent_en[i])
        begin
          devent_r[i] <= devent_nxt[i];
        end
      end
    end  
  end : evt_reg_PROC

`ifdef ABV_ON
  //
  // Assertions
  //
  for (genvar gc = 0; gc < NC; gc++)
  begin : prop_GEN
    property prop_devt;
    @(posedge clk) disable iff (rst_a == 1'b1) devent_nxt[gc][4] |-> !devent_r[gc][0];
    endproperty : prop_devt
    property prop_ievt;
    @(posedge clk) disable iff (rst_a == 1'b1) ievent_nxt[gc][4] |-> !ievent_r[gc][0];
    endproperty : prop_ievt
    a_devt: assert property (prop_devt) else $fatal(1, "Error: done event overlap");
    a_ievt: assert property (prop_ievt) else $fatal(1, "Error: issue event overlap");
  end : prop_GEN
`endif
 

  // next trace state
  // outputs: trace_valid_nxt, trace_ivalid_nxt, trace_dvalid_nxt, trace_en, trace_ien, trace_den, trace_id_nxt
  always_comb
  begin : trace_nxt_PROC
    // defaults
    trace_valid_nxt  = trace_valid_r;
    trace_ivalid_nxt = trace_ivalid_r;
    trace_dvalid_nxt = trace_dvalid_r;
    trace_en         = 1'b0;
    trace_ien        = 1'b0;
    trace_den        = 1'b0;
    trace_id_nxt     = {1'b1,trace_did_r[30:0]};
    // check if trace accepts
    if (trace_accept)
    begin
      trace_valid_nxt = 1'b0;
    end
    // check if new event can be traced
    // to guarantee multi-cycle stability, new event can only be issued after old event finishes for 2 cycles
    if (~trace_valid_nxt & ~trace_valid_r & ~trace_valid_d1)
    begin
      if (trace_dvalid_r)
      begin
        // done event
        trace_dvalid_nxt = 1'b0;
        trace_valid_nxt  = 1'b1;
        trace_en         = 1'b1;
      end
      else if (trace_ivalid_r)
      begin
        // issue event
        trace_ivalid_nxt = 1'b0;
        trace_valid_nxt  = 1'b1;
        trace_en         = 1'b1;
        trace_id_nxt     = {1'b0,trace_iid_r[30:0]};
      end
    end
    // add new events
    if (out1_wvalid)
    begin
      trace_ivalid_nxt = 1'b1;
      trace_ien        = 1'b1;
    end
    if (out_rvalid & out_raccept)
    begin
      trace_dvalid_nxt = 1'b1;
      trace_den        = 1'b1;
    end
  end : trace_nxt_PROC
  
  // outputs: trace_valid_r, trace_ivalid_r, trace_dvalid_r, trace_id_r, trace_iid_r, trace_did_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : trace_reg_PROC
    if (rst_a == 1'b1)
    begin
      trace_valid_r  <= 1'b0;
      trace_ivalid_r <= 1'b0;
      trace_dvalid_r <= 1'b0;
      trace_id_r     <= 'd0;
      trace_iid_r    <= 'd0;
      trace_did_r    <= 'd0;
      trace_valid_d1 <= 1'b0;
    end
    else
    begin
      trace_valid_r  <= trace_valid_nxt;
      trace_ivalid_r <= trace_ivalid_nxt;
      trace_dvalid_r <= trace_dvalid_nxt;
      trace_valid_d1 <= trace_valid_r;
      if (trace_en)
      begin
        trace_id_r <= trace_id_nxt;
      end
      if (trace_ien)
      begin
        trace_iid_r <= out_wid;
      end
      if (trace_den)
      begin
        trace_did_r <= out_rid;
      end
    end
  end : trace_reg_PROC
    
  // assign trace outputs from flops
  assign trace_valid = trace_valid_r;
  assign trace_id    = trace_id_r;

  // hold value: hold rdata when rready not assert
  always_ff @(posedge clk or
              posedge rst_a)
  begin : hold_rdata_reg_PROC
    if (rst_a == 1'b1)
    begin
      mmio_rdata_hld       <= 'd0;
      mmio_rdata_shadow_r  <= 'd0;
    end
    else
    begin
      if (saxi_state_r == saxi_rdata_e) 
      begin 
        mmio_rdata_hld   <= ~mmio_axi_rready;
        if ((mmio_axi_rready == 1'b0) && (mmio_rdata_hld == 1'b0))
        begin
          mmio_rdata_shadow_r  <= i_mmio_axi_rdata;
        end
      end
    end
  end : hold_rdata_reg_PROC
    
  assign mmio_axi_rdata = (mmio_rdata_hld == 1'b1) ? mmio_rdata_shadow_r : i_mmio_axi_rdata;
endmodule : npu_shared_hl_ctrl_dma_mmio
