// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2020-2023 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2011, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

//----------------------------------------------------------------------------
//
//
//
//
// ===========================================================================
//
// Description:
//   Support for RASCAL pipe monitor (simulation only).
/*

Module rtl_pipemon supports RASCAL pipemon.  It provides to pipemon five kinds
of information:

- instruction(s) executed at the commit point
- the address of issued loads
- the address and, optionally, the data of issued stores
- the register/register pair and data of any writebacks.
- the flags zncv

pipemon inspects rtl_pipemon for internally declared signals that provide the
above information.  Those signals need not be output from npuarc_rtl_pipemon.

The pipemon module is recogized if it contains the signal

    wire [31:0]             pipemon_config;      // configuration register
    reg [3:0]               zncv;
(We may change zncv to status32 in the near future.)

pipemon_config fields:
    7:0    -- 6 for 64-bit cores, and 4 for 32-bit cores.
    8      -- if 1, a vector vdsp bundle signal is present in the instruction interface.
    11:9   -- size of floating-point registers in powers of 2.
              Valid values are >= 2.  Typical: 2, 3
              A value of < 2 means there are no floating-point registers.
    12     -- instr(ix>_uop bit is included in the instruction interface.
    Remainder of the fields are 0.

The quantity of each kind of information may be different in different
instantiations of npuarc_rtl_pipemon.   The quantity is identified by these four signals:

    wire [1:0]              num_instrs;           // Up to 3.
    wire [1:0]              num_stores;           // Up to 3.
    wire [1:0]              num_loads;            // Up to 3.
    wire [2:0]              num_writebacks;       // Up to 7.
    // looks at num_fpwritebacks only if pipemon_config
    // declares a valid size for the floating-point registers.
    wire [2:0]              num_fpwritebacks;     // Up to 7.
(You can increase the range to support larger values.  RASCAL loads the
signal value as a 32-bit quantity.)

The range 1:0 above is just an example; RASCAL pipemon will read these
signals as 32 bit quantities.

Instructions
------------

For each instruction, RASCAL pipemon expects these signals to be declared:

    reg                instr<ix>_valid;        // instr is valid.
    reg                instr<ix>_is_16_bit;    // Instr is 16-bit
    reg [31:0]         instr<ix>_inst;         // Instruction.  If 16-bit, it's in the upper half.
    reg                instr<ix>_limm_valid;   // limm valid for this instruction
    reg [31:0]         instr<ix>_limm;         // limm value
    reg [`PMON_PC_RANGE] instr<ix>_pc;         // PC of this instruction
    reg                instr<ix>_pipe;         // Pipe index 0, 1, ... N-1.
    reg                instr<ix>_debug;        // Debug instr
    reg                instr<ix>_uop;          // UOP instr. (if bit 12 of config)
    reg [`BUNDLE_RANGE] instr<ix>_vdsp;        // Only if bit 8 of pipemon_config.

where <ix> is the index: 0, 1, 2... of the instruction.  Dual-issue HS
cores use indexes 0 and 1; single-issue cores use just index 0.
However, RASCAL pipemon is capable of displaying any number of pipes.

An instruction is valid only if instr<ix>_valid is true.
If more than one instruction is valid, the execution order of the instructions
must be the same as the indices.  E.g. for dual-issue, index 0 designates
the first executed instruction, and 1 the second.  RASCAL pipemon uses
the instruction pipe value to show which pipe the instruction executed from.

If an instruction is valid, debug is false, and the vdsp signal is present,
the vdsp bundle is checked for a valid bundle (one of certain major opcodes).
If so, RASCAL pipemon disassembles the bundle; otherwise it disassembles the inst.

Pipeline support
----------------
If bit 13 is set in pipemon_config, each instruction pipe is accompanied by 
the following signal:

    reg [`PIPELINE_RANGE] instr<ix>_pipeline;        // Only if bit 13 of pipemon_config.

PIPELINE_RANGE is a multiple of 8 bits; the size is dynamically discovered
by RASCAL pipemon.  It is a string of bytes B1 B2 ... Bn where each byte Bn
is the bottom byte of the PC in pipeline stage n.  If B is odd, a bubble is denoted.
The display in RASCAL pipeline could look something like this, where .. denotes
a bubble:

    f2|f0|ec|..|e6|e4|e0

e0 corresponds to an instruction being executed, as it's the last pipeline stage.

In a multiple-issue core the pipelines are printed side-by-side, pipe 0 at the left:

    f4|..|d2|cc|c8|b6|ae // f6|d4|d0|ca|c6|..|ac

In this case instructions ad ae and ac are being executed.

Writebacks
------------
For each writeback, RASCAL pipemon expects these signals to be declared:

    reg                wb<ix>_valid;           // wb is valid.
    reg [2:0]          wb<ix>_size;            // power of 2: 2^wb<ix>size = 1/2/4/8/16.
    reg [`npuarc_DATA_RANGE]  wb<ix>_data_lo;
    reg [`npuarc_DATA_RANGE]  wb<ix>_data_hi;
    reg [5:0]          wb<ix>_reg;

A writeback is valid only if wb<ix>_valid is true.
RASCAL pipemon prints the register wb<ix>_reg and its associated data_lo value.
If the size is greater than that of a single register, RASCAL pipemon assumes
the writeback is a register pair, and prints wb<ix>_reg+1 and the data_hi value.
The size of a register is determined from the pipemon_config value.

A writeback print looks like:
         w1: r4  <- 01020304 r5  <- 01020307
This happens to be a register pair r4/r5 on writeback 1.

For each FPU register writeback, RASCAL pipemon expects these signals to be declared:

    reg [1:0]          fpwb<ix>_valid;           // wb is valid.
    reg [2:0]          fpwb<ix>_size;            // power of 2: 2^wb<ix>size = 1/2/4/8/16.
    reg [`npuarc_DATA_RANGE]  fpwb<ix>_data_lo;
    reg [`npuarc_DATA_RANGE]  fpwb<ix>_data_hi;
    reg [5:0]          fpwb<ix>_reg;

A writeback is valid only if fpwb<ix>_valid[0] is true.
RASCAL pipemon prints the register fpwb<ix>_reg and its associated data_lo value.
If the size is greater than that of a single FPU register, RASCAL pipemon assumes
the writeback is a register pair, and prints fpwb<ix>_reg+1 and the data_hi value.
The size of a register is determined from the pipemon_config value.

The result is written to the register file if bit 0 of _valid is true.
If bit 0 is 0 but bit 1 is 1, the writeback was squashed.

A writeback print looks like:
         w1: f4  <- 01020304 f5  <- 01020307
This happens to be a register pair f4/f5 on writeback 1.

The size of an FPU register is specified in pipemon_config.

Loads
------------
For each load, RASCAL pipemon expects these signals to be declared:

    reg                load<ix>_valid;        // load inst.
    reg [2:0]          load<ix>_size;         // load size, power of 2.
    reg [`npuarc_ADDR_RANGE]  load<ix>_addr;         // load addr.

A load is valid only if load<ix>_valid is true.
RASCAL pipemon prints the address of the load, but not the result, as it
is unavailable.  The size of the load may be printed by RASCAL pipemon.

A load print looks like:
        ld [1000]

Stores
------------
For each store, RASCAL pipemon expects these signals to be declared:

    reg                store<ix>_valid;        // store inst.
    reg [2:0]          store<ix>_size;         // store size, power of 2.
    reg [`npuarc_DATA_RANGE]  store<ix>_data_lo;      // store data.
    reg [`npuarc_DATA_RANGE]  store<ix>_data_hi;      // store data.
    reg                store<ix>_data_valid;   // store data valid at time of commit.
    reg [`npuarc_ADDR_RANGE]  store<ix>_addr;         // store addr.

A store is valid only if store<ix>_valid is true.
RASCAL pipemon prints the address of the store, and may print its size.
    reg                store<ix>_data_valid;   // store data valid at time of commit.
The data is printed if avalable.

A store print looks like:
    st 1020307 -> [1004]
or, if data is unavailable, like this:
    st ____ -> [1004]


Synthesis issues
----------------
npuarc_rtl_pipemon is designed so that if SYNTHESIS is defined, it disappears.

Presently, it is operational for HS 32-bit only if RTL_PIPEMON is defined
when compiling the RTL.  After final testing it will be enabled by default.
It is always operational for HS 64-bit.

*/

//
// ===========================================================================

// Include definitions for the microcode constants, including both ARC
// base-case and any User extension instructions which may be defined.
//

// Set simulation timescale
//
`include "const.def"


`define PMON_PC_RANGE 31:0



`ifdef npuarc_RTL_PIPEMON  // {
`ifdef SYNTHESIS // {
`undef npuarc_RTL_PIPEMON
`endif // }
`endif // }




module npuarc_rtl_pipemon (
  ////////// Clock and reset //////////////////////////////////////////
  //
  input                     clk,
  input                     rst_a,


  ////////// Interface with DA stage, pipe 0 /////////////////////////////
  //
  input                     da_0_valid_r,
  input                     da_0_pass,
  input                     da_0_is_16bit_r,
  input [31:0]       da_0_inst_r,
  input                     da_0_has_limm_r ,
  input [31:0]       da_0_limm_r,

  ////////// Interface with SA .. CA stages, pipe 0 /////////////////////
  //
  input                     sa_0_pass,
  input                     x1_0_pass,
  input                     x2_0_pass,
  input                     x3_0_pass,
  input                     ca_0_pass,
  input [`PMON_PC_RANGE]    ca_0_pc,


  input [`PMON_PC_RANGE]    ar_pc,
  input [3:0]               ar_zncv,

  ////////// Debug interface ////////////////////////////////////////////////////////
  //
  input                     db_active,           // Debugger inserted instruction

  ////////// Micro-op sequencer //////////////////////////////////////////////////////
  //
  input                     ca_uop_active_r,     // CA instruction are part of micro-op

  ////////// LD/ST interface //////////////////////////////////////////////////////
  //
  input                     ca_load_r,
  input                     ca_store_r,
  input [2:0]               ca_size_r,
  input [1:0]               ca_store_grad,
  input [`npuarc_ADDR_RANGE]       ca_mem_addr_r,
  input [`npuarc_DATA_RANGE]       ca_write_data_lo,

  ////////// Register-file write-backs  //////////////////////////////////////////////
  //

  //====================== Channel 0 ======================================
  //
  input                     wa_rf_wenb0_r,
  input                     wa_rf_wenb0_hi_r,       // 2nd register of pair.
  input [`npuarc_RGF_ADDR_RANGE]   wa_rf_wa0_r,
  input [`npuarc_DATA_RANGE]       wa_rf_wdata0_lo_r,
  input [`npuarc_DATA_RANGE]       wa_rf_wdata0_hi_r,

  //====================== Channel 1 ======================================
  //
  input                     wa_rf_wenb1_r,
  input                     wa_rf_wenb1_hi_r,       // 2nd register of pair.
  input [`npuarc_RGF_ADDR_RANGE]   wa_rf_wa1_r,
  input [`npuarc_DATA_RANGE]       wa_rf_wdata1_lo_r,
  input [`npuarc_DATA_RANGE]       wa_rf_wdata1_hi_r,


  ////////// Call graph ////////////////////////////////////////////////////////
  //
  input                     wa_pass,
  input [`npuarc_BR_TYPE_RANGE]    wa_type,
  input [`PMON_PC_RANGE]    wa_target

);



localparam BITS_IN_SUBSET = 8;
localparam [7:0] BUBBLE= 1;	// 1 can never be a PC.

    wire [31:0] da_0_pc = {u_alb_dec_regs.da_pc_r, 1'b0};
    wire [7:0] da_0_pcb = da_0_valid_r ? da_0_pc[7:0] : BUBBLE;
    always @(da_0_pc) begin
	if (0) $display("da_0_pc is now %08x at %1d",da_0_pc,$time);
	end

////////// Output interface to PIPEMON - INST ////////////////////////////////////

wire [31:0]             pipemon_config /* verilator public_flat */;      // configuration register 

wire [1:0]              num_instrs /* verilator public_flat */; 

reg                instr0_valid /* verilator public_flat */;        // instr is valid. 
reg                instr0_is_16_bit /* verilator public_flat */;    // Instr is 16-bit 
reg [31:0]         instr0_inst /* verilator public_flat */;         // Instruction.  If 16-bit, it's in the upper half. 
reg                instr0_limm_valid /* verilator public_flat */;   // limm valid for this instruction 
reg [31:0]         instr0_limm /* verilator public_flat */;         // limm value 
reg [`PMON_PC_RANGE]         instr0_pc /* verilator public_flat */;           // PC of this instruction, without bottom bit. 
reg                instr0_pipe /* verilator public_flat */;         // Pipe index 0, 1, ... N-1.  Adjust [0:0] when 3 pipes 
reg                instr0_debug /* verilator public_flat */;        // Debug instr 
reg                instr0_uop /* verilator public_flat */;          // UOP instr 

reg [3:0]          zncv /* verilator public_flat */;                // ZNCV flags {Z, N, C, V} 

////////// Output interface to PIPEMON - LD/ST ////////////////////////////////////

wire [1:0]         num_loads /* verilator public_flat */; 

reg                load0_valid /* verilator public_flat */;        // load inst. 
reg [2:0]          load0_size /* verilator public_flat */;         // load size, power of 2. 
reg [`npuarc_ADDR_RANGE]  load0_addr /* verilator public_flat */;         // load addr. 

wire [1:0]         num_stores /* verilator public_flat */;

reg                store0_valid /* verilator public_flat */;        // store inst. 
reg [2:0]          store0_size /* verilator public_flat */;         // store size, power of 2. 
reg [`npuarc_DATA_RANGE]  store0_data_lo /* verilator public_flat */;      // store data. 
reg [`npuarc_DATA_RANGE]  store0_data_hi /* verilator public_flat */;      // store data. 
reg                store0_data_valid /* verilator public_flat */;   // store data valid at time of commit. 
reg [`npuarc_ADDR_RANGE]  store0_addr /* verilator public_flat */;         // store addr. 

////////// Output interface to PIPEMON - Register writebacks ////////////////////////

wire [2:0]         num_writebacks /* verilator public_flat */;       // Total number of write-back ports 
reg                wb0_valid /* verilator public_flat */;           // wb is valid. 
reg [2:0]          wb0_size /* verilator public_flat */;            // power of 2: 2^size = 1/2/4/8/16.  
reg [`npuarc_DATA_RANGE]  wb0_data_lo /* verilator public_flat */; 
reg [`npuarc_DATA_RANGE]  wb0_data_hi /* verilator public_flat */; 
reg [5:0]          wb0_reg /* verilator public_flat */; 
reg                wb1_valid /* verilator public_flat */;           // wb is valid. 
reg [2:0]          wb1_size /* verilator public_flat */;            // power of 2: 2^size = 1/2/4/8/16.  
reg [`npuarc_DATA_RANGE]  wb1_data_lo /* verilator public_flat */; 
reg [`npuarc_DATA_RANGE]  wb1_data_hi /* verilator public_flat */; 
reg [5:0]          wb1_reg /* verilator public_flat */; 


// END OF INTERFACE
/////////////////////////////////////////////////////////////////////////////////////



wire sa_0_kill = u_alb_exec_pipe.sa_kill;
wire x1_0_kill = u_alb_exec_pipe.x1_kill;
wire x2_0_kill = u_alb_exec_pipe.x2_kill;
wire x3_0_kill = u_alb_exec_pipe.x3_kill;
wire ca_0_kill = u_alb_exec_pipe.ca_kill;


////////////////////////// Pipe 0
// pipe 0 SA stage
reg [31:0]    sa_0_inst_r;
reg           sa_0_is_16bit_r;
reg           sa_0_has_limm_r;
reg [31:0]    sa_0_limm_r;
reg [7:0]     sa_0_pcb; // Last byte of the PC.
reg           sa_0_bubble;

// pipe 0 X1 stage
reg [31:0]    x1_0_inst_r;
reg           x1_0_is_16bit_r;
reg           x1_0_has_limm_r;
reg [31:0]    x1_0_limm_r;
reg [7:0]     x1_0_pcb; // Last byte of the PC.
reg           x1_0_bubble;

// pipe 0 X2 stage
reg [31:0]    x2_0_inst_r;
reg           x2_0_is_16bit_r;
reg           x2_0_has_limm_r;
reg [31:0]    x2_0_limm_r;
reg [7:0]     x2_0_pcb; // Last byte of the PC.
reg           x2_0_bubble;

// pipe 0 X3 stage
reg [31:0]    x3_0_inst_r;
reg           x3_0_is_16bit_r;
reg           x3_0_has_limm_r;
reg [31:0]    x3_0_limm_r;
reg [7:0]     x3_0_pcb; // Last byte of the PC.
reg           x3_0_bubble;

// pipe 0 CA stage
reg [31:0]    ca_0_inst_r;
reg           ca_0_is_16bit_r;
reg           ca_0_has_limm_r;
reg [31:0]    ca_0_limm_r;
reg [7:0]     ca_0_pcb; // Last byte of the PC.
reg           ca_0_bubble;

// pipe 0 WA stage
reg [31:0]    wa_0_inst_r;
reg           wa_0_is_16bit_r;
reg           wa_0_has_limm_r;
reg [31:0]    wa_0_limm_r;
reg [7:0]     wa_0_pcb; // Last byte of the PC.
reg           wa_0_bubble;


reg [`PMON_PC_RANGE]        wa_0_pc_r;
reg                         wa_0_uop_r;

reg                         wa_0_valid_r;

localparam                  wa_0_older_r = 1'b1; // A constant in single-core.
localparam                  wa_1_valid_r = 1'b0; // Single-issue core: no 2nd instr.


// LD/ST
//
reg                         wa_load_r;
reg                         wa_store_r;
reg [2:0]                   wa_size_r;
reg [1:0]                   wa_store_grad_r;
reg [`npuarc_ADDR_RANGE]           wa_mem_addr_r;
reg [`npuarc_DATA_RANGE]           wa_write_data_lo_r;

/// Vector unit
localparam has_vec = 0;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Move instructions down the pipe
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk) begin
      sa_0_bubble = 1;
      x1_0_bubble = 1;
      x2_0_bubble = 1;
      x3_0_bubble = 1;
      ca_0_bubble = 1;
      wa_0_bubble = 1;

  if (da_0_pass)        begin // SA pipe 0
    begin
    sa_0_inst_r        <= da_0_inst_r;
    sa_0_is_16bit_r    <= da_0_is_16bit_r;
    sa_0_has_limm_r    <= da_0_has_limm_r;
    sa_0_limm_r        <= da_0_limm_r;
    sa_0_pcb           <= da_0_pcb;
    sa_0_bubble	  = 0;	// Used locally, so not delayed assignment.
    end
    end


   if (sa_0_pass) begin // x1_0 <- sa_0
    begin
    x1_0_inst_r        <= sa_0_inst_r;
    x1_0_is_16bit_r    <= sa_0_is_16bit_r;
    x1_0_has_limm_r    <= sa_0_has_limm_r;
    x1_0_limm_r        <= sa_0_limm_r;
    x1_0_pcb           <= sa_0_pcb;
    x1_0_bubble	  = 0;	// Used locally, so not delayed assignment.
    end
     if (sa_0_bubble) sa_0_pcb <= BUBBLE;
     end
   if (sa_0_kill) sa_0_pcb <= BUBBLE;

   if (x1_0_pass) begin // x2_0 <- x1_0
    begin
    x2_0_inst_r        <= x1_0_inst_r;
    x2_0_is_16bit_r    <= x1_0_is_16bit_r;
    x2_0_has_limm_r    <= x1_0_has_limm_r;
    x2_0_limm_r        <= x1_0_limm_r;
    x2_0_pcb           <= x1_0_pcb;
    x2_0_bubble	  = 0;	// Used locally, so not delayed assignment.
    end
     if (x1_0_bubble) x1_0_pcb <= BUBBLE;
     end
   if (x1_0_kill) x1_0_pcb <= BUBBLE;

   if (x2_0_pass) begin // x3_0 <- x2_0
    begin
    x3_0_inst_r        <= x2_0_inst_r;
    x3_0_is_16bit_r    <= x2_0_is_16bit_r;
    x3_0_has_limm_r    <= x2_0_has_limm_r;
    x3_0_limm_r        <= x2_0_limm_r;
    x3_0_pcb           <= x2_0_pcb;
    x3_0_bubble	  = 0;	// Used locally, so not delayed assignment.
    end
     if (x2_0_bubble) x2_0_pcb <= BUBBLE;
     end
   if (x2_0_kill) x2_0_pcb <= BUBBLE;

   if (x3_0_pass) begin // ca_0 <- x3_0
    begin
    ca_0_inst_r        <= x3_0_inst_r;
    ca_0_is_16bit_r    <= x3_0_is_16bit_r;
    ca_0_has_limm_r    <= x3_0_has_limm_r;
    ca_0_limm_r        <= x3_0_limm_r;
    ca_0_pcb           <= x3_0_pcb;
    ca_0_bubble	  = 0;	// Used locally, so not delayed assignment.
    end
     if (x3_0_bubble) x3_0_pcb <= BUBBLE;
     end
   if (x3_0_kill) x3_0_pcb <= BUBBLE;

   if (ca_0_pass) begin // wa_0 <- ca_0
    begin
    wa_0_inst_r        <= ca_0_inst_r;
    wa_0_is_16bit_r    <= ca_0_is_16bit_r;
    wa_0_has_limm_r    <= ca_0_has_limm_r;
    wa_0_limm_r        <= ca_0_limm_r;
    wa_0_pcb           <= ca_0_pcb;
    wa_0_bubble	  = 0;	// Used locally, so not delayed assignment.
    end
     if (ca_0_bubble) ca_0_pcb <= BUBBLE;
     end
   if (ca_0_kill) ca_0_pcb <= BUBBLE;

  // Do not increment PC for the micro-ops
  if (ca_0_pass) begin
    wa_0_pc_r          <= ca_uop_active_r ? ar_pc : ca_0_pc;
    wa_0_uop_r         <= ca_uop_active_r;
    end
  else
    if (wa_0_bubble) wa_0_pcb <= BUBBLE;

  wa_0_valid_r <= ca_0_pass;

  // LD/ST
  //
  wa_load_r            <= ca_load_r;
  wa_store_r           <= ca_store_r;
  wa_size_r            <= ca_size_r;
  wa_store_grad_r      <= ca_store_grad;
  wa_mem_addr_r        <= ca_mem_addr_r;
  wa_write_data_lo_r    <= ca_write_data_lo;
end

// Pipeline stages.
// DA SA X1 X2 X3 CA

`define CAT {     \
    da_0_pcb, \
    sa_0_pcb, \
    x1_0_pcb, \
    x2_0_pcb, \
    x3_0_pcb, \
    ca_0_pcb, \
    wa_0_pcb }
localparam CATBITS = $bits(`CAT);
localparam STAGES = CATBITS/8;
typedef logic [CATBITS-1:0] Pipeline;
Pipeline instr0_pipeline;
assign instr0_pipeline =  `CAT;
`undef CAT

////////////////////////////////////////////////////////////////////////////////
// Instructions
//
////////////////////////////////////////////////////////////////////////////////
assign pipemon_config = 
      32'd4 	// core version.
    | has_vec 			// vdsp bundle present
    | 0		// FPU register configuration: bits 9 10 11
    | 4096	// uop field in instr interface	bit 12
    | 8192		// Pipeline signals. bit 13
    | 0;

assign num_instrs = 2'd1;

always @*
begin
  // Default

  instr0_valid        = 1'b0;
  instr0_is_16_bit    = wa_0_is_16bit_r;
  instr0_inst         = wa_0_inst_r;
  instr0_limm_valid   = wa_0_has_limm_r;
  instr0_limm         = wa_0_limm_r;
  instr0_pc           = wa_0_pc_r;
  instr0_pipe         = 1'b0;
  instr0_debug        = db_active;
  instr0_uop          = wa_0_uop_r;

  zncv                = ar_zncv;

  // Display instructions in order of execution
  //
  case ({wa_0_valid_r, wa_1_valid_r, wa_0_older_r})
  3'b1_0_1:
  begin
    // WA0 only

    instr0_valid        = 1'b1;
    instr0_is_16_bit    = wa_0_is_16bit_r;
    instr0_inst         = wa_0_inst_r;
    instr0_limm_valid   = wa_0_has_limm_r;
    instr0_limm         = wa_0_limm_r;
    instr0_pc           = wa_0_pc_r;
    instr0_uop          = wa_0_uop_r;
    instr0_pipe         = 1'b0;
  end


  default:
  begin
    instr0_valid        = 1'b0;
  end
  endcase
end

////////////////////////////////////////////////////////////////////////////////
// Load/Store
//
////////////////////////////////////////////////////////////////////////////////

assign num_loads  = 2'd1;
assign num_stores = 2'd1;

always @*
begin

  // LD/ST information
  //
  load0_valid        = wa_load_r & wa_0_valid_r;
  load0_size         = wa_size_r;
  load0_addr         = wa_mem_addr_r;

  store0_valid       = wa_store_r & wa_0_valid_r;
  store0_size        = wa_size_r;
  store0_data_lo     = wa_write_data_lo_r;
  store0_data_hi     = {`npuarc_DATA_SIZE{1'b0}};
  store0_data_valid  = wa_store_grad_r  == 2'b00;
  store0_addr        = wa_mem_addr_r;
end

////////////////////////////////////////////////////////////////////////////////
// Register write-back
//
////////////////////////////////////////////////////////////////////////////////

assign num_writebacks = `npuarc_NUM_WRITEBACKS;

always @*
begin
  // Register write-back
  //

  wb0_valid   = wa_rf_wenb0_r;
  wb0_data_lo = wa_rf_wdata0_lo_r;
  wb0_data_hi = wa_rf_wdata0_hi_r;
  wb0_reg     = wa_rf_wa0_r;
  wb0_size = wa_rf_wenb0_hi_r ? 2+1 : 2;

  wb1_valid   = wa_rf_wenb1_r;
  wb1_data_lo = wa_rf_wdata1_lo_r;
  wb1_data_hi = wa_rf_wdata1_hi_r;
  wb1_reg     = wa_rf_wa1_r;
  wb1_size = wa_rf_wenb1_hi_r ? 2+1 : 2;
end


endmodule

