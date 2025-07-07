// Library ARCv2HS-4.0.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2013 Synopsys, Inc. All rights reserved.
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
// Description:
//
// The JTAG Debug Port is the module that contains all the
// internal JTAG registers and performs the actual communication
// between the ARCv2HS and the host. Refer to the JTAG section in
// the ARC interface manual for an explanation on how to
// communicate with the complete module. In this revision, the
// debug port does not contain the address, data, command, or
// status registers.  These physically reside on the other side
// of a BVCI interface, and are read by the debug port during the
// Capture-DR state and written during the Update-DR state. A
// command is initiated during the Run-Test/Idle state by writing
// a do-command address over the BVCI interface, and the
// registers are reset during the Test-Logic-Reset state by
// writing a reset address.
//
//======================= Inputs to this block =======================--
//
// jtag_trst_n          The internal version of TRST*, conditioned to be
//                      asynchronously applied and synchronously released
//
// jtag_tck             The JTAG clock
//
// jtag_tdi             JTAG Test Data In, input to the data and instruction
//                      shift registers
//
// test_logic_reset     TAP controller state decodes
//                      run_test_idle
//                      capture_ir
//                      shift_ir
//                      update_ir
//                      capture_dr
//                      shift_dr
//
// select_r             Selects instruction or data shift register for TDO
//
// test_logic_reset_nxt TAP controller next state decodes
//                      run_test_idle_nxt
//                      select_dr_scan_nxt
//                      capture_dr_nxt
//                      update_dr_nxt
//
// dbg_rdata            Read data from the BVCI debug port
//
//====================== Output from this block ======================--
//
// bvci_addr_r          Variable part of BVCI address, to be synchronized with
//                      clk_main
//
// bvci_cmd_r           BVCI command, to be synchronized with clk_main
//
// dbg_be               BVCI Byte Enables. All bytes always enabled
//
// dbg_eop              BVCI End Of Packet. Always true; we only do one-word
//                      transfers
//
// dbg_rspack           BVCI Response Acknowledge. Always true.
//
// dbg_wdata            BVCI Write Data. Only changed on entry to Update-DR, do
//                      doesn't need to be synchronized
//
// do_bvci_cycle        Request to perform a transaction on the BVCI debug
//                      interface. Edge-signaling.
//
// jtag_tdo_r           JTAG Test Data Out. Output from shift registers
//
//====================================================================--
//
// leda W389 off
// LMD: Multiple clocks in the module
// LJ:  Two clocks used (jtag_tck and jtag_tck_muxed); using inverted clock for
//      negedge clocking of shift reg/TDO output.
// spyglass disable_block W193
// SMD: empty statements
// SJ:  empty default statements kept and empty statements cause no problems
// spyglass disable_block W391
// SMD: Uses both edges of clock
// SJ:  Two clocks used (jtag_tck and jtag_tck_muxed); using inverted clock for
//      negedge clocking of shift reg/TDO output.

// Configuration-dependent macro definitions
//
`define NPU_JF_RESET_TAP_CT    10'h01
`define NPU_JF_TLR_WRITE_IR    10'h02
`define NPU_JF_TLR_WRITE_DR    10'h04
`define NPU_JF_SDS_WRITE_IR    10'h08
`define NPU_JF_SDS_WRITE_DR    10'h10
`define NPU_JF_END_RUNTESTIDLE 10'h20
`define NPU_JF_END_BYPASS_IDLE 10'h40
`define NPU_JF_STEP_TMS_HIGH   10'h80
`define NPU_JF_STEP_TMS_LOW    10'h100
`define NPU_JF_CAPTURE_TDO     10'h200
`define NPU_JTAG_BSR_REG             4'h0
`define NPU_JTAG_EXTEST_REG          4'h1
`define NPU_JTAG_UNUSED_REG0         4'h2
`define NPU_JTAG_UNUSED_REG1         4'h3
`define NPU_JTAG_UNUSED_REG2         4'h4
`define NPU_JTAG_UNUSED_REG3         4'h5
`define NPU_JTAG_UNUSED_REG4         4'h6
`define NPU_JTAG_UNUSED_REG5         4'h7
`define NPU_JTAG_STATUS_REG          4'h8
`define NPU_JTAG_TRANSACTION_CMD_REG 4'h9
`define NPU_JTAG_ADDRESS_REG         4'hA
`define NPU_JTAG_DATA_REG            4'hB
`define NPU_JTAG_IDCODE_REG          4'hC
`define NPU_JTAG_UNUSED_REG6         4'hD
`define NPU_JTAG_UNUSED_REG7         4'hE
`define NPU_JTAG_BYPASS_REG          4'hF
`define NPU_JTAG_INSTRUCTION_REG_LEN     4
`define NPU_JTAG_BSR_REG_LEN             32
`define NPU_JTAG_STATUS_REG_LEN          7
`define NPU_JTAG_TRANSACTION_CMD_REG_LEN 4
`define NPU_JTAG_ADDRESS_REG_LEN         32
`define NPU_JTAG_DATA_REG_LEN            32
`define NPU_JTAG_IDCODE_REG_LEN          32
`define NPU_JTAG_BYPASS_REG_LEN          1
`define NPU_JTAG_STATUS_STALLED     0
`define NPU_JTAG_STATUS_FAILURE     1
`define NPU_JTAG_STATUS_READY       2
`define NPU_JTAG_STATUS_PC_SEL      3
`define NPU_CMD_WRITE_CORE        4'h1
`define NPU_CMD_READ_CORE         4'h5
`define NPU_CMD_WRITE_AUX         4'h2
`define NPU_CMD_READ_AUX          4'h6
`define NPU_CMD_WRITE_MEM         4'h0
`define NPU_CMD_READ_MEM          4'h4
`define NPU_CMD_WRITE_MADI        4'h7
`define NPU_CMD_READ_MADI         4'h8
`define NPU_CMD_NOP               4'h3
`define NPU_JTAG_STATUS_REG_INIT             4'b1100
`define NPU_JTAG_TRANSACTION_CMD_REG_INIT    3
`define NPU_JTAG_ADDRESS_REG_INIT            32'h00000000
`define NPU_JTAG_DATA_REG_INIT               32'h00000000
`define NPU_JTAG_IDCODE_REG_INIT             32'h00000000
`define NPU_JTAG_VERSION            4'b0001
`define NPU_ARC_TYPE_A4             6'b000000
`define NPU_ARC_TYPE_A5             6'b000001
`define NPU_ARC_TYPE_ARC600         6'b000010
`define NPU_ARC_TYPE_ARC700         6'b000011
`define NPU_ARC_JEDEC_CODE          11'b01001011000
`define NPU_ARC_TYPE                6'd5
`define NPU_TCK_CLOCK_PERIOD     5.000
`define NPU_DELAY_ON_TDO 1.25
`define NPU_TCK_HALF_PERIOD 2.5
`define NPU_TCK_HALF_PERIOD_TDO 1.25
`define NPU_BASE_ADDRESS          32'hffff0000
`define NPU_BASE_ADDR             134215680
`define NPU_STATUS_R_ADDR         3'b000
`define NPU_DO_CMD_ADDR           3'b000
`define NPU_COMMAND_R_ADDR        3'b001
`define NPU_ADDRESS_R_ADDR        3'b010
`define NPU_DATA_R_ADDR           3'b011
`define NPU_RESET_ADDR            3'b100
`define NPU_MEM_OFFSET            32'h00000004
`define NPU_REG_OFFSET            32'h00000001
`define NPU_CMD_MEM               2'b00
`define NPU_CMD_CORE              2'b01
`define NPU_CMD_AUX               2'b10
`define NPU_CMD_READ              2'b01
`define NPU_CMD_WRITE             2'b00
`define NPU_CMD_RD_MEM            4'b0100
`define NPU_CMD_WR_MEM            4'b0000
`define NPU_CMD_RD_AUX            4'b0110
`define NPU_CMD_WR_AUX            4'b0010
`define NPU_CMD_RD_CORE           4'b0101
`define NPU_CMD_WR_CORE           4'b0001
`define NPU_CMD_RD_MADI           4'b1000
`define NPU_CMD_WR_MADI           4'b0111
`define NPU_CMD_RESET_VALUE       4'b0011
`define NPU_HAS_ADDRESS_AUTO_INCREMENT 1'b0
`define NPU_IR_EXTEST            4'b0000
`define NPU_IR_SAMPLE            4'b0001
`define NPU_IR_UNUSED0           4'b0010
`define NPU_IR_UNUSED1           4'b0011
`define NPU_IR_UNUSED2           4'b0100
`define NPU_IR_UNUSED3           4'b0101
`define NPU_IR_UNUSED4           4'b0110
`define NPU_IR_UNUSED5           4'b0111
`define NPU_IR_STATUS            4'b1000
`define NPU_IR_COMMAND           4'b1001
`define NPU_IR_ADDRESS           4'b1010
`define NPU_IR_DATA              4'b1011
`define NPU_IR_IDCODE            4'b1100
`define NPU_IR_UNUSED6           4'b1101
`define NPU_IR_UNUSED7           4'b1110
`define NPU_IR_BYPASS            4'b1111
`define NPU_IR_INIT              4'b0001
`define NPU_SREG_SIZE            32
`define NPU_SREG_MSB             31
`define NPU_JTAG_CMD_SIZE        4
`define NPU_JTAG_CMD_MSB         3
`define NPU_JTAG_STATUS_SIZE     7
`define NPU_JTAG_STATUS_MSB      6
`define NPU_BVCI_CMD_WDTH        2
`define NPU_BVCI_CMD_WDTH_MSB    1
`define NPU_BVCI_CMD_RNGE        1:0
`define NPU_BVCI_CMD_NOOP        2'b00
`define NPU_BVCI_CMD_RD          2'b01
`define NPU_BVCI_CMD_WR          2'b10
`define NPU_BVCI_CMD_LOCKRD      2'b11


module npu_debug_port(
  input    [7:0]              arcnum,
// leda NTL_STR61 off
// LMD: Do not use clk/enable signals as data inputs
// LJ:  Locally inverted/muxed clock used for negedge FFs and test mode
  input                       jtag_tck,
  input                       jtag_tck_muxed,
// leda NTL_STR61 on
  input                       jtag_trst_n,
  input                       jtag_tdi,
  output reg                  jtag_tdo_r,

  input        [31:0]         dbg_rdata,  // Read data

  input                       test_logic_reset,
  input                       run_test_idle,
  input                       shift_ir,
  input                       update_dr,
  input                       update_ir,
  input                       shift_dr,
  input                       capture_dr,
  input                       capture_ir,

  input                       select_r,

  input                       test_logic_reset_nxt,
  input                       run_test_idle_nxt,
  input                       select_dr_scan_nxt,
  input                       capture_dr_nxt,
  input                       shft2exit1_dr_nxt,
  input                       update_dr_nxt,

  output                      do_bvci_cycle,

  output reg   [4:2]          bvci_addr_r,    // Longword address, variable part
  output reg   [1:0]          bvci_cmd_r,     // Command
  output       [31:0]         dbg_wdata       // Write data
);

//  Signal used to communicate with the BVCI cycle initiator.
reg             i_do_bvci_cycle_r;

//  The following signals are generated from D-type-flops with enables
//  and are used to hold the data register contents. The registers are
//  commonly referred to as shadow latches (IEEE Std 1149.1).
reg     [31:0]  shift_register_r;       // the shift reg (used by DRs)
reg     [3:0]   ir_latch_r;     // the instruction register
reg     [3:0]   ir_sreg_r;      // shift register for IR
reg             bypass_reg_r;   // bypass reg, a one bit reg

//  The following signals are used to connect to the TDO output. The TDO
//  output can be connected to two source outputs, the data registers or
//  the instruction register.
wire            tdo_src_dr;     // DRs muxed to TDO
wire            tdo_src_ir;     // IR muxed to TDO

//  The concurrent statement below is used to select the appropriate data
//  register output for the TDO signal. The signal inputs to this mux are
//  taken from the LSB of the shift register. Only one of LSB bits is
//  selected to the tdo_src_dr output dependent upon the value contained
//  in the instruction latch. The selected signal is then pass on into
//  the final mux, which determines what goes onto the TDO output pin.
//  As per the JTAG spec, all unused instructions select the bypass
//  register.
assign tdo_src_dr = ((ir_latch_r == `NPU_IR_STATUS) || (ir_latch_r == `NPU_IR_COMMAND) ||
                     (ir_latch_r == `NPU_IR_ADDRESS)|| (ir_latch_r == `NPU_IR_DATA) ||
                     (ir_latch_r == `NPU_IR_IDCODE)) ?
                      shift_register_r[0] :
                      bypass_reg_r;        // Covers ir_latch_r == `IR_BYPASS
                                           // and all other cases

//  the LSB of the instruction register is always selected for this source.
assign tdo_src_ir = ir_sreg_r[0];

//  The process statement below selects between the data or instruction
//  register to the main TDO output. The selection is made according to
//  the select_r signal that comes from the TAP controller. It indicates
//  what type of register is being accessed (if any). HIGH = instruction
//  register access, LOW = data register access. The TDO output always
//  changes on the falling edge of TCK.
//
// leda S_2C_R off
// LMD: Use rising edge flipflop
// LJ:  Using locally inverted clock (jtag_trst_n) for negedge except test mode
// leda B_1205 off
// LMD: The clock signal is not coming directly from a port of the current unit
// LJ:  Using locally inverted clock (jtag_trst_n) for negedge except test mode
// spyglass disable_block Reset_sync01 Reset_check07 Clock_check04
// SMD: Asynchronous reset signal that is not deasserted synchronously
// SJ:  jtag_trst_n must be synchronously deasserted
// SMD: Potential race between flop and it's clk
// SJ:  jtag_trst_n must be synchronously deasserted
// SMD: Recommended positive edge of clock not used
// SJ:  Using negedge of clock as required by IEEE spec
//
always @(posedge jtag_tck_muxed or negedge jtag_trst_n)
begin : tdo_output_PROC
  if (jtag_trst_n == 1'b0)
    jtag_tdo_r <= 1'b0;

  else 
    if (test_logic_reset == 1'b1)
      jtag_tdo_r <= 1'b0;

    else if ((shift_dr == 1'b1) | (shift_ir == 1'b1))
      begin
        if (select_r == 1'b0)
          jtag_tdo_r <= tdo_src_dr;
        else
          jtag_tdo_r <= tdo_src_ir;
      end
end
//
// leda S_2C_R on
// leda B_1205 on
// spyglass enable_block Reset_sync01 Reset_check07 Clock_check04

//  The shift Data Register Cell
//
//  The shift data register is used to load and unload data from the
//  selected data register and serially shift data in from TDI and out
//  through TDO. Data is loaded into the shift cell when the capture_dr
//  state is entered and the instruction register contains a valid
//  instruction code.
//
// leda NTL_CLK05 off
// LMD: All asynchronous inputs to a clock system must be clocked twice.
// LJ:  dbg_rdata from bvci read port async but stable at sample

// leda B_1205 off
// LMD: The clock signal is not coming directly from a port of the current unit
// LJ:  Using locally inverted clock (jtag_trst_n) for posedge except test mode
// spyglass disable_block Clock_sync01 Clock_sync09 Ac_unsync02 Ac_conv04 Clock_check10 Ar_resetcross01
// SMD: unsynchronized clock domain crossings
// SJ:  CDC accross pseudo-bvci interface handled by protocol/clk ratio
// spyglass disable_block Ac_glitch03 Ac_glitch02
// SMD: crossing from source, may be subject to glitches 
// SJ:  crossings from clk to jtag_tck is acceptable as jtag_tck is slow compared to clk 
// spyglass disable_block Ac_glitch04
// SMD: Reconvergence without enable condition 
// SJ:  Reconvergence between jtag_tck_muxed and jtag_tck is acceptable as they are in phase.
//      They are also inverted when test_mode=0 but logic was designed based on this 
//
always @(posedge jtag_tck or negedge jtag_trst_n)
begin : dr_shift_reg_cell_PROC
  if (jtag_trst_n == 1'b0)
    shift_register_r <= { `NPU_SREG_SIZE { 1'b0 }};

  else 
    if (test_logic_reset == 1'b1)
      shift_register_r <= { `NPU_SREG_SIZE { 1'b0 }};

    else if (shift_dr == 1'b1)
      case (ir_latch_r)

        //  Command is 4 bits
        `NPU_IR_COMMAND :
        begin //  shift register one by one
            shift_register_r[0] <= shift_register_r[1];
            shift_register_r[1] <= shift_register_r[2];
            shift_register_r[2] <= shift_register_r[3];
          shift_register_r[`NPU_JTAG_CMD_MSB] <= jtag_tdi; // latch new data
        end

        // Status is 6 bits
        `NPU_IR_STATUS :
        begin //  shift register one by one
            shift_register_r[0] <= shift_register_r[1];
            shift_register_r[1] <= shift_register_r[2];
            shift_register_r[2] <= shift_register_r[3];
            shift_register_r[3] <= shift_register_r[4];
            shift_register_r[4] <= shift_register_r[5];
            shift_register_r[5] <= shift_register_r[6];
          shift_register_r[`NPU_JTAG_STATUS_MSB] <= jtag_tdi; // latch new data
        end

        default : //  All others are 32 bits
        begin //  shift register one by one
            shift_register_r[0] <= shift_register_r[1];
            shift_register_r[1] <= shift_register_r[2];
            shift_register_r[2] <= shift_register_r[3];
            shift_register_r[3] <= shift_register_r[4];
            shift_register_r[4] <= shift_register_r[5];
            shift_register_r[5] <= shift_register_r[6];
            shift_register_r[6] <= shift_register_r[7];
            shift_register_r[7] <= shift_register_r[8];
            shift_register_r[8] <= shift_register_r[9];
            shift_register_r[9] <= shift_register_r[10];
            shift_register_r[10] <= shift_register_r[11];
            shift_register_r[11] <= shift_register_r[12];
            shift_register_r[12] <= shift_register_r[13];
            shift_register_r[13] <= shift_register_r[14];
            shift_register_r[14] <= shift_register_r[15];
            shift_register_r[15] <= shift_register_r[16];
            shift_register_r[16] <= shift_register_r[17];
            shift_register_r[17] <= shift_register_r[18];
            shift_register_r[18] <= shift_register_r[19];
            shift_register_r[19] <= shift_register_r[20];
            shift_register_r[20] <= shift_register_r[21];
            shift_register_r[21] <= shift_register_r[22];
            shift_register_r[22] <= shift_register_r[23];
            shift_register_r[23] <= shift_register_r[24];
            shift_register_r[24] <= shift_register_r[25];
            shift_register_r[25] <= shift_register_r[26];
            shift_register_r[26] <= shift_register_r[27];
            shift_register_r[27] <= shift_register_r[28];
            shift_register_r[28] <= shift_register_r[29];
            shift_register_r[29] <= shift_register_r[30];
            shift_register_r[30] <= shift_register_r[31];
          shift_register_r[`NPU_SREG_MSB] <= jtag_tdi; // latch new data
        end
    
      endcase

    else if (capture_dr == 1'b1)
      case (ir_latch_r)
        `NPU_IR_ADDRESS, `NPU_IR_DATA :
          shift_register_r <= dbg_rdata;
    
        `NPU_IR_COMMAND :
        begin
          shift_register_r[`NPU_JTAG_CMD_MSB : 0] <=
            dbg_rdata[`NPU_JTAG_CMD_MSB : 0];
          shift_register_r[`NPU_SREG_MSB : `NPU_JTAG_CMD_SIZE] <=
            { `NPU_SREG_SIZE - `NPU_JTAG_CMD_SIZE { 1'b0 }}; // Zero upper bits
        end
    
        `NPU_IR_STATUS :
        begin
          shift_register_r[`NPU_JTAG_STATUS_MSB : 0] <=
            dbg_rdata[`NPU_JTAG_STATUS_MSB : 0];
          shift_register_r[`NPU_SREG_MSB : `NPU_JTAG_STATUS_SIZE] <=
            { `NPU_SREG_SIZE - `NPU_JTAG_STATUS_SIZE { 1'b0 }}; // Zero upper bits
        end
    
        `NPU_IR_IDCODE :
          shift_register_r <= {`NPU_JTAG_VERSION, 2'b00, arcnum, `NPU_ARC_TYPE,
                             `NPU_ARC_JEDEC_CODE, 1'b1}; //  load id register

        default :
          shift_register_r <= { `NPU_SREG_SIZE { 1'b0 }};

      endcase
end
//
// leda NTL_CLK05 on
// leda B_1205    on
// spyglass enable_block Clock_sync01 Clock_sync09 Ac_unsync02 Ac_conv04 Clock_check10 Ar_resetcross01
// spyglass enable_block Ac_glitch03 Ac_glitch02
// spyglass enable_block Ac_glitch04

//  The Shift Instruction Register Cell
//
//  The shift instruction register cell is used to shift the elements of the
//  instruction register.  The capture circuitry loads a 0001 pattern into the
//  instruction register every time the Capture-IR state is entered. This
//  allow the communicating device to detect faults along a 1149.1 bus.
always @(posedge jtag_tck or negedge jtag_trst_n)
begin : IR_SHIFT_REG_CELL_PROC
  if (jtag_trst_n == 1'b0)
    ir_sreg_r <= 4'b0000;

  else
    if (capture_ir == 1'b1)
      ir_sreg_r <= `NPU_IR_INIT; //  whenever we capture IR we must load a 01 into
                             //  the two LSBs. This aids in diagnosing
                             //  faults along the IEEE 1149.1-1990 bus

  else if (shift_ir == 1'b1)
  begin
    ir_sreg_r[3] <= jtag_tdi;       // latch new data in on TDI
    ir_sreg_r[2] <= ir_sreg_r[3];   // shift register on by one
    ir_sreg_r[1] <= ir_sreg_r[2];
    ir_sreg_r[0] <= ir_sreg_r[1];
  end
end

//  The following processes are used to load shifted data into instruction or
//  a selected data register. A D type flip flop with an enable is inferred
//  for all registers. The enable is asserted active on all data registers
//  only when the update_dr state is entered and the instruction latch
//  contains the selected data register code. The instruction register is
//  updated only when the update-ir state is entered. Note all registers are
//  updated on the falling edge of the TCK clock when in the update-ir/dr
//  state, except for the address, command, and data registers, which are
//  updated via a write over the BVCI interface.
always @(posedge jtag_tck or negedge jtag_trst_n)
begin : BVCI_PROC
  if (jtag_trst_n == 1'b0)
  begin
    bvci_cmd_r  <= `NPU_BVCI_CMD_NOOP;
    bvci_addr_r <= `NPU_RESET_ADDR;
  end

  else //  Generate the BVCI address and command
    if (update_dr_nxt == 1'b1)
    begin
      bvci_cmd_r <= `NPU_BVCI_CMD_WR;
      case (ir_latch_r)
        `NPU_IR_ADDRESS :
          bvci_addr_r <= `NPU_ADDRESS_R_ADDR;
        `NPU_IR_DATA :
          bvci_addr_r <= `NPU_DATA_R_ADDR;
        `NPU_IR_COMMAND :
          bvci_addr_r <= `NPU_COMMAND_R_ADDR;
        default :
          bvci_addr_r <= `NPU_RESET_ADDR;
      endcase
    end

    // The address must be presented for two clocks to allow the
    // returned read data to be synchronized before use, as it's
    // generated on the system clock.
    else if ((capture_dr_nxt == 1'b1) || (select_dr_scan_nxt == 1'b1))
    begin
      bvci_cmd_r <= `NPU_BVCI_CMD_RD;
      case (ir_latch_r)
        `NPU_IR_ADDRESS :
          bvci_addr_r <= `NPU_ADDRESS_R_ADDR;
        `NPU_IR_DATA :
          bvci_addr_r <= `NPU_DATA_R_ADDR;
        `NPU_IR_COMMAND :
          bvci_addr_r <= `NPU_COMMAND_R_ADDR;
        `NPU_IR_STATUS :
          bvci_addr_r <= `NPU_STATUS_R_ADDR;
        default :
          bvci_addr_r <= `NPU_RESET_ADDR;
      endcase
    end
  
    else if (run_test_idle_nxt == 1'b1)
    begin
      bvci_cmd_r  <= `NPU_BVCI_CMD_WR;
      bvci_addr_r <= `NPU_DO_CMD_ADDR;
    end
  
    else if (test_logic_reset_nxt == 1'b1)
    begin
      bvci_cmd_r  <= `NPU_BVCI_CMD_WR;
      bvci_addr_r <= `NPU_RESET_ADDR;
    end
  
    else
    begin
      bvci_cmd_r  <= `NPU_BVCI_CMD_NOOP;
      bvci_addr_r <= `NPU_RESET_ADDR;
    end
end

assign dbg_wdata = {32{ ~test_logic_reset}} & shift_register_r;
//assign dbg_wdata = shift_register_r;


//  This process manages the do_bvci_cycle flop, which is toggled to
//  request a BVCI cycle. This edge-signaling, rather than level-
//  signaling, is done so that we can request BVCI cycles on consecutive
//  JTAG clocks.
always @(posedge jtag_tck or negedge jtag_trst_n)
begin : DO_BVCI_CMD_PROC
  if (jtag_trst_n == 1'b0)
    i_do_bvci_cycle_r <= 1'b0;

  else
    if (update_dr_nxt == 1'b1) // write addr, data or cmd
      case (ir_latch_r)
        `NPU_IR_ADDRESS, `NPU_IR_DATA, `NPU_IR_COMMAND :
          i_do_bvci_cycle_r <= ~ i_do_bvci_cycle_r;
        default :
          ;
      endcase

    else if (select_dr_scan_nxt == 1'b1) // We do the read speculatively
      case (ir_latch_r)
        `NPU_IR_ADDRESS, `NPU_IR_DATA, `NPU_IR_COMMAND, `NPU_IR_STATUS :
          i_do_bvci_cycle_r <= ~ i_do_bvci_cycle_r;
        default :
          ;
      endcase

    else if ((run_test_idle_nxt == 1'b1) && (run_test_idle == 1'b0))
      case (ir_latch_r)
        `NPU_IR_BYPASS, `NPU_IR_EXTEST, `NPU_IR_SAMPLE, `NPU_IR_UNUSED0, `NPU_IR_UNUSED1,
        `NPU_IR_UNUSED2, `NPU_IR_UNUSED3, `NPU_IR_UNUSED4, `NPU_IR_UNUSED5, `NPU_IR_UNUSED6,
        `NPU_IR_UNUSED7, `NPU_IR_IDCODE :
          ;
        default :
          i_do_bvci_cycle_r <= ~ i_do_bvci_cycle_r;
      endcase

    else if (test_logic_reset_nxt == 1'b1)
      i_do_bvci_cycle_r <= ~ i_do_bvci_cycle_r;
end

assign do_bvci_cycle = i_do_bvci_cycle_r; //  Drive the output

//  Note that the instruction register, as required by the JTAG spec, updates
//  on the falling edge of JTAG clock.
//
// leda S_2C_R off
// LMD: Use rising edge flipflop
// LJ:  Using negedge of clock as required by IEEE spec
//
// spyglass disable_block Clock_check04
// SMD: Recommended positive edge of clock not used
// SJ:  Using negedge of clock as required by IEEE spec
always @(posedge jtag_tck_muxed or negedge jtag_trst_n)
begin : THE_INSTRUCTION_REG_PROC
  if (jtag_trst_n == 1'b0)
    ir_latch_r <= `NPU_IR_IDCODE;

  else
    if (test_logic_reset == 1'b1)
      ir_latch_r <= `NPU_IR_IDCODE;

    else if (update_ir == 1'b1)
      ir_latch_r <= ir_sreg_r; //  update the instruction reg
end
//
// leda S_2C_R on
// spyglass enable_block Clock_check04

//  The following process defines the BYPASS register. The Bypass mode is set
//  when all ones have been written into instruction register or when the JTAG
//  port has be reset. The bypass register is set to zero on during
//  Capture-DR, and to TDI during Shift-DR, and is held in all other states,
//  as per the JTAG spec.
always @(posedge jtag_tck or negedge jtag_trst_n)
begin : BYPASS_BIT_PROC
  if (jtag_trst_n == 1'b0)
    bypass_reg_r <= 1'b0;

  else
    if (capture_dr == 1'b1)
      bypass_reg_r <= 1'b0;

    else if (shift_dr == 1'b1)
      bypass_reg_r <= jtag_tdi;
end


// leda W389 on
// spyglass enable_block W193
// spyglass enable_block W391

endmodule // module npu_debug_port

`undef NPU_JF_RESET_TAP_CT
`undef NPU_JF_TLR_WRITE_IR
`undef NPU_JF_TLR_WRITE_DR
`undef NPU_JF_SDS_WRITE_IR
`undef NPU_JF_SDS_WRITE_DR
`undef NPU_JF_END_RUNTESTIDLE
`undef NPU_JF_END_BYPASS_IDLE
`undef NPU_JF_STEP_TMS_HIGH
`undef NPU_JF_STEP_TMS_LOW
`undef NPU_JF_CAPTURE_TDO
`undef NPU_JTAG_BSR_REG
`undef NPU_JTAG_EXTEST_REG
`undef NPU_JTAG_UNUSED_REG0
`undef NPU_JTAG_UNUSED_REG1
`undef NPU_JTAG_UNUSED_REG2
`undef NPU_JTAG_UNUSED_REG3
`undef NPU_JTAG_UNUSED_REG4
`undef NPU_JTAG_UNUSED_REG5
`undef NPU_JTAG_STATUS_REG
`undef NPU_JTAG_TRANSACTION_CMD_REG
`undef NPU_JTAG_ADDRESS_REG
`undef NPU_JTAG_DATA_REG
`undef NPU_JTAG_IDCODE_REG
`undef NPU_JTAG_UNUSED_REG6
`undef NPU_JTAG_UNUSED_REG7
`undef NPU_JTAG_BYPASS_REG
`undef NPU_JTAG_INSTRUCTION_REG_LEN
`undef NPU_JTAG_BSR_REG_LEN
`undef NPU_JTAG_STATUS_REG_LEN
`undef NPU_JTAG_TRANSACTION_CMD_REG_LEN
`undef NPU_JTAG_ADDRESS_REG_LEN
`undef NPU_JTAG_DATA_REG_LEN
`undef NPU_JTAG_IDCODE_REG_LEN
`undef NPU_JTAG_BYPASS_REG_LEN
`undef NPU_JTAG_STATUS_STALLED
`undef NPU_JTAG_STATUS_FAILURE
`undef NPU_JTAG_STATUS_READY
`undef NPU_JTAG_STATUS_PC_SEL
`undef NPU_CMD_WRITE_CORE
`undef NPU_CMD_READ_CORE
`undef NPU_CMD_WRITE_AUX
`undef NPU_CMD_READ_AUX
`undef NPU_CMD_WRITE_MEM
`undef NPU_CMD_READ_MEM
`undef NPU_CMD_WRITE_MADI
`undef NPU_CMD_READ_MADI
`undef NPU_CMD_NOP
`undef NPU_JTAG_STATUS_REG_INIT
`undef NPU_JTAG_TRANSACTION_CMD_REG_INIT
`undef NPU_JTAG_ADDRESS_REG_INIT
`undef NPU_JTAG_DATA_REG_INIT
`undef NPU_JTAG_IDCODE_REG_INIT
`undef NPU_JTAG_VERSION
`undef NPU_ARC_TYPE_A4
`undef NPU_ARC_TYPE_A5
`undef NPU_ARC_TYPE_ARC600
`undef NPU_ARC_TYPE_ARC700
`undef NPU_ARC_JEDEC_CODE
`undef NPU_ARC_TYPE
`undef NPU_TCK_CLOCK_PERIOD
`undef NPU_DELAY_ON_TDO
`undef NPU_TCK_HALF_PERIOD
`undef NPU_TCK_HALF_PERIOD_TDO
`undef NPU_BASE_ADDRESS
`undef NPU_BASE_ADDR
`undef NPU_STATUS_R_ADDR
`undef NPU_DO_CMD_ADDR
`undef NPU_COMMAND_R_ADDR
`undef NPU_ADDRESS_R_ADDR
`undef NPU_DATA_R_ADDR
`undef NPU_RESET_ADDR
`undef NPU_MEM_OFFSET
`undef NPU_REG_OFFSET
`undef NPU_CMD_MEM
`undef NPU_CMD_CORE
`undef NPU_CMD_AUX
`undef NPU_CMD_READ
`undef NPU_CMD_WRITE
`undef NPU_CMD_RD_MEM
`undef NPU_CMD_WR_MEM
`undef NPU_CMD_RD_AUX
`undef NPU_CMD_WR_AUX
`undef NPU_CMD_RD_CORE
`undef NPU_CMD_WR_CORE
`undef NPU_CMD_RD_MADI
`undef NPU_CMD_WR_MADI
`undef NPU_CMD_RESET_VALUE
`undef NPU_HAS_ADDRESS_AUTO_INCREMENT
`undef NPU_IR_EXTEST
`undef NPU_IR_SAMPLE
`undef NPU_IR_UNUSED0
`undef NPU_IR_UNUSED1
`undef NPU_IR_UNUSED2
`undef NPU_IR_UNUSED3
`undef NPU_IR_UNUSED4
`undef NPU_IR_UNUSED5
`undef NPU_IR_STATUS
`undef NPU_IR_COMMAND
`undef NPU_IR_ADDRESS
`undef NPU_IR_DATA
`undef NPU_IR_IDCODE
`undef NPU_IR_UNUSED6
`undef NPU_IR_UNUSED7
`undef NPU_IR_BYPASS
`undef NPU_IR_INIT
`undef NPU_SREG_SIZE
`undef NPU_SREG_MSB
`undef NPU_JTAG_CMD_SIZE
`undef NPU_JTAG_CMD_MSB
`undef NPU_JTAG_STATUS_SIZE
`undef NPU_JTAG_STATUS_MSB
`undef NPU_BVCI_CMD_WDTH
`undef NPU_BVCI_CMD_WDTH_MSB
`undef NPU_BVCI_CMD_RNGE
`undef NPU_BVCI_CMD_NOOP
`undef NPU_BVCI_CMD_RD
`undef NPU_BVCI_CMD_WR
`undef NPU_BVCI_CMD_LOCKRD
