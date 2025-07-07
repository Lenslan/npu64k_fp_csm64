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
// File defining macros for a parameterizable ARCSYNC interface
// Parameters to control the instantiation

//
//  ARCSYNC to NAME interface
//
`define ARCSYNCCOREIF(NAME) \
output logic  [7:0]              NAME``_arcnum,               // Specifies the processor ID \
// Boot                                                       // Check the value is defined from bit0 or bit12 \
output logic[31:12]              NAME``_intvbase,             // Reset value for core interrupt vector table base address \
// Halt \
output logic                     NAME``_halt_req,             // processor asynchronous halt request \
input  logic                     NAME``_halt_ack_a,           // processor halt request acknowledge \
// Run \
output logic                     NAME``_run_req,              // processor asynchronous run request \
input  logic                     NAME``_run_ack_a,            // processor run request acknowledge \
// Status \
input  logic                     NAME``_sys_sleep,            // If true then processor is sleeping \
input  logic   [2:0]             NAME``_sys_sleep_mode,       // Indicated sleep mode of processor \
input  logic                     NAME``_sys_halt,             // If true then processor is halted \
input  logic                     NAME``_sys_tf_halt,          // If true then processor is halted due to triple fault exception \
input  logic   [1:0]             NAME``_pmode,                // current power mode state for processor \
// Reset \
output logic                     NAME``_rst_req,              // processor asynchronous reset request. \
input  logic                     NAME``_rst_ack_a,            // processor reset request acknowledge. \
input  logic                     NAME``_wdt_reset,            // Watchdog timer reset \
// IRQ and Event \
output logic                     NAME``_irq,                  // 4 asynchronous interrupt outputs per VDSP core \
output logic   [1:0]             NAME``_event                 // An asynchronous event output per VDSP core \

`define ARCSYNCCOREINT(NAME) \
logic  [7:0]              NAME``_arcnum;               // Specifies the processor ID \
// Boot                                                // Check the value is defined from bit0 or bit12 \
logic  [31:12]            NAME``_intvbase;             // Reset value for core interrupt vector table base address \
// Halt \
logic                     NAME``_halt_req;             // processor asynchronous halt request \
logic                     NAME``_halt_ack_a;           // processor halt request acknowledge \
// Run \
logic                     NAME``_run_req;              // processor asynchronous run request \
logic                     NAME``_run_ack_a;            // processor run request acknowledge \
// Status \
logic                     NAME``_sys_sleep;            // If true then processor is sleeping \
logic   [2:0]             NAME``_sys_sleep_mode;       // Indicated sleep mode of processor \
logic                     NAME``_sys_halt;             // If true then processor is halted \
logic                     NAME``_sys_tf_halt;          // If true then processor is halted due to triple fault exception \
logic   [1:0]             NAME``_pmode;                // current power mode state for processor \
// Reset \
logic                     NAME``_rst_req;              // processor asynchronous reset request. \
logic                     NAME``_rst_ack_a;            // processor reset request acknowledge. \
logic                     NAME``_wdt_reset;            // Watchdog timer reset \
// IRQ and Event \
logic                     NAME``_irq;                  // 4 asynchronous interrupt outputs per VDSP core \
logic   [1:0]             NAME``_event;                // An asynchronous event output per VDSP core
