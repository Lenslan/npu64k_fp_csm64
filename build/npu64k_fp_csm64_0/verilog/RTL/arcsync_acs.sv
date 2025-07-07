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

`include "arcsync_defines.v"
module arcsync_acs
#(
  parameter ADDR_WIDTH      = 32,
  parameter DATA_WIDTH      = 32,
  parameter logic [31:0] CORE_NUM   = 32'd1,
  parameter logic        CORE_CLK_ENA_RST = 1,
  localparam             CORE_NUM_S = signed'(CORE_NUM) // NOTE: signed version for genvar type checking
)
(
  input     logic     [CORE_NUM-1:0]       arcsync_core_exist,                 
  input     logic     [CORE_NUM-1:0]       arcsync_core_wr_enable,
  input     logic                          mmio_sel,   // select target register group, valid at the cycle when *en is high
  input     logic     [ADDR_WIDTH-1:0]     mmio_addr,  // register address, valid at the cycle when *en is high
  input     logic                          mmio_wen,   // write enable for register
  input     logic                          mmio_ren,   // read enable for register
  output    logic     [DATA_WIDTH-1:0]     mmio_rdata, // read data, valid at the cycle when ren is high
  input     logic     [DATA_WIDTH-1:0]     mmio_wdata, // write data, valid at the cycle when wen is high
  output    logic     [1:0]                mmio_resp,  // {err, ack} the response is received at the cycle when *en is high
  // Core Type
  input     logic     [CORE_NUM-1:0]       core_arcsync_arc64,             // ARC32 if '0'. ARC64 if '1'. 
  // Boot                                                              // [REVISIT] need to support ARC64 with its interface 
  output    logic     [CORE_NUM-1:0][63:0] arcsync_core_intvbase,          // Reset value for core interrupt vector table base address
  // Halt
  output    logic     [CORE_NUM-1:0]       arcsync_core_halt_req,          // processor asynchronous halt request
  input     logic     [CORE_NUM-1:0]       core_arcsync_halt_ack,          // processor halt request acknowledge
  // Run
  output    logic     [CORE_NUM-1:0]       arcsync_core_run_req,           // processor asynchronous run request
  input     logic     [CORE_NUM-1:0]       core_arcsync_run_ack,           // processor run request acknowledge
  // Status
  input     logic     [CORE_NUM-1:0]       core_arcsync_sys_sleep,         // If true then processor is sleeping
  input     logic     [CORE_NUM-1:0][2:0]  core_arcsync_sys_sleep_mode,    // Indicated sleep mode of processor
  input     logic     [CORE_NUM-1:0]       core_arcsync_sys_halt,          // If true then processor is halted
  input     logic     [CORE_NUM-1:0]       core_arcsync_sys_tf_halt,       // If true then processor is halted due to triple fault exception
  // Reset
  output    logic     [CORE_NUM-1:0]       arcsync_core_rst_req,           // core asynchronous run request.
  // Clk_en
  output    logic     [CORE_NUM-1:0]       arcsync_core_clk_en,            // core clk_en
  // PMode   
  input     logic     [CORE_NUM-1:0][2:0]  core_arcsync_pmode,             // Power Mode Current State
  // Clock, reset and configuration
  input     logic             rst_a,                                    // Asynchronous reset, active high
  input     logic             clk                                       // Clock
);

//-------------------------------------------------------------------------------------------------------
// MMIO Registers
//-------------------------------------------------------------------------------------------------------
// Core control and status
//-------------------------------------------------------------------------------------------------------
localparam logic [31:0]  ADDR_CORE_RUN            = `ADDR_CORE_RUN        ; 
localparam logic [31:0]  ADDR_CORE_HALT           = `ADDR_CORE_HALT       ; 
localparam logic [31:0]  ADDR_CORE_BOOT_IVB_LO    = `ADDR_CORE_BOOT_IVB_LO; 
localparam logic [31:0]  ADDR_CORE_BOOT_IVB_HI    = `ADDR_CORE_BOOT_IVB_HI; 
localparam logic [31:0]  ADDR_CORE_STATUS         = `ADDR_CORE_STATUS     ; 
localparam logic [31:0]  ADDR_CORE_RESET          = `ADDR_CORE_RESET      ; 
localparam logic [31:0]  ADDR_CORE_CLK_EN         = `ADDR_CORE_CLK_EN     ;
logic [CORE_NUM-1:0][31:0] CORE_RUN;           // Put the core in running mode  0x1000  0x1000 + 4N -4  For each core_id
logic [CORE_NUM-1:0][31:0] CORE_HALT;          // Put the core in halted mode 0x1000 +  4N  0x1000 + 8N -4
logic [CORE_NUM-1:0][31:0] CORE_BOOT_IVB_LO;   // Set the boot address (interrupt vector base) lower 32bits 0x1000 +  8N  0x1000 + 12N -4
logic [CORE_NUM-1:0][31:0] CORE_BOOT_IVB_HI;   // Set the boot address (interrupt vector base) upper 8bits (when MMU and PAE is used) 0x1000 +  12N 0x1000 + 16N -4
logic [CORE_NUM-1:0][31:0] CORE_STATUS;        // Read status of the core 0x1000 +  16N 0x1000 + 20N -4
logic [CORE_NUM-1:0][31:0] CORE_RESET;         // Soft reset the core 0x1000 +  20N 0x1000 + 24N -4
logic [CORE_NUM-1:0][31:0] CORE_CLK_EN;        // Core clock enable 0x1000 +  24N 0x1000 + 28N -4
logic                      valid_req;
logic [CORE_NUM-1:0]       core_reg_en;          
logic [CORE_NUM-1:0][0:0]  core_run_nxt;          
logic [CORE_NUM-1:0][0:0]  core_halt_nxt;         
logic [CORE_NUM-1:0][31:0] core_boot_ivb_lo_nxt;  
logic [CORE_NUM-1:0][20:0] core_boot_ivb_hi_nxt;  
logic [CORE_NUM-1:0][0:0]  core_reset_nxt;         
logic [CORE_NUM-1:0][0:0]  core_run_req_nxt;          
logic [CORE_NUM-1:0][0:0]  core_halt_req_nxt;         
logic [CORE_NUM-1:0][0:0]  core_reset_req_nxt;         
logic [CORE_NUM-1:0][0:0]  core_clk_en_nxt;
logic [CORE_NUM-1:0][0:0]  core_run_r;          
logic [CORE_NUM-1:0][0:0]  core_halt_r;         
logic [CORE_NUM-1:0][31:0] core_boot_ivb_lo_r;  
logic [CORE_NUM-1:0][20:0] core_boot_ivb_hi_r;  
logic [CORE_NUM-1:0][0:0]  core_clk_en_r;
logic [CORE_NUM-1:0][0:0]  core_run_req_r;          
logic [CORE_NUM-1:0][0:0]  core_halt_req_r;         
logic [CORE_NUM-1:0][0:0]  core_reset_req_r;         

logic [CORE_NUM-1:0] core_arcsync_halt_ack_r;
logic [CORE_NUM-1:0] core_arcsync_run_ack_r;
logic [CORE_NUM-1:0] core_arcsync_halt_acked;
logic [CORE_NUM-1:0] core_arcsync_run_acked;

logic [CORE_NUM-1:0] core_run_wen;
logic [CORE_NUM-1:0] core_halt_wen;
logic [CORE_NUM-1:0] core_run_wen_valid_req;
logic [CORE_NUM-1:0] core_halt_wen_valid_req;
logic [CORE_NUM-1:0] core_boot_ivb_lo_wen;
logic [CORE_NUM-1:0] core_boot_ivb_hi_wen;
logic [CORE_NUM-1:0] core_boot_ivb_hi_wen_valid_req;
logic [CORE_NUM-1:0] core_rst_set;
logic [CORE_NUM-1:0] core_rst_clr;
logic [CORE_NUM-1:0] core_clk_en_wen;
logic [CORE_NUM-1:0] core_pmode_wen;

logic [CORE_NUM-1:0] core_run_en;
logic [CORE_NUM-1:0] core_halt_en;
logic [CORE_NUM-1:0] core_boot_ivb_lo_en;
logic [CORE_NUM-1:0] core_boot_ivb_hi_en;
logic [CORE_NUM-1:0] core_rst_en;
logic [CORE_NUM-1:0] core_clk_en_en;
logic [CORE_NUM-1:0] core_status_en;

logic [CORE_NUM-1:0] core_running;
logic [CORE_NUM-1:0] core_halting;
logic [CORE_NUM-1:0] core_sleeping;
logic [CORE_NUM-1:0] core_power_on;

logic clk_ena_rst;

assign clk_ena_rst = CORE_CLK_ENA_RST;
assign  mmio_resp = {(mmio_sel && !valid_req), mmio_sel};
always_comb
begin: mmio_ack_PROC
// spyglass disable_block Ac_conv03
// sync DFF converge
  mmio_rdata  = {DATA_WIDTH{1'b0}};
// spyglass enable_block Ac_conv03
  for (int unsigned i=0;i<CORE_NUM; i++)
  begin: core_ack_PROC
    if (mmio_ren)
    begin
      if (|core_run_en)
          // return the run handshake status 
        mmio_rdata = mmio_rdata | {32{core_run_en[i]}} & CORE_RUN[i]; 
      else if (|core_halt_en)
          // return the halt handshake status 
        mmio_rdata = mmio_rdata | {32{core_halt_en[i]}} & CORE_HALT[i]; 
      else if (|core_boot_ivb_lo_en)
          // return the current boot address
          // this value should be the same as what the target core read
          // If the value is written without reset properly, this is a software error 
        mmio_rdata = mmio_rdata | {32{core_boot_ivb_lo_en[i]}} & CORE_BOOT_IVB_LO[i]; 
      else if (|core_boot_ivb_hi_en)
          // return the current boot address
          // this value should be the same as what the target core read
          // If the value is written without reset properly, this is a software error 
        mmio_rdata = mmio_rdata | {32{core_boot_ivb_hi_en[i]}} & CORE_BOOT_IVB_HI[i]; 
      else if (|core_status_en)
        // return the core status 
        mmio_rdata = mmio_rdata | {32{core_status_en[i]}} & CORE_STATUS[i]; 
      else if (|core_rst_en)
          // return the reset handshake status 
        mmio_rdata = mmio_rdata | {32{core_rst_en[i]}} & CORE_RESET[i]; 
      else if (|core_clk_en_en)
          // return the core_clk_en status
        mmio_rdata = mmio_rdata | {32{core_clk_en_en[i]}} & CORE_CLK_EN[i];
    end
  end: core_ack_PROC  
end: mmio_ack_PROC  
always_comb 
begin: mmio_intf_PROC
  logic [ADDR_WIDTH-1:0]  addr_core_run         ; 
  logic [ADDR_WIDTH-1:0]  addr_core_halt        ; 
  logic [ADDR_WIDTH-1:0]  addr_core_boot_ivb_lo ; 
  logic [ADDR_WIDTH-1:0]  addr_core_boot_ivb_hi ; 
  logic [ADDR_WIDTH-1:0]  addr_core_status      ; 
  logic [ADDR_WIDTH-1:0]  addr_core_reset       ; 
  logic [ADDR_WIDTH-1:0]  addr_core_clk_en      ; 
  for (int unsigned i=0;i<CORE_NUM; i++)
  begin: mmio_per_core_PROC
    addr_core_run    = ADDR_CORE_RUN + 4*i;
    addr_core_halt   = ADDR_CORE_HALT + 4*i;
    addr_core_boot_ivb_lo = ADDR_CORE_BOOT_IVB_LO + 4*i;
    addr_core_boot_ivb_hi = ADDR_CORE_BOOT_IVB_HI + 4*i;
    addr_core_status = ADDR_CORE_STATUS + 4*i;
    addr_core_reset  = ADDR_CORE_RESET + 4*i;
    addr_core_clk_en = ADDR_CORE_CLK_EN + 4*i;
      
    // The request accesses CORE_RUN register
    core_run_en[i] = (mmio_sel && arcsync_core_exist[i]) && (mmio_addr == addr_core_run);
    // write 1 to trigger run request and write 0 ignored 
    core_run_wen[i] = core_run_en[i] && mmio_wen && arcsync_core_wr_enable[i] &&  mmio_wdata[0] && core_power_on[i];
    core_run_wen_valid_req[i] = core_run_en[i] && mmio_wen && arcsync_core_wr_enable[i];

    // The request accesses CORE_HALT register
    core_halt_en[i] =  (mmio_sel && arcsync_core_exist[i]) && (mmio_addr == addr_core_halt);
    // write 1 to trigger halt request and write 0 ignored 
    core_halt_wen[i] = core_halt_en[i] && mmio_wen && arcsync_core_wr_enable[i] && mmio_wdata[0] && core_power_on[i];
    core_halt_wen_valid_req[i] = core_halt_en[i] && mmio_wen && arcsync_core_wr_enable[i];

    // The request accesses CORE_BOOT_IVB_LO register
    core_boot_ivb_lo_en[i] =  (mmio_sel && arcsync_core_exist[i]) && (mmio_addr == addr_core_boot_ivb_lo);
    // set the hard coded "intvbase_in" value of other ARC cores 
    core_boot_ivb_lo_wen[i]  = core_boot_ivb_lo_en[i] && mmio_wen && arcsync_core_wr_enable[i];

    // The request accesses CORE_BOOT_IVB_HI register
    core_boot_ivb_hi_en[i] = (mmio_sel && arcsync_core_exist[i]) && (mmio_addr == addr_core_boot_ivb_hi);
    // ARC32 core programing CORE_BOOT_IVB_HI* registers will take no effect. 
    core_boot_ivb_hi_wen[i]  = core_boot_ivb_hi_en[i] && mmio_wen && arcsync_core_wr_enable[i] && core_arcsync_arc64[i];
    core_boot_ivb_hi_wen_valid_req[i] = core_boot_ivb_hi_en[i] && mmio_wen && arcsync_core_wr_enable[i];

    // The request accesses CORE_STATUS register
    core_status_en[i] =  (mmio_sel && arcsync_core_exist[i]) && (mmio_addr == addr_core_status);
    // Write ignored, read to return the status of core
     
    // The request accesses CORE_RESET register
    core_rst_en[i] =  (mmio_sel && arcsync_core_exist[i]) && (mmio_addr == addr_core_reset);
    // write {0x5A5A, core_id} to trigger reset request. otherwise, ignored
    // There is no reset interface for VPX, if the corresponging register is written, it stays at '1' 
    core_rst_set[i] = core_rst_en[i] && mmio_wen && arcsync_core_wr_enable[i] && (mmio_wdata[31:16] == 16'h5A5A) && (mmio_wdata[15:0] == i); 
    core_rst_clr[i] = core_rst_en[i] && mmio_wen && arcsync_core_wr_enable[i] && (mmio_wdata[31:16] == 16'hA5A5) && (mmio_wdata[15:0] == i); 

    core_clk_en_en[i] =  (mmio_sel && arcsync_core_exist[i]) && (mmio_addr == addr_core_clk_en);
    core_clk_en_wen[i] = core_clk_en_en[i] && mmio_wen && arcsync_core_wr_enable[i];

  end:mmio_per_core_PROC  
end: mmio_intf_PROC  
assign valid_req = mmio_ren  && 
                   ((|core_run_en) || (|core_halt_en)    || (|core_boot_ivb_lo_en) || (|core_boot_ivb_hi_en) ||
                    (|core_rst_en) || (|core_clk_en_en)  || (|core_status_en)) ||
                   mmio_wen &&
                   ((|core_run_wen_valid_req) || (|core_halt_wen_valid_req) || (|core_boot_ivb_lo_wen) || (|core_boot_ivb_hi_wen_valid_req) ||
                    (|core_rst_set) || (|core_rst_clr) || (|core_clk_en_wen) || (|core_status_en));

for (genvar i=0;i<CORE_NUM_S; i++)
begin: individual_core_PROC 
  // outputs for each request
  assign CORE_RUN[i]        = {31'b0, core_run_r[i]};       
  assign CORE_HALT[i]       = {31'b0, core_halt_r[i]};      
  assign CORE_BOOT_IVB_LO[i]= core_boot_ivb_lo_r[i];
  assign CORE_BOOT_IVB_HI[i]= {11'b0, core_boot_ivb_hi_r[i]};
  assign CORE_STATUS[i] ={ {23{1'b0}}, 
                           core_arcsync_pmode[i],     
                           core_arcsync_sys_sleep_mode[i],     
                           core_arcsync_sys_sleep[i],
                           core_arcsync_sys_tf_halt[i],      
                           core_arcsync_sys_halt[i]};   
  assign CORE_RESET[i]      = {31'h0, core_reset_req_r[i]};
  assign CORE_CLK_EN[i]     = {31'b0, core_clk_en_r[i]};
  assign arcsync_core_intvbase[i]    = core_arcsync_arc64[i]?({CORE_BOOT_IVB_HI[i], CORE_BOOT_IVB_LO[i]}<<11):
                                                             ({CORE_BOOT_IVB_HI[i], CORE_BOOT_IVB_LO[i]}<<10);
  // The request will de-assert after the ack signal comes                                                            
  assign arcsync_core_run_req[i]     = core_run_req_r[i];
  assign arcsync_core_halt_req[i]    = core_halt_req_r[i];
  assign arcsync_core_rst_req[i]     = core_reset_req_r[i];
  assign arcsync_core_clk_en[i]      = core_clk_en_r[i];
  // Track the hand-shake procedure that the ack signal is de-asserted
  assign core_arcsync_run_acked[i]   = core_arcsync_run_ack_r[i]  && !core_arcsync_run_ack[i];
  assign core_arcsync_halt_acked[i]  = core_arcsync_halt_ack_r[i] && !core_arcsync_halt_ack[i];

  // extract the process states
  assign core_halting[i]   = core_arcsync_sys_halt[i] || core_arcsync_sys_tf_halt[i];
  assign core_sleeping[i]  = core_arcsync_sys_sleep[i];
  assign core_running[i]   = ~core_halting[i] & ~core_sleeping[i];
  assign core_power_on[i]  = core_arcsync_pmode[i]==3'h0;

  always_comb
  begin: core_run_PROC
    core_run_nxt[i] = core_run_r[i];
    if (core_arcsync_run_acked[i])
      // When the run handshake is done, back to 0
      core_run_nxt[i] = 1'b0;
    else if (core_run_wen[i] && !(core_running[i]))
      // If core is power-down, the run request is not sent.
      // If core is halted or sleeping, assert the run request until the core is waken-up and run
      // If core is running, the run request is masked 
      core_run_nxt[i] = 1'b1;
  end: core_run_PROC
  always_comb
  begin: core_run_req_PROC
// spyglass disable_block Ac_conv03
// ext_arc_run_ack sync DFF converge
    core_run_req_nxt[i] = core_run_req_r[i];
// spyglass enable_block Ac_conv03
    if (core_arcsync_run_ack[i])
      // When the run ack comes, back to 0
      core_run_req_nxt[i] = 1'b0;
    else if (core_run_wen[i] && !(core_running[i]))
      // When the core_run register is written, send run_req
      core_run_req_nxt[i] = 1'b1;
  end: core_run_req_PROC
  always_comb
  begin:core_halt_PROC
    core_halt_nxt[i] = core_halt_r[i];
    if (core_halt_wen[i] && !(core_halting[i]) & core_arcsync_halt_acked[i])
      // When core_halt is set back to back, the core_halt_r should keep 1.
      core_halt_nxt[i] = 1'b1;
    else if (core_arcsync_halt_acked[i])
      // When the halt handshake is done, back to 0
      core_halt_nxt[i] = 1'b0;
    else if (core_halt_wen[i] && !(core_halting[i]))
      // If the core receive a halt request when it's power down and halting,
      // When it wakes up, it will see a halt request but it might not be able to send halt_ack. 
      // If core is power-down, the halt request is not sent
      // assert the halt request until the core is waken-up and halted
      // If core is halted, the halt request is masked 
      core_halt_nxt[i] = 1'b1;
  end: core_halt_PROC
  always_comb
  begin:core_halt_req_PROC
// spyglass disable_block Ac_conv03
// ext_arc_halt_ack sync DFF converge
    core_halt_req_nxt[i] = core_halt_req_r[i];
// spyglass enable_block Ac_conv03
    if (core_arcsync_halt_ack[i])
      // When the halt ack comes, back to 0
      core_halt_req_nxt[i] = 1'b0;
    else if (core_halt_wen[i] && !(core_halting[i]))
      // When the core_halt register is written, send halt_req
      core_halt_req_nxt[i] = 1'b1;
  end: core_halt_req_PROC
  always_comb
  begin: core_boot_lo_PROC
    core_boot_ivb_lo_nxt[i] = core_boot_ivb_lo_r[i];
    if (core_boot_ivb_lo_wen[i])
    begin
      if (core_arcsync_arc64[i]) 
        // For ARC64 core, all field is valid 
        core_boot_ivb_lo_nxt[i] = mmio_wdata;
      else
        // For ARC32 core, LSB 22-bit is valid 
        core_boot_ivb_lo_nxt[i] = {{10{1'b0}}, mmio_wdata[21:0]};
    end  
  end: core_boot_lo_PROC
  always_comb
  begin: core_boot_hi_PROC
    core_boot_ivb_hi_nxt[i] = core_boot_ivb_hi_r[i];
    if (core_boot_ivb_hi_wen[i])
      // For ARC64 core, LSB 21-bit is valid mostly
      // [FIXME] adjust with different address width later 
      core_boot_ivb_hi_nxt[i] = mmio_wdata[20:0];
  end: core_boot_hi_PROC

  always_comb
  begin: core_reset_req_PROC
    core_reset_req_nxt[i] = core_reset_req_r[i];
    if (core_rst_clr[i])
      // de-assert the reset
      core_reset_req_nxt[i] = 1'b0;
    else if (core_rst_set[i])
      // assert the reset
      core_reset_req_nxt[i] = 1'b1;
  end: core_reset_req_PROC 

  always_comb
  begin: core_clk_en_PROC
    core_clk_en_nxt[i] = core_clk_en_r[i];
    if (core_clk_en_wen[i])
      core_clk_en_nxt[i] = mmio_wdata[0];
  end: core_clk_en_PROC


// spyglass disable_block Ac_conv03
// ext_arc_run_ack, ext_arc_halt_ack sync DFF converge
  assign core_reg_en[i]        =  core_arcsync_run_acked[i]  || core_arcsync_halt_acked[i]  
                               || core_arcsync_run_ack[i]  || core_arcsync_halt_ack[i]  
                               || (mmio_wen && mmio_sel && arcsync_core_wr_enable[i]);
// spyglass enable_block Ac_conv03
  always_ff @(posedge clk or posedge rst_a)
  begin: core_reg_PROC
    if (rst_a)
    begin  
      core_run_r[i]        <= 'b0; 
      core_halt_r[i]       <= 'b0;
      core_boot_ivb_lo_r[i]<= 'b0;
      core_boot_ivb_hi_r[i]<= 'b0;
      //core_reset_r[i]      <= 'b0;
      core_clk_en_r[i]     <= clk_ena_rst;
      core_run_req_r[i]    <= 'b0; 
      core_halt_req_r[i]   <= 'b0;
      core_reset_req_r[i]  <= 'b1;
      core_arcsync_run_ack_r[i]  <=  1'b0;
      core_arcsync_halt_ack_r[i] <=  1'b0;
    end
    else  
    begin  
      if (core_reg_en[i])       
      begin  
        core_run_r[i]        <= core_run_nxt[i]        ; 
        core_halt_r[i]       <= core_halt_nxt[i]       ;
        core_boot_ivb_lo_r[i]<= core_boot_ivb_lo_nxt[i];
        core_boot_ivb_hi_r[i]<= core_boot_ivb_hi_nxt[i];
        //core_reset_r[i]      <= core_reset_nxt[i]      ;
        core_clk_en_r[i]       <= core_clk_en_nxt[i]     ;
        core_run_req_r[i]    <= core_run_req_nxt[i]    ; 
        core_halt_req_r[i]   <= core_halt_req_nxt[i]   ;
        core_reset_req_r[i]  <= core_reset_req_nxt[i]  ;
        core_arcsync_run_ack_r[i]  <=  core_arcsync_run_ack[i];
        core_arcsync_halt_ack_r[i] <=  core_arcsync_halt_ack[i];
      end  
    end
  end: core_reg_PROC
end: individual_core_PROC

//-------------------------------------------------------------------------------------------------------
// Properties
//-------------------------------------------------------------------------------------------------------
`ifdef FORMAL_ASSERT_ON
  `include "prop_arcsync_acs_pmu.sv"
`endif
endmodule
