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

//
// File defining the MMIO and control interface for safety control
//
// MMIO registers accessible over AXI:
//
// name                              aoffset    roffset  rd/wr  width Description
// NPU_ERP_CTRL                      0x000       0       RW     32b   NPU slice error protection hardware control register
// NPU_SBE_CNT                       0x024       9       RW     32b   NPU slice single bit error counter register
// NPU_ERP_BUILD                     0x028       A       RO     32b   NPU slice error protection configuration register

`include "npu_defines.v"
`include "npu_macros.svh"
`include "npu_axi_macros.svh"
`include "npu_vm_ecc_macros.sv"
`include "npu_am_ecc_macros.sv"

module npu_sfty_ctrl_mmio
  import npu_types::*;
  import npu_ecc_types::*;
  #(
    parameter int  SAXIIDW  = 1,             // AXI MMIO slave ID width
    parameter int  SAXIAWUW = 1,             // AXI MMIO slave AW user width
    parameter int  SAXIWUW  = 1,             // AXI MMIO slave W user width
    parameter int  SAXIBUW  = 1,             // AXI MMIO slave B user width
    parameter int  SAXIARUW = 1,             // AXI MMIO slave AR user width
    parameter int  SAXIRUW  = 1,             // AXI MMIO slave R user width
    parameter int  VM_RPORTS = 45 +2,
    parameter int  AM_RPORTS = 3 + 1,
    parameter int  NUM_VM_BANKS = 32,
    parameter int  NUM_AM_BANKS = 2 
   ,localparam int  NUM_VM_ERR_PORT = NUM_VM_BANKS,
    localparam int  NUM_AM_ERR_PORT = NUM_AM_BANKS
  )
  (
   // AXI MMIO interface 64b wide data
// spyglass disable_block W240
// SMD: Declare but not read 
// SJ: Not used signals
   `AXISLV(SAXIIDW,64,SAXIAWUW,SAXIWUW,SAXIBUW,SAXIARUW,SAXIRUW,mmio_axi_),
// spyglass enable_block W240
   
   // ECC input interface
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
   input  logic                           rst_a     // asynchronous reset, active high, synchronous deassertion
  );
  //
  // local parameters
  //
  localparam int VM_BNK_WIDTH=$clog2(NUM_VM_BANKS);
  localparam int AM_BNK_WIDTH=$clog2(NUM_AM_BANKS);
  localparam int VM_ERR_RPT_WIDTH=$clog2(NUM_VM_ERR_PORT);
  localparam int AM_ERR_RPT_WIDTH=$clog2(NUM_AM_ERR_PORT);
  localparam int VM_DATA_RNG_WIDTH =$clog2(VM_NUM_ECC);
  localparam int AM_DATA_RNG_WIDTH =$clog2(AM_NUM_ECC);
  // MMIO register offsets, see table at head of the file
  localparam logic [9:0] NPU_ERP_CTRL_ROS   = 10'h0;
  localparam logic [9:0] NPU_SBE_CNT_ROS    = 10'h9;
  localparam logic [9:0] NPU_ERP_BUILD_ROS  = 10'hA;

  // MMIO address offsets, see table at head of the file
  localparam logic [11:0] NPU_ERP_CTRL_AOS   = 12'h00;
  localparam logic [11:0] NPU_SBE_CNT_AOS    = 12'h24;
  localparam logic [11:0] NPU_ERP_BUILD_AOS  = 12'h28;

  //
  // local types
  //  
  // AXI MMIO slave interface state
  typedef enum logic [3:0] { 
    SAXI_RST,   // reset state
    SAXI_RCMD,  // accept MMIO read command
    SAXI_WCMD,  // accept MMIO write command
    SAXI_WDATA, // accept MMIO write data
    SAXI_RDATA, // return MMIO read data
    SAXI_BRESP, // return MMIO write OK response
    SAXI_WERR,  // ignore remaining writes after error on MMIO
    SAXI_BERR,  // return write error on MMIO
    SAXI_RERR   // ignore remaining reads after error on MMIO
  } saxi_state_t;
  //
  // local functions
  //
  function automatic logic check_write(input logic [11:2] addr, input logic dual);
  begin    
    logic [11:2] addr_tmp = {addr[11:3], (dual | addr[2])};

    // check if an MMIO register is writable
// spyglass disable_block W263
// SMD: Case Selector width mismatch
// SJ: Reviewed
    casez (addr_tmp)
      // writeable regs
      NPU_ERP_CTRL_ROS
     ,NPU_SBE_CNT_ROS
      :
      begin
        check_write = 1'b1;
      end  
      default:
      begin    
        // in input HLAPI range
        check_write = 1'b0;
      end  
    endcase // casez (addr)
// spyglass enable_block W263
  end  
  endfunction : check_write

  //
  // registers and wires
  //
  // MMIO registers and wires
  logic                        mmio_wen;             // register enables: true if register is written
  logic                        mmio_erp_ctrl_we;     // erp_ctrl register write program enable
  logic                        mmio_erp_ctrl_en;     // erp_ctrl register enable
  logic         [31:0]         mmio_erp_ctrl_nxt;
  logic         [31:0]         mmio_erp_ctrl_r;
  logic         [11:6]         mmio_erp_ctrl;
  logic                        mmio_sbe_cnt_en;
  logic                        mmio_sbe_cnt_we;
  logic         [31:0]         mmio_sbe_cnt_nxt;
  logic         [31:0]         mmio_sbe_cnt_r;

  // AXI slave state registers and wires
  logic                        saxi_state_en;  // AXI slave state register enable
  saxi_state_t                 saxi_state_nxt; // AXI slave state next
  saxi_state_t                 saxi_state_r;   // AXI slave state register
  logic                        saxi_size_nxt;  // AXI slave data size register
  logic                        saxi_size_r;    // AXI slave data size
  logic                        saxi_cnt_en;    // AXI slave read burst count register enable
  npu_axi_len_t                saxi_cnt_nxt;   // AXI slave read burst count register
  npu_axi_len_t                saxi_cnt_r;     // AXI slave read burst count register
  logic         [11:2]         saxi_addr_nxt;  // AXI slave address next
  logic         [11:2]         saxi_addr_r;    // AXI slave address register
  logic         [SAXIIDW-1:0]  saxi_id_nxt;    // AXI response ID
  logic         [SAXIIDW-1:0]  saxi_id_r;      // AXI response ID

  logic                        saxi_ar_token;  // AXI slave ar transaction token
  logic                        saxi_aw_token;  // AXI slave aw transaction token
  logic                        saxi_r_token;   // AXI slave r transaction token
  logic                        saxi_w_token;   // AXI slave w transaction token
  logic                        saxi_b_token;   // AXI slave b transaction token
  logic                        saxi_cmd_token;  // AXI slave ar or aw transaction token
  
  logic                        mmio_axi_rdata_hld; // hold rdata when rready not assert
  logic         [63:0]         mmio_axi_rdata_nxt; // Internal AXI rdata 
  logic         [63:0]         mmio_axi_rdata_r;   // Internal AXI rdata register

  // misc signal
  localparam CFG_SECDED = 'h1;
  localparam CFG_VM_ECC = 1'b1;
  localparam CFG_AM_ECC = 1'b1;
  localparam CFG_E2E = 1'b0;
  logic                      canwrite; // check register writable
  logic                      vm_dbe_o_r;
  logic                      am_dbe_o_r;
  logic                      vm_sbe_o_r;
  logic                      am_sbe_o_r;
  logic                      mmio_erp_ctrl_clr_r, mmio_erp_ctrl_clr_nxt;
  logic                      vm_db_error_clr_r, vm_db_error_clr_nxt;
  logic                      am_db_error_clr_r, am_db_error_clr_nxt;
  logic                      mem_ecc_irq_en;
  logic                      mem_ecc_irq_nxt;
  logic                      mem_ecc_irq_r;
  logic                      am_mem_ecc_en;
  logic                      vm_mem_ecc_en;
  logic                      vm_int_en; // vm interrupt enable
  logic                      am_int_en; // am interrupt enable
  logic [1:0]                ecc_sbe_status;
  logic [1:0]                ecc_dbe_status;
  assign vm_prot_en = vm_mem_ecc_en;
  assign am_prot_en = am_mem_ecc_en;
  assign ecc_sbe_status[0] = vm_sb_err;
  assign ecc_sbe_status[1] = am_sb_err;
  assign ecc_dbe_status[0] = vm_db_err;
  assign ecc_dbe_status[1] = am_db_err;
  assign mmio_erp_ctrl[6] = (mmio_erp_ctrl_clr_r | vm_db_error_clr_r)? 1'b0 : (vm_mem_ecc_en && !mmio_erp_ctrl_r[6])? ecc_dbe_status[0] : mmio_erp_ctrl_r[6];
  assign mmio_erp_ctrl[7] = (mmio_erp_ctrl_clr_r | am_db_error_clr_r)? 1'b0 : (am_mem_ecc_en && !mmio_erp_ctrl_r[7])? ecc_dbe_status[1] : mmio_erp_ctrl_r[7];
  assign mmio_erp_ctrl[9:8] = '0;  
  assign mmio_erp_ctrl[11:10] = '0;

  always_ff @(posedge clk or posedge rst_a)
  begin : db_sb_reg_PROC
    if (rst_a == 1'b1)
    begin
      vm_dbe_o_r <= '0;
      am_dbe_o_r <= '0;
      vm_sbe_o_r <= '0;
      am_sbe_o_r <= '0;
    end
    else
    begin
      vm_dbe_o_r <= ecc_dbe_status[0];
      am_dbe_o_r <= ecc_dbe_status[1];
      vm_sbe_o_r <= ecc_sbe_status[0];
      am_sbe_o_r <= ecc_sbe_status[1];
    end
  end : db_sb_reg_PROC  
  assign vm_ecc_dbe = vm_dbe_o_r;
  assign am_ecc_dbe = am_dbe_o_r;
  assign vm_ecc_sbe = vm_sbe_o_r;
  assign am_ecc_sbe = am_sbe_o_r;

  
  //
  // AXI MMIO interface, s//upports 32b and 64b linear bursts or single
  //
  // tied user signals
  assign mmio_axi_buser = '0;
  assign mmio_axi_ruser = '0;

  /// output ID
  assign mmio_axi_bid = saxi_id_r;
  assign mmio_axi_rid = saxi_id_r;

  // other axi output
  assign mmio_axi_rlast = (saxi_cnt_r == 8'h00);
  assign mmio_axi_rdata = (mmio_axi_rdata_hld == 1'b1) ? mmio_axi_rdata_r : mmio_axi_rdata_nxt;
  
  // register enable
  assign saxi_state_en = |(saxi_state_r^saxi_state_nxt);
  assign saxi_ar_token = mmio_axi_arvalid & mmio_axi_arready;
  assign saxi_aw_token = mmio_axi_awvalid & mmio_axi_awready;
  assign saxi_r_token  = mmio_axi_rvalid  & mmio_axi_rready;
  assign saxi_w_token  = mmio_axi_wvalid  & mmio_axi_wready;
  assign saxi_b_token  = mmio_axi_bvalid  & mmio_axi_bready;
  assign saxi_cmd_token = saxi_ar_token | saxi_aw_token;
  assign saxi_cnt_en =  saxi_ar_token 
                      | saxi_r_token 
                      | saxi_aw_token
                      | saxi_w_token & (saxi_state_r != SAXI_WERR);

  // AXI slave state dependent outputs and next state
  always_comb
  begin : saxi_state_nxt_PROC
    canwrite = check_write(saxi_addr_r, saxi_size_r);
    // defaults
    saxi_state_nxt   = saxi_state_r;
    saxi_size_nxt    = mmio_axi_ar.size == 3'd3;
    saxi_cnt_nxt     = saxi_cnt_r - 1'b1;
    saxi_addr_nxt    = saxi_addr_r + (saxi_size_r ? 10'd2 : 10'd1);
    saxi_id_nxt      = mmio_axi_arid;
    mmio_wen         = 1'b0;
    // default AXI outputs
    mmio_axi_awready = 1'b0;
    mmio_axi_wready  = 1'b0;
    mmio_axi_bvalid  = 1'b0;
    mmio_axi_bresp   = npu_axi_resp_okay_e;
    mmio_axi_arready = 1'b0;
    mmio_axi_rvalid  = 1'b0;
    mmio_axi_rresp   = npu_axi_resp_okay_e;
    // state dependent outputs
    casez (saxi_state_r)
    SAXI_RST:
    begin
      saxi_state_nxt = SAXI_RCMD;
    end // SAXI_RST
    SAXI_RCMD:
    begin
      mmio_axi_arready = 1'b1;
      if (mmio_axi_arvalid)
      begin
        saxi_cnt_nxt   = mmio_axi_ar.len;
        saxi_addr_nxt  = {mmio_axi_ar.addr[11:3], mmio_axi_ar.addr[2] & (mmio_axi_ar.size == 3'd2)};
        if (mmio_axi_ar.prot[0]) //priviledge access
        begin    
          if ((mmio_axi_ar.size == 3'd2 || mmio_axi_ar.size == 3'd3) && (mmio_axi_ar.burst == npu_axi_burst_incr_e || mmio_axi_ar.len == 8'h00))
          begin
            saxi_state_nxt  = SAXI_RDATA;
          end
          else
          begin
            saxi_state_nxt = SAXI_RERR;
          end
        end
        else // non-priviledge access, return err
        begin
            saxi_state_nxt = SAXI_RERR;
        end
      end
      else if (mmio_axi_awvalid)
      begin
        saxi_state_nxt = SAXI_WCMD;
      end
    end // SAXI_RCMD
    SAXI_WCMD:
    begin
      mmio_axi_awready = 1'b1;
      saxi_size_nxt  = mmio_axi_aw.size == 3'd3;
      saxi_id_nxt    = mmio_axi_awid;
      if (mmio_axi_awvalid) 
      begin
        if (mmio_axi_aw.prot[0]) //priviledge access
        begin    
          saxi_addr_nxt  = {mmio_axi_aw.addr[11:3], mmio_axi_aw.addr[2] & (mmio_axi_aw.size == 3'd2)};
          if ((mmio_axi_aw.size == 2 || mmio_axi_aw.size == 3) && (mmio_axi_aw.burst == npu_axi_burst_incr_e || mmio_axi_aw.len == 8'h00))
          begin
            saxi_state_nxt = SAXI_WDATA;
          end
          else
          begin
            saxi_state_nxt = SAXI_WERR;
          end
        end
        else // non-priviledge access, return err
        begin
            saxi_state_nxt = SAXI_WERR;
        end
      end
      else if (mmio_axi_arvalid)
      begin
        saxi_state_nxt = SAXI_RCMD;
      end
    end // SAXI_WCMD
    SAXI_WDATA:
    begin
      mmio_axi_wready = 1'b1;
      if (mmio_axi_wvalid) 
      begin
        mmio_wen = canwrite;
        if (mmio_axi_wlast)
        begin
          if (!mmio_wen)
          begin
            saxi_state_nxt = SAXI_BERR;
          end
          else
          begin
            saxi_state_nxt = SAXI_BRESP;
            mmio_wen = 1'b1;
          end
        end
        else 
        begin
          if (!mmio_wen)
          begin    
            saxi_state_nxt = SAXI_WERR;
          end
        end
      end 
    end // SAXI_WDATA
    SAXI_RDATA:
    begin
      mmio_axi_rvalid = 1'b1;
      if (mmio_axi_rready)
      begin
        if (mmio_axi_rlast)
        begin
          saxi_state_nxt = SAXI_WCMD;
        end
      end
    end // SAXI_RDATA
    SAXI_BRESP:
    begin
      mmio_axi_bvalid = 1'b1;
      if (mmio_axi_bready)
      begin
        saxi_state_nxt = SAXI_RCMD;
      end
    end // SAXI_BRESP
    SAXI_WERR:
    begin
      // terminate remainder of burst by accept write data
      mmio_axi_wready = 1'b1;
      if (mmio_axi_wlast && mmio_axi_wvalid)
      begin 
        saxi_state_nxt = SAXI_BERR;
      end 
    end // SAXI_WERR
    SAXI_RERR:
    begin
        mmio_axi_rvalid = 1'b1;
        mmio_axi_rresp  = npu_axi_resp_slverr_e;
        if (mmio_axi_rready) 
        begin
          if (saxi_cnt_r == 8'h00)
          begin
            saxi_state_nxt = SAXI_WCMD;
          end
        end
    end // SAXI_RERR
    SAXI_BERR:
    begin
      mmio_axi_bvalid = 1'b1;
      mmio_axi_bresp  = npu_axi_resp_slverr_e;
      if (mmio_axi_bready) 
      begin
        saxi_state_nxt = SAXI_RCMD;
      end
    end // SAXI_BERR 
    default:
    begin
      saxi_cnt_nxt     = saxi_cnt_r;
      saxi_addr_nxt    = saxi_addr_r;
    end     
    endcase
  end : saxi_state_nxt_PROC

  // AXI MMIO slave interface state registers
  always_ff @(posedge clk or posedge rst_a)
  begin : saxi_state_reg_PROC
    if (rst_a == 1'b1) 
    begin
      saxi_state_r   <= SAXI_RST;
      saxi_size_r    <= '0;
      saxi_cnt_r     <= '0;
      saxi_addr_r    <= '0;
      saxi_id_r      <= '0;
    end
    else
    begin
      if (saxi_state_en)
      begin
        saxi_state_r <= saxi_state_nxt;
      end
      if (saxi_cmd_token)
      begin
        saxi_id_r    <= saxi_id_nxt;
        saxi_size_r  <= saxi_size_nxt;
      end
      if (saxi_cnt_en)
      begin
        saxi_addr_r  <= saxi_addr_nxt;
        saxi_cnt_r   <= saxi_cnt_nxt;
      end
    end
  end : saxi_state_reg_PROC
  
  // hold value: hold rdata when rready not assert
  always_ff @(posedge clk or posedge rst_a)
  begin : hold_rdata_reg_PROC
    if (rst_a == 1'b1)
    begin
      mmio_axi_rdata_hld <= 'd0;
      mmio_axi_rdata_r   <= 'd0;
    end
    else
    begin
      if (saxi_state_r == SAXI_RDATA)
      begin 
        mmio_axi_rdata_hld   <= ~mmio_axi_rready;
        if ((mmio_axi_rready == 1'b0) && (mmio_axi_rdata_hld == 1'b0))
        begin
          mmio_axi_rdata_r    <= mmio_axi_rdata_nxt;
        end
      end
    end
  end : hold_rdata_reg_PROC

  //
  // MMIO register values
  //

  // AXI MMIO read data
  always_comb
  begin : saxi_mmio_rd_PROC
    // default
    mmio_axi_rdata_nxt = '0;
// spyglass disable_block W263
// SMD: Case Selector width mismatch
// SJ: Reviewed
    casez (saxi_addr_r)
    NPU_ERP_CTRL_ROS :
    begin
      mmio_axi_rdata_nxt = {32'b0, 1'b0, mmio_erp_ctrl_r[30:0]}; // clr bit return 0 when read
    end    
    NPU_SBE_CNT_ROS:
    begin
      mmio_axi_rdata_nxt = {mmio_sbe_cnt_r,32'b0};
    end 
    NPU_ERP_BUILD_ROS: //TBD need processed with vpp
    begin
      mmio_axi_rdata_nxt[10] = CFG_E2E; // bus protection
      mmio_axi_rdata_nxt[9] = CFG_AM_ECC; // am protection
      mmio_axi_rdata_nxt[8] = CFG_VM_ECC; // vm protection
      mmio_axi_rdata_nxt[7:0] = CFG_SECDED;
    end 
    default:
    begin
      mmio_axi_rdata_nxt = mmio_axi_rdata_r;
    end    
    endcase // casez (saxi_addr_r)
// spyglass enable_block W263
  end : saxi_mmio_rd_PROC

  // update MMIO registers
  always_comb
  begin : saxi_mmio_wr_PROC
    mmio_erp_ctrl_we            = '0;
    mmio_sbe_cnt_we             = '0;
    // AXI write
    if (mmio_wen) // MMIO write operation
    begin
      if (!saxi_addr_r[2]) // write even registers
      begin
        casez ({saxi_addr_r[11:3],3'b000})
        NPU_ERP_CTRL_AOS:
        begin
          mmio_erp_ctrl_we      = 1'b1;
        end
        default:
        begin
          mmio_erp_ctrl_we      = '0;
        end    
        endcase
      end // if (!saxi_addr_r[2])
      if (saxi_addr_r[2] || saxi_size_r) // write odd registers
      begin
        casez ({saxi_addr_r[11:3],3'b100})
        NPU_SBE_CNT_AOS:
        begin
          mmio_sbe_cnt_we       = 1'b1;
        end 
        default:
        begin
          mmio_sbe_cnt_we       = '0;
        end    
        endcase
      end    
    end // if (mmio_wen)   
  end : saxi_mmio_wr_PROC

  always_ff @(posedge clk or posedge rst_a)
  begin : saxi_mmio_reg_PROC
    if (rst_a == 1'b1)
    begin
      mmio_erp_ctrl_r                      <= {30'h0,CFG_AM_ECC ,CFG_VM_ECC};
      mmio_sbe_cnt_r                       <= '0;
    end
    else
    begin
      if(mmio_erp_ctrl_en)
        mmio_erp_ctrl_r                     <= mmio_erp_ctrl_nxt;
      if(mmio_sbe_cnt_en)
        mmio_sbe_cnt_r                     <= mmio_sbe_cnt_nxt;
    end
  end : saxi_mmio_reg_PROC

  always_comb
  begin : mmio_erp_ctrl_PROC // odd register
    mmio_erp_ctrl_en = '0;  
    mmio_erp_ctrl_nxt     = mmio_erp_ctrl_r;
    mmio_erp_ctrl_nxt[31] = 1'b0; // [31]: clearr fail bit
    if (mmio_erp_ctrl_we)
    begin    
       mmio_erp_ctrl_en = 1'b1; 
       mmio_erp_ctrl_nxt[31] = mmio_axi_wdata[31];  // [31]: clearr fail bit
       mmio_erp_ctrl_nxt[5:4] = mmio_axi_wdata[5:4]; // [5]: am init enable,     [4]: vm init enable
       mmio_erp_ctrl_nxt[3:2] = mmio_axi_wdata[3:2]; // [3]: am interupt enable, [2]: vm interrupt enable
       mmio_erp_ctrl_nxt[1:0] = mmio_axi_wdata[1:0]; // [1]: am ecc enable,      [0]: vm ecc enable
    end   
    else
    begin    
      mmio_erp_ctrl_en = 1'b1;
      mmio_erp_ctrl_nxt[11:6] = mmio_erp_ctrl[11:6];
      if (vm_init_end | am_init_end) // sram init enable auto clear
      begin    
      mmio_erp_ctrl_nxt[4] = mmio_erp_ctrl_r[4] & ~vm_init_end; // auto reset vm init enable to 0 when vm init is done
      mmio_erp_ctrl_nxt[5] = mmio_erp_ctrl_r[5] & ~am_init_end; // auto reset am init enable to 0 when am init is done
      end
    end  
  end : mmio_erp_ctrl_PROC

  assign vm_db_error_clr_nxt   = (mmio_erp_ctrl_we && !mmio_axi_wdata[6]);
  assign am_db_error_clr_nxt   = (mmio_erp_ctrl_we && !mmio_axi_wdata[7]);
  assign mmio_erp_ctrl_clr_nxt = (mmio_erp_ctrl_we &&  mmio_axi_wdata[31]);
  
  always@(posedge clk or posedge rst_a)
  begin : erp_clr_reg_PROC
    if (rst_a == 1'b1)
    begin    
      vm_db_error_clr_r   <= 'b0;
      am_db_error_clr_r   <= 'b0;
      mmio_erp_ctrl_clr_r <= 'b0;
    end   
    else
    begin    
      vm_db_error_clr_r   <= vm_db_error_clr_nxt;
      am_db_error_clr_r   <= am_db_error_clr_nxt;
      mmio_erp_ctrl_clr_r <= mmio_erp_ctrl_clr_nxt;
    end
  end : erp_clr_reg_PROC

  always_comb
  begin : mmio_sbe_cnt_PROC // even register
    mmio_sbe_cnt_en = '0;  
    mmio_sbe_cnt_nxt = mmio_sbe_cnt_r;
    if (mmio_sbe_cnt_we) 
    begin
      mmio_sbe_cnt_en = 1'b1;
      mmio_sbe_cnt_nxt[31] = mmio_axi_wdata[32+31];
      mmio_sbe_cnt_nxt[30] = mmio_axi_wdata[32+30];
    end
    else if (mmio_sbe_cnt_r[31])
    begin
      mmio_sbe_cnt_en = 1'b1;
      mmio_sbe_cnt_nxt[3:0] = '0;
      mmio_sbe_cnt_nxt[7:4] = '0;
      mmio_sbe_cnt_nxt[31] = 1'b0;
    end    
    else if (mmio_sbe_cnt_r[30])
    begin
      mmio_sbe_cnt_en = 1'b0;  
    end    
    else
    begin
      mmio_sbe_cnt_en = 1'b1;  
      if (ecc_sbe_status[0] && ~(&mmio_sbe_cnt_r[3:0])) // vm sbe err && cntr != 4'hf
        mmio_sbe_cnt_nxt[3:0] = mmio_sbe_cnt_r[3:0] + 1'b1;
      if (ecc_sbe_status[1] && ~(&mmio_sbe_cnt_r[7:4])) // am sbe err && cntr != 4'hf
        mmio_sbe_cnt_nxt[7:4] = mmio_sbe_cnt_r[7:4] + 1'b1;
    end    
  end : mmio_sbe_cnt_PROC
  
  // interrupt signal
  assign vm_int_en = mmio_erp_ctrl_r[2]; // vm interrupt enable
  assign am_int_en = mmio_erp_ctrl_r[3]; // am interrupt enable
  assign mem_ecc_irq_nxt = ((vm_mem_ecc_en & vm_int_en) & mmio_erp_ctrl_r[6]) // sticky vm dbe
                         | ((am_mem_ecc_en & am_int_en) & mmio_erp_ctrl_r[7]) // sticky am dbe
                         ;
  assign mem_ecc_irq_en = mem_ecc_irq_nxt^mem_ecc_irq_r;
  always@(posedge clk or posedge rst_a)
  begin : mem_ecc_irq_reg_PROC
    if (rst_a == 1'b1)
      mem_ecc_irq_r <= '0;
    else if(mem_ecc_irq_en)
      mem_ecc_irq_r <= mem_ecc_irq_nxt;
  end : mem_ecc_irq_reg_PROC

  // output signal
  assign vm_init = mmio_erp_ctrl_r[4];
  assign am_init = mmio_erp_ctrl_r[5];
  assign mem_ecc_irq = mem_ecc_irq_r;

  assign vm_mem_ecc_en = mmio_erp_ctrl_r[0];
  assign am_mem_ecc_en = mmio_erp_ctrl_r[1];




endmodule
