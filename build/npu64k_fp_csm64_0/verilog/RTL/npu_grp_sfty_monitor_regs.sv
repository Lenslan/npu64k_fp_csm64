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
// File defining the npu fabric safety monitor
//

`include "npu_defines.v"
`include "npu_macros.svh"
`include "npu_axi_macros.svh"
module npu_grp_sfty_monitor_regs
  import npu_types::*;
  (
// spyglass disable_block W240
// SMD: Declared but not used 
// SJ: wstrb unused
   // read command channel
  input  logic                        sfty_cfg_axi_arvalid, // read command valid
  output logic                        sfty_cfg_axi_arready, // read command accept
  input  logic          [1-1:0]  sfty_cfg_axi_arid,    // read command ID
  input  logic          [1-1:0] sfty_cfg_axi_aruser,  // read command user field
  input  logic          [NPU_AXI_ADDR_W-1:0]   sfty_cfg_axi_araddr  ,      // read command
  input  logic          [3:0]         sfty_cfg_axi_arcache ,      // read command
  input  logic          [2:0]         sfty_cfg_axi_arprot  ,      // read command
  input  logic          [1-1:0]         sfty_cfg_axi_arlock  ,      // read command
  input  logic          [1:0]         sfty_cfg_axi_arburst ,      // read command
  input  logic          [3:0]         sfty_cfg_axi_arlen   ,      // read command
  input  logic          [2:0]         sfty_cfg_axi_arsize  ,      // read command
  input  logic          [NPU_AXI_REGION_W-1:0]         sfty_cfg_axi_arregion,      // read command
  // read data channel
  output logic                        sfty_cfg_axi_rvalid,  // read data valid
  input  logic                        sfty_cfg_axi_rready,  // read data accept
  output logic          [1-1:0]  sfty_cfg_axi_rid,     // read data id
  output logic          [32-1:0]   sfty_cfg_axi_rdata,   // read data
  output logic          [1:0]         sfty_cfg_axi_rresp,   // read response
  output logic          [1-1:0]  sfty_cfg_axi_ruser,   // read data user field
  output logic                        sfty_cfg_axi_rlast,   // read last
  // write command channel
  input  logic                        sfty_cfg_axi_awvalid, // write command valid
  output logic                        sfty_cfg_axi_awready, // write command accept
  input  logic          [1-1:0]  sfty_cfg_axi_awid,    // write command ID
  input  logic          [1-1:0] sfty_cfg_axi_awuser,  // write command user field
  input  logic          [NPU_AXI_ADDR_W-1:0]   sfty_cfg_axi_awaddr  ,      // read command
  input  logic          [3:0]         sfty_cfg_axi_awcache ,      // read command
  input  logic          [2:0]         sfty_cfg_axi_awprot  ,      // read command
  input  logic          [1-1:0]         sfty_cfg_axi_awlock  ,      // read command
  input  logic          [1:0]         sfty_cfg_axi_awburst ,      // read command
  input  logic          [3:0]         sfty_cfg_axi_awlen   ,      // read command
  input  logic          [2:0]         sfty_cfg_axi_awsize  ,      // read command
  input  logic          [NPU_AXI_REGION_W-1:0]         sfty_cfg_axi_awregion,      // read command
  // write data channel
  input  logic                        sfty_cfg_axi_wvalid,  // write data valid
  output logic                        sfty_cfg_axi_wready,  // write data accept
  input  logic          [32-1:0]   sfty_cfg_axi_wdata,   // write data
  input  logic          [32/8-1:0] sfty_cfg_axi_wstrb,   // write data strobe
  input  logic          [1-1:0]  sfty_cfg_axi_wuser,   // write data user field
  input  logic                        sfty_cfg_axi_wlast,   // write data last
  // write response channel
  output logic                        sfty_cfg_axi_bvalid,  // write response valid
  input  logic                        sfty_cfg_axi_bready,  // write response accept
  output logic          [1-1:0]  sfty_cfg_axi_bid,     // write response id
  output logic          [1-1:0]  sfty_cfg_axi_buser,   // read data user field
  output logic          [1:0]         sfty_cfg_axi_bresp,   // write response,
// spyglass enable_block W240
   output logic [31:0]                     npu_grp_dbank_ecc_ctrl_r,
   // dbank ctrl & status
   input  logic                         dbnk_dbe,
   input  logic                         dbnk_sbe,
   input  logic                            dbnk_init_done,
   input  logic [7:0]                      dbnk_num,
   //Clock and Reset
   input  logic                           clk,       // always-on clock
   input  logic                           rst_a     // asynchronous reset, active high, synchronous deassertion
   );

// NPU Safety registers accessible over AXI:
//
// name                            aoffset    roffset rd/wr width Description
// GRP_DBANK_ECC_CTRL             0x024       9        RW    32b  NPU Grouo Dbank ECC Control and Status Register

  // local parameters
  localparam int GRP_DBANK_ECC_CTRL           = 10'h9;
  localparam int SAXIIDW  = 1;             // AXI MMIO slave ID width
  localparam int SAXIAWUW = 1;             // AXI MMIO slave AW user width
  localparam int SAXIWUW  = 1;             // AXI MMIO slave W user width
  localparam int SAXIBUW  = 1;             // AXI MMIO slave B user width
  localparam int SAXIARUW = 1;             // AXI MMIO slave AR user width
  localparam int SAXIRUW  = 1;             // AXI MMIO slave R user width
  
  // local types
  // AXI slave interface state
  typedef enum logic [8:0] { 
    SAXI_RST    = 9'b0_0000_0001, // reset state
    SAXI_RCMD   = 9'b0_0000_0010, // accept AXI read command
    SAXI_WCMD   = 9'b0_0000_0100, // accept AXI write command
    SAXI_WDATA  = 9'b0_0000_1000, // accept AXI write data
    SAXI_RDATA  = 9'b0_0001_0000, // return AXI read data
    SAXI_BRESP  = 9'b0_0010_0000, // return AXI write OK response
    SAXI_WERR   = 9'b0_0100_0000, // ignore remaining writes after error on AXI
    SAXI_BERR   = 9'b0_1000_0000, // return write error on AXI
    SAXI_RERR   = 9'b1_0000_0000  // ignore remaining reads after error on AXI
  } saxi_state_t;

  //
  // local functions
  //
  //function automatic logic check_write(input logic [11:2] addr, input logic dual);
  function automatic logic check_write(input logic [11:2] addr);
  begin    

    // check if a register is writable
    casez (addr[11:2])
      // writeable regs
      GRP_DBANK_ECC_CTRL
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
  end  
  endfunction : check_write
  //
  // MMIO registers and wires local declerations
  logic                       reg_wen;             // register enables: true if register is written
  localparam CFG_DBNK_ECC = 1'b1;
  logic                       npu_grp_dbank_ecc_ctrl_we;     // npu_grp_dbank_ecc_ctrl register write program enable
  logic                       npu_grp_dbank_ecc_ctrl_en; 
  logic [31:0]                npu_grp_dbank_ecc_ctrl_nxt;
  
  // AXI slave state registers and wires
  logic                        saxi_state_en;  // AXI slave state register enable
  saxi_state_t                 saxi_state_nxt; // AXI slave state next
  saxi_state_t                 saxi_state_r;   // AXI slave state register
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
  
  logic                        sfty_cfg_axi_rdata_hld; // hold rdata when rready not assert
  logic         [31:0]         sfty_cfg_axi_rdata_nxt; // Internal AXI rdata 
  logic         [31:0]         sfty_cfg_axi_rdata_r;   // Internal AXI rdata register

  logic                        canwrite; // check register writable

 //----------------------------------------------------------------------------------------------------------------------------------------//
 //                                                Safety Config AXI                                                                       // 
 //----------------------------------------------------------------------------------------------------------------------------------------//
  
  // AXI interface, supports 32b linear bursts or single
  //
  // tied user signals
  assign sfty_cfg_axi_buser = '0;
  assign sfty_cfg_axi_ruser = '0;

  assign sfty_cfg_axi_bid = saxi_id_r;
  assign sfty_cfg_axi_rid = saxi_id_r;
  // other axi output
  assign sfty_cfg_axi_rlast = (saxi_cnt_r == 8'h00);
  assign sfty_cfg_axi_rdata = (sfty_cfg_axi_rdata_hld == 1'b1) ? sfty_cfg_axi_rdata_r : sfty_cfg_axi_rdata_nxt;
  
  // register enable
  assign saxi_state_en = |(saxi_state_r^saxi_state_nxt);
  assign saxi_ar_token = sfty_cfg_axi_arvalid & sfty_cfg_axi_arready;
  assign saxi_aw_token = sfty_cfg_axi_awvalid & sfty_cfg_axi_awready;
  assign saxi_r_token  = sfty_cfg_axi_rvalid  & sfty_cfg_axi_rready;
  assign saxi_w_token  = sfty_cfg_axi_wvalid  & sfty_cfg_axi_wready;
  assign saxi_b_token  = sfty_cfg_axi_bvalid  & sfty_cfg_axi_bready;
  assign saxi_cmd_token = saxi_ar_token | saxi_aw_token;
  assign saxi_cnt_en =  saxi_ar_token 
                      | saxi_r_token 
                      | saxi_aw_token
                      | saxi_w_token & (saxi_state_r != SAXI_WERR);

  // AXI slave state dependent outputs and next state
  always_comb
  begin : saxi_state_nxt_PROC
    canwrite = check_write(saxi_addr_r);
    // defaults
    saxi_state_nxt   = saxi_state_r;
    saxi_cnt_nxt     = saxi_cnt_r - 1'b1;
    saxi_addr_nxt    = saxi_addr_r + 10'd1;
    saxi_id_nxt      = sfty_cfg_axi_arid;
    reg_wen         = 1'b0;
    // default AXI outputs
    sfty_cfg_axi_awready = 1'b0;
    sfty_cfg_axi_wready  = 1'b0;
    sfty_cfg_axi_bvalid  = 1'b0;
    sfty_cfg_axi_bresp   = npu_axi_resp_okay_e;
    sfty_cfg_axi_arready = 1'b0;
    sfty_cfg_axi_rvalid  = 1'b0;
    sfty_cfg_axi_rresp   = npu_axi_resp_okay_e;
    // state dependent outputs
    casez (saxi_state_r)
    SAXI_RST:
    begin
      saxi_state_nxt = SAXI_RCMD;
    end // SAXI_RST
    SAXI_RCMD:
    begin
      sfty_cfg_axi_arready = 1'b1;
      if (sfty_cfg_axi_arvalid)
      begin
        saxi_cnt_nxt   = sfty_cfg_axi_arlen;
        saxi_addr_nxt  = {sfty_cfg_axi_araddr[11:3], sfty_cfg_axi_araddr[2] & (sfty_cfg_axi_arsize == 3'd2)};
        if (sfty_cfg_axi_arprot[0]) // priviledge access
        begin
          if ((sfty_cfg_axi_arsize == 3'd2) && (sfty_cfg_axi_arburst == npu_axi_burst_incr_e || sfty_cfg_axi_arlen == 8'h00))
          begin
            saxi_state_nxt  = SAXI_RDATA;
          end
          else
          begin
            saxi_state_nxt = SAXI_RERR;
          end
        end
        else // non-priviledge access, return error
        begin
          saxi_state_nxt = SAXI_RERR;
        end
      end    
      else if (sfty_cfg_axi_awvalid)
      begin
        saxi_state_nxt = SAXI_WCMD;
      end    
    end // SAXI_RCMD
    SAXI_WCMD:
    begin
      sfty_cfg_axi_awready = 1'b1;
      saxi_id_nxt    = sfty_cfg_axi_awid;
      if (sfty_cfg_axi_awvalid) 
      begin
        if (sfty_cfg_axi_awprot[0]) // priviledge access
        begin
          saxi_addr_nxt  = {sfty_cfg_axi_awaddr[11:3], sfty_cfg_axi_awaddr[2] & (sfty_cfg_axi_awsize == 3'd2)};
          if ((sfty_cfg_axi_awsize == 2) && (sfty_cfg_axi_awburst == npu_axi_burst_incr_e || sfty_cfg_axi_awlen == 8'h00))
          begin
            saxi_state_nxt = SAXI_WDATA;
          end
          else
          begin
            saxi_state_nxt = SAXI_WERR;
          end
        end
        else // non-priviledge access, return error
        begin
          saxi_state_nxt = SAXI_WERR;
        end
      end
      else if (sfty_cfg_axi_arvalid)
      begin
        saxi_state_nxt = SAXI_RCMD;
      end 
    end // SAXI_WCMD
    SAXI_WDATA:
    begin
      sfty_cfg_axi_wready = 1'b1;
      if (sfty_cfg_axi_wvalid) 
      begin
        reg_wen = canwrite;
        if (sfty_cfg_axi_wlast)
        begin
          if (!reg_wen)
          begin
            saxi_state_nxt = SAXI_BERR;
          end
          else
          begin
            saxi_state_nxt = SAXI_BRESP;
            reg_wen = 1'b1;
          end
        end
        else 
        begin
          if (!reg_wen)
          begin    
            saxi_state_nxt = SAXI_WERR;
          end
        end
      end 
    end // SAXI_WDATA
    SAXI_RDATA:
    begin
      sfty_cfg_axi_rvalid = 1'b1;
      if (sfty_cfg_axi_rready)
      begin
        if (saxi_cnt_r == 8'h00)
        begin
          saxi_state_nxt = SAXI_WCMD;
        end
      end
    end // SAXI_RDATA
    SAXI_BRESP:
    begin
      sfty_cfg_axi_bvalid = 1'b1;
      if (sfty_cfg_axi_bready)
      begin
        saxi_state_nxt = SAXI_RCMD;
      end
    end // SAXI_BRESP
    SAXI_WERR:
    begin
      // terminate remainder of burst by accept write data
      sfty_cfg_axi_wready = 1'b1;
      if (sfty_cfg_axi_wlast && sfty_cfg_axi_wvalid)
      begin 
        saxi_state_nxt = SAXI_BERR;
      end 
    end // SAXI_WERR
    SAXI_RERR:
    begin
        sfty_cfg_axi_rvalid = 1'b1;
        sfty_cfg_axi_rresp  = npu_axi_resp_slverr_e;
        if (sfty_cfg_axi_rready) 
        begin
          if (sfty_cfg_axi_rlast)
          begin
            saxi_state_nxt = SAXI_WCMD;
          end
        end
    end // SAXI_RERR
    SAXI_BERR:
    begin
      sfty_cfg_axi_bvalid = 1'b1;
      sfty_cfg_axi_bresp  = npu_axi_resp_slverr_e;
      if (sfty_cfg_axi_bready) 
      begin
        saxi_state_nxt = SAXI_RCMD;
      end
    end
    default:
    begin
      saxi_cnt_nxt   = saxi_cnt_r;
      saxi_addr_nxt  = saxi_addr_r;
    end   
    endcase
  end : saxi_state_nxt_PROC

  // AXI MMIO slave interface state registers
  always_ff @(posedge clk or posedge rst_a)
  begin : saxi_state_reg_PROC
    if (rst_a == 1'b1) 
    begin
      saxi_state_r   <= SAXI_RST;
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
      sfty_cfg_axi_rdata_hld <= 'd0;
      sfty_cfg_axi_rdata_r   <= 'd0;
    end
    else
    begin
      if (saxi_state_r == SAXI_RDATA)
      begin 
        sfty_cfg_axi_rdata_hld   <= ~sfty_cfg_axi_rready;
        if ((sfty_cfg_axi_rready == 1'b0) && (sfty_cfg_axi_rdata_hld == 1'b0))
        begin
          sfty_cfg_axi_rdata_r    <= sfty_cfg_axi_rdata_nxt;
        end
      end
    end
  end : hold_rdata_reg_PROC

  //
  // MMIO register values

  // AXI REG read data
  always_comb
  begin : saxi_reg_rd_PROC
    // default
    sfty_cfg_axi_rdata_nxt = '0;
    casez (saxi_addr_r)
    GRP_DBANK_ECC_CTRL:
    begin
      sfty_cfg_axi_rdata_nxt = npu_grp_dbank_ecc_ctrl_r;
    end
    default:
    begin
      sfty_cfg_axi_rdata_nxt = sfty_cfg_axi_rdata_r;
    end    
    endcase // casez (saxi_addr_r)
  end : saxi_reg_rd_PROC

  // update registers
  always_comb
  begin : saxi_reg_wr_PROC
    npu_grp_dbank_ecc_ctrl_we = 1'b0;
    // AXI write
    if (reg_wen) // Register write operation
    begin
        casez (saxi_addr_r)
        GRP_DBANK_ECC_CTRL:
        begin
          npu_grp_dbank_ecc_ctrl_we = 1'b1;
        end
        default:
        begin
          npu_grp_dbank_ecc_ctrl_we = 1'b0;
        end    
        endcase
    end // if (reg_wen)   
  end : saxi_reg_wr_PROC

//
  always_ff @(posedge clk or posedge rst_a)
  begin : saxi_reg_PROC
    if (rst_a == 1'b1)
    begin
      npu_grp_dbank_ecc_ctrl_r             <= {31'b0, CFG_DBNK_ECC};
    end
    else
    begin
      if(npu_grp_dbank_ecc_ctrl_en)
      begin
        npu_grp_dbank_ecc_ctrl_r            <= npu_grp_dbank_ecc_ctrl_nxt;
      end
    end
  end : saxi_reg_PROC


  logic dbnk_ecc_enb;
  logic dbnk_ecc_err_we;
  logic dbnk_init_done_we;
  logic sbe_cnt_clr;
  logic sbe_cnt_add;
  logic       dbank_ecc_ctrl_clr_nxt;
  logic       dbank_ecc_ctrl_clr_r;
  logic dbnk_db_error;
  logic dbnk_sb_error;
  logic [24:16] npu_grp_dbank_ecc_ctrl;
  assign dbnk_db_error = dbnk_dbe;
  assign dbnk_sb_error = dbnk_sbe;
  assign dbank_ecc_ctrl_clr_nxt = (npu_grp_dbank_ecc_ctrl_we && !sfty_cfg_axi_wdata[16])? 1'b1 : 1'b0;
  always_ff @(posedge clk or posedge rst_a)
  begin : dbank_ecc_ctrl_clr_PROC
    if (rst_a == 1'b1) dbank_ecc_ctrl_clr_r <= 1'b0;
    else               dbank_ecc_ctrl_clr_r <= dbank_ecc_ctrl_clr_nxt;
  end
  logic dbank_ecc_ctrl_clr;
  assign dbank_ecc_ctrl_clr = dbank_ecc_ctrl_clr_r;
  assign dbnk_ecc_enb = npu_grp_dbank_ecc_ctrl_r[0];
  assign dbnk_ecc_err_we = (dbnk_ecc_enb &&  dbnk_db_error && !npu_grp_dbank_ecc_ctrl_r[16]);
  assign dbnk_init_done_we = dbnk_init_done^npu_grp_dbank_ecc_ctrl_r[3];
  assign sbe_cnt_clr  = (npu_grp_dbank_ecc_ctrl_we && ~(|sfty_cfg_axi_wdata[31:28]));
  assign sbe_cnt_add  = (dbnk_ecc_enb && dbnk_sb_error && ~(&npu_grp_dbank_ecc_ctrl_r[31:28]));
  assign npu_grp_dbank_ecc_ctrl = dbank_ecc_ctrl_clr? '0: dbnk_ecc_err_we? {dbnk_num, dbnk_db_error} : npu_grp_dbank_ecc_ctrl_r[24:16];
  always_comb
  begin : npu_grp_dbank_ecc_ctrl_PROC
    npu_grp_dbank_ecc_ctrl_en = '0;  
    npu_grp_dbank_ecc_ctrl_nxt        = npu_grp_dbank_ecc_ctrl_r;
    if (npu_grp_dbank_ecc_ctrl_we)
    begin    
       npu_grp_dbank_ecc_ctrl_en = 1'b1; 
       npu_grp_dbank_ecc_ctrl_nxt[0]  = sfty_cfg_axi_wdata[0]; // dbank_ecc_en
       npu_grp_dbank_ecc_ctrl_nxt[1]  = sfty_cfg_axi_wdata[1]; // dbank_scrub_en
       npu_grp_dbank_ecc_ctrl_nxt[2]  = sfty_cfg_axi_wdata[2]; // dbank_init
    end
    if (dbank_ecc_ctrl_clr | dbnk_ecc_err_we)
    begin
       npu_grp_dbank_ecc_ctrl_en = 1'b1; 
       npu_grp_dbank_ecc_ctrl_nxt[24:16] = npu_grp_dbank_ecc_ctrl[24:16];
    end
    if (dbnk_init_done_we) 
    begin
       npu_grp_dbank_ecc_ctrl_en = 1'b1; 
       npu_grp_dbank_ecc_ctrl_nxt[2] = dbnk_init_done? 1'b0 : npu_grp_dbank_ecc_ctrl_r[2]; // auto clr dbank_init
       npu_grp_dbank_ecc_ctrl_nxt[3] = dbnk_init_done; // dbank_init_done
    end
    if (sbe_cnt_clr)
    begin
       npu_grp_dbank_ecc_ctrl_en = 1'b1;
       npu_grp_dbank_ecc_ctrl_nxt[31:28] = '0; // clr dbank sbe cnt
    end
    else if (sbe_cnt_add)
    begin
       npu_grp_dbank_ecc_ctrl_en = 1'b1;
       npu_grp_dbank_ecc_ctrl_nxt[31:28] = npu_grp_dbank_ecc_ctrl_r[31:28] + 1'b1; // incr dbank sbe cnt
    end
  end : npu_grp_dbank_ecc_ctrl_PROC

endmodule


