
/*
 * Copyright (C) 2021-2022 Synopsys, Inc. All rights reserved.
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
// The AXI configuration MMIO register module controls the address map of the AXI matrix modules inside the NPX processor. The AXI configuration module has the following parameters
//   -int CFGIDW: ID signal width on AXI slave interface
//   -int NUMAP: Number of address apertures to be controlled, maximum 32
//   -int NUMMST: Number of master ports, maximum 32
// This slave interface is 12b address, 32b data, ID signal width CFGIDW, support ASIZE=2 only (else error), support INCR bursts up to 16 beats
// AXI address map configuration interface
// MMIO register accessible over AXI:
// Reg Name         offset                 R/W      Width       Description
// DECBASE0         0x000                   RW       28         Aperture 0 base address without 12 lsbs
// DECBASE1         0x004                   RW       28         Aperture 1 base address without 12 lsbs
// ......
// DECBASENUMAP-1   (NUMAP-1)*0x004         RW       28         Aperture NUMAP-1 base address without 12 lsbs
// DECSIZE0         0x080                   RW       28         Aperture 0 address mask without 12 lsbs
// DECSIZE1         0x084                   RW       28         Aperture 1 address mask without 12 lsbs
// ......
// DECSIZENUMAP-1   0x80+(NUMAP-1)*0x004    RW       28         Aperture NUMAP-1 address mask without 12 lsbs
// DECMST0          0x100                   RW       6          Aperture 0 AXI matrix output port index 0..31; if >= 32 then disable aperture
// DECMST1          0x104                   RW       6          Aperture 1 AXI matrix output port index 0..31; if >= 32 then disable aperture
// ......
// DECMSTNUMAP-1    0x100+(NUMAP-1)*0x004   RW       6          Aperture NUMAP-1 AXI matrix output port index 0..31; if >= 32 then disable aperture
// All registers support R/W, and accessing beyond the above valid address range will trigger ErrResponse. Id fields fixed to be zeros and base address
// decode will be handled out of this module. 


`include "npu_defines.v"
`include "npu_macros.svh"
`include "npu_axi_macros.svh"

module npu_axi_config
  import npu_types::*;
  #(
    parameter int CFGIDW = 4,
    parameter int NUMAP  = 4,
    parameter int NUMMST = 4,
    parameter [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] DECBASE_RST_VAL = {NUMAP{28'h0}},
    parameter [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] DECSIZE_RST_VAL = {NUMAP{28'h0}},
    parameter [NUMAP-1:0][5:0]                 DECMST_RST_VAL  = {NUMAP{6'h20}}
  )
  (
   // clock and reset
   input logic clk,
   input logic rst_a,
   // AXI slave interface
   `AXISLV(CFGIDW,32,1,1,1,1,1,axi_slv_),
   input logic [NUMAP-1:0]                       swit_ena,
   input logic [NPU_AXI_ADDR_W-1:24]             swit_base,
   // configuration interface
   output logic [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] decbase,     // 4KB base address per aperture
   output logic [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] decsize,     // 4KB mask to specify aperture size
   output logic [NUMAP-1:0][NUMMST-1:0]          decmst       // onehot index of the decoded master
  );

  // AXI MMIO slave interface state
  typedef enum logic [7:0] { 
    saxi_rst_e   = 8'b0000_0001,          // reset state
    saxi_cmd_e   = 8'b0000_0010,          // accept MMIO read command
    saxi_wdata_e = 8'b0000_0100,        // accept MMIO write data
    saxi_rdata_e = 8'b0000_1000,        // return MMIO read data
    saxi_bresp_e = 8'b0001_0000,        // return MMIO write OK response
    saxi_werr_e  = 8'b0010_0000,         // ignore remaining writes after error on MMIO
    saxi_berr_e  = 8'b0100_0000,         // return write error on MMIO
    saxi_rerr_e  = 8'b1000_0000          // ignore remaining reads after error on MMIO
  } saxi_state_t;

  // AXI slave state registers and wires
  logic         [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] decbase_r;
  logic         [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] decbase_nxt;
  logic         [NUMAP-1:0]                      decbase_en;
  logic         [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] decsize_r;
  logic         [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] decsize_nxt;
  logic         [NUMAP-1:0]                      decsize_en;
  logic         [NUMAP-1:0][5:0]                 decmst_r;
  logic         [NUMAP-1:0][5:0]                 decmst_nxt;
  logic         [NUMAP-1:0]                      decmst_en;

  logic                        saxi_state_en;        // AXI slave state register enable
  saxi_state_t                 saxi_state_r;         // AXI slave state register
  saxi_state_t                 saxi_state_nxt;       // AXI slave state next
  logic                        saxi_cnt_en;          // AXI slave burst count register enable
  npu_axi_len_t                saxi_cnt_r;           // AXI slave burst count register
  npu_axi_len_t                saxi_cnt_nxt;         // AXI slave burst count register next value
  logic                        saxi_addr_en;         // AXI slave address register enable
  logic         [11:2]         saxi_addr_r;          // AXI slave address register
  logic         [11:2]         saxi_addr_nxt;        // AXI slave address register next value
  logic                        saxi_id_en;           // AXI slave ID register enable
  logic         [CFGIDW-1:0]   saxi_id_r;            // AXI slave ID register
  logic         [CFGIDW-1:0]   saxi_id_nxt;          // AXI slave ID register next value
  logic                        saxi_user_en;         // AXI slave User register enable
  logic         [1-1:0]        saxi_user_r;          // AXI slave User register
  logic         [1-1:0]        saxi_user_nxt;        // AXI slave User register next value

  logic                        mmio_wen;
  logic                        addr_out_bound;       // Read or Write address out of valid bound of NUMAP



   // AXI MMIO interface 64b wide data
  assign axi_slv_buser = saxi_user_r;
  assign axi_slv_ruser = saxi_user_r;

  // output ID
  assign axi_slv_bid = saxi_id_r;
  assign axi_slv_rid = saxi_id_r;

  // address valid bound check
  assign addr_out_bound = (saxi_addr_r[6:2] >= NUMAP)|(saxi_addr_r[11:7] > 5'h2);

  for (genvar i = 0; i < NUMAP; i++)
  begin : dec_map_GEN
    assign decbase[i] = decbase_r[i];
    assign decsize[i] = decsize_r[i];
    assign decmst[i]  = unsigned'(1<<decmst_r[i]);
  end : dec_map_GEN

  // AXI slave state dependent outputs and next state
  always_comb
  begin : saxi_next_PROC
    // defaults
    saxi_state_en    = 1'b0;
    saxi_cnt_en      = 1'b0;
    saxi_addr_en     = 1'b0;
    saxi_id_en       = 1'b0;
    saxi_user_en     = 1'b0;
    saxi_state_nxt   = saxi_cmd_e;
    saxi_cnt_nxt     = saxi_cnt_r - 1'b1;
    saxi_addr_nxt    = saxi_addr_r + 10'd1;
    saxi_id_nxt      = saxi_id_r;
    saxi_user_nxt    = saxi_user_r;
    // default AXI outputs
    mmio_wen        = 1'b0;
    axi_slv_awready = 1'b0;
    axi_slv_wready  = 1'b0;
    axi_slv_bvalid  = 1'b0;
    axi_slv_bresp   = npu_axi_resp_okay_e;
    axi_slv_arready = 1'b0;
    axi_slv_rvalid  = 1'b0;
    axi_slv_rresp   = npu_axi_resp_okay_e;
    axi_slv_rlast   = saxi_cnt_r == '0;
    // state dependent outputs
    casez (saxi_state_r)
    saxi_rst_e: 
      begin
        saxi_state_en  = 1'b1;
        saxi_state_nxt = saxi_cmd_e;
      end

    saxi_cmd_e: 
      begin
        // accept read command
        if (axi_slv_arvalid) 
        begin
          axi_slv_arready = 1'b1;    
          saxi_state_en  = 1'b1;
          saxi_cnt_en    = 1'b1;
          saxi_cnt_nxt   = axi_slv_ar.len;
          saxi_addr_en   = 1'b1;
          saxi_addr_nxt  = axi_slv_ar.addr[11:2];
          saxi_id_en     = 1'b1;
          saxi_user_en   = 1'b1;
          saxi_id_nxt    = axi_slv_arid;
          saxi_user_nxt  = axi_slv_aruser;
          // new read command accepted
          if ((axi_slv_ar.size == 3'd2) && (axi_slv_ar.burst == npu_axi_burst_incr_e || axi_slv_ar.len == '0) && (axi_slv_ar.prot[0] == 1'b1)) //only 32b support, check privileged
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
        else if (axi_slv_awvalid) 
        begin
          axi_slv_awready = 1'b1;    
          saxi_state_en  = 1'b1;
          saxi_addr_en   = 1'b1;
          saxi_addr_nxt  = axi_slv_aw.addr[11:2];
          saxi_id_en     = 1'b1;
          saxi_user_en   = 1'b1;
          saxi_id_nxt    = axi_slv_awid;
          saxi_user_nxt  = axi_slv_awuser;
          // new read command accepted
          if ((axi_slv_aw.size == 3'd2) && (axi_slv_aw.burst == npu_axi_burst_incr_e || axi_slv_aw.len == '0) && (axi_slv_aw.prot[0] == 1'b1)) //only 32b support, check privileged
          begin
            // command is OK, start write data burst
            saxi_state_nxt  = saxi_wdata_e;
          end
          else
          begin
            // command is not OK, return errors
            saxi_state_nxt = saxi_werr_e;
          end
        end
      end

    saxi_rdata_e: 
      begin
        // return read data
        axi_slv_rvalid = 1'b1;
        if (axi_slv_rready)
        begin
          saxi_cnt_en    = 1'b1;
          saxi_addr_en   = 1'b1;
          if (saxi_cnt_r == '0) //read last
          begin
            saxi_state_en  = 1'b1;
            saxi_state_nxt = saxi_cmd_e;
            if(addr_out_bound)
            begin
              axi_slv_rresp  = npu_axi_resp_slverr_e;
            end
          end
          else if(addr_out_bound)
          begin
            saxi_state_en  = 1'b1;
            saxi_state_nxt = saxi_rerr_e;
            axi_slv_rresp  = npu_axi_resp_slverr_e;
          end
        end
      end

    saxi_rerr_e: 
      begin
        // return read ERR response
        axi_slv_rvalid = 1'b1;
        axi_slv_rresp  = npu_axi_resp_slverr_e;
        if (axi_slv_rready) 
        begin
          // done, accept next command
          saxi_cnt_en   = 1'b1;
          if (saxi_cnt_r == '0)
          begin
            saxi_state_en  = 1'b1;
            saxi_state_nxt = saxi_cmd_e;
          end
        end
      end        

    saxi_wdata_e:
      begin
          // accept write data
          axi_slv_wready = 1'b1;
          if (axi_slv_wvalid) 
          begin
            saxi_addr_en  = 1'b1;
            // new write data, update address
            if (axi_slv_wlast) 
            begin
              // done accepting write data
              saxi_state_en  = 1'b1;
              if(addr_out_bound)
              begin
                saxi_state_nxt = saxi_berr_e;
              end
              else 
              begin
                saxi_state_nxt = saxi_bresp_e;
                mmio_wen = 1'b1;
              end
            end
            else if(addr_out_bound)
            begin
              saxi_state_en = 1'b1;
              saxi_state_nxt = saxi_werr_e;
            end
            else
            begin
              mmio_wen = 1'b1;
            end
          end
      end // case: saxi_wdata_e

    saxi_bresp_e: 
      begin
        // return write OK response
        axi_slv_bvalid = 1'b1;
        if (axi_slv_bready) begin
          // done, accept next command
          saxi_state_en  = 1'b1;
          saxi_state_nxt = saxi_cmd_e;
        end
      end
 
    saxi_werr_e: 
      begin
        // terminate remainder of burst by accept write data
        axi_slv_wready = 1'b1;
        if (axi_slv_wlast && axi_slv_wvalid) begin
          saxi_state_en  = 1'b1;
          saxi_state_nxt = saxi_berr_e;
        end
      end

    saxi_berr_e: 
      begin
        // return write ERR response
        axi_slv_bvalid = 1'b1;
        axi_slv_bresp  = npu_axi_resp_slverr_e;
        if (axi_slv_bready) 
        begin
          // done, accept next command
          saxi_state_en  = 1'b1;
          saxi_state_nxt = saxi_cmd_e;
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
  //`VPOST_OFF
  always_ff @(posedge clk or posedge rst_a)
  begin : saxi_state_reg_PROC
    if (rst_a == 1'b1)
    begin
      // reset
      saxi_state_r   <= saxi_rst_e;
    end
    else
    begin
      if (saxi_state_en)
      begin
        saxi_state_r <= saxi_state_nxt;
      end
    end
  end : saxi_state_reg_PROC
  //`VPOST_ON

  always_ff @(posedge clk or posedge rst_a)
  begin : saxi_cnt_reg_PROC
    if (rst_a == 1'b1)
    begin
      // reset
      saxi_cnt_r     <= '0;
    end
    else
    begin
      if (saxi_cnt_en)
      begin
        saxi_cnt_r   <= saxi_cnt_nxt;
      end
    end
  end : saxi_cnt_reg_PROC

  always_ff @(posedge clk or posedge rst_a)
  begin : saxi_addr_reg_PROC
    if (rst_a == 1'b1)
    begin
      // reset
      saxi_addr_r    <= 10'h0;
    end
    else
    begin
      if (saxi_addr_en)
      begin
        saxi_addr_r  <= saxi_addr_nxt;
      end
    end
  end : saxi_addr_reg_PROC

  always_ff @(posedge clk or posedge rst_a)
  begin : saxi_id_reg_PROC
    if (rst_a == 1'b1)
    begin
      // reset
      saxi_id_r  <= '0;
    end
    else
    begin
      if (saxi_id_en)
      begin
        saxi_id_r    <= saxi_id_nxt;
      end
    end
  end : saxi_id_reg_PROC

  always_ff @(posedge clk or posedge rst_a)
  begin : saxi_user_reg_PROC
    if (rst_a == 1'b1)
    begin
      // reset
      saxi_user_r <= '0;
    end
    else
    begin
      if (saxi_user_en)
      begin
        saxi_user_r  <= saxi_user_nxt;
      end
    end
  end : saxi_user_reg_PROC

  logic [NUMAP-1:0]         decbase_match;
  logic [NUMAP-1:0]         decsize_match;
  logic [NUMAP-1:0]         decmst_match;
  always_comb
  begin : addr_match_PROC
    integer i;
    decbase_match = {NUMAP{1'b0}};
    decsize_match = {NUMAP{1'b0}};
    decmst_match  = {NUMAP{1'b0}};
  
    for (i = 0; i < NUMAP; i = i + 1)
    begin
      decbase_match[i] = (saxi_addr_r[11:7] == 5'h0 && saxi_addr_r[6:2] == i);
      decsize_match[i] = (saxi_addr_r[11:7] == 5'h1 && saxi_addr_r[6:2] == i);
      decmst_match[i]  = (saxi_addr_r[11:7] == 5'h2 && saxi_addr_r[6:2] == i);
    end
  end

  //
  // MMIO register values
  //
  // AXI MMIO read data
  always_comb
  begin : saxi_rd_PROC
  integer j;
    // default
    axi_slv_rdata = '0;
    for(j=0; j<NUMAP; j++) begin
            axi_slv_rdata  |=  ({32{decbase_match[j]}} & {{(32-NPU_AXI_ADDR_W+12){1'h0}},decbase_r[j]}) |
                           ({32{decsize_match[j]}} & {{(32-NPU_AXI_ADDR_W+12){1'h0}},decsize_r[j]}) |
                           ({32{decmst_match[j]}}  & {26'h0,decmst_r[j]}) ;
    end
  end


  always_comb
  begin : nxt_data_PROC
    for(int j=0; j<NUMAP; j++)
    begin
      decbase_en[j]  = ((mmio_wen&&decbase_match[j] == 1'b1) || (swit_ena[j] == 1));
      decbase_nxt[j] = swit_ena[j] ? {swit_base, decbase_r[j][23:12]} : axi_slv_wdata[0+:NPU_AXI_ADDR_W-12];
      decsize_en[j]  = mmio_wen&&decsize_match[j] == 1'b1;
      decsize_nxt[j] = axi_slv_wdata[0+:NPU_AXI_ADDR_W-12];
      decmst_en[j]   = mmio_wen&&decmst_match[j] == 1'b1;
      decmst_nxt[j]  = axi_slv_wdata[0+:6];
    end
  end : nxt_data_PROC


  always_ff @(posedge clk or posedge rst_a)
  begin : base_write_PROC
    if(rst_a)
    begin
      decbase_r <= DECBASE_RST_VAL;
    end
    else
    begin
      `FOR_ASSIGN_EN(0, NUMAP, decbase_en, decbase_r, decbase_nxt)
    end
  end

  always_ff @(posedge clk or posedge rst_a)
  begin : size_write_PROC
    if(rst_a)
    begin
      decsize_r <= DECSIZE_RST_VAL;
    end
    else
    begin
      `FOR_ASSIGN_EN(0, NUMAP, decsize_en, decsize_r, decsize_nxt)
    end
  end

  always_ff @(posedge clk or posedge rst_a)
  begin : mst_write_PROC
    if(rst_a)
    begin
      decmst_r <= DECMST_RST_VAL;
    end
    else
    begin
      `FOR_ASSIGN_EN(0, NUMAP, decmst_en, decmst_r, decmst_nxt)
    end
  end

endmodule : npu_axi_config
