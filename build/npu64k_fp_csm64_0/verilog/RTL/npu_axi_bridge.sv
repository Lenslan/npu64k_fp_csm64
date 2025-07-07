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

// AXI bridge module to convert AXI width
// bridge only supports incremental accesses
// bridge does not support arsize&awsize smaller than bus width
// narrowing configurations will serialize all transactions to a single ID


`include "npu_defines.v"
`include "npu_axi_macros.svh"

module npu_axi_bridge
  import npu_types::*;
  #(
    parameter int AXIIDW = 4,
    parameter int AXISDW = 128,
    parameter int AXIMDW = 512,
    parameter int AXISAWUW = 1,
    parameter int AXISWUW  = 1,
    parameter int AXISBUW  = 1,
    parameter int AXISARUW = 1,
    parameter int AXISRUW  = 1,
    parameter int AXIMAWUW = 1,
    parameter int AXIMWUW  = 1,
    parameter int AXIMBUW  = 1,
    parameter int AXIMARUW = 1,
    parameter int AXIMRUW  = 1
  )
  (
   // clock and reset
   input logic clk,
   input logic rst_a,
// spyglass disable_block W240
// SMD: Declared but not used 
// SJ: Reviewed

   // AXI slave interface
   `AXISLV(AXIIDW,AXISDW,AXISAWUW,AXISWUW,AXISBUW,AXISARUW,AXISRUW,axi_slv_),
   // AXI master interface
   `AXIMST(AXIIDW,AXIMDW,AXIMAWUW,AXIMWUW,AXIMBUW,AXIMARUW,AXIMRUW,axi_mst_)
   );
// spyglass enable_block W240
  //
  // log2 of datawidth in bytes
  localparam int AXISDWL2 = $clog2(AXISDW/8);
  localparam int AXIMDWL2 = $clog2(AXIMDW/8);
  localparam int MAX_BURST_LEN = 16;
  localparam int AXILENREQDBITS = $clog2(MAX_BURST_LEN);
  localparam int DS_RATIO      = 1<<(AXISDWL2-AXIMDWL2);
  localparam int RDATA_NUM     = 16;
  localparam int SPL_OST       = 4;
  localparam int MAXID         = 1<<AXIIDW;


// generate different code depending on interface parameters
if (AXISDW == AXIMDW)
begin : eq_GEN
  assign axi_mst_awvalid = axi_slv_awvalid;
  assign axi_slv_awready = axi_mst_awready;
  assign axi_mst_awid    = axi_slv_awid;
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :user is not used in this case
  assign axi_mst_awuser  = axi_slv_awuser;
// spyglass enable_block W164a
  always_comb
  begin : aw_PROC
    axi_mst_aw                    = axi_slv_aw;
    //axi_mst_aw.addr[AXISDWL2-1:0] = '0;
    //axi_mst_aw.size               = unsigned'(AXISDWL2);
    //axi_mst_aw.burst              = npu_axi_burst_incr_e;
  end : aw_PROC
  assign axi_mst_wvalid  = axi_slv_wvalid;
  assign axi_slv_wready  = axi_mst_wready;
  assign axi_mst_wdata   = axi_slv_wdata;
  assign axi_mst_wstrb   = axi_slv_wstrb;
  assign axi_mst_wuser   = axi_slv_wuser;
  assign axi_mst_wlast   = axi_slv_wlast;
  assign axi_slv_bvalid  = axi_mst_bvalid;
  assign axi_mst_bready  = axi_slv_bready;
  assign axi_slv_bid     = axi_mst_bid;
  assign axi_slv_buser   = axi_mst_buser;
  assign axi_slv_bresp   = axi_mst_bresp;
  assign axi_mst_arvalid = axi_slv_arvalid;
  assign axi_slv_arready = axi_mst_arready;
  assign axi_mst_arid    = axi_slv_arid;
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :user is not used in this case
  assign axi_mst_aruser  = axi_slv_aruser;
// spyglass enable_block W164a
  always_comb
  begin : ar_PROC
    axi_mst_ar                    = axi_slv_ar;
    //axi_mst_ar.addr[AXISDWL2-1:0] = '0;
    //axi_mst_ar.size               = unsigned'(AXISDWL2);
    //axi_mst_ar.burst              = npu_axi_burst_incr_e;
  end : ar_PROC
  assign axi_slv_rvalid  = axi_mst_rvalid;
  assign axi_mst_rready  = axi_slv_rready;
  assign axi_slv_rid     = axi_mst_rid;
  assign axi_slv_rdata   = axi_mst_rdata;
  assign axi_slv_rresp   = axi_mst_rresp;
  assign axi_slv_ruser   = axi_mst_ruser;
  assign axi_slv_rlast   = axi_mst_rlast;
end : eq_GEN

// generate different code depending on interface parameters
if (AXISDW > AXIMDW)
begin : narrow_GEN
  // master interface is narrower than slave interface

  // output write command
  logic                       aw_valid_r;   // command is valid register
  logic                       aw_valid_nxt; // command is valid next
  logic  [AXIIDW-1:0]         aw_id_r;      // write command ID
  logic  [AXISAWUW-1:0]       aw_user_r;    // write command user field
  npu_axi_cmd_t               aw_aw_r;      // write command register
  npu_axi_cmd_t               aw_aw_nxt;    // next write command
  logic                       aw_last;      // if true then last sp command
  logic                       aw_fst_r;     // if true then first sp command
  logic                       aw_en;        // command enable
  logic                       aw_slv_en;    // slave command enable
  // write data transaction FIFO
  logic                       wfifo_wval;   // write FIFO input valid
  logic                       wfifo_wacc;   // write FIFO input accept
  logic                       wfifo_rval;   // write FIFO output valid
  logic                       wfifo_racc;   // write FIFO output accept
  logic [8+AXISDWL2:0]        wfifo_wr;     // write FIFO input data
  logic [8+AXISDWL2:0]        wfifo_rd;     // write FIFO output data
  logic                       w_en;         // write data state enable
  logic          [3:0]        w_cnt_r;      // write data counter
  logic          [3:0]        w_cnt_nxt;    // write data counter next state
  logic                       wl;           // last partial write data
  // write response transaction FIFO
  logic                       bfifo_wval;   // write response FIFO input valid
  logic                       bfifo_wacc;   // write response FIFO input accept
  logic                       bfifo_rval;   // write response FIFO output valid
  logic                       bfifo_racc;   // write response FIFO output accept
  logic          [AXIIDW:0]   bfifo_wr;     // true if last in slave burst
  logic          [AXIIDW:0]   bfifo_rd;     // fifo output
  logic                       b_en;         // enble write response state
  npu_axi_resp_t              b_r;          // write response state
  npu_axi_resp_t              b_nxt;        // write response next state
  // output read command
  logic                       ar_valid_r;   // command is valid register
  logic                       ar_valid_nxt; // command is valid next
  logic  [AXIIDW-1:0]         ar_id_r;      // write command ID
  logic  [AXISAWUW-1:0]       ar_user_r;    // read command user field
  npu_axi_cmd_t               ar_ar_r;      // read command register
  npu_axi_cmd_t               ar_ar_nxt;    // next write command
  logic                       ar_last;      // if true then last command
  logic                       ar_fst_r;     // if true then first command
  logic                       ar_en;        // command enable
  logic                       ar_slv_en;    // slave command enable
  // read data transaction FIFO
  logic                       rfifo_wval;   // read FIFO input valid
  logic                       rfifo_wacc;   // read FIFO input accept
  logic                       rfifo_rval;   // read FIFO output valid
  logic                       rfifo_racc;   // read FIFO output accept
  logic [AXIIDW+4+AXISDWL2:0] rfifo_wr;     // read FIFO input data
  logic [AXIIDW+4+AXISDWL2:0] rfifo_rd;     // read FIFO output data
  logic                       rl;           // last partial read data
  logic                       r_en;         // read data state enable
  logic          [3:0]        r_cnt_r;      // read data counter
  logic          [3:0]        r_cnt_nxt;    // read data counter next state
  logic          [AXISDW-1:0] r_data_nxt;   // read data next state
  npu_axi_resp_t              r_resp_r;     // read response state
  npu_axi_resp_t              r_resp_nxt;   // read response next state


  
  ////////////////////////////////////////////////////////////////////////////
  //
  // Write datapath
  //
  ////////////////////////////////////////////////////////////////////////////

  logic [31:0]  w_pp_numbytes;       // number of bytes for pp burst
  logic [31:0]  w_ds_numbytes;       // number of bytes for sp burst 
  logic [3+AXISDWL2-AXIMDWL2:0] w_ds_addr_msk;  
  logic [3+AXISDWL2-AXIMDWL2:0] w_ds_addr_sub;  
  logic [AXILENREQDBITS+AXISDWL2-AXIMDWL2:0] w_ds_len_tot;
  logic [AXILENREQDBITS+AXISDWL2-AXIMDWL2:0] w_ds_len_tot_r;
  logic [2:0]   aw_sp_size;

  //
  // write command channel
  //

  // accept a new write command if idle
  // launch a new command on the master as long as the wfifo and bfifo have space
  // wfifo stores the burst length on master side
  // bfifo stores a bit indicating if slave burst is last in master burst  
  
  
  // simple assignments
  assign aw_sp_size      = (aw_aw_r.size<AXIMDWL2) ? aw_aw_r.size : AXIMDWL2;
  assign axi_mst_awvalid = aw_valid_r & wfifo_wacc & bfifo_wacc;
  assign wfifo_wval      = aw_valid_r & bfifo_wacc & axi_mst_awready;
  assign bfifo_wval      = aw_valid_r & wfifo_wacc & axi_mst_awready;
  assign wfifo_wr        = {((aw_aw_r.addr[AXISDWL2-1:0])&({AXISDWL2{1'b1}}<<aw_sp_size)), aw_fst_r, aw_last, aw_aw_r.size, axi_mst_aw.len};
  assign axi_mst_awid    = aw_id_r;
  if (AXISAWUW >= AXIMAWUW) begin
  assign axi_mst_awuser  = aw_user_r[AXIMAWUW-1:0];
  end
  else begin
  assign axi_mst_awuser  = {{(AXIMAWUW-AXISAWUW){1'b0}},aw_user_r};
  end
  assign axi_slv_awready = ~aw_valid_r;
  assign aw_valid_nxt    = (axi_slv_awvalid & axi_slv_awready) | (aw_valid_r & ~(axi_mst_awvalid & axi_mst_awready & aw_last));
  assign aw_en           = (axi_slv_awvalid & axi_slv_awready) | (axi_mst_awvalid & axi_mst_awready);
  assign aw_slv_en       = (axi_slv_awvalid & axi_slv_awready);

  assign w_pp_numbytes     = (axi_slv_aw.len+1) << axi_slv_aw.size;
  assign w_ds_addr_msk     = ~({(4+AXISDWL2-AXIMDWL2){1'b1}} << axi_slv_aw.size) & ({(4+AXISDWL2-AXIMDWL2){1'b1}} << AXIMDWL2);
  assign w_ds_addr_sub     = (axi_slv_aw.addr[3+AXISDWL2-AXIMDWL2:0] & w_ds_addr_msk);
  assign w_ds_numbytes     = w_pp_numbytes - w_ds_addr_sub;
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
  assign w_ds_len_tot      = w_ds_numbytes >> ((axi_slv_aw.size<AXIMDWL2) ? axi_slv_aw.size : AXIMDWL2);
// spyglass enable_block W164a

  // next command
  // outputs: axi_mst_aw, aw_last, aw_aw_nxt
  always_comb
  begin : aw_conv_PROC
    // burst length at output
    // drive output command
    axi_mst_aw       = aw_aw_r;
    axi_mst_aw.len   = (w_ds_len_tot_r > MAX_BURST_LEN) ? MAX_BURST_LEN-1 : w_ds_len_tot_r-1;
    axi_mst_aw.size  = (aw_aw_r.size<AXIMDWL2) ? aw_aw_r.size : AXIMDWL2;
    axi_mst_aw.burst = npu_axi_burst_incr_e;
    aw_last          = w_ds_len_tot_r <= MAX_BURST_LEN;
    // update state
    if (aw_valid_r)
    begin
      // update burst length and address
      aw_aw_nxt       = aw_aw_r;
      aw_aw_nxt.addr[NPU_AXI_ADDR_W-1:AXIMDWL2] += MAX_BURST_LEN;
      aw_aw_nxt.addr[AXIMDWL2-1:0] = aw_aw_r.addr[AXIMDWL2-1:0]&({AXIMDWL2{1'b1}}<<aw_sp_size);
    end
    else
    begin
      // capture full command
      aw_aw_nxt       = axi_slv_aw;
    end
  end : aw_conv_PROC
  
  // AW state registers
  // outputs: aw_valid_r, aw_id_r, aw_user_r, aw_aw_r
  always_ff @(posedge clk or posedge rst_a)
  begin : aw_reg_PROC
    if (rst_a == 1'b1)
    begin
      aw_valid_r <= 1'b0;
      aw_id_r    <= '0;
      aw_user_r  <= '0;
      aw_aw_r    <= npu_axi_cmd_t'(0);
    end
    else if (aw_en) 
    begin
        aw_valid_r <= aw_valid_nxt;
        aw_aw_r    <= aw_aw_nxt;
        if (aw_slv_en) 
        begin
            aw_id_r      <= axi_slv_awid;
            aw_user_r    <= axi_slv_awuser;
        end
    end
  end : aw_reg_PROC
 
  always_ff @(posedge clk or posedge rst_a)
  begin : ds_len_reg_PROC
    if (rst_a == 1'b1)
    begin 
      w_ds_len_tot_r <= '0;
      aw_fst_r       <= '0;
    end
    else if (aw_slv_en) 
    begin
      w_ds_len_tot_r <= w_ds_len_tot;
      aw_fst_r       <= '1;
    end
    else if(axi_mst_awvalid & axi_mst_awready) begin
      w_ds_len_tot_r <= w_ds_len_tot_r - MAX_BURST_LEN;
      aw_fst_r       <= '0;
    end
  end

  //
  // Write data channel
  //
  logic [127:0]  w_init_dec;
  logic [127:0]  w_msb_dec;
  logic [2:0]    w_pp_size;
  logic [2:0]    w_sp_size;
  logic [AXISDW/8-1:0] w_shift_r;
  logic [AXISDW/8-1:0] w_shift;
  logic [DS_RATIO-1:0] w_sel_oh;
  logic [7:0] w_pp_size_1hot_r;
  logic [7:0] w_pp_size_1hot;
  logic [7:0] w_sp_size_1hot_r;
  logic [7:0] w_sp_size_1hot;
  logic [127:0] w_shift_pop;
  logic [AXISDWL2-1:0] w_align_addr;
 

  // simple assignments
  assign axi_mst_wvalid = wfifo_rval & axi_slv_wvalid;
  assign axi_slv_wready = wfifo_rval & axi_mst_wready & wl; //end of pp_size in current beat 
  assign axi_mst_wuser  = axi_slv_wuser;  
  assign axi_mst_wlast  = w_cnt_r == wfifo_rd[3:0];  //end of len in current burst
  assign wfifo_racc     = axi_mst_wvalid & axi_mst_wready & axi_mst_wlast;
  assign w_en           = axi_mst_wvalid & axi_mst_wready;
  assign w_cnt_nxt      = wfifo_racc ? '0 : w_cnt_r + 1'b1;
  assign w_pp_size      = wfifo_rd[6:4];
  assign w_sp_size      = (w_pp_size>AXIMDWL2)? AXIMDWL2 : w_pp_size;
  assign w_align_addr   = wfifo_rd[AXISDWL2-1+9:9]&({AXISDWL2{1'b1}}<<w_sp_size); 

  always_comb
  begin: w_size1hot_PROC
    integer i; 
    w_sp_size_1hot_r = 8'b0; 
    w_pp_size_1hot_r = 8'b0; 
    for (i=0; i<=AXIMDWL2; i=i+1)
      if (i==w_sp_size) w_sp_size_1hot_r[i] = 1'b1;
    for (i=0; i<=AXISDWL2; i=i+1)
      if (i==w_pp_size) w_pp_size_1hot_r[i] = 1'b1;  // 
  end   
  
  always_comb 
  begin : w_sp_size_1hotw_PROC
     w_sp_size_1hot[7:0] = 8'b0;
     w_sp_size_1hot[AXIMDWL2:0] = w_sp_size_1hot_r[AXIMDWL2:0];
  end

  always_comb
  begin : w_pp_size_1hotw_PROC
     w_pp_size_1hot[7:0] = 8'b0;
     w_pp_size_1hot[AXISDWL2:0] = w_pp_size_1hot_r[AXISDWL2:0];
  end

  always_comb
  begin : w_init_dec_PROC
    w_init_dec = {{127{1'b0}}, 1'b1};
    w_msb_dec  = {{127{1'b0}}, 1'b1};
    casez (w_sp_size_1hot)
      8'b??????1?:  w_msb_dec = {{126{1'b0}}, {2{1'b1}}};
      8'b?????10?:  w_msb_dec = {{124{1'b0}}, {4{1'b1}}};
      8'b????100?:  w_msb_dec = {{120{1'b0}}, {8{1'b1}}};
      8'b???1000?:  w_msb_dec = {{112{1'b0}}, {16{1'b1}}};
      8'b??10000?:  w_msb_dec = {{96{1'b0}}, {32{1'b1}}};
      8'b?100000?:  w_msb_dec = {{64{1'b0}}, {64{1'b1}}};
      8'b1000000?:  w_msb_dec = {128{1'b1}};
      default: w_msb_dec = {{127{1'b0}}, 1'b1};      
    endcase
    w_init_dec = w_msb_dec << w_align_addr;  
  end : w_init_dec_PROC

  always_ff @(posedge clk or posedge rst_a)
  begin: w_shift_PROC
    if (rst_a == 1'b1) 
    begin
      w_shift_r <= {(AXISDW/8){1'b1}};
    end 
    else if (w_en && w_shift[AXISDW/8-1])
    begin
      w_shift_r <= w_msb_dec[AXISDW/8-1:0];
    end
    else if (w_en && wfifo_rd[8] && (w_cnt_r == '0))
    begin
      w_shift_r <= w_init_dec[AXISDW/8-1:0] << (1 << w_sp_size);
    end
    else if(w_en)
    begin
      w_shift_r <= w_shift_r << (1 << w_sp_size);
    end
  end

  assign w_shift = (wfifo_rd[8] && (w_cnt_r == '0)) ? w_init_dec[AXISDW/8-1:0] : w_shift_r;

// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self-determin expression
// SJ: Reviewed
  always_comb 
  begin : w_sel_oh_PROC
    integer i, x; 
    w_sel_oh = {DS_RATIO{1'b0}};
    for (i=0; i<DS_RATIO; i=i+1) begin
      for (x=0; x<AXIMDW/8; x=x+1) begin
        w_sel_oh[i] = w_sel_oh[i] | w_shift[(i*AXIMDW/8) + x];
      end
    end
  end : w_sel_oh_PROC

  always_comb 
  begin : wdata_mux_logic_PROC
    integer i, j;
    axi_mst_wdata = {AXIMDW{1'b0}};
    for (i = 0; i <= (DS_RATIO-1); i = i + 1) begin
      for (j = 0; j <= (AXIMDW-1); j = j + 1) begin
        axi_mst_wdata[j] = axi_mst_wdata[j] | axi_slv_wdata[AXIMDW*i +j]&w_sel_oh[i];     
      end
    end
  end : wdata_mux_logic_PROC

  always_comb 
  begin : wstrb_mux_logic_PROC
    integer i, j;
    axi_mst_wstrb = {(AXIMDW/8){1'b0}};
    for (i = 0; i <= (DS_RATIO-1); i = i + 1) begin
      for (j = 0; j <= (AXIMDW/8-1); j = j + 1) begin
        axi_mst_wstrb[j] = axi_mst_wstrb[j] | axi_slv_wstrb[(AXIMDW/8)*i +j]&w_sel_oh[i];
      end
    end
  end : wstrb_mux_logic_PROC
// spyglass enable_block SelfDeterminedExpr-ML

  if ((AXISDW/8)==128) 
  begin
    assign w_shift_pop = w_shift;
  end 
  else 
  begin
    assign w_shift_pop = { {(128-(AXISDW/8)){1'b0}}, w_shift[(AXISDW/8)-1:0]};
  end

  always_comb 
  begin : w_fifo_pop_PROC
    integer x;
    wl = 1'b0;
    casez (w_pp_size_1hot)
      8'b??????1?:  begin
        // DW=16 Pop When bits [1], [3], [5], etc high 
        for (x=1; x<128 ; x=x+2) begin
          wl = wl | w_shift_pop[x];
        end
      end
      8'b?????10?: begin
        // DW=32 Pop When bits [3], [7], [11], etc high 
        for (x=3; x<128 ; x=x+4) begin
          wl = wl | w_shift_pop[x];
        end
      end
      8'b????100?: begin
        // DW=64 Pop When bits [7], [15], etc high 
        for (x=7; x<128 ; x=x+8) begin
          wl = wl | w_shift_pop[x];
        end
      end
      8'b???1000?: begin
        // DW=128 Pop When bits [15], [31], etc high 
        for (x=15; x<128 ; x=x+16) begin
          wl = wl | w_shift_pop[x];
        end
      end
      8'b??10000?: begin
        // DW=256 Pop When bits [31], [63], etc high 
        for (x=31; x<128 ; x=x+32) begin
          wl = wl | w_shift_pop[x];
        end
      end
      8'b?100000?: begin
        // DW=512 Pop When bits [63], [127], etc high 
        for (x=63; x<128 ; x=x+64) begin
          wl = wl | w_shift_pop[x];
        end
      end
      8'b1000000?: begin
        // DW=1024 Pop When bits [127], etc high 
        wl = w_shift_pop[127];
      end
      default: begin
        // DW=8 Pop on every cycle i.e. if any bit high
        wl = |w_shift_pop;  
      end
    endcase
  end

  // write data FIFO
  //
  npu_fifo
    #(
      .SIZE   ( SPL_OST   ),
      .DWIDTH ( 9+AXISDWL2),
      .FRCVAL ( 1'b0 ),
      .FRCACC ( 1'b0 )
      ) 
  u_wfifo_inst
    (
     .clk          ( clk        ),
     .rst_a        ( rst_a      ),
     .valid_write  ( wfifo_wval ),
     .accept_write ( wfifo_wacc ),
     .data_write   ( wfifo_wr   ),
     .valid_read   ( wfifo_rval ),
     .accept_read  ( wfifo_racc ),
     .data_read    ( wfifo_rd   )
     );
  //
  
  // W state registers
  // outputs: w_cnt_r
  always_ff @(posedge clk or posedge rst_a)
  begin : w_reg_PROC
    if (rst_a == 1'b1)
    begin
      w_cnt_r    <= '0;
    end
    else if (w_en)
    begin
      w_cnt_r    <= w_cnt_nxt;
    end
  end : w_reg_PROC

  //
  // Write response channel
  //
  
  // simple assignments
  assign axi_slv_bvalid = bfifo_rval & bfifo_rd[0] & axi_mst_bvalid;
  assign axi_mst_bready = bfifo_rval & ((~bfifo_rd[0]) | axi_slv_bready);
  assign bfifo_racc     = axi_mst_bvalid & axi_mst_bready;
  assign bfifo_wr       = {aw_id_r,aw_last};
  assign b_en           = bfifo_racc;
  assign b_nxt          = bfifo_rd[0] ? npu_axi_resp_okay_e : npu_axi_resp_t'(b_r|axi_mst_bresp);
  assign axi_slv_bid    = bfifo_rd[1+:AXIIDW];
  assign axi_slv_buser  = axi_mst_buser;
  assign axi_slv_bresp  = npu_axi_resp_t'(b_r|axi_mst_bresp);
  
  // store write response
  // outputs: b_r
  always_ff @(posedge clk or posedge rst_a)
  begin : b_reg_PROC
    if (rst_a == 1'b1)
    begin
      b_r <= npu_axi_resp_okay_e;
    end
    else if (b_en)
    begin
      b_r <= b_nxt;
    end
  end : b_reg_PROC
  
  // write response FIFO
  //
  npu_fifo
    #(
      .SIZE   ( SPL_OST  ),
      .DWIDTH ( AXIIDW+1 ),
      .FRCVAL ( 1'b0     ),
      .FRCACC ( 1'b0     )
      ) 
  u_bfifo_inst
    (
     .clk          ( clk        ),
     .rst_a        ( rst_a      ),
     .valid_write  ( bfifo_wval ),
     .accept_write ( bfifo_wacc ),
     .data_write   ( bfifo_wr   ),
     .valid_read   ( bfifo_rval ),
     .accept_read  ( bfifo_racc ),
     .data_read    ( bfifo_rd   )
     );
  //


  
  ////////////////////////////////////////////////////////////////////////////
  //
  // Read datapath
  //
  ////////////////////////////////////////////////////////////////////////////

  //
  // read command channel
  //
  logic [31:0]  r_pp_numbytes;
  logic [31:0]  r_ds_numbytes;
  logic [3+AXISDWL2-AXIMDWL2:0] r_ds_addr_msk;
  logic [3+AXISDWL2-AXIMDWL2:0] r_ds_addr_sub;
  logic [AXILENREQDBITS+AXISDWL2-AXIMDWL2:0] r_ds_len_tot;
  logic [AXILENREQDBITS+AXISDWL2-AXIMDWL2:0] r_ds_len_tot_r;
  logic [2:0]   ar_sp_size;

  // accept a new read command if idle
  // launch a new command on the master as long as the rfifo has space
  // rfifo stores a bit indicating if slave burst is last in master burst  
  assign ar_sp_size        = (ar_ar_r.size<AXIMDWL2) ? ar_ar_r.size : AXIMDWL2;
  assign r_pp_numbytes     = (axi_slv_ar.len+1) << axi_slv_ar.size;
  assign r_ds_addr_msk     = ~({(4+AXISDWL2-AXIMDWL2){1'b1}} << axi_slv_ar.size) & ({(4+AXISDWL2-AXIMDWL2){1'b1}} << AXIMDWL2);
  assign r_ds_addr_sub     = (axi_slv_ar.addr[3+AXISDWL2-AXIMDWL2:0] & r_ds_addr_msk);
  assign r_ds_numbytes     = r_pp_numbytes - r_ds_addr_sub;
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
  assign r_ds_len_tot      = r_ds_numbytes >> ((axi_slv_ar.size<AXIMDWL2) ? axi_slv_ar.size : AXIMDWL2);
// spyglass enable_block W164a
 
  
  // simple assignments
  assign axi_mst_arvalid = ar_valid_r & rfifo_wacc;
  assign rfifo_wval      = axi_mst_arvalid & axi_mst_arready;
  assign rfifo_wr        = {((ar_ar_r.addr[AXISDWL2-1:0])&({AXISDWL2{1'b1}}<<ar_sp_size)), ar_fst_r, ar_ar_r.size, ar_id_r, ar_last};
  assign axi_mst_arid    = ar_id_r;
  if (AXISAWUW >= AXIMAWUW) begin
  assign axi_mst_aruser  = ar_user_r[AXIMAWUW-1:0];
  end
  else begin
  assign axi_mst_aruser  = {{(AXIMAWUW-AXISAWUW){1'b0}},ar_user_r};
  end
  assign axi_slv_arready = ~ar_valid_r;
  assign ar_valid_nxt    = (axi_slv_arvalid & axi_slv_arready) | (ar_valid_r & ~(axi_mst_arvalid & axi_mst_arready & ar_last));
  assign ar_en           = (axi_slv_arvalid & axi_slv_arready) | (axi_mst_arvalid & axi_mst_arready);
  assign ar_slv_en       = (axi_slv_arvalid & axi_slv_arready);
  
  // next command
  // outputs: axi_mst_ar, ar_last, ar_ar_nxt
  always_comb
  begin : ar_conv_PROC
    // drive output command
    axi_mst_ar       = ar_ar_r;
    axi_mst_ar.len   = (r_ds_len_tot_r > MAX_BURST_LEN) ? MAX_BURST_LEN-1 : r_ds_len_tot_r-1;
    axi_mst_ar.size  = (ar_ar_r.size<AXIMDWL2) ? ar_ar_r.size : AXIMDWL2;
    axi_mst_ar.burst = npu_axi_burst_incr_e;
    ar_last          = r_ds_len_tot_r <= MAX_BURST_LEN;
    // update state
    if (ar_valid_r)
    begin
      // update burst length and address
      ar_ar_nxt       = ar_ar_r;
      ar_ar_nxt.addr[NPU_AXI_ADDR_W-1:AXIMDWL2] += MAX_BURST_LEN;
      ar_ar_nxt.addr[AXIMDWL2-1:0] = ar_ar_r.addr[AXIMDWL2-1:0]&({AXIMDWL2{1'b1}}<<ar_sp_size);
    end
    else
    begin
      // capture full command
      ar_ar_nxt       = axi_slv_ar;
    end
  end : ar_conv_PROC
  
  // AR state registers
  // outputs: ar_valid_r, ar_id_r, ar_user_r, ar_ar_r
  always_ff @(posedge clk or posedge rst_a)
  begin : ar_reg_PROC
    if (rst_a == 1'b1)
    begin
      ar_valid_r <= 1'b0;
      ar_id_r    <= '0;
      ar_user_r  <= '0;
      ar_ar_r    <= npu_axi_cmd_t'(0);
    end
    else if (ar_en)
    begin
      ar_valid_r <= ar_valid_nxt;
      ar_ar_r    <= ar_ar_nxt;
      if (ar_slv_en)
      begin
        ar_id_r    <= axi_slv_arid;
        ar_user_r  <= axi_slv_aruser;
      end
    end
  end : ar_reg_PROC
 
  always_ff @(posedge clk or posedge rst_a)
  begin : r_ds_len_reg_PROC
    if (rst_a == 1'b1)
    begin 
      r_ds_len_tot_r <= '0;
      ar_fst_r       <= '0;
    end
    else if (ar_slv_en) 
    begin
        r_ds_len_tot_r <= r_ds_len_tot;
        ar_fst_r       <= 1'b1;
    end
    else if(axi_mst_arvalid & axi_mst_arready) begin
        r_ds_len_tot_r <= r_ds_len_tot_r - MAX_BURST_LEN;
        ar_fst_r       <= 1'b0;
    end
  end
 

  //
  // read data channel
  //
  logic [127:0]  r_init_dec;
  logic [127:0]  r_msb_dec;
  logic [2:0]    r_pp_size;
  logic [2:0]    r_sp_size;
  logic [AXISDW/8-1:0] r_shift_r;
  logic [AXISDW/8-1:0] r_shift;
  logic [7:0] r_pp_size_1hot_r;
  logic [7:0] r_pp_size_1hot;
  logic [7:0] r_sp_size_1hot_r;
  logic [7:0] r_sp_size_1hot;
  logic [127:0] r_shift_pop;
  logic [AXISDW-1:0] rdata_w;
  logic [AXISDWL2-1:0] r_align_addr;
  logic [AXISDW-1:0] slv_rdata_r;

  // read response FIFO
  //
  npu_fifo
    #(
      .SIZE   ( RDATA_NUM ),
      .DWIDTH ( 1+AXIIDW+3+1+AXISDWL2),
      .FRCVAL ( 1'b0     ),
      .FRCACC ( 1'b0     )
      ) 
  u_rfifo_inst
    (
     .clk          ( clk        ),
     .rst_a        ( rst_a      ),
     .valid_write  ( rfifo_wval ),
     .accept_write ( rfifo_wacc ),
     .data_write   ( rfifo_wr   ),
     .valid_read   ( rfifo_rval ),
     .accept_read  ( rfifo_racc ),
     .data_read    ( rfifo_rd   )
     );
  //

  // simple assignmnets
  assign axi_slv_rvalid = rfifo_rval & axi_mst_rvalid & rl;
  assign axi_mst_rready = rfifo_rval & (axi_slv_rready | (~rl));

  assign rfifo_racc     = axi_mst_rvalid & axi_mst_rready & axi_mst_rlast;
  assign axi_slv_ruser  = axi_mst_ruser;
  assign axi_slv_rresp  = npu_axi_resp_t'(r_resp_r|axi_mst_rresp);
  assign axi_slv_rid    = rfifo_rd[AXIIDW:1];
  assign axi_slv_rlast  = axi_mst_rlast & rfifo_rd[0];
  assign r_resp_nxt     = rl ? npu_axi_resp_okay_e : npu_axi_resp_t'(r_resp_r|axi_mst_rresp);
  assign r_en           = axi_mst_rvalid & axi_mst_rready;
  assign r_cnt_nxt      = axi_mst_rlast ? '0 : r_cnt_r + 1'b1; 
  assign r_pp_size      = rfifo_rd[AXIIDW+3:AXIIDW+1];
  assign r_sp_size      = (r_pp_size>AXIMDWL2)? AXIMDWL2 : r_pp_size;
  assign r_align_addr   = rfifo_rd[AXISDWL2-1+AXIIDW+5:AXIIDW+5]&({AXISDWL2{1'b1}}<<r_sp_size);
  
  always_comb
  begin: r_size1hot_PROC
    integer i; 
    r_sp_size_1hot_r = 8'b0; 
    r_pp_size_1hot_r = 8'b0; 
    for (i=0; i<=AXIMDWL2; i=i+1)
      if (i==r_sp_size) r_sp_size_1hot_r[i] = 1'b1;
    for (i=0; i<=AXISDWL2; i=i+1)
      if (i==r_pp_size) r_pp_size_1hot_r[i] = 1'b1;  // 
  end   
  
  always_comb 
  begin : r_sp_size_1hotw_PROC
     r_sp_size_1hot[7:0] = 8'b0;
     r_sp_size_1hot[AXIMDWL2:0] = r_sp_size_1hot_r[AXIMDWL2:0];
  end

  always_comb
  begin : r_pp_size_1hotw_PROC
     r_pp_size_1hot[7:0] = 8'b0;
     r_pp_size_1hot[AXISDWL2:0] = r_pp_size_1hot_r[AXISDWL2:0];
  end

  always_comb
  begin : r_init_dec_PROC
    r_init_dec = {{127{1'b0}}, 1'b1};
    r_msb_dec  = {{127{1'b0}}, 1'b1};
    casez (r_sp_size_1hot)
      8'b??????1?:  r_msb_dec = {{126{1'b0}}, {2{1'b1}}};
      8'b?????10?:  r_msb_dec = {{124{1'b0}}, {4{1'b1}}};
      8'b????100?:  r_msb_dec = {{120{1'b0}}, {8{1'b1}}};
      8'b???1000?:  r_msb_dec = {{112{1'b0}}, {16{1'b1}}};
      8'b??10000?:  r_msb_dec = {{96{1'b0}}, {32{1'b1}}};
      8'b?100000?:  r_msb_dec = {{64{1'b0}}, {64{1'b1}}};
      8'b1000000?:  r_msb_dec = {128{1'b1}};
      default: r_msb_dec = {{127{1'b0}}, 1'b1};      
    endcase
    r_init_dec = r_msb_dec << r_align_addr;  
  end : r_init_dec_PROC

  always_ff @(posedge clk or posedge rst_a)
  begin: r_shift_PROC
    if (rst_a == 1'b1) begin
      r_shift_r <= {(AXISDW/8){1'b1}};
    end else begin 
      if (r_en) begin
        if (r_shift[AXISDW/8-1]) begin
          r_shift_r <= r_msb_dec[AXISDW/8-1:0];
        end else if (rfifo_rd[AXIIDW+4]&& (r_cnt_r == '0)) begin
          r_shift_r <= r_init_dec[AXISDW/8-1:0] << (1 << r_sp_size);
        end else begin
          r_shift_r <= r_shift_r << (1 << r_sp_size);
        end
      end
    end
  end

  assign r_shift = (rfifo_rd[AXIIDW+4] && (r_cnt_r == '0)) ? r_init_dec[AXISDW/8-1:0] : r_shift_r;
  assign rdata_w        = {DS_RATIO{axi_mst_rdata}};
  
// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self-determin expression
// SJ: Reviewed
  for (genvar i = 0; i <AXISDW/8; i = i + AXIMDW/8) begin : pk_byte
    always @(posedge clk or posedge rst_a) begin: byte_PROC
      if (rst_a == 1'b1) 
      begin
        slv_rdata_r[(i*8)+:AXIMDW] <= {AXIMDW{1'b0}};
      end
      else if (rl && r_en) 
      begin
        slv_rdata_r[(i*8)+:AXIMDW] <= {AXIMDW{1'b0}};
      end
      else if (|r_shift[i+:AXIMDW/8])
      begin
        slv_rdata_r[(i*8)+:AXIMDW] <= rdata_w[(i*8)+:AXIMDW];
      end
    end : byte_PROC
  end : pk_byte


  for (genvar j = 0; j < AXISDW/8; j = j + AXIMDW/8) begin : axi_slv_rdata_pack
    always_comb
    begin : axi_slv_rdata_PROC
      axi_slv_rdata[(j*8)+:AXIMDW] = slv_rdata_r[(j*8)+:AXIMDW];
      if(rl)
      begin
        if(|r_shift[j+:AXIMDW/8])
          axi_slv_rdata[(j*8)+:AXIMDW] = rdata_w[(j*8)+:AXIMDW];
        else
          axi_slv_rdata[(j*8)+:AXIMDW] = slv_rdata_r[(j*8)+:AXIMDW];
      end
      else
      begin
        axi_slv_rdata[(j*8)+:AXIMDW] = '0;
      end
    end : axi_slv_rdata_PROC
  end : axi_slv_rdata_pack

// spyglass enable_block SelfDeterminedExpr-ML
     
  if (AXISDW/8==128)
  begin
    assign r_shift_pop = r_shift ;
  end 
  else 
  begin
    assign r_shift_pop = { {(128-(AXISDW/8)){1'b0}}, r_shift[(AXISDW/8)-1:0]};
  end

  always_comb 
  begin : r_fifo_pop_PROC
    integer x;
    rl = 1'b0;
    casez (r_pp_size_1hot)
      8'b??????1?: begin
        // DW=16 Pop When bits [1], [3], [5], etc high 
        for (x=1; x<128 ; x=x+2) begin
          rl = rl | r_shift_pop[x];
        end
      end
      8'b?????10?: begin
        // DW=32 Pop When bits [3], [7], [11], etc high 
        for (x=3; x<128 ; x=x+4) begin
          rl = rl | r_shift_pop[x];
        end
      end
      8'b????100?: begin
        // DW=64 Pop When bits [7], [15], etc high 
        for (x=7; x<128 ; x=x+8) begin
          rl = rl | r_shift_pop[x];
        end
      end
      8'b???1000?: begin
        // DW=128 Pop When bits [15], [31], etc high 
        for (x=15; x<128 ; x=x+16) begin
          rl = rl | r_shift_pop[x];
        end
      end
      8'b??10000?: begin
        // DW=256 Pop When bits [31], [63], etc high 
        for (x=31; x<128 ; x=x+32) begin
          rl = rl | r_shift_pop[x];
        end
      end
      8'b?100000?: begin
        // DW=512 Pop When bits [63], [127], etc high 
        for (x=63; x<128 ; x=x+64) begin
          rl = rl | r_shift_pop[x];
        end
      end
      8'b1000000?: begin
        // DW=1024 Pop When bits [127], etc high 
        rl = r_shift_pop[127];
      end
      default: begin
        // DW=8 Pop on every cycle i.e. if any bit high
        rl = |r_shift_pop;  
      end
    endcase
  end
 
 
  // R state registers
  // outputs: r_cnt_r, r_resp_r
  always_ff @(posedge clk or posedge rst_a)
  begin : r_reg_PROC
    if (rst_a == 1'b1)
    begin
      r_cnt_r    <= '0;
      r_resp_r   <= npu_axi_resp_okay_e;
    end
    else if (r_en)
    begin
      r_cnt_r    <= r_cnt_nxt;
      r_resp_r   <= r_resp_nxt;
    end
  end : r_reg_PROC

end : narrow_GEN

// generate different code depending on interface parameters
if (AXISDW < AXIMDW)
begin : wide_GEN
  // write data transaction FIFO
  logic                                wfifo_wval;   // write FIFO input valid
  logic                                wfifo_wacc;   // write FIFO input accept
  logic                                wfifo_rval;   // write FIFO output valid
  logic                                wfifo_racc;   // write FIFO output accept
  logic [AXIMDWL2+NPU_AXI_SIZE_W-1:0]  wfifo_wr;     // write FIFO input data
  logic [AXIMDWL2+NPU_AXI_SIZE_W-1:0]  wfifo_rd;     // write FIFO output data
  logic                                wstate_nxt;   // write data state next
  logic                                wvalid_nxt;   // valid write data available next
  logic                                walsb_en;     // address lsb enable
  logic [AXIMDWL2-1:0]                 walsb_nxt;    // write address lsbs
  logic [AXIMDW-1:0]                   wdata_nxt;    // write data next state
  logic [AXIMDW/8-1:0]                 wstrb_nxt;    // write strobe next state
  logic                                wlast_nxt;    // write last next state
  logic                                wstate_r;     // write data state
  logic                                wvalid_r;     // valid write data available
  logic [AXIMDWL2-1:0]                 walsb_r;      // write address lsbs
  logic                                wlast_r;      // write last state
  logic [AXISWUW-1:0]                  wuser_r;      // user attribute
  // read data transaction FIFO
  logic [MAXID-1:0]                               rfifo_wval;   // read FIFO input valid
  logic [MAXID-1:0]                               rfifo_wacc;   // read FIFO input accept
  logic [MAXID-1:0]                               rfifo_racc;   // read FIFO output accept
  logic [MAXID-1:0][AXIMDWL2+NPU_AXI_SIZE_W+3:0]  rfifo_wr;     // read FIFO input data
  logic [MAXID-1:0][AXIMDWL2+NPU_AXI_SIZE_W+3:0]  rfifo_rd;     // read FIFO output data
  logic                                           r_en;         // read state enable
  logic [MAXID-1:0][AXIMDWL2-1:0]                 ralsb_r;      // read address counter
  logic [MAXID-1:0][AXIMDWL2-1:0]                 ralsb_nxt;    // read address counter next
  logic [MAXID-1:0][3:0]                          rlen_r;       // read length counter
  logic [MAXID-1:0][3:0]                          rlen_nxt;     // read length counter next
  logic [MAXID-1:0][NPU_AXI_SIZE_W-1:0]           rsize_r;      // read burst size
  logic [MAXID-1:0][NPU_AXI_SIZE_W-1:0]           rsize_nxt;    // read burst size next
  logic                                           mux_rfifo_wval;   // MUXED read FIFO input valid
  logic                                           mux_rfifo_wacc;   // MUXED read FIFO input accept
  logic                                           mux_rfifo_racc;   // MUXED read FIFO output accept
  logic [AXIMDWL2+NPU_AXI_SIZE_W+3:0]             mux_rfifo_wr;     // MUXED read FIFO input data
  logic [AXIMDWL2+NPU_AXI_SIZE_W+3:0]             mux_rfifo_rd;     // MUXED read FIFO output data
  logic [AXIMDWL2-1:0]                            mux_ralsb_r;      // MUXED read address counter
  logic [AXIMDWL2-1:0]                            mux_ralsb_nxt;    // MUXED read address counter next
  logic [3:0]                                     mux_rlen_r;       // MUXED read length counter
  logic [3:0]                                     mux_rlen_nxt;     // MUXED read length counter next
  logic [NPU_AXI_SIZE_W-1:0]                      mux_rsize_r;      // MUXED read burst size
  logic [NPU_AXI_SIZE_W-1:0]                      mux_rsize_nxt;    // MUXED read burst size next

  
  ////////////////////////////////////////////////////////////////////////////
  //
  // Write datapath
  //
  ////////////////////////////////////////////////////////////////////////////


  //
  // write command channel
  //

  // simple assignments
  assign axi_mst_awvalid = axi_slv_awvalid & wfifo_wacc;
  assign wfifo_wval      = axi_slv_awvalid & axi_mst_awready;
  assign axi_slv_awready = axi_mst_awready & wfifo_wacc;
  assign wfifo_wr        = {axi_slv_aw.size, axi_slv_aw.addr[AXIMDWL2-1:0]};
  assign axi_mst_awid    = axi_slv_awid;
  assign axi_mst_awuser  = axi_slv_awuser;

  // next command on output
  // outputs: axi_mst_aw
  always_comb
  begin : aw_conv_PROC
    // drive output command
    axi_mst_aw                    = axi_slv_aw;
  end : aw_conv_PROC

  //
  // Write data channel
  //

  // FIFO storing lsbs of write address
  //
  npu_fifo
    #(
      .SIZE   ( SPL_OST           ),
      .DWIDTH ( AXIMDWL2+NPU_AXI_SIZE_W   ),
      .FRCVAL ( 1'b0              ),
      .FRCACC ( 1'b0              )
      ) 
  u_wfifo_inst
    (
     .clk          ( clk        ),
     .rst_a        ( rst_a      ),
     .valid_write  ( wfifo_wval ),
     .accept_write ( wfifo_wacc ),
        .data_write   ( wfifo_wr   ),
     .valid_read   ( wfifo_rval ),
     .accept_read  ( wfifo_racc ),
     .data_read    ( wfifo_rd   )
     );
  //

  // drive write data flow
  assign axi_mst_wvalid = axi_slv_wvalid & wstate_r;
  assign axi_mst_wdata  = wdata_nxt;
  assign axi_mst_wstrb  = wstrb_nxt;
  assign axi_mst_wlast  = axi_slv_wlast & wstate_r;
  assign axi_mst_wuser  = axi_slv_wuser;
  assign axi_slv_wready = axi_mst_wready & wstate_r;
  assign wfifo_racc     = axi_mst_wvalid & axi_slv_wready & axi_mst_wlast;
  always_comb
  begin : wdata_PROC
    // default outputs
    walsb_en       = '0;
    wstate_nxt     = wstate_r;
    wvalid_nxt     = '0;
    walsb_nxt      = walsb_r;
    wdata_nxt      = '0;
    wstrb_nxt      = '0;
    wlast_nxt      = '0;
    // update state if data transferred to output
    if ((wstate_r == 1'b0) && wfifo_rval)
    begin
      // invalidate state and clear strobes
      wstate_nxt = 1'b1;
    end
    else if ((wstate_r == 1'b1) && axi_mst_wvalid && axi_mst_wready && axi_mst_wlast) begin
      wstate_nxt = 1'b0;
    end
    // append write data
    if (wstate_r && axi_mst_wvalid && axi_mst_wready)
    begin
      walsb_nxt = walsb_r + ('d1<<wfifo_rd[AXIMDWL2+:NPU_AXI_SIZE_W]);
      walsb_en  = 1'b1;
    end
    else if (wstate_r == 1'b0)
    begin
      walsb_en  = wfifo_rval;
      walsb_nxt = wfifo_rd[AXIMDWL2-1:0];
    end
    // add data to buffer
// spyglass disable_block W164a W362 SelfDeterminedExpr-ML
// SMD: LHS width is less than RHS
// SJ: Reviewed
    for (int i = 0; i < AXIMDW/AXISDW; i++)
    begin
      if (walsb_r[AXIMDWL2-1:AXISDWL2] == unsigned'(i))
      begin
        wdata_nxt[i*AXISDW+:AXISDW]      = axi_slv_wdata;
        wstrb_nxt[i*AXISDW/8+:AXISDW/8]  = axi_slv_wstrb;
      end
    end
// spyglass enable_block W164a W362 SelfDeterminedExpr-ML
  end : wdata_PROC

  // write data state
  // outputs: wstate_r, walsb_r, wvalid_r, wlast_r
  always_ff @(posedge clk or posedge rst_a)
  begin : wstate_reg_PROC
    if (rst_a == 1'b1)
    begin
      wstate_r <= 1'b0;
      walsb_r  <= '0;
      wvalid_r <= 1'b0;
      wlast_r  <= 1'b0;
      wuser_r  <= '0;
    end
    else
    begin
      wstate_r <= wstate_nxt;
      if (walsb_en)
      begin
        walsb_r  <= walsb_nxt;
        wuser_r  <= axi_slv_wuser;
        wlast_r  <= wlast_nxt;
      end
      wvalid_r <= wvalid_nxt;
    end
  end : wstate_reg_PROC


  //
  // Write response channel
  //
  
  // simple assignments
  assign axi_slv_bvalid = axi_mst_bvalid;
  assign axi_mst_bready = axi_slv_bready;
  assign axi_slv_bid    = axi_mst_bid;
  assign axi_slv_buser  = axi_mst_buser;
  assign axi_slv_bresp  = axi_mst_bresp;


  
  ////////////////////////////////////////////////////////////////////////////
  //
  // Read datapath
  //
  ////////////////////////////////////////////////////////////////////////////

  always_comb
  begin : mux_rfifo_r_PROC
    rfifo_racc        = 0;
    rlen_nxt          = rlen_r;
    ralsb_nxt         = ralsb_r;
    rsize_nxt         = rsize_r;
    for (int i=0; i<MAXID; i=i+1)
    begin
      if (axi_slv_rid == unsigned'(i))
      begin
        rfifo_racc[i]   = mux_rfifo_racc;
        rlen_nxt[i]     = mux_rlen_nxt;
        ralsb_nxt[i]    = mux_ralsb_nxt;
        rsize_nxt[i]    = mux_rsize_nxt;
      end
    end
  end : mux_rfifo_r_PROC

  always_comb
  begin : mux_fifo_PROC
    mux_rfifo_wacc    = 0;
    mux_rfifo_rd      = 0;
    mux_rlen_r        = 0;
    mux_ralsb_r       = 0;
    mux_rsize_r       = 0;
    rfifo_wval        = 0;
    rfifo_wr          = 0;
    for (int i=0; i<MAXID; i=i+1)
    begin
      if (axi_slv_arid == unsigned'(i))
      begin
        mux_rfifo_wacc  = rfifo_wacc[i];
        rfifo_wval[i]   = mux_rfifo_wval;
        rfifo_wr[i]     = mux_rfifo_wr;
      end
      if (axi_slv_rid == unsigned'(i))
      begin
        mux_rfifo_rd    = rfifo_rd[i];
        mux_rlen_r      = rlen_r[i];
        mux_ralsb_r     = ralsb_r[i];
        mux_rsize_r     = rsize_r[i];
      end
    end
  end : mux_fifo_PROC

  //
  // read command channel
  //

  // simple assignments
  assign axi_mst_arvalid     = axi_slv_arvalid & mux_rfifo_wacc;
  assign mux_rfifo_wval      = axi_slv_arvalid & axi_mst_arready;
  assign axi_slv_arready     = axi_mst_arready & mux_rfifo_wacc;
  assign mux_rfifo_wr        = {axi_slv_ar.size, axi_slv_ar.len, axi_slv_ar.addr[AXIMDWL2-1:0]};
  assign axi_mst_arid        = axi_slv_arid;
  assign axi_mst_aruser      = axi_slv_aruser;

  // next command on output
  // outputs: axi_mst_ar
  always_comb
  begin : ar_conv_PROC
    logic [AXIMDWL2-AXISDWL2:0] end_lsb;
    // drive output command
    axi_mst_ar                    = axi_slv_ar;
  end : ar_conv_PROC

  //
  // read data channel
  //

// spyglass disable_block W287b
// SMD: Output port to an instance is not connected
// SJ: intend open
  // read response FIFO
  //
  for (genvar gs = 0; gs < MAXID; gs++)
  begin : gen_GEN
    npu_fifo
      #(
        .SIZE   ( SPL_OST    ),
        .DWIDTH ( NPU_AXI_SIZE_W+4+AXIMDWL2   ),
        .FRCVAL ( 1'b1                ),
        .FRCACC ( 1'b0                )
        ) 
    u_rfifo_inst
      (
       .clk          ( clk        ),
       .rst_a        ( rst_a      ),
       .valid_write  ( rfifo_wval[gs] ),
       .accept_write ( rfifo_wacc[gs] ),
       .data_write   ( rfifo_wr[gs]   ),
       .valid_read   (            ),
       .accept_read  ( rfifo_racc[gs] ),
       .data_read    ( rfifo_rd[gs]   )
       );
  end : gen_GEN
// spyglass enable_block W287b
  //

  // Read data flow
  assign axi_slv_rvalid     = axi_mst_rvalid;
  assign axi_slv_rid        = axi_mst_rid;
  assign axi_slv_ruser      = axi_mst_ruser;
  assign mux_rfifo_racc     = axi_slv_rvalid & axi_slv_rready & (mux_rlen_r == '1);
  assign r_en               = axi_slv_rvalid & axi_slv_rready;
  assign axi_slv_rresp      = axi_mst_rresp;
  // outputs: ralsb_nxt, rlen_nxt, axi_slv_rdata, axi_slv_rlast
  always_comb
  begin : rd_PROC
    // get lsbs of address
    if (mux_rlen_r != '1)
    begin
      mux_ralsb_nxt      = mux_ralsb_r;
      mux_rlen_nxt       = mux_rlen_r;
      mux_rsize_nxt      = mux_rsize_r;
    end
    else
    begin
      {mux_rsize_nxt,mux_rlen_nxt,mux_ralsb_nxt} = mux_rfifo_rd;
    end
    // select read data
    axi_slv_rdata = '0;
// spyglass disable_block W164a W362 SelfDeterminedExpr-ML
// SMD: LHS width is less than RHS
// SJ: Reviewed
    for (int i = 0; i < AXIMDW/AXISDW; i++)
    begin
      if (mux_ralsb_nxt[AXIMDWL2-1:AXISDWL2] == unsigned'(i))
      begin
        axi_slv_rdata = axi_mst_rdata[i*AXISDW+:AXISDW];
      end
    end
// spyglass enable_block W164a W362 SelfDeterminedExpr-ML
    // accept
    axi_mst_rready = axi_slv_rready;
    // read last and id
    axi_slv_rlast = axi_mst_rlast;
    // update address lsbs
    mux_ralsb_nxt = mux_ralsb_nxt + ('d1<<mux_rsize_nxt);
    mux_rlen_nxt  = mux_rlen_nxt - 'd1;
  end : rd_PROC

  // read data registers
  // outputs: ralsb_r, rlen_r, rsize_r
  always_ff @(posedge clk or posedge rst_a)
  begin : rstate_reg_PROC
    if (rst_a == 1'b1)
    begin
      ralsb_r <= '0;
      rlen_r  <= '1;
      rsize_r <= '0;
    end
    else if (r_en)
    begin
      ralsb_r <= ralsb_nxt;
      rlen_r  <= rlen_nxt;
      rsize_r <= rsize_nxt;
    end
  end : rstate_reg_PROC
                          
`ifdef ABV_ON
  //
  // Assertions
  //
  property prop_rlast;
  @(posedge clk) disable iff (rst_a == 1'b1) axi_slv_rvalid & axi_slv_rlast |-> axi_mst_rlast;
  endproperty : prop_rlast
  a_rlast: assert property (prop_rlast) else $fatal(1, "Error: unexpected slave rlast");
`endif


                          
end : wide_GEN


`ifdef ABV_ON
  //
  // Assertions
  //

`endif
  
endmodule 


