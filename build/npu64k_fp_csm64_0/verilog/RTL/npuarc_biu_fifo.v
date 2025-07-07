// Library ARCv2CC-3.2.999999999
// spyglass disable_block Ac_conv01
// SMD: 5 synchronizers converge on combinational gate occp_en
// SJ: These are independent control signals which are not cared
// spyglass disable_block Reset_sync02
// spyglass disable_block Reset_check07
// spyglass disable_block Ar_asyncdeassert01
// SMD: i_ahbl2ibp.u_ibp_cmd_fifo is asynchronously de-asserted relative to clock signal
// SJ: // In AHB-lite Spec, it said:
    // The reset signal, HRESETn, is the only active LOW signal in the AHB-Lite
    // protocol and is the primary reset for all bus elements.
    // The reset can be asserted asynchronously, but is deasserted
    // synchronously after the rising edge of HCLK.
    // During reset all slaves must ensure that HREADYOUT is HIGH.
    // So for AHB slave module, it must use the rst_a and make sure the hreadyout
    // to be high.
// spyglass disable_block Ar_unsync01
// SMD: reset is unsynchronized
// SJ: The rst_a is synced by biu_reset_ctrl module
//      only the biu_ahb2ibp module used the real async reset because of AHB-lite protocol require all the AHB bus interface component must directly use HRESET
// spyglass disable_block Ac_unsync01
// spyglass disable_block Ac_unsync02
// SMD: Unsynchronized Crossing
// SJ: The BIU_FIFO module was used only internally or at the integer clock ratio boundry, it is not async path

//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2014 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2012, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//      ######     #    ######   ####
//      #          #    #       #    #
//      #####      #    #####   #    #
//      #          #    #       #    #
//      #          #    #       #    #
//      #          #    #        ####
//
// ===========================================================================
//
// Description:
//  Verilog module for general FIFO
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_biu_defines.v"

// Set simulation timescale
//
`include "const.def"


module npuarc_biu_fifo # (
  // The fifo depth can be 0,1,2,3,... any value
  // When it is 0, then it is actually a pass through comb logic, the clock ratio signals do not apply to this case
  // When it is 1, then it is actually a single stage
  // When it is > 1, then it is actually a really fifo
  // When it is 0, the clock ratio can't be configured on (NOTE)
  parameter FIFO_DEPTH = 8,
  parameter FIFO_WIDTH = 32,

  // The timing can be cut by not allowing in and out same cycle
  // When it is 0, then only allowing new data get in when there is at least 1 empty entry
  // When it is 1, then even allowing new data get in when fifo is full but there is 1 empty leaving
  // When it is 1, the clock ratio can't be configured on (NOTE)
  parameter IN_OUT_MWHILE = 1,

  // Support clock ratios. If this is configure on,
     // if the FIFO entries is 0, qualify the input signals only
     // if the FIFO entries larger than 0 and IN_OUT_MWHILE must be 0
  parameter O_SUPPORT_RTIO = 0,
  parameter I_SUPPORT_RTIO = 0
) (
    // leda NTL_CON13C off
    // LMD: non driving port
    // LJ: No care about this
  // Standard handshake interface
  input                   i_valid,
  output                  i_ready,
  input  [FIFO_WIDTH-1:0] i_data,
  output                  o_valid,
  input                   o_ready,
  output [FIFO_WIDTH-1:0] o_data,

  // The fifo occupation vector indicate the occupation status
  // e.g., if fifo is empty, then it is 'b0000...0000
  // e.g., if 1 entry occuped, then it is 'b0000...0001
  // e.g., if 3 entry occuped, then it is 'b0000...0111
  // e.g., if fifo is full, then it is 'b1111...0111
  // Just declared 1 more bit wider in case of FIFO_DEPTH is 0, the MSB bit is always 1'b0
  // spyglass disable_block W287b
  // SMD: Instance output port is not connected
  // SJ: No care about the warning
  output [FIFO_DEPTH:0]   i_occp,
  output [FIFO_DEPTH:0]   o_occp,
  // spyglass enable_block W287b

  // The clock ratio can be supported
  // clock ratio requires:
  //    * The input control signal to be qualifed with x_clk_en, payload signals no needed
  //    * The output signal must only toggle after the x_clk_en, payload signals also needed
  // If clock ratio is not supported (I_SUPPORT_RTIO or O_SUPPORT_RTIO == 0), the i_clk_en or o_clk_en must be tied to 1
  // spyglass disable_block W240
  // SMD: declared but not read
  // SJ: do not care this wrn
  input                   i_clk_en,
  input                   o_clk_en,

  input                   clk,
  input                   nmi_restart_r, // NMI reset signal
  input                   rst_a
  // spyglass enable_block W240
    // leda NTL_CON13C on
);



`ifdef VERILATOR  // {
if(FIFO_DEPTH == 0) begin: fifo_dep_eq_1//{ pass through
    if((I_SUPPORT_RTIO == 0) && (O_SUPPORT_RTIO == 0)) begin:no_support_rtio //{
        assign o_valid = i_valid & (~nmi_restart_r);
        assign i_ready = o_ready;
        assign o_data  = i_data;
        assign i_occp = 1'b0;
        assign o_occp = 1'b0;
    end
    else begin:support_rtio  //}{// The transparent FIFO (0-depth) with the clock ratio supported
        assign i_occp = 1'b0;
        assign o_occp = 1'b0;
        reg [1:0]  r_ptr_r;
        reg [1:0]  w_ptr_r;
        reg [FIFO_WIDTH-1:0] fifo_r [1:0];
        wire[FIFO_WIDTH-1:0] fifo_o_data =  fifo_r[r_ptr_r[0]];
        wire[FIFO_WIDTH-1:0] fifo_i_data =  i_data;

        wire fifo_i_valid = i_valid & i_clk_en & (~byp_fifo);
        wire fifo_o_ready = o_ready & o_clk_en;

        wire wr_ena = fifo_i_valid & fifo_i_ready ;
        wire rd_ena = fifo_o_valid & fifo_o_ready ;
        always @(posedge clk or posedge rst_a) begin
           if (rst_a == 1'b1) begin
               fifo_r[0] <= {FIFO_WIDTH{1'b0}};
               fifo_r[1] <= {FIFO_WIDTH{1'b0}};
               w_ptr_r <= 2'b0;
               r_ptr_r <= 2'b0;
           end
           else if (nmi_restart_r == 1'b1) begin
               if (i_clk_en) begin
                 w_ptr_r <= 2'b0;
               end
               if (i_clk_en) begin               
                 r_ptr_r <= 2'b0;
               end
           end           
           else begin
               if (wr_ena == 1'b1) begin
                   fifo_r[w_ptr_r[0]] <= fifo_i_data;
                   w_ptr_r <=  w_ptr_r + 2'b1;
               end
               if (rd_ena == 1'b1) begin
                   r_ptr_r <=  r_ptr_r + 2'b1;
               end
           end
        end

        wire fifo_empty = (r_ptr_r[1] == w_ptr_r[1]) & (r_ptr_r[0] == w_ptr_r[0]);
        wire fifo_full  = (r_ptr_r[1] != w_ptr_r[1]) & (r_ptr_r[0] == w_ptr_r[0]);

        wire fifo_i_ready = ~fifo_full;
        wire fifo_o_valid = ~fifo_empty;

        wire byp_fifo = (~fifo_o_valid) & i_valid & i_clk_en & o_ready & o_clk_en ;

        assign o_valid = (fifo_o_valid | (i_valid & i_clk_en)) & (~nmi_restart_r);
        assign i_ready = fifo_i_ready;

        assign o_data = fifo_o_valid ? fifo_o_data : (i_data & {FIFO_WIDTH{i_valid & i_clk_en}});
    end  // }
end  // }
else begin: fifo_dep_gt_1//{

    localparam FIFO_IDX_WIDTH =
        FIFO_DEPTH <=   2 ? 1 :
        FIFO_DEPTH <=   4 ? 2 :
        FIFO_DEPTH <=   8 ? 3 :
        FIFO_DEPTH <=  16 ? 4 :
        FIFO_DEPTH <=  32 ? 5 :
        FIFO_DEPTH <=  64 ? 6 :
        FIFO_DEPTH <= 128 ? 7 :
        FIFO_DEPTH <= 256 ? 8 :
        FIFO_DEPTH <= 512 ? 9 : 10;

    // Define Effective fifo read/write enable signal
    wire wen = i_valid & i_clk_en & i_ready;
    wire ren = o_valid & o_clk_en & o_ready;

    // Define FIFO registers file
    reg  [FIFO_WIDTH-1:0] rf_r [FIFO_DEPTH-1:0];

    // Both VTOC and Verilator like array indexing once rather than using
    // a pre-decoded one-hot bit vector to drive an AND-OR tree for read
    // selection and to drive the correct write enable for write selection
    //
    // Those are fine techniques to specify high clock rate hardware,
    // but they don't model well when the primitives are not logic gates
    // but X86 instructions.
    reg  [FIFO_IDX_WIDTH-1:0] rptr_idx_r;
    reg  [FIFO_IDX_WIDTH-1:0] wptr_idx_r;
    wire [FIFO_IDX_WIDTH-1:0] idx_inc = 1;

    always @(posedge clk or posedge rst_a) begin
        if (rst_a == 1'b1) begin
            rptr_idx_r <= {FIFO_IDX_WIDTH{1'b0}};
            wptr_idx_r <= {FIFO_IDX_WIDTH{1'b0}};
        end
        else if (nmi_restart_r == 1'b1) begin
            if (o_clk_en) begin
              rptr_idx_r <= {FIFO_IDX_WIDTH{1'b0}};
            end
            if (i_clk_en) begin            
              wptr_idx_r <= {FIFO_IDX_WIDTH{1'b0}};
            end
        end        
        else begin
            if (ren == 1'b1) begin
                if (FIFO_DEPTH > 1) begin
                    rptr_idx_r <= (rptr_idx_r == (FIFO_DEPTH - 1))
                        ? {FIFO_IDX_WIDTH{1'b0}}
                        : rptr_idx_r + idx_inc;
                end
            end
            if (wen == 1'b1) begin
                if (FIFO_DEPTH > 1) begin
                    wptr_idx_r <= (wptr_idx_r == (FIFO_DEPTH - 1))
                        ? {FIFO_IDX_WIDTH{1'b0}}
                        : wptr_idx_r + idx_inc;
                end
                rf_r[wptr_idx_r] <= i_data;
            end
        end
    end
    wire [FIFO_WIDTH-1:0] r_data = rf_r[rptr_idx_r];
    assign o_data = (o_valid_r == 1'b1) ? r_data : {FIFO_WIDTH{1'b0}};


    ////////////////
    ///////// occp generation
    wire [FIFO_DEPTH:0] occp_nxt;
    reg  [FIFO_DEPTH:0] occp_r;
    reg  [FIFO_DEPTH:0] occp_cpy_r;
    wire occp_en = (ren | wen );
    assign occp_nxt =
           ((~ren) & ( wen)) ? {occp_r[FIFO_DEPTH-1:0], 1'b1} :
           (( ren) & (~wen)) ? (occp_r >> 1) :
                                occp_r;

    // spyglass disable_block FlopEConst
    // SMD: Flip-flop enable pin is permanently disabled or enabled
    // SJ: No care about enable pin is a constant value
    always @(posedge clk or posedge rst_a) begin : occp_DFFEAR_PROC
        if (rst_a == 1'b1) begin
            occp_r     <= { {FIFO_DEPTH{1'b0}}, 1'b1};
            occp_cpy_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
        end
        else if (nmi_restart_r == 1'b1) begin
            occp_r     <= { {FIFO_DEPTH{1'b0}}, 1'b1};
            occp_cpy_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
        end        
        else if (occp_en == 1'b1) begin
            occp_r     <= occp_nxt;
            occp_cpy_r <= occp_nxt;
        end
    end
    // spyglass enable_block FlopEConst


    ////////////////
    ///////// input side
    if(I_SUPPORT_RTIO == 1) begin:i_support_rtio //{
        reg  occp_en_i_dly_r;
        wire occp_en_i_dly_set = occp_en & (~i_clk_en);
        wire occp_en_i_dly_clr = i_clk_en & occp_en_i_dly_r;
        wire occp_en_i_dly_ena = occp_en_i_dly_set | occp_en_i_dly_clr;
        wire occp_en_i_dly_nxt = occp_en_i_dly_set | (~occp_en_i_dly_clr);
        always @(posedge clk or posedge rst_a) begin : occp_dly_DFFEAR_PROC
            if (rst_a == 1'b1)
                occp_en_i_dly_r <= 1'b1;
            if (nmi_restart_r == 1'b1)
                occp_en_i_dly_r <= 1'b1;                
            else if (occp_en_i_dly_ena == 1'b1)
                occp_en_i_dly_r <= occp_en_i_dly_nxt;
        end
        wire [FIFO_DEPTH:0] occp_in = occp_en ? occp_nxt : occp_r;
        reg  [FIFO_DEPTH:0] i_occp_r;
        wire i_occp_ena = i_clk_en & (occp_en | occp_en_i_dly_r);
always @(posedge clk or posedge rst_a) begin : i_occp_DFFEAR_PROC
            if (rst_a == 1'b1)
                i_occp_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
            else if ((nmi_restart_r == 1'b1) && (i_clk_en == 1'b1))
                i_occp_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
            else if (i_occp_ena == 1'b1)
                i_occp_r <= occp_in;
end
        assign i_occp = {1'b0,i_occp_r[FIFO_DEPTH:1]};
    end//}
    else begin:i_not_support_rtio//{
        assign i_occp = {1'b0,occp_r[FIFO_DEPTH:1]};
    end//}

    wire [FIFO_DEPTH:0]   o_occp_cpy;
    ////////////////
    ///////// output side
    if(O_SUPPORT_RTIO == 1) begin:o_support_rtio //{
      reg occp_en_o_dly_r;
      wire occp_en_o_dly_set = occp_en & (~o_clk_en);
      wire occp_en_o_dly_clr = o_clk_en & occp_en_o_dly_r;
      wire occp_en_o_dly_ena = occp_en_o_dly_set | occp_en_o_dly_clr;
      wire occp_en_o_dly_nxt = occp_en_o_dly_set | (~occp_en_o_dly_clr);
always @(posedge clk or posedge rst_a)
begin : occp_dly_DFFEAR_PROC
  if (rst_a == 1'b1)
    occp_en_o_dly_r <= 1'b1;
  else if (nmi_restart_r == 1'b1)
    occp_en_o_dly_r <= 1'b1;
  else if (occp_en_o_dly_ena == 1'b1)
    occp_en_o_dly_r <= occp_en_o_dly_nxt;
end
      wire [FIFO_DEPTH:0] occp_in = occp_en ? occp_nxt : occp_r;
      reg  [FIFO_DEPTH:0] o_occp_r;
      reg  [FIFO_DEPTH:0] o_occp_cpy_r;
      wire o_occp_ena = o_clk_en & (occp_en | occp_en_o_dly_r);
      always @(posedge clk or posedge rst_a)
      begin : o_occp_DFFEAR_PROC
        if (rst_a == 1'b1) begin
          o_occp_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
          o_occp_cpy_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
        end
        else if ((nmi_restart_r == 1'b1) && (o_clk_en == 1'b1))  begin
          o_occp_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
          o_occp_cpy_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
        end
        else if (o_occp_ena == 1'b1) begin
          o_occp_r <= occp_in;
          o_occp_cpy_r <= occp_in;
        end
      end
      assign o_occp = {1'b0,o_occp_r[FIFO_DEPTH:1]};
      assign o_occp_cpy = {1'b0,o_occp_cpy_r[FIFO_DEPTH:1]};
    end//}
    else begin:o_not_support_rtio//{
      assign o_occp = {1'b0,occp_r[FIFO_DEPTH:1]};
    // spyglass disable_block FlopEConst
    // SMD: Flip-flop enable pin is permanently disabled or enabled
    // SJ: No care about enable pin is a constant value
      assign o_occp_cpy = {1'b0,occp_cpy_r[FIFO_DEPTH:1]};
    // spyglass enable_block FlopEConst
    end//}


    if(IN_OUT_MWHILE == 0) begin:in_out_mwhile//{
      // If the fifo is not full, then it can accept more
      assign i_ready = (~i_occp[FIFO_DEPTH-1]);
    end//}
    else begin:no_in_out_mwhile//{
      // If the fifo is not full, or it have one entry leaving then it can accept more
      // Must not the clock ratio supported
      assign i_ready = ((~i_occp[FIFO_DEPTH-1]) | ren);
    end//}

    // If the fifo is not empty,pthen it can output valid
    assign o_valid = o_occp[0];
    wire o_valid_r = o_occp_cpy[0];


  end  // }
`else  // } {


// spyglass disable_block W528
// SMD: Variable set but not read
// SJ: No care about the warning
//spyglass disable_block Clock_Reset_check02
// SMD: Potential race between flop
// SJ:  The flops its clock (by clock gate) conditionally
//      if not gated, its clock runs every other core clock
//      Therefore there is no racing condition
    reg [2:0] w_ptr_r_pty;
    reg [2:0] r_ptr_r_pty;
    reg  [FIFO_WIDTH-1:0] rf_r [FIFO_DEPTH-1:0];
    reg [FIFO_DEPTH-1:0] rptr_vec_r_pty;
    reg rptr_vec_r_pty_r;

    reg [FIFO_DEPTH-1:0] wptr_vec_r;

    reg [FIFO_DEPTH-1:0] wptr_vec_r_pty;
    reg wptr_vec_r_pty_r;

    reg [FIFO_DEPTH:0] occp_r;
    reg [FIFO_DEPTH:0] occp_cpy_r;
    reg [FIFO_DEPTH:0] o_occp_r;
    reg [FIFO_DEPTH:0] o_occp_cpy_r;

    reg [FIFO_DEPTH+1:0] occp_r_pty;
    reg [FIFO_DEPTH+1:0] occp_cpy_r_pty;

      reg occp_en_i_dly_r;
      reg occp_en_o_dly_r;

    reg [1:0] occp_en_i_dly_r_pty;

    reg [FIFO_DEPTH+1:0] i_occp_r_pty;
    reg [FIFO_DEPTH+1:0] i_occp_r_ideal_pty;
    reg [1:0] occp_en_o_dly_r_pty;

    reg [FIFO_DEPTH+1:0] o_occp_r_pty;
    reg [FIFO_DEPTH+1:0] o_occp_cpy_r_pty;

    reg [FIFO_DEPTH+1:0] o_occp_r_ideal_pty;
    reg [FIFO_DEPTH+1:0] o_occp_cpy_r_ideal_pty;

    reg [FIFO_WIDTH-1:0] r_data;
     reg [1:0]  r_ptr_r;
     reg [1:0]  w_ptr_r;
     reg  [FIFO_WIDTH-1:0] fifo_r [1:0];
    reg [FIFO_DEPTH-1:0] rptr_vec_r;
      reg [FIFO_DEPTH:0] i_occp_r;
      reg [FIFO_DEPTH:0] i_occp_r_ideal;

genvar i;
generate //{

  if(FIFO_DEPTH == 0) begin: fifo_dep_eq_1//{ pass through



   if((I_SUPPORT_RTIO == 0) && (O_SUPPORT_RTIO == 0)) begin:no_support_rtio //{
     assign o_valid = i_valid & (~nmi_restart_r);
     assign i_ready = o_ready;
     assign o_data  = i_data;
     assign i_occp = 1'b0;
     assign o_occp = 1'b0;
   end
   else begin:support_rtio//}{// The transparent FIFO (0-depth) with the clock ratio supported
     assign i_occp = 1'b0;
     assign o_occp = 1'b0;

     // Two entriy FIFOs
     wire fifo_o_valid;
     wire fifo_i_valid;
     wire fifo_i_ready;
     wire fifo_o_ready;
     //reg  [FIFO_WIDTH-1:0] fifo_r [1:0];
     wire[FIFO_WIDTH-1:0] fifo_o_data =  fifo_r[r_ptr_r[0]];
     wire[FIFO_WIDTH-1:0] fifo_i_data =  i_data;


     wire  wr_ena = fifo_i_valid & fifo_i_ready ;
     wire  rd_ena = fifo_o_valid & fifo_o_ready ;

// spyglass disable_block FlopEConst
// SMD: tie to constant
// SJ: No care about the warning
    always @(posedge clk or posedge rst_a)
       begin : data_0_byp_PROC
           if (rst_a == 1'b1) begin
               fifo_r[0] <= {FIFO_WIDTH{1'b0}};
           end
           else if ((wr_ena & (~w_ptr_r[0])) == 1'b1) begin
               fifo_r[0] <= fifo_i_data;
           end
       end

    always @(posedge clk or posedge rst_a)
       begin : data_1_byp_PROC
           if (rst_a == 1'b1) begin
               fifo_r[1] <= {FIFO_WIDTH{1'b0}};
           end
           else if ((wr_ena & w_ptr_r[0]) == 1'b1) begin
               fifo_r[1] <= fifo_i_data;
           end
       end
// spyglass enable_block FlopEConst

    // leda B_3208 off
    // leda B_3208_A off
    // leda B_3200 off
    // LMD: Unequal length  operand in conditional expression
    // LJ: to work around VTOC issue, no risk about the this unequal
    always @(posedge clk or posedge rst_a)
       begin : w_ptr_byp_PROC
           if (rst_a == 1'b1) begin
               w_ptr_r <= 2'b0;
           end
           else if ((nmi_restart_r == 1'b1) & i_clk_en) begin
               w_ptr_r <= 2'b0;
           end           
           else if (wr_ena == 1'b1) begin
               w_ptr_r <=  w_ptr_r + 1'b1;
           end
       end


    always @(posedge clk or posedge rst_a)
       begin : r_ptr_byp_PROC
           if (rst_a == 1'b1) begin
               r_ptr_r <= 2'b0;
           end
           else if ((nmi_restart_r == 1'b1) & o_clk_en) begin
               r_ptr_r <= 2'b0;
           end           
           else if (rd_ena == 1'b1) begin
               r_ptr_r <=  r_ptr_r + 1'b1;
           end
       end
    // leda B_3208 on
    // leda B_3208_A on
    // leda B_3200 on



     assign fifo_o_valid = ~((r_ptr_r[1] == w_ptr_r[1]) & (r_ptr_r[0] == w_ptr_r[0]));
     assign fifo_i_ready = ~((r_ptr_r[1] != w_ptr_r[1]) & (r_ptr_r[0] == w_ptr_r[0]));
     //

     wire byp_fifo = (~fifo_o_valid) & i_valid & i_clk_en & o_ready & o_clk_en ;

     assign fifo_i_valid = i_valid & i_clk_en & (~byp_fifo);
     assign fifo_o_ready = o_ready & o_clk_en;

     assign o_valid = (fifo_o_valid | (i_valid & i_clk_en)) & (~nmi_restart_r);

     assign i_ready   = fifo_i_ready;
     assign o_data = fifo_o_valid ? fifo_o_data : (i_data & {FIFO_WIDTH{i_valid & i_clk_en}});
   end //}

  end//}
  else begin: fifo_dep_gt_1//{

    //////////////////////////////////////////////////////////////////////////////
    //                                                                          //
    //            local wires and regs declaration                              //
    //                                                                          //
    //////////////////////////////////////////////////////////////////////////////
    //
    // Define FIFO registers file
    // leda NTL_CON32 off
    // LMD: Change on net has no effect
    // LJ: no care about this
    //reg  [FIFO_WIDTH-1:0] rf_r [FIFO_DEPTH-1:0];
    wire [FIFO_DEPTH-1:0] rf_en;
    // leda NTL_CON32 on
    // Define Effective fifo read/write enable signal
    wire wen = i_valid & i_clk_en & i_ready;
    wire ren = o_valid & o_clk_en & o_ready;

    ////////////////
    ///////// rptr_vec generation
    wire [FIFO_DEPTH-1:0] rptr_vec_nxt;
    //reg [FIFO_DEPTH-1:0] rptr_vec_r;
    wire rptr_vec_en = ren;
// leda B_3208 off
// leda B_3208_A off
// leda B_3200 off
// LMD: Unequal length  operand in conditional expression
// LJ: to work around VTOC issue, no risk about the this unequal
// spyglass disable_block FlopEConst
// SMD: Flip-flop enable pin is permanently disabled or enabled
// SJ: No care about enable pin is a constant value
    if(FIFO_DEPTH == 1) begin:rptr_fifo_depth_is_1
      assign rptr_vec_nxt = 1'b1;
    end
    else begin:rptr_fifo_depth_is_not_1
      assign rptr_vec_nxt =
           rptr_vec_r[FIFO_DEPTH-1] ? {{FIFO_DEPTH{1'b0}}, 1'b1} :
                                      (rptr_vec_r << 1);
    end
// spyglass enable_block FlopEConst
// leda B_3200 on
// leda B_3208_A on
// leda B_3208 on

// spyglass disable_block FlopEConst
// SMD: Flip-flop enable pin is permanently disabled or enabled
// SJ: No care about enable pin is a constant value

    always @(posedge clk or posedge rst_a)
    begin : rptr_vec_DFFEAR_PROC
      if (rst_a == 1'b1)
// leda B_3208 off
// leda B_3208_A off
// leda B_3200 off
// LMD: Unequal length  operand in conditional expression
// LJ: to work around VTOC issue, no risk about the this unequal
        rptr_vec_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
      else if ((nmi_restart_r == 1'b1) & o_clk_en)
        rptr_vec_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
// leda B_3200 on
// leda B_3208_A on
// leda B_3208 on
      else if (rptr_vec_en == 1'b1)
        rptr_vec_r <= rptr_vec_nxt;
    end
// spyglass enable_block FlopEConst

    ////////////////
    ///////// wptr_vec generation
    wire [FIFO_DEPTH-1:0] wptr_vec_nxt;
   // reg [FIFO_DEPTH-1:0] wptr_vec_r;
    wire wptr_vec_en = wen;
// leda B_3208 off
// leda B_3208_A off
// leda B_3200 off
// LMD: Unequal length  operand in conditional expression
// LJ: to work around VTOC issue, no risk about the this unequal
// spyglass disable_block FlopEConst
// SMD: Flip-flop enable pin is permanently disabled or enabled
// SJ: No care about enable pin is a constant value
    if(FIFO_DEPTH == 1) begin:wptr_fifo_depth_is_1
      assign wptr_vec_nxt = 1'b1;
    end
    else begin:wptr_fifo_depth_is_not_1
      assign wptr_vec_nxt =
           wptr_vec_r[FIFO_DEPTH-1] ? {{FIFO_DEPTH{1'b0}}, 1'b1} :
                                      (wptr_vec_r << 1);
    end
// spyglass enable_block FlopEConst
// leda B_3200 on
// leda B_3208_A on
// leda B_3208 on

    always @(posedge clk or posedge rst_a)
    begin : wptr_vec_DFFEAR_PROC
      if (rst_a == 1'b1)
// leda B_3208 off
// leda B_3208_A off
// leda B_3200 off
// LMD: Unequal length  operand in conditional expression
// LJ: to work around VTOC issue, no risk about the this unequal
        wptr_vec_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
      else if ((nmi_restart_r == 1'b1) & i_clk_en)
        wptr_vec_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
// leda B_3200 on
// leda B_3208_A on
// leda B_3208 on
      else if (wptr_vec_en == 1'b1)
// spyglass disable_block FlopEConst
// SMD: Flip-flop enable pin is permanently disabled or enabled
// SJ: No care about enable pin is a constant value          
        wptr_vec_r <= wptr_vec_nxt;
// spyglass enable_block FlopEConst
    end


    ////////////////
    ///////// occp generation
    wire [FIFO_DEPTH:0] occp_nxt;
    //`if(0 != 0)//{
    //wire [FIFO_DEPTH:0] occp_r;
    //wire [FIFO_DEPTH:0] occp_cpy_r;
    //`else
    //reg [FIFO_DEPTH:0] occp_r;
    //reg [FIFO_DEPTH:0] occp_cpy_r;
    //`endif//}
    wire occp_en = (ren ^ wen );
    assign occp_nxt =
             wen ? {occp_r[FIFO_DEPTH-1:0], 1'b1} : (occp_r >> 1);
    // spyglass disable_block FlopEConst
    // SMD: Flip-flop enable pin is permanently disabled or enabled
    // SJ: No care about enable pin is a constant value
    always @(posedge clk or posedge rst_a)
    begin : occp_DFFEAR_PROC
      if (rst_a == 1'b1) begin
        occp_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
        occp_cpy_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
      end
      else if (nmi_restart_r == 1'b1) begin
        occp_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
        occp_cpy_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
      end
      else if (occp_en == 1'b1) begin
        occp_r <= occp_nxt;
        occp_cpy_r <= occp_nxt;
      end
    end
    // spyglass enable_block FlopEConst

    ////////////////
    ///////// input side
    if(I_SUPPORT_RTIO == 1) begin:i_support_rtio //{
     // reg occp_en_i_dly_r;
      wire occp_en_i_dly_set = occp_en & (~i_clk_en);
      wire occp_en_i_dly_clr = i_clk_en & occp_en_i_dly_r;
      wire occp_en_i_dly_ena = occp_en_i_dly_set | occp_en_i_dly_clr;
      wire occp_en_i_dly_nxt = occp_en_i_dly_set | (~occp_en_i_dly_clr);
      always @(posedge clk or posedge rst_a)
      begin : occp_dly_DFFEAR_PROC
        if (rst_a == 1'b1)
          occp_en_i_dly_r <= 1'b1;
        else if (nmi_restart_r == 1'b1)
          occp_en_i_dly_r <= 1'b1;          
        else if (occp_en_i_dly_ena == 1'b1)
          occp_en_i_dly_r <= occp_en_i_dly_nxt;
      end
      wire [FIFO_DEPTH:0] occp_in = occp_en ? occp_nxt : occp_r;
      //reg [FIFO_DEPTH:0] i_occp_r;
      wire i_occp_ena = i_clk_en & (occp_en | occp_en_i_dly_r);
      always @(posedge clk or posedge rst_a)
      begin : i_occp_DFFEAR_PROC
        if (rst_a == 1'b1)
          i_occp_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
        else if ((nmi_restart_r == 1'b1) && (i_clk_en == 1'b1))
          i_occp_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};          
        else if (i_occp_ena == 1'b1)
          i_occp_r <= occp_in;
      end
      assign i_occp = {1'b0,i_occp_r[FIFO_DEPTH:1]};


    end//}
    else begin:i_not_support_rtio//{
      assign i_occp = {1'b0,occp_r[FIFO_DEPTH:1]};
    end//}


    wire [FIFO_DEPTH:0]   o_occp_cpy;
    ////////////////
    ///////// output side
    if(O_SUPPORT_RTIO == 1) begin:o_support_rtio //{
      //reg occp_en_o_dly_r;
      wire occp_en_o_dly_set = occp_en & (~o_clk_en);
      wire occp_en_o_dly_clr = o_clk_en & occp_en_o_dly_r;
      wire occp_en_o_dly_ena = occp_en_o_dly_set | occp_en_o_dly_clr;
      wire occp_en_o_dly_nxt = occp_en_o_dly_set | (~occp_en_o_dly_clr);
      always @(posedge clk or posedge rst_a)
      begin : occp_dly_DFFEAR_PROC
        if (rst_a == 1'b1)
          occp_en_o_dly_r <= 1'b1;
        else if (nmi_restart_r == 1'b1)
          occp_en_o_dly_r <= 1'b1;          
        else if (occp_en_o_dly_ena == 1'b1)
          occp_en_o_dly_r <= occp_en_o_dly_nxt;
      end
      wire [FIFO_DEPTH:0] occp_in = occp_en ? occp_nxt : occp_r;
     // reg [FIFO_DEPTH:0] o_occp_r;
     // reg [FIFO_DEPTH:0] o_occp_cpy_r;
      wire o_occp_ena = o_clk_en & (occp_en | occp_en_o_dly_r);
      always @(posedge clk or posedge rst_a)
      begin : o_occp_DFFEAR_PROC
        if (rst_a == 1'b1) begin
          o_occp_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
          o_occp_cpy_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
        end
        else if ((nmi_restart_r == 1'b1) && (o_clk_en == 1'b1)) begin 
          o_occp_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
          o_occp_cpy_r <= { {FIFO_DEPTH{1'b0}}, 1'b1};
        end
        else if (o_occp_ena == 1'b1) begin
          o_occp_r <= occp_in;
          o_occp_cpy_r <= occp_in;
        end
      end
      assign o_occp = {1'b0,o_occp_r[FIFO_DEPTH:1]};
      assign o_occp_cpy = {1'b0,o_occp_cpy_r[FIFO_DEPTH:1]};


    end//}
    else begin:o_not_support_rtio//{
      assign o_occp = {1'b0,occp_r[FIFO_DEPTH:1]};
    // spyglass disable_block FlopEConst
    // SMD: Flip-flop enable pin is permanently disabled or enabled
    // SJ: No care about enable pin is a constant value
      assign o_occp_cpy = {1'b0,occp_cpy_r[FIFO_DEPTH:1]};
    // spyglass enable_block FlopEConst

    end//}


    if(IN_OUT_MWHILE == 0) begin:in_out_mwhile//{
      // If the fifo is not full, then it can accept more
      assign i_ready = (~i_occp[FIFO_DEPTH-1]);
    end//}
    else begin:no_in_out_mwhile//{
      // If the fifo is not full, or it have one entry leaving then it can accept more
      // Must not the clock ratio supported
      assign i_ready = ((~i_occp[FIFO_DEPTH-1]) | ren);
    end//}

    // If the fifo is not empty, then it can output valid
    assign o_valid = (o_occp[0]);
    wire o_valid_r = (o_occp_cpy[0]);


    ////////////////
    ///////// write the fifo array
    for (i=0; i<FIFO_DEPTH; i=i+1) begin:fifo_rf
      assign rf_en[i] = wen & wptr_vec_r[i];

// spyglass disable_block FlopEConst
// SMD: Flip-flop enable pin is permanently disabled or enabled
// SJ: No care about enable pin is a constant value
// spyglass disable_block Clock_delay01
// SMD: Simulation mismatch for destination register and source register
// SJ: It's not an issue, caused when lock step.
// leda NTL_RST03 off
// leda S_1C_R off
// spyglass disable_block ResetFlop-ML 
// LMD: Include an asynchronous reset/set/load function for all flipflops
// LJ: No care about the reset
      always @(posedge clk)
      begin : rf_DFFE_PROC
        if (rf_en[i] == 1'b1)
        begin
// spyglass disable_block STARC-2.3.4.3 
// LMD: AsyncResetOrSet
// LJ: no reset function
// spyglass disable_block Ar_resetcross01
// LMD: Unsynchronized reset crossing detected
// LJ: no reset function
          rf_r[i] <= i_data;
// spyglass enable_block Ar_resetcross01          
// spyglass enable_block STARC-2.3.4.3           
        end
      end
// spyglass enable_block Clock_delay01
// spyglass enable_block ResetFlop-ML 
// leda S_1C_R on
// leda NTL_RST03 on
// spyglass enable_block FlopEConst
    end

    ////////////////
    ///////// read the fifo array
    //reg [FIFO_WIDTH-1:0] r_data;
    //debug wire [FIFO_WIDTH-1:0] r_data_mask_0 = {FIFO_WIDTH{1'b0}};
    //debug assign o_data = (o_valid_r == 1'b1) ? r_data : r_data_mask_0;
    //debug integer j;
    //debug always @*
    //debug begin : rd_port_PROC
    //debug   r_data = {FIFO_WIDTH{1'b0}};
    //debug   for(j=0; j<FIFO_DEPTH; j=j+1) begin
    //debug     r_data = r_data | ((rptr_vec_r[j] == 1'b1) ? rf_r[j] : r_data_mask_0);
    //debug   end
    //debug end
    
    //debug
    integer j;
    reg  [FIFO_WIDTH-1:0] r_data_vec [FIFO_DEPTH-1:0];
    always @*
    begin : r_data_vec_PROC
      for(j=0; j<FIFO_DEPTH; j=j+1) begin
        r_data_vec[j] = {FIFO_WIDTH{1'b0}};
        if (rptr_vec_r[j] == 1'b1)
            r_data_vec[j] = rf_r[j];
      end
    end

    always @*
    begin : rd_port_PROC
      r_data = {FIFO_WIDTH{1'b0}};
      for(j=0; j<FIFO_DEPTH; j=j+1) begin
        r_data = r_data | r_data_vec[j];
      end
    end
    assign o_data = (o_valid_r == 1'b1) ? r_data : {FIFO_WIDTH{1'b0}};

  end//}
endgenerate//}

wire fifo_empty = (~o_valid);
wire fifo_full = (~i_ready);

//spyglass enable_block Clock_Reset_check02
// spyglass enable_block W528

`endif  // }

endmodule // biu_fifo

// spyglass enable_block Ac_unsync01
// spyglass enable_block Ac_unsync02
// spyglass enable_block Ar_unsync01
// spyglass enable_block Ar_asyncdeassert01
// spyglass enable_block Reset_check07
// spyglass enable_block Reset_sync02
// spyglass enable_block Ac_conv01
