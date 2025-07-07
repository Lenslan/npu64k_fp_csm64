// Library ARCv2CC-3.2.999999999
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
//   ####    ####             ##    #    #  #    #
//  #    #  #    #           #  #   #    #   #  #
//  #       #               #    #  #    #    ##
//  #       #               ######  #    #    ##
//  #    #  #    #          #    #  #    #   #  #
//   ####    ####  #######  #    #   ####   #    #
//
// ===========================================================================
//
// Description:
//  Verilog module defining the common cluster auxiliary register interface.
//
// ===========================================================================


// Configuration-dependent macro definitions
//
`include "npuarc_cc_exported_defines.v"
`include "npuarc_cc_defines.v"








// Set simulation timescale
//
// `include "const.def"



// spyglass disable_block Reset_info09b
// SMD: Reset net is tied to its inactive value with a constant value 0
// SJ: do not care this wrn
module npuarc_cc_aux (


  ////////// Core 0 interface signals ///////////////////////////////////////
  //
  // Read and Status Channel from core 0
  input  wire [`npuarc_CC_AUX_ADDR_RANGE]  aux_rs_addr,
  input  wire [`npuarc_CC_AUX_RGN_RANGE]   aux_rs_region,
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  signals not always needed in all configurations
// leda NTL_CON37 off
// LMD: Signal/Net must read from the input port
// LJ:  signals not always needed in all configurations
// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ: Unused instance ports are port-mapped but not connected
  input  wire                       aux_rs_valid,
  input  wire                       aux_rs_read,
// spyglass enable_block W240
// leda NTL_CON13C on
// leda NTL_CON37 on
  input  wire                       aux_rs_write,
  //
  output wire [`npuarc_CC_AUX_STAT_RANGE]  aux_rs_status,
  output wire [`npuarc_CC_AUX_DATA_RANGE]  aux_rs_data,
  output wire                       aux_rs_accept,
  //
  // Write Channel from core 0
  input  wire                       aux_wr_valid,
  input  wire [`npuarc_CC_AUX_ADDR_RANGE]  aux_wr_addr,
  input  wire [`npuarc_CC_AUX_RGN_RANGE]   aux_wr_region,
  input  wire [`npuarc_CC_AUX_DATA_RANGE]  aux_wr_data,
  //
  output wire                       aux_wr_allow,
  //
  // Commit Channel from core 0
  input  wire                       aux_cm_phase,
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port; signal/Net must read from the input port
// LJ: unused input port is intentionally unused (part of the protocol)
// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ: Unused instance ports are port-mapped but not connected
  input  wire                       aux_cm_valid,
// spyglass enable_block W240
// leda NTL_CON13C on
// leda NTL_CON37 on


  output                            cc_aux_l1_clk_enable,
  input                             cc_aux_accept_en,
  input                             cc_top_l1_cg_dis,


  output                            cc_gaux_idle,
  ////////// GAUX interface //////////////////////////////////////////////////
  //
  output                            cc_top_cg_en_gaux_cmd_valid,
  input                             cc_top_cg_en_gaux_cmd_accept,
  output [`npuarc_CC_GAUX_CMD_WIDTH-1:0]   cc_top_cg_en_gaux_cmd,
  input                             cc_top_cg_en_gaux_res_valid,
  output                            cc_top_cg_en_gaux_res_accept,
  input  [`npuarc_CC_GAUX_RES_WIDTH-1:0]   cc_top_cg_en_gaux_res_data,
  output                            cc_top_cg_en_gaux_wen_valid,
  output [`npuarc_CC_GAUX_WADDR_WIDTH-1:0] cc_top_cg_en_gaux_wen_addr,
  output [`npuarc_CC_GAUX_WDATA_WIDTH-1:0] cc_top_cg_en_gaux_wen_data,
  output [`npuarc_CC_GAUX_CORE_ID_RANGE]   cc_top_cg_en_gaux_wen_core_id,



  ////////// General input signals ///////////////////////////////////////////
  //
  input                             nmi_restart_r,  // NMI reset signal
  input                             rst_a,          // reset signal
  input                             ungated_clk,    //ungated clk
  input                             clk             //gated clock signal
  );

// spyglass disable_block W528
// SMD: Variable set but not read
// SJ: No care about the warning

// spyglass disable_block Ac_conv01
// SMD:  Ac_conv01 Convergence, 6 synchronizers converge on combinational gate
// SJ: These signals are independent which is not need to be cared
reg  gaux_cmd_valid_r;
reg  gaux_wen_valid_r;
assign cc_gaux_idle =
    (~gaux_cmd_valid_r)
  & (~gaux_wen_valid_r)
  & (~cc_top_cg_en_gaux_cmd_valid)
  & (~cc_top_cg_en_gaux_wen_valid)
  ;
// spyglass enable_block Ac_conv01

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Input and output buffer registers at the interface with cores and SLC    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg [`npuarc_CC_NUM_CORES-1:0]   rs_source_1h_r;
reg                       rs_request_cg0;

reg [`npuarc_CC_AUX_DATA_RANGE]  rs_data_r;
reg [5:0]                 rs_status_r;
reg                       rs_response_cg0;

reg [`npuarc_CC_NUM_CORES-1:0]   wr_source_1h_r;
reg                       wr_request_cg0;

// Read and Status Channel signals to core 0
//
reg                       c0_rs_accept_r;

// Write Channel to core 0
reg                       c0_wr_valid_r;
reg                       c0_wr_allow_r;
reg [`npuarc_CC_AUX_ADDR_RANGE]  c0_wr_addr_r;
reg [`npuarc_CC_AUX_RGN_RANGE]   c0_wr_region_r;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs
// LMJ: some bits are unused, as aux registers do not always implement 32 bits
reg [`npuarc_CC_AUX_DATA_RANGE]  c0_wr_data_r;
// leda NTL_CON32 on
//
reg                       c0_wr_request_cg0;



reg                       gaux_rs_valid_cg0;
reg                       gaux_rs_region_cg0;
reg                       gaux_cmd_valid_nxt;
reg [`npuarc_CC_GAUX_CMD_WIDTH-1:0]  gaux_cmd_r;
reg [`npuarc_CC_GAUX_CMD_WIDTH-1:0]  gaux_cmd_nxt;
reg                       gaux_wen_valid_set;
wire                       gaux_wen_valid_clr;
wire                       gaux_wen_valid_ena;
wire                       gaux_wen_valid_nxt;
reg [`npuarc_CC_GAUX_WADDR_WIDTH-1:0]  gaux_wen_addr_r;
reg [`npuarc_CC_GAUX_WDATA_WIDTH-1:0]  gaux_wen_data_r;
reg [`npuarc_CC_GAUX_CORE_ID_RANGE] gaux_wen_core_id_r;
reg                       gaux_rs_abort_cg0;
reg                       gaux_rs_abort_nxt;
reg                       gaux_rs_abort_r;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Internal signals                                                         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                       c0_rs_request;
reg  [`npuarc_CC_NUM_CORES-1:0]  rs_requests;    // vector of active R/S requests
wire [`npuarc_CC_NUM_CORES-1:0]  rs_select_1h;   // 1-hot selected R/S request

reg [`npuarc_CC_AUX_ADDR_RANGE]  i_rs_addr;      // selected rs_addr signals
reg [`npuarc_CC_AUX_RGN_RANGE]   i_rs_region;    // selected rs_region signals
reg                       i_rs_read;      // selected rs_read signal
reg                       i_cm_valid;     // selected cm_valid signal
reg                       i_rs_write;     // selected rs_write signal
reg                       i_cm_phase;     // selected cm_phase signal
reg [`npuarc_CC_GAUX_CORE_ID_RANGE] i_rs_core_id;

reg  [5:0]                rs_status_nxt;
reg  [`npuarc_CC_AUX_DATA_RANGE] rs_data_nxt;
reg                       c0_rs_accept_nxt;

reg                       c0_wr_valid_nxt;
reg                       c0_wr_allow_nxt;
reg                       c0_wr_request;
reg                       c0_write_done;

reg  [`npuarc_CC_NUM_CORES-1:0]  wr_requests;    // vector of active Write requests
wire [`npuarc_CC_NUM_CORES-1:0]  wr_select_1h;   // 1-hot selected Write request

reg [`npuarc_CC_AUX_ADDR_RANGE]  i_wr_addr;      // selected wr_addr signals
reg [`npuarc_CC_AUX_RGN_RANGE]   i_wr_region;    // selected wr_region signals
// leda NTL_CON13A off
// LMD: non driving internal net
// LMJ: some bits are unused, as aux registers do not always implement 32 bits
reg [`npuarc_CC_AUX_DATA_RANGE]  i_wr_data;      // selected wr_data signal
// leda NTL_CON13A on
reg [`npuarc_CC_GAUX_CORE_ID_RANGE] i_wr_core_id;

reg                       do_rs_accept;
reg                       do_rs_commit;
reg                       do_wr_accept;

// internal wire/regs for CC GAUX interface
wire                      gaux_cmd_accept;
wire                      gaux_res_valid;
wire                      gaux_res_accept;
wire [`npuarc_CC_GAUX_RES_WIDTH-1:0] gaux_res_data;
reg  [`npuarc_CC_GAUX_RGN_RANGE] gaux_rs_region_r;
reg  [`npuarc_CC_GAUX_RGN_RANGE] gaux_wr_region_r;
wire [`npuarc_CC_GAUX_RGN_RANGE] gaux_rs_region_nxt;
wire [`npuarc_CC_GAUX_RGN_RANGE] gaux_wr_region_nxt;

wire                              cc_top_cg_en_gaux_cmd_valid_int;
wire                              cc_top_cg_en_gaux_cmd_accept_int;
wire [`npuarc_CC_GAUX_CMD_WIDTH-1:0]     cc_top_cg_en_gaux_cmd_int;
wire                              cc_top_cg_en_gaux_res_valid_int;
wire                              cc_top_cg_en_gaux_res_accept_int;
wire [`npuarc_CC_GAUX_RES_WIDTH-1:0]     cc_top_cg_en_gaux_res_data_int;
wire                              cc_top_cg_en_gaux_wen_valid_int;
wire                              cc_top_cg_en_gaux_wen_accept_int;
wire [`npuarc_CC_GAUX_WADDR_WIDTH-1:0]   cc_top_cg_en_gaux_wen_addr_int;
wire [`npuarc_CC_GAUX_WDATA_WIDTH-1:0]   cc_top_cg_en_gaux_wen_data_int;
wire [`npuarc_CC_GAUX_CORE_ID_RANGE]     cc_top_cg_en_gaux_wen_core_id_int;




/////////////////////////////////////////////////////////////////////////////
//                                                                          //
// FSM state encoding parameter definitions for the Read/Status FSM and for //
// the Write channel FSM.                                                   //
//////////////////////////////////////////////////////////////////////////////

localparam RS_IDLE      = 4'd0;
localparam RS_DECODE    = 4'd1;
localparam RS_SLC_S1    = 4'd2;
localparam RS_SLC_S2    = 4'd3;
localparam RS_UAUX_S1   = 4'd4;
localparam RS_UAUX_S2   = 4'd5;
localparam RS_UAUX_S3   = 4'd6;
localparam RS_COMMIT    = 4'd7;
localparam RS_GAUX_S1   = 4'd8;
localparam RS_GAUX_S2   = 4'd9;

localparam WR_IDLE      = 3'd0;
localparam WR_DECODE    = 3'd1;
localparam WR_SLC_S1    = 3'd2;
localparam WR_SLC_S2    = 3'd3;
localparam WR_UAUX_S1   = 3'd4;
localparam WR_UAUX_S2   = 3'd5;
localparam WR_UAUX_S3   = 3'd6;

parameter CC_AUX_IDLE         = 2'd0;
parameter CC_AUX_GOING_IDLE   = 2'd1;
parameter CC_AUX_GOING_ACTIVE = 2'd2;
parameter CC_AUX_ACTIVE       = 2'd3;


reg [3:0]                 rs_state_r;
reg [2:0]                 wr_state_r;

reg [3:0]                 rs_state_nxt;
reg [2:0]                 wr_state_nxt;

wire                      cc_aux_fsm_cg0;
// spyglass disable_block Ac_conv01
// SMD:  Ac_conv01 Convergence, 9 synchronizers converge on combinational gate
// SJ: These signals are not need to be cared
assign cc_aux_fsm_cg0   = (rs_state_r != rs_state_nxt)
                        | (wr_state_r != wr_state_nxt)
                        ;

wire                    cc_aux_idle;
reg     [1:0]           cc_aux_accept_sta_cur;
reg     [1:0]           cc_aux_accept_sta_nxt;

assign cc_aux_idle = (rs_state_r == RS_IDLE)
                   & (wr_state_r == WR_IDLE)
                   & (~aux_rs_valid)
                   & (~aux_wr_valid)
                   & cc_gaux_idle
                     ;

wire cc_aux_l1_clk_enable_prel;
reg cc_aux_l1_clk_enable_prel_r;

assign cc_aux_l1_clk_enable_prel = ~cc_aux_idle | cc_top_l1_cg_dis;
assign cc_aux_l1_clk_enable = cc_aux_l1_clk_enable_prel_r;
// spyglass enable_block Ac_conv01

// spyglass disable_block Reset_sync04
// SMD:  Asynchronous reset signal
// SJ: These signals are not need to be cared
always @(posedge ungated_clk or posedge rst_a)
begin : cc_aux_l1_clk_enable_prel_PROC
  if (rst_a == 1'b1) begin
    cc_aux_l1_clk_enable_prel_r <= 1'b1;
  end 
  else if (nmi_restart_r == 1'b1) begin
    cc_aux_l1_clk_enable_prel_r <= 1'b1;
  end 
  else begin
    cc_aux_l1_clk_enable_prel_r <= cc_aux_l1_clk_enable_prel;
  end
end
// spyglass enable_block Reset_sync04

always @(posedge ungated_clk or posedge rst_a)
begin : cc_aux_accept_sta_PROC
  if (rst_a == 1'b1) begin
    cc_aux_accept_sta_cur <= CC_AUX_IDLE;
  end 
  else if (nmi_restart_r == 1'b1) begin
    cc_aux_accept_sta_cur <= CC_AUX_IDLE;
  end 
  else begin
    cc_aux_accept_sta_cur <= cc_aux_accept_sta_nxt;
  end
end

// spyglass disable_block Ac_conv01
// SMD:  Ac_conv01 Convergence, 6 synchronizers converge on combinational gate
// SJ: These signals are independent which is not need to be cared
always @*
begin : cc_aux_accept_FSM_PROC
  cc_aux_accept_sta_nxt = cc_aux_accept_sta_cur;
  case(cc_aux_accept_sta_cur)
    CC_AUX_IDLE:
      begin
        if (cc_aux_l1_clk_enable_prel) begin
          cc_aux_accept_sta_nxt = CC_AUX_GOING_ACTIVE;
        end
      end
    CC_AUX_GOING_ACTIVE:
      begin
        if (~cc_aux_l1_clk_enable_prel) begin
          cc_aux_accept_sta_nxt = CC_AUX_GOING_IDLE;
        end else if (cc_aux_accept_en) begin
          cc_aux_accept_sta_nxt = CC_AUX_ACTIVE;
        end
      end
    CC_AUX_ACTIVE:
      begin
        if (~cc_aux_l1_clk_enable_prel) begin
          cc_aux_accept_sta_nxt = CC_AUX_GOING_IDLE;
        end
      end
    default:
    //CC_AUX_GOING_IDLE:
      begin
        if (~cc_aux_accept_en) begin
          cc_aux_accept_sta_nxt = CC_AUX_IDLE;
        end
      end
  endcase
end
// spyglass enable_block Ac_conv01

assign cc_aux_real_accept_en = cc_aux_accept_sta_cur[1] & cc_aux_accept_sta_cur[0];//active status



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Create bit-vectors of the registered valid states on the Read/Status and //
// the Write channels.                                                      //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : request_vector_PROC

  c0_rs_request  = aux_rs_valid & aux_wr_allow & !c0_rs_accept_r & cc_aux_real_accept_en;
  c0_wr_request  = aux_wr_valid & aux_wr_allow & cc_aux_real_accept_en;

 rs_requests  = {
                  c0_rs_request
                }
              ;

 wr_requests  = {
                  c0_wr_request
                }
              ;

end // request_vector_PROC

assign rs_select_1h[0] = rs_requests[0];
assign wr_select_1h[0] = wr_requests[0];

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to multiplex the registered Read/Status channel    //
// requests according to the 1-hot selection vector rs_select_1h.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// spyglass disable_block Ac_conv01
// SMD:  Ac_conv01 Convergence, 6 synchronizers converge on combinational gate
// SJ: These signals are independent which is not need to be cared
always @*
begin : rs_mux_PROC

  i_rs_addr     = {`npuarc_CC_AUX_AW{1'b0}}
                | ({`npuarc_CC_AUX_AW{rs_source_1h_r[0]}} & aux_rs_addr)
                ;
  i_rs_region   = {`npuarc_CC_AUX_RGN_BITS{1'b0}}
                | ({`npuarc_CC_AUX_RGN_BITS{rs_source_1h_r[0]}} & aux_rs_region)
                ;
  i_rs_read     = 1'b0
                | (rs_source_1h_r[0] & aux_rs_read)
                ;

  i_cm_valid    = 1'b0
                | (rs_source_1h_r[0] & aux_cm_valid)
                ;

  i_rs_write    = 1'b0
                | (rs_source_1h_r[0] & aux_rs_write)
                ;

  i_cm_phase    = 1'b0
                | (rs_source_1h_r[0] & aux_cm_phase)
                ;

end // rs_mux_PROC
// spyglass enable_block Ac_conv01

always @*
begin : rs_core_id_PROC
  integer i;
  i_rs_core_id = {`npuarc_CC_GAUX_CORE_ID_WIDTH{1'b0}};
  for (i = 0; i < `npuarc_CC_NUM_CORES; i = i + 1)
     begin
        if (rs_source_1h_r[i] == 1)
           i_rs_core_id = $unsigned(i);
     end
end // rs_core_id_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to multiplex the Write channel requests according  //
// to the 1-hot selection vector wr_select_1h.                              //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : wr_mux_PROC

  i_wr_addr     = {`npuarc_CC_AUX_AW{1'b0}}
                | ({`npuarc_CC_AUX_AW{wr_source_1h_r[0]}} & c0_wr_addr_r)
                ;

  i_wr_region   = {`npuarc_CC_AUX_RGN_BITS{1'b0}}
                | ({`npuarc_CC_AUX_RGN_BITS{wr_source_1h_r[0]}} & c0_wr_region_r)
                ;

  i_wr_data     = {`npuarc_CC_AUX_DW{1'b0}}
                | ({`npuarc_CC_AUX_DW{wr_source_1h_r[0]}} & c0_wr_data_r)
                ;

end // rs_mux_PROC

always @*
begin : wr_core_id_PROC
  integer i;
  i_wr_core_id = {`npuarc_CC_GAUX_CORE_ID_WIDTH{1'b0}};
  for (i = 0; i < `npuarc_CC_NUM_CORES; i = i + 1)
     begin
        if (wr_source_1h_r[i] == 1)
           i_wr_core_id = $unsigned(i);
     end
end // wr_core_id_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process controlling the responses back to each core        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : cc_response_PROC

  //==========================================================================
  // define the next Read/Status channel rs_accept signal to each core
  //
  c0_rs_accept_nxt = do_rs_accept;

  rs_response_cg0  = do_rs_accept;

  //==========================================================================
  // define the next Write channel handshake signals to each core
  //
  c0_write_done       = do_wr_accept;
  c0_wr_valid_nxt  = aux_wr_valid
                   | (c0_wr_valid_r & !c0_write_done)
                   ;

  c0_wr_allow_nxt  = c0_write_done
                   | (c0_wr_allow_r & !aux_wr_valid)
                   ;

  c0_wr_request_cg0 = c0_wr_valid_nxt & !c0_wr_valid_r;


end // cc_request_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to implement the Read/Status FSM.                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// spyglass disable_block Ac_conv01
// SMD:  Ac_conv01 Convergence, 6 synchronizers converge on combinational gate
// SJ: These signals are independent which is not need to be cared
always @*
begin : rs_fsm_PROC

  rs_state_nxt      = RS_IDLE;
  rs_request_cg0    = 1'b0;
  rs_data_nxt       = {`npuarc_CC_AUX_DW{1'b0}};
  rs_status_nxt     = {`npuarc_CC_AUX_STAT_BITS{1'b0}};
  do_rs_accept      = 1'b0;
  do_rs_commit      = 1'b0;
  gaux_rs_valid_cg0  = 1'b0;
  gaux_rs_region_cg0 = 1'b0;
  gaux_cmd_valid_nxt = 1'b0;
  gaux_cmd_nxt       = {`npuarc_CC_GAUX_CMD_WIDTH{1'b0}};
  gaux_rs_abort_cg0  = 1'b0;
  gaux_rs_abort_nxt  = 1'b0;

  case (rs_state_r)
    //========================================================================
    // RS_IDLE state accepts new prioritized aux Read / Status requests.
    //========================================================================
    RS_IDLE:
      begin
// leda W563 off
// LMD: Reduction of a single bit expression is redundant
// LJ:  Generic IP can contain more than 1 Core
      if ((|rs_select_1h) == 1'b1)
// leda W563 on
        begin
        rs_request_cg0 = 1'b1;
        rs_state_nxt   = RS_DECODE;
        end
      end

    //========================================================================
    // RS_DECODE state processes current auxiliary Read / Status request.
    //========================================================================
    RS_DECODE:
      begin
      case (1'b1) // {

      i_rs_region[`npuarc_CC_AUX_GAUX_IDX]:
        begin
        rs_state_nxt       = RS_GAUX_S1;   // goto GAUX state S1
        gaux_rs_valid_cg0  = 1'b1;         // write to GAUX request registers
        gaux_rs_region_cg0 = 1'b1;         // write to GAUX sub-region registers
        gaux_cmd_valid_nxt = 1'b1;         // activate request to GAUX
        gaux_cmd_nxt       = { i_rs_core_id,
                               i_rs_read,
                               i_rs_write,
                               i_rs_addr[`npuarc_CC_GAUX_ADDR_RANGE]
                             }
                           ;
        end

      default:
        begin
        rs_state_nxt      = RS_IDLE;
        end

      endcase // }
      end

    RS_GAUX_S1:
      begin
         if (gaux_cmd_accept)
           begin
              rs_state_nxt = RS_GAUX_S2;
              gaux_rs_valid_cg0 = 1'b1;         // clear to GAUX request registers
           end
         else
           begin
              rs_state_nxt = RS_GAUX_S1;
           end

         // store commit abort info and do abort when gaux handshake completes
         if ((i_cm_phase == 1'b1) && (i_cm_valid == 1'b0))
           begin
              gaux_rs_abort_cg0 = 1'b1;
              gaux_rs_abort_nxt = 1'b1;
           end
      end

    RS_GAUX_S2:
      begin
         rs_data_nxt       = gaux_res_data[`npuarc_CC_GAUX_RES_DATA];
         rs_status_nxt     = gaux_res_data[`npuarc_CC_GAUX_RES_STRICT:`npuarc_CC_GAUX_RES_ILLEGAL];
         if (gaux_res_valid)
           begin
              rs_state_nxt = RS_COMMIT;
              gaux_rs_region_cg0 = 1'b1;
              if (((i_cm_phase == 1'b1) && (i_cm_valid == 1'b0)) || (gaux_rs_abort_r == 1'b1))
                do_rs_accept = 1'b0;
              else
                do_rs_accept = 1'b1;
           end
         else
           begin
              rs_state_nxt = RS_GAUX_S2;
           end

         // store commit abort info and do abort when gaux handshake completes
         if ((i_cm_phase == 1'b1) && (i_cm_valid == 1'b0))
           begin
              gaux_rs_abort_cg0 = 1'b1;
              gaux_rs_abort_nxt = 1'b1;
           end
      end

    //========================================================================
    // Commit state holds the current Read/Status transaction open until the
    // initiating core signals that the corresponding LR, SR or AEX operation
    // has reached the commit phase. At this point, the cc_aux read/status
    // channel can move on to the next request. If the instruction was
    // committed by the initiating core the i_cm_valid signal will be
    // asserted, and this must be forwarded to the UAUX bus if present.
    //========================================================================
    RS_COMMIT:
      begin
      gaux_rs_abort_cg0 = 1'b1;
      if ((i_cm_phase == 1'b1) || (gaux_rs_abort_r == 1'b1))
        begin
        rs_state_nxt = RS_IDLE;
        do_rs_commit = 1'b1;
        end
      else
        rs_state_nxt = RS_COMMIT;
      end
// spyglass disable_block W193
// SMD: empty statement
// SJ: no impact
    default:;
// spyglass enable_block W193
  endcase
end

// spyglass enable_block Ac_conv01

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to implement the Write FSM.                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
wire gaux_wen_i_accept;

always @*
begin : wr_fsm_PROC

  wr_state_nxt      = WR_IDLE;
  gaux_wen_valid_set = 1'b0;
  wr_request_cg0    = 1'b0;
  do_wr_accept      = 1'b0;

  case (wr_state_r)
    //========================================================================
    // WR_IDLE state accepts new prioritized aux Write requests.
    //========================================================================
    WR_IDLE:
      begin
// leda W563 off
// LMD: Reduction of a single bit expression is redundant
// LJ:  Generic IP can contain more than 1 Core
      if ((|wr_select_1h) == 1'b1)
// leda W563 on
        begin
        wr_request_cg0 = 1'b1;
        wr_state_nxt   = WR_DECODE;
        end
      end

    //========================================================================
    // WR_DECODE decodes the region from the current Write request and
    // branches the FSM to the appropriate sequence for each region.
    //========================================================================
    WR_DECODE:
      begin
      case (1'b1) // {


      i_wr_region[`npuarc_CC_AUX_GAUX_IDX]:
        begin
          if(gaux_wen_i_accept) begin
              wr_state_nxt      = WR_IDLE;      // write completes immediately
              gaux_wen_valid_set = 1'b1;         // write to GAUX request registers
              do_wr_accept      = 1'b1;         // accept initiating core's write to gaux buffer
          end
          else begin
              wr_state_nxt      = wr_state_r;      // write completes immediately
              gaux_wen_valid_set = 1'b0;         // write to GAUX request registers
              do_wr_accept      = gaux_wen_i_accept;   // accept initiating core's write to gaux buffer
          end
        end

// spyglass disable_block W193
// SMD: empty statement
// SJ: no impact
      default:
        begin
           gaux_wen_valid_set = 1'b0;
        end
// spyglass enable_block W193
      endcase // }
      end

// spyglass disable_block W193
// SMD: empty statement
// SJ: no impact
  default:;
// spyglass enable_block W193
  endcase
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous process to implement the internal registers of the cc_aux    //
// module                                                                   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////


// spyglass disable_block Clock_delay01
// SMD: Simulation mismatch for destination register and source register
// SJ: It's not an issue, caused when lock step.
always @(posedge clk or posedge rst_a)
begin : c1_aux_regs_PROC
  if (rst_a == 1'b1)
    begin
    rs_source_1h_r  <= {`npuarc_CC_NUM_CORES{1'b0}};
    rs_status_r     <= {`npuarc_CC_AUX_STAT_BITS{1'b0}};
    rs_data_r       <= {`npuarc_CC_AUX_DW{1'b0}};
    wr_source_1h_r  <= {`npuarc_CC_NUM_CORES{1'b0}};
    c0_rs_accept_r   <= 1'b0;
    c0_wr_allow_r    <= 1'b1;
    //
    c0_wr_valid_r    <= 1'b0;
    c0_wr_addr_r     <= {`npuarc_CC_AUX_AW{1'b0}};
    c0_wr_region_r   <= {`npuarc_CC_AUX_RGN_BITS{1'b0}};
    c0_wr_data_r     <= {`npuarc_CC_AUX_DW{1'b0}};
    end
  else if (nmi_restart_r == 1'b1) begin
    rs_source_1h_r  <= {`npuarc_CC_NUM_CORES{1'b0}};
    rs_status_r     <= {`npuarc_CC_AUX_STAT_BITS{1'b0}};
    rs_data_r       <= {`npuarc_CC_AUX_DW{1'b0}};
    wr_source_1h_r  <= {`npuarc_CC_NUM_CORES{1'b0}};
    c0_rs_accept_r   <= 1'b0;
    c0_wr_allow_r    <= 1'b1;
    //
    c0_wr_valid_r    <= 1'b0;
    c0_wr_addr_r     <= {`npuarc_CC_AUX_AW{1'b0}};
    c0_wr_region_r   <= {`npuarc_CC_AUX_RGN_BITS{1'b0}};
    c0_wr_data_r     <= {`npuarc_CC_AUX_DW{1'b0}};
  end 
  else
    begin

    if (rs_request_cg0 == 1'b1)
      begin
      rs_source_1h_r  <= rs_select_1h;
      end

    if (rs_response_cg0 == 1'b1)
      begin
      rs_status_r   <= rs_status_nxt;
      rs_data_r     <= rs_data_nxt;
      end

    c0_rs_accept_r   <= c0_rs_accept_nxt;

    c0_wr_valid_r    <= c0_wr_valid_nxt;


    if (c0_wr_request_cg0 == 1'b1)
      begin
      c0_wr_addr_r     <= aux_wr_addr;
      c0_wr_region_r   <= aux_wr_region;
      c0_wr_data_r     <= aux_wr_data;
      end

    if (wr_request_cg0 == 1'b1)
      begin
      wr_source_1h_r  <= wr_select_1h;
      end

    c0_wr_allow_r    <= c0_wr_allow_nxt;

    end
end // cc_aux_regs_PROC
// spyglass enable_block Clock_delay01

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous process to implement the FSM states for the Read/Status      //
// channel and the Write channel.                                           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////


always @(posedge clk or posedge rst_a)
begin : fsm_states_PROC
  if (rst_a == 1'b1)
    begin
    rs_state_r  <= 4'd0;
    wr_state_r  <= 3'd0;
    end
  else if (nmi_restart_r == 1'b1) begin
    rs_state_r  <= 4'd0;
    wr_state_r  <= 3'd0;
    end
  else
    begin
    if (cc_aux_fsm_cg0 == 1'b1)
      begin
      rs_state_r  <= rs_state_nxt;
      wr_state_r  <= wr_state_nxt;
      end
    end
end // fsm_states_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous process to implement the output registers for the GAUX busses//
//                                                                          //
//////////////////////////////////////////////////////////////////////////////


  always @(posedge clk or posedge rst_a)
  begin : gaux_regs_PROC
    if (rst_a == 1'b1)
      begin
         gaux_cmd_valid_r <= 1'b0;
         gaux_cmd_r       <= {`npuarc_CC_GAUX_CMD_WIDTH{1'b0}};
         gaux_wen_addr_r  <= {`npuarc_CC_GAUX_WADDR_WIDTH{1'b0}};
         gaux_wen_data_r  <= {`npuarc_CC_GAUX_WDATA_WIDTH{1'b0}};
         gaux_rs_region_r <= {`npuarc_CC_GAUX_RGN_WIDTH{1'b0}};
         gaux_wr_region_r <= {`npuarc_CC_GAUX_RGN_WIDTH{1'b0}};
         gaux_rs_abort_r  <= 1'b0;
         gaux_wen_core_id_r  <= {`npuarc_CC_GAUX_CORE_ID_WIDTH{1'b0}};
      end
  else if (nmi_restart_r == 1'b1) begin
         gaux_cmd_valid_r <= 1'b0;
         gaux_cmd_r       <= {`npuarc_CC_GAUX_CMD_WIDTH{1'b0}};
         gaux_rs_region_r <= {`npuarc_CC_GAUX_RGN_WIDTH{1'b0}};
         gaux_wr_region_r <= {`npuarc_CC_GAUX_RGN_WIDTH{1'b0}};
         gaux_rs_abort_r  <= 1'b0;
         gaux_wen_core_id_r  <= {`npuarc_CC_GAUX_CORE_ID_WIDTH{1'b0}};
      end
    else
      begin
        if (gaux_rs_valid_cg0 == 1'b1)
          begin
             gaux_cmd_valid_r <= gaux_cmd_valid_nxt;
             gaux_cmd_r       <= gaux_cmd_nxt;
          end

        if (gaux_rs_region_cg0 == 1'b1)
          begin
             gaux_rs_region_r <= gaux_rs_region_nxt;
          end

        if (gaux_rs_abort_cg0 == 1'b1)
          begin
             gaux_rs_abort_r <= gaux_rs_abort_nxt;
          end

        if (gaux_wen_valid_set == 1'b1)
          begin
             gaux_wr_region_r <= gaux_wr_region_nxt;
             gaux_wen_addr_r  <= i_wr_addr[`npuarc_CC_GAUX_ADDR_RANGE];
             gaux_wen_data_r  <= i_wr_data;
             gaux_wen_core_id_r  <= i_wr_core_id;
          end
      end
  end

  wire gaux_wen_o_accept;
  assign gaux_wen_valid_clr = gaux_wen_valid_r & gaux_wen_o_accept;
  assign gaux_wen_valid_ena = gaux_wen_valid_set | gaux_wen_valid_clr;
  assign gaux_wen_valid_nxt = gaux_wen_valid_set | (~gaux_wen_valid_clr);

  always @(posedge clk or posedge rst_a)
  begin : gaux_wen_valid_PROC
    if (rst_a == 1'b1) begin
         gaux_wen_valid_r <= 1'b0;
    end
    else if (nmi_restart_r == 1'b1) begin
         gaux_wen_valid_r <= 1'b0;
    end
    else if (gaux_wen_valid_ena == 1'b1) begin
         gaux_wen_valid_r <= gaux_wen_valid_nxt;
    end
  end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output assignments                                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign aux_rs_status  = rs_status_r;
assign aux_rs_data    = rs_data_r;
assign aux_rs_accept  = c0_rs_accept_r & cc_aux_real_accept_en;
assign aux_wr_allow   = c0_wr_allow_r & cc_aux_real_accept_en;


////////////////////////////////
// GAUX interface assignments
assign gaux_res_accept = (rs_state_r == RS_GAUX_S2);

// cc_top_cg_en_gaux
assign gaux_rs_region_nxt[0] = ((rs_state_r == RS_DECODE)
                                    && ((i_rs_addr[`npuarc_CC_GAUX_ADDR_RANGE] >= 12'h9A9)
                                       && (i_rs_addr[`npuarc_CC_GAUX_ADDR_RANGE] <= 12'h9A9  ))
                                      );
assign gaux_wr_region_nxt[0] = ((wr_state_r == WR_DECODE)
                                    && ((i_wr_addr[`npuarc_CC_GAUX_ADDR_RANGE] >= 12'h9A9)
                                       && (i_wr_addr[`npuarc_CC_GAUX_ADDR_RANGE] <= 12'h9A9  ))
                                      );

assign cc_top_cg_en_gaux_cmd_valid_int   = gaux_rs_region_r[0] & gaux_cmd_valid_r;
assign cc_top_cg_en_gaux_cmd_int         = gaux_cmd_r[`npuarc_CC_GAUX_CMD_WIDTH-1:0];
assign cc_top_cg_en_gaux_res_accept_int  = gaux_rs_region_r[0] & gaux_res_accept;
assign cc_top_cg_en_gaux_wen_valid_int   = gaux_wr_region_r[0] & gaux_wen_valid_r;
assign cc_top_cg_en_gaux_wen_addr_int    = gaux_wen_addr_r[`npuarc_CC_GAUX_WADDR_WIDTH-1:0];
assign cc_top_cg_en_gaux_wen_data_int    = gaux_wen_data_r;
assign cc_top_cg_en_gaux_wen_core_id_int = gaux_wen_core_id_r;


assign gaux_wen_i_accept = (~gaux_wen_valid_r);

assign gaux_wen_o_accept = 1'b0
      | (gaux_wr_region_r[0] & cc_top_cg_en_gaux_wen_accept_int)
     ;

assign gaux_cmd_accept          =  1'b0
                                | (gaux_rs_region_r[0] & cc_top_cg_en_gaux_cmd_accept_int)
                                ;

assign gaux_res_valid           =  1'b0
                                | (gaux_rs_region_r[0] & cc_top_cg_en_gaux_res_valid_int)
                                ;

// spyglass disable_block Ac_conv01
// SMD:  Ac_conv01 Convergence, 6 synchronizers converge on combinational gate
// SJ: These signals are independent which is not need to be cared
assign gaux_res_data           =  {`npuarc_CC_GAUX_RES_WIDTH{1'b0}}
                                | ({`npuarc_CC_GAUX_RES_WIDTH{gaux_rs_region_r[0]}} & cc_top_cg_en_gaux_res_data_int)
// spyglass enable_block Ac_conv01
                                ;

// add pipeline buffers for cc_top_cg_en_ gaux interface
npuarc_cc_gaux_buffer u_cc_top_cg_en_gaux_buffer (

  .i_gaux_cmd_valid     (cc_top_cg_en_gaux_cmd_valid_int),
  .i_gaux_cmd_accept    (cc_top_cg_en_gaux_cmd_accept_int),
  .i_gaux_cmd           (cc_top_cg_en_gaux_cmd_int),
  .i_gaux_res_valid     (cc_top_cg_en_gaux_res_valid_int),
  .i_gaux_res_accept    (cc_top_cg_en_gaux_res_accept_int),
  .i_gaux_res_data      (cc_top_cg_en_gaux_res_data_int),
  .i_gaux_wen_valid     (cc_top_cg_en_gaux_wen_valid_int),
  .i_gaux_wen_accept    (cc_top_cg_en_gaux_wen_accept_int),
  .i_gaux_wen_addr      (cc_top_cg_en_gaux_wen_addr_int),
  .i_gaux_wen_data      (cc_top_cg_en_gaux_wen_data_int),
  .i_gaux_wen_core_id   (cc_top_cg_en_gaux_wen_core_id_int),
  .o_gaux_cmd_valid     (cc_top_cg_en_gaux_cmd_valid),
  .o_gaux_cmd_accept    (cc_top_cg_en_gaux_cmd_accept),
  .o_gaux_cmd           (cc_top_cg_en_gaux_cmd),
  .o_gaux_res_valid     (cc_top_cg_en_gaux_res_valid),
  .o_gaux_res_accept    (cc_top_cg_en_gaux_res_accept),
  .o_gaux_res_data      (cc_top_cg_en_gaux_res_data),
  .o_gaux_wen_valid     (cc_top_cg_en_gaux_wen_valid),
  .o_gaux_wen_accept    (1'b1),
  .o_gaux_wen_addr      (cc_top_cg_en_gaux_wen_addr),
  .o_gaux_wen_data      (cc_top_cg_en_gaux_wen_data),
  .o_gaux_wen_core_id   (cc_top_cg_en_gaux_wen_core_id),

  .nmi_restart_r           (1'b0),

  .rst_a                (rst_a),
  .clk                  (clk)
  );




// spyglass enable_block W528
endmodule // cc_aux
// spyglass enable_block Reset_info09b
