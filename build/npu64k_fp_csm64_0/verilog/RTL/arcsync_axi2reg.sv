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


`include "arcsync_bus_gs_DW_axi_gs_all_includes.vh"
`include "arcsync_defines.v"
module arcsync_axi2reg
#(
  parameter logic [31:0] CLUSTER_NUM     = 32'd1,
  parameter NUM_CORE_C03    = 4,
  parameter NUM_CORE_C74    = 0,
  parameter MAX_CORE_NUM    = 1,
  parameter HAS_PMU             = 0,
  parameter AXI_ID_WIDTH        = 2 ,
  parameter AXI_ADDR_WIDTH      = 32,
  parameter AXI_DATA_WIDTH      = 64,
  parameter ARCSYNC_ADDR_WIDTH  = 32,
  parameter ARCSYNC_DATA_WIDTH  = 64, 
  parameter AXI_WSTRB_WIDTH     = 8,
  parameter BASE_ADDR_WIDTH     = 32,
  parameter logic [31:0] AC_NUM   = 32'd3,
  parameter logic [31:0] CORE_NUM = 32'd1,
  parameter ARCSYNC_VIRT_MACHINES = 16,
  parameter logic        CL_GRP_CLK_EN_RST = 1

)(
  input logic [CLUSTER_NUM-1:0]      npx_L2_grp_exist,
  input logic [CLUSTER_NUM-1:0][3:0] npx_L1_grp_exist,

  // sys base address
  // Per Cluster interfaces
  // 
  output logic [CLUSTER_NUM-1:0][BASE_ADDR_WIDTH-1:16] arcsync_core_csm_addr_base,
  output logic [CLUSTER_NUM-1:0][BASE_ADDR_WIDTH-1:16] arcsync_core_periph_addr_base,

  output logic [CLUSTER_NUM-1:0]      cl_enable,
  output logic [CLUSTER_NUM-1:0][3:0] cl_grp_clk_en,
  output logic [CLUSTER_NUM-1:0][4:0] cl_grp_rst,
  input  logic                        npu_ctrl_safety,
  input  logic [1:0]                  num_vm,

  // ARCSync_axi2reg
  // Transfer AXI interface to in-order sram-like with accept interface
  // AXI Interfaces
  input logic                                          arcsync_axi_arvalid,
  output logic 					       arcsync_axi_arready,
  input logic [AXI_ID_WIDTH-1:0] 		       arcsync_axi_arid,
  input logic [AXI_ADDR_WIDTH-1:0] 		       arcsync_axi_araddr,
  input logic [2:0] 				       arcsync_axi_arsize,
  input logic [3:0] 				       arcsync_axi_arlen,
  input logic [1:0] 				       arcsync_axi_arburst,
  input logic [2:0] 				       arcsync_axi_arprot,
  input logic [3:0] 				       arcsync_axi_arcache,
  
  input logic 					       arcsync_axi_awvalid,
  output logic 					       arcsync_axi_awready,
  input logic [AXI_ID_WIDTH-1:0] 		       arcsync_axi_awid,
  input logic [AXI_ADDR_WIDTH-1:0] 		       arcsync_axi_awaddr,
  input logic [2:0] 				       arcsync_axi_awsize,
  input logic [3:0] 				       arcsync_axi_awlen,
  input logic [1:0] 				       arcsync_axi_awburst,
  input logic [2:0] 				       arcsync_axi_awprot,
  input logic [3:0] 				       arcsync_axi_awcache,
  
  output logic 					       arcsync_axi_rvalid,
  input logic 					       arcsync_axi_rready,
  output logic [AXI_DATA_WIDTH-1:0] 		       arcsync_axi_rdata,
  output logic 					       arcsync_axi_rlast,
  output logic [1:0] 				       arcsync_axi_rresp,
  output logic [AXI_ID_WIDTH-1:0] 		       arcsync_axi_rid, 
  
  input logic 					       arcsync_axi_wvalid,
  output logic 					       arcsync_axi_wready,
  input logic [AXI_DATA_WIDTH-1:0] 		       arcsync_axi_wdata,
  input logic [AXI_WSTRB_WIDTH-1:0] 		       arcsync_axi_wstrb,
  input logic 					       arcsync_axi_wlast,
  
  output logic [AXI_ID_WIDTH-1:0] 		       arcsync_axi_bid,
  output logic 					       arcsync_axi_bvalid,
  output logic [1:0] 				       arcsync_axi_bresp,
  input logic 					       arcsync_axi_bready,

//-------------------------------------------------------------------------------------------------------
// Only valid address region with defined higher bits is sent with corresponding sel signal. 
// These sel signals are one-hot0
// Conditions for resp_error is received: 
// 1. If that is a address hole in the address region
// 2. write attemp to a read-only register
// 3. invalid write value to a register
//-------------------------------------------------------------------------------------------------------
  output logic 					       mmio_sel_gfrc, // select target register group
  output logic 					       mmio_sel_pmu,
  output logic 					       mmio_sel_sfty,
  output logic 					       mmio_sel_acs, 
  output logic 					       mmio_sel_eid, 
  output logic 					       mmio_sel_ac,
  output logic                                         mmio_sel_map_vm_vproc,
  output logic                                         mmio_sel_vm_eid,
  output logic [ARCSYNC_ADDR_WIDTH-1:0] 	       mmio_addr, // register address, valid with sel* 
  output logic 					       mmio_wen, // write enable for register, valid with sel*
  output logic 					       mmio_ren, // read enable for register, valid with sel*
  output logic 					       mmio_gfrc_read_64b, // read enable for register, valid with sel*
  output logic [ARCSYNC_DATA_WIDTH-1:0] 	       mmio_wdata, // write data, valid at the cycle when wen is high
  input logic [AXI_DATA_WIDTH-1:0] 		       mmio_rdata_gfrc, // read data, valid at the cycle when ren is high
  input logic [ARCSYNC_DATA_WIDTH-1:0] 		       mmio_rdata_pmu, //
  input logic [ARCSYNC_DATA_WIDTH-1:0] 		       mmio_rdata_sfty, // 
  input logic [ARCSYNC_DATA_WIDTH-1:0] 		       mmio_rdata_acs, // 
  input logic [ARCSYNC_DATA_WIDTH-1:0] 		       mmio_rdata_eid, // 
  input logic [ARCSYNC_DATA_WIDTH-1:0] 		       mmio_rdata_ac, // 
  input logic [ARCSYNC_DATA_WIDTH-1:0]                 mmio_rdata_map_vm_vproc, //
  input logic [ARCSYNC_DATA_WIDTH-1:0]                 mmio_rdata_vm_eid, //
  input logic [1:0] 				       mmio_resp_gfrc, // {ack, err} the response is received at the cycle when *en is high
  input logic [1:0] 				       mmio_resp_pmu, //
  input logic [1:0] 				       mmio_resp_sfty, // 
  input logic [1:0] 				       mmio_resp_acs, // 
  input logic [1:0] 				       mmio_resp_eid, // 
  input logic [1:0] 				       mmio_resp_ac, // 
  input logic [1:0]                                    mmio_resp_map_vm_vproc, //
  input logic [1:0]                                    mmio_resp_vm_eid, //

  // Clock, reset and configuration
  input logic 					       rst_a, // Asynchronous reset, active high
  input logic 					       clk               // Clock
);

//-------------------------------------------------------------------------------------------------------
// localparam
//-------------------------------------------------------------------------------------------------------
localparam logic [31:0] ARCSYNC_ADDR_CONFIG     = `ARCSYNC_ADDR_CONFIG    ;
localparam logic [31:0] ADDR_AS_BLD_CFG         = `ADDR_AS_BLD_CFG        ;
localparam logic [31:0] ADDR_AS_NUM_CORE_C03    = `ADDR_AS_NUM_CORE_C03   ;
localparam logic [31:0] ADDR_AS_NUM_CORE_C47    = `ADDR_AS_NUM_CORE_C47   ;
localparam logic [31:0] ARCSYNC_ADDR_CONFIG_MAX = `ARCSYNC_ADDR_CONFIG_MAX;
localparam logic [31:0] ARCSYNC_ADDR_GFRC       = `ARCSYNC_ADDR_GFRC      ;
localparam logic [31:0] ARCSYNC_ADDR_GFRC_MAX   = `ARCSYNC_ADDR_GFRC_MAX  ;
localparam logic [31:0] ARCSYNC_ADDR_PMU_REGION_0       = `ARCSYNC_ADDR_PMU_REGION_0      ;
localparam logic [31:0] ARCSYNC_ADDR_PMU_REGION_0_MAX   = `ARCSYNC_ADDR_PMU_REGION_0_MAX  ;
localparam logic [31:0] ARCSYNC_ADDR_PMU_REGION_1       = `ARCSYNC_ADDR_PMU_REGION_1      ;
localparam logic [31:0] ARCSYNC_ADDR_PMU_REGION_1_MAX   = `ARCSYNC_ADDR_PMU_REGION_1_MAX  ;
localparam logic [31:0] ARCSYNC_ADDR_ACS       = `ARCSYNC_ADDR_ACS      ;
localparam logic [31:0] ARCSYNC_ADDR_ACS_MAX   = `ARCSYNC_ADDR_ACS_MAX  ;
localparam logic [31:0] ADDR_EID_SEND_EVENT_0  = `ADDR_EID_SEND_EVENT_0; 
localparam logic [31:0] ADDR_EID_SEND_EVENT_1  = `ADDR_EID_SEND_EVENT_1; 
localparam logic [31:0] ADDR_EID_SEND_EVENT_MAX= `ADDR_EID_SEND_EVENT_MAX;
localparam logic [31:0] ADDR_EID_RAISE_IRQ_0   = `ADDR_EID_RAISE_IRQ_0 ;   
localparam logic [31:0] ADDR_EID_RAISE_IRQ_1   = `ADDR_EID_RAISE_IRQ_1 ; 
localparam logic [31:0] ADDR_EID_ACK_IRQ_MAX   = `ADDR_EID_ACK_IRQ_MAX ;
localparam logic [31:0] ARCSYNC_ADDR_AC        = `ARCSYNC_ADDR_AC      ; 
localparam logic [31:0] ARCSYNC_ADDR_AC_MAX    = `ARCSYNC_ADDR_AC_MAX  ; 
localparam logic [31:0] ADDR_AC_CONFIG         = `ADDR_AC_CONFIG       ; 
localparam logic [31:0] ADDR_AC_CONFIG_MAX     = `ADDR_AC_CONFIG_MAX   ; 
localparam logic [31:0] ADDR_AC_CONTROL        = `ADDR_AC_CONTROL      ; 
localparam logic [31:0] ADDR_AC_CONTROL_MAX    = `ADDR_AC_CONTROL_MAX  ; 
localparam logic [31:0] ADDR_CL_ENABLE         = `ADDR_CL_ENABLE    ;
localparam logic [31:0] ADDR_CL_GRP_CLK_EN     = `ADDR_CL_GRP_CLK_EN;
localparam logic [31:0] ADDR_CL_GRP_RESET      = `ADDR_CL_GRP_RESET ;
localparam logic [31:0] ADDR_CL_CONTROL_MAX    = `ADDR_CL_CONTROL_MAX;
localparam logic [31:0] ADDR_CSM_ADDR_BASE       = `ADDR_CSM_ADDR_BASE ;  
localparam logic [31:0] ADDR_CL_PERIPH_ADDR_BASE = `ADDR_CL_PERIPH_ADDR_BASE;
localparam logic [31:0] ARCSYNC_ADDR_SFTY       = `ARCSYNC_ADDR_SFTY      ;
localparam logic [31:0] ARCSYNC_ADDR_SFTY_MAX   = `ARCSYNC_ADDR_SFTY_MAX  ;
localparam logic [31:0] ARCSYNC_ADDR_VM_CONFIG         = `ARCSYNC_ADDR_VM_CONFIG        ;
localparam logic [31:0] ARCSYNC_ADDR_VM_CONFIG_MAX     = `ARCSYNC_ADDR_VM_CONFIG_MAX    ;
localparam logic [31:0] ARCSYNC_ADDR_VM0_EID            = `ARCSYNC_ADDR_VM0_EID           ;
localparam logic [31:0] ARCSYNC_ADDR_VM0_EID_MAX        = `ARCSYNC_ADDR_VM0_EID_MAX       ;
parameter ADDR_VM0_EID_SEND_EVENT_0   = `ADDR_VM0_EID_SEND_EVENT_0  ; 
parameter ADDR_VM0_EID_SEND_EVENT_MAX = `ADDR_VM0_EID_SEND_EVENT_MAX;
parameter ADDR_VM0_EID_RAISE_IRQ_0    = `ADDR_VM0_EID_RAISE_IRQ_0   ;
parameter ADDR_VM0_EID_ACK_IRQ_MAX    = `ADDR_VM0_EID_ACK_IRQ_MAX   ;
parameter ADDR_VM0_AC_NOTIFY_SRC      = `ADDR_VM0_AC_NOTIFY_SRC;
parameter ADDR_VM0_AC_MAX             = `ADDR_VM0_AC_MAX;

parameter ARCSYNC_VM_GFRC_LO_OFFSET   = `ARCSYNC_VM_GFRC_LO_OFFSET;
parameter ARCSYNC_VM_GFRC_HI_OFFSET   = `ARCSYNC_VM_GFRC_HI_OFFSET;
  
//-------------------------------------------------------------------------------------------------------
// MMIO Registers
//-------------------------------------------------------------------------------------------------------
localparam logic [31:0] AS_MAX_CORE_NUM =  $clog2(MAX_CORE_NUM); 
localparam logic [31:0] AS_AC_NUM =  $clog2(AC_NUM); 
// set AS_BLD_CFG register
logic [31:0] AS_BLD_CFG;                  // Get the version  value of the configuration options set at RTL generation time
logic [31:0] AS_NUM_CORE_C03;             // Number of cores in clusters 0,1,2,3
logic [31:0] AS_NUM_CORE_C47;             // Number of cores in clusters 4,5,6,7

logic [CLUSTER_NUM-1:0][31:0] CL_ENABLE;
logic [CLUSTER_NUM-1:0][31:0] CL_GRP_CLK_EN;
logic [CLUSTER_NUM-1:0][31:0] CL_GRP_RESET;
logic [CLUSTER_NUM-1:0][31:0] CL_SM_ADDR_BASE;
logic [CLUSTER_NUM-1:0][31:0] CL_PERIPH_ADDR_BASE;

logic [7:0]  cluster_num;
logic [2:0]  ac_num;
logic [2:0]  max_core_num;
logic        has_pmu;

assign cluster_num = CLUSTER_NUM - 1; 
assign ac_num = AS_AC_NUM-4; 
assign max_core_num = AS_MAX_CORE_NUM-2;

assign AS_BLD_CFG      ={5'd0, num_vm, 1'b0, npu_ctrl_safety, has_pmu, ac_num, max_core_num, cluster_num, 8'd2};    
assign AS_NUM_CORE_C03 = NUM_CORE_C03;
assign AS_NUM_CORE_C47 = NUM_CORE_C74;

//GENERIC SLAVE INTERFACE
//Request Channel
logic [`ARCSYNC_REG_GS_AW-1:0]   gif_maddr;
logic                gif_mread;
logic                gif_mwrite;
logic [2:0]          gif_msize;
logic [1:0]          gif_mburst;
logic [`ARCSYNC_REG_GS_BW-1:0]   gif_mlen;
logic                gif_mlast;
logic [`ARCSYNC_REG_GS_DW-1:0]   gif_mdata;
logic [`ARCSYNC_REG_GS_DW/8-1:0] gif_mwstrb;
//Response Channel
logic                gif_svalid;
logic [1:0]          gif_sresp;
logic [`ARCSYNC_REG_GS_DW-1:0]   gif_sdata;
logic                gif_mready;

typedef enum reg [2:0] {
  S_IDLE           = 3'b000,  // 0 - Idle state             
  S_CHK_COND0      = 3'b001,  // 1 - Check gif_m*_r, for synthesis timing improvement. 
  S_RESP           = 3'b010,  // 2 - Send back response to axi_gs module
  S_2ND_REQ        = 3'b011,  // 3 - handle the second half request of 64-b transaction
  S_WAIT           = 3'b100   // 4 - waiting response from sub-module
} mmio_st_t;

// wire/reg declarations
mmio_st_t                      mmio_st_nxt;
mmio_st_t                      mmio_st_r;
logic mmio_st_IDLE_cs      ;
logic mmio_st_CHK_COND0_cs ;
logic mmio_st_RESP_cs      ;
logic mmio_st_2ND_REQ_cs   ;
logic mmio_st_WAIT_cs      ;
logic [CLUSTER_NUM-1:0]        mmio_csm_addr_base_en;
logic [CLUSTER_NUM-1:0]        mmio_per_addr_base_en;
logic [CLUSTER_NUM-1:0]        mmio_cl_enable_en;
logic [CLUSTER_NUM-1:0]        mmio_cl_grp_clk_en_en;
logic [CLUSTER_NUM-1:0]        mmio_cl_grp_reset_en;
logic [CLUSTER_NUM-1:0]        cl_enable_set;
logic [CLUSTER_NUM-1:0]        cl_enable_clr;
logic [CLUSTER_NUM-1:0]        cl_grp_clk_en_set;
logic [CLUSTER_NUM-1:0]        cl_grp_clk_en_clr;
logic [CLUSTER_NUM-1:0]        cl_grp_rst_set;
logic [CLUSTER_NUM-1:0]        cl_grp_rst_clr;
logic                          config_valid_req;
logic [CLUSTER_NUM-1:0]        cl_grp_clk_en_wen_valid_req;
logic [CLUSTER_NUM-1:0]        cl_grp_rst_wen_valid_req;
logic [CLUSTER_NUM-1:0]        mmio_csm_addr_base_wen_valid_req;
logic [CLUSTER_NUM-1:0]        mmio_per_addr_base_wen_valid_req;
logic [CLUSTER_NUM-1:0][23:0]  mmio_csm_addr_base_r;
logic [CLUSTER_NUM-1:0][23:0]  mmio_per_addr_base_r;
logic [CLUSTER_NUM-1:0][23:0]  mmio_csm_addr_base_nxt;
logic [CLUSTER_NUM-1:0][23:0]  mmio_per_addr_base_nxt;
logic [CLUSTER_NUM-1:0]        mmio_cl_enable_r;
logic [CLUSTER_NUM-1:0]        mmio_cl_enable_nxt;
logic [CLUSTER_NUM-1:0][3:0]   mmio_cl_grp_clk_en_r;
logic [CLUSTER_NUM-1:0][3:0]   mmio_cl_grp_clk_en_nxt;
logic [CLUSTER_NUM-1:0][4:0]   mmio_cl_grp_rst_r;
logic [CLUSTER_NUM-1:0][4:0]   mmio_cl_grp_rst_nxt;
logic                          mmio_sel_config;
logic                          mmio_sel_fail;
logic                          mmio_ren_nxt;
logic                          mmio_ren_r;
logic                          mmio_reg_en;
logic                          mmio_wen_nxt;
logic                          mmio_wen_r;
logic                          mmio_addr_check;
logic [ARCSYNC_DATA_WIDTH-1:0] mmio_rdata;  
logic [ARCSYNC_DATA_WIDTH-1:0] mmio_rdata_gfrc_hi;  
logic [ARCSYNC_DATA_WIDTH-1:0] mmio_rdata_config;  
logic [ARCSYNC_DATA_WIDTH-1:0] mmio_rdata_cl_ctrl;
logic [ARCSYNC_DATA_WIDTH-1:0] mmio_rdata_sys_base;  
logic [ARCSYNC_DATA_WIDTH-1:0] mmio_wdata_nxt;  
logic [ARCSYNC_DATA_WIDTH-1:0] mmio_wdata_r;  
logic                          mmio_resp_err;
logic                          mmio_resp_ack;
logic [1:0]                    mmio_resp_config;
logic                          write_burst;
logic                          write_burst_nxt;
logic                          write_burst_r;
logic                          valid_req;
logic                          full_write;
logic                          access_gfrc_full;
logic                          access_64b;
logic                          access_64b_nxt;
logic                          access_64b_r;
logic                          gif_saccept;
logic                          gif_svalid_nxt;
logic                          gif_svalid_r;
logic [1:0]                    gif_sresp_nxt; 
logic [1:0]                    gif_sresp_r; 
logic [`ARCSYNC_REG_GS_DW-1:0]             gif_sdata_nxt; 
logic [`ARCSYNC_REG_GS_DW-1:0]             gif_sdata_r; 

logic [`ARCSYNC_REG_GS_AW-1:0]   iarcsync_axi_awaddr;
logic [`ARCSYNC_REG_GS_AW-1:0]   iarcsync_axi_araddr;

logic mmio_sel_VM_EID_valid_range;
logic mmio_sel_VM_AC_valid_range;
logic mmio_cl_ctrl_wen;
logic mmio_sys_base_wen;

logic [`ARCSYNC_REG_GS_AW-1:0]   gif_maddr_r;
logic                            gif_mread_r;
logic                            gif_mwrite_r;
logic [2:0]                      gif_msize_r;
logic [1:0]                      gif_mburst_r;
logic [`ARCSYNC_REG_GS_BW-1:0]   gif_mlen_r;
logic                            gif_mlast_r;
logic [`ARCSYNC_REG_GS_DW-1:0]   gif_mdata_r;
logic [`ARCSYNC_REG_GS_DW/8-1:0] gif_mwstrb_r;
logic get_gif_m;
logic cond1;
logic incr_gif_maddr_r;
logic config_err;
logic mmio_AS_CFG_en;

if (AXI_ADDR_WIDTH == 40) begin
  always_comb
  begin
    iarcsync_axi_araddr  =  arcsync_axi_araddr;
    iarcsync_axi_awaddr  =  arcsync_axi_awaddr;
  end
end
else begin
  always_comb
  begin
    iarcsync_axi_araddr  =  {8'b0,arcsync_axi_araddr};
    iarcsync_axi_awaddr  =  {8'b0,arcsync_axi_awaddr};
  end
end

if (HAS_PMU == 1) begin
  always_comb
  begin
    has_pmu = 1'b1;
  end
end
else begin
  always_comb
  begin
    has_pmu = 1'b0;
  end
end

    arcsync_bus_gs_DW_axi_gs #() 
       u_arcsync_bus_axi2mmio (
         // Outputs
         .awready(arcsync_axi_awready),
         .wready (arcsync_axi_wready),
         .bid    (arcsync_axi_bid),
         .bresp  (arcsync_axi_bresp),
         .bvalid (arcsync_axi_bvalid),
         .arready(arcsync_axi_arready),
         .rid    (arcsync_axi_rid),
         .rdata  (arcsync_axi_rdata),
         .rresp  (arcsync_axi_rresp),
         .rlast  (arcsync_axi_rlast),
         .rvalid (arcsync_axi_rvalid),
         .maddr  (gif_maddr  ),
         .mread  (gif_mread  ),
         .mwrite (gif_mwrite ),
         .msize  (gif_msize  ),
         .mburst (gif_mburst ),
         .mlen   (gif_mlen   ),
         .mlast  (gif_mlast  ),
         .mdata  (gif_mdata  ),
         .mwstrb (gif_mwstrb ),
         .mready (gif_mready ),
         // Inputs
         .aclk   (clk),
         .aresetn(!rst_a),
         .awid   (arcsync_axi_awid),
         .awaddr (iarcsync_axi_awaddr),
         .awlen  (arcsync_axi_awlen),
         .awsize (arcsync_axi_awsize),
         .awburst(2'b01), // ARCSync only INCR
         .awlock (1'b0),                //not support exclusive access
         .awcache(arcsync_axi_awcache),
         .awprot (arcsync_axi_awprot),
         .awvalid(arcsync_axi_awvalid),
         .wdata  (arcsync_axi_wdata),
         .wstrb  (arcsync_axi_wstrb),
         .wlast  (arcsync_axi_wlast),
         .wvalid (arcsync_axi_wvalid),
         .bready (arcsync_axi_bready),
         .arid   (arcsync_axi_arid),
         .araddr (iarcsync_axi_araddr),
         .arlen  (arcsync_axi_arlen),
         .arsize (arcsync_axi_arsize),
         .arburst(2'b01), // ARCSync only INCR
         .arlock (1'b0),
         .arcache(arcsync_axi_arcache),
         .arprot (arcsync_axi_arprot),
         .arvalid(arcsync_axi_arvalid),
         .rready (arcsync_axi_rready),
         .gclken (1'b1),
         .saccept(gif_saccept),
         .svalid (gif_svalid), 
         .sdata  (gif_sdata),  
         .sresp  (gif_sresp)  
                 );

// the axi request should be 
// 1. a single beat transaction
// 2. an aligned transaction with 32-b or 64-b request
// 3. not a partial write
// Otherwise, send error back instead
// note: gif interface doesn't support axcache and axprot
assign full_write = gif_mwrite_r?  
                  ((gif_msize_r==3'b010 && ((!gif_maddr_r[2] && (&gif_mwstrb_r[3:0])) || 
                                           (gif_maddr_r[2] && (&gif_mwstrb_r[7:4]))))  
                || (gif_msize_r==3'b011 && (&gif_mwstrb_r[7:0])))
                              : 1'b1;  
assign write_burst = (|gif_mlen_r) && gif_mwrite_r;
assign valid_req = (~|gif_mlen_r) && full_write &&
                   ((gif_msize_r==3'b010 && (~|gif_maddr_r[1:0])) || 
                    (gif_msize_r==3'b011 && (~|gif_maddr_r[2:0])));  
assign access_gfrc_full = (mmio_addr==`ADDR_GFRC_READ_LO) && (gif_msize_r==3'b011); 
assign access_64b = valid_req &&  gif_msize_r==3'b011 && !access_gfrc_full;                  

assign mmio_rdata_gfrc_hi = {32{mmio_resp_gfrc[0] && access_gfrc_full}} & mmio_rdata_gfrc[AXI_DATA_WIDTH-1:ARCSYNC_DATA_WIDTH]; 
assign mmio_rdata_config = ({32{mmio_addr==`ADDR_AS_BLD_CFG}}      & AS_BLD_CFG     ) |
                           ({32{mmio_addr==`ADDR_AS_NUM_CORE_C03}} & AS_NUM_CORE_C03) |
                           ({32{mmio_addr==`ADDR_AS_NUM_CORE_C47}} & AS_NUM_CORE_C47) |
                           ({32{(|mmio_cl_enable_en) || (|mmio_cl_grp_clk_en_en) || (|mmio_cl_grp_reset_en)}} & mmio_rdata_cl_ctrl) |
                           ({32{((|mmio_csm_addr_base_en) || (|mmio_per_addr_base_en))}} & mmio_rdata_sys_base);
// CFG registers are read only; write: if cl_enable=0, return error response
assign config_valid_req =    mmio_ren && ((|mmio_cl_grp_clk_en_en) || (|mmio_cl_grp_reset_en) || (|mmio_csm_addr_base_en) || (|mmio_per_addr_base_en))
                          || (|cl_grp_clk_en_wen_valid_req) || (|cl_grp_rst_wen_valid_req) || (|mmio_csm_addr_base_wen_valid_req) || (|mmio_per_addr_base_wen_valid_req)
                          || mmio_AS_CFG_en 
                          || (|mmio_cl_enable_en) ;

assign config_err = mmio_sel_config & !config_valid_req;
assign mmio_resp_config  = {config_err, mmio_sel_config};  
// spyglass disable_block Ac_conv03
// sync DFF converge
assign mmio_rdata = mmio_ren?(({32{mmio_resp_config[0]}} & mmio_rdata_config)  |
// spyglass enable_block Ac_conv03
                              ({32{mmio_resp_gfrc[0]}} & mmio_rdata_gfrc[ARCSYNC_DATA_WIDTH-1:0]) |
                              ({32{mmio_resp_ac[0]}}   & mmio_rdata_ac)  |
                              ({32{mmio_resp_acs[0]}}  & mmio_rdata_acs) |
                              ({32{mmio_resp_eid[0]}}  & mmio_rdata_eid) |
                              ({32{mmio_resp_pmu[0]}}  & mmio_rdata_pmu) |
                              ({32{mmio_resp_sfty[0]}} & mmio_rdata_sfty)|
                              ({32{mmio_resp_map_vm_vproc[0]}} & mmio_rdata_map_vm_vproc)|
                              ({32{mmio_resp_vm_eid[0]}} & mmio_rdata_vm_eid)) 
                            : 'b0; 
assign mmio_resp_ack = (mmio_resp_config[0]) || (mmio_resp_gfrc[0]) ||
                       (mmio_resp_ac[0])     || (mmio_resp_acs[0])  ||
                       (mmio_resp_eid[0])    || (mmio_resp_pmu[0]) || (mmio_resp_sfty[0]) ||
                       (mmio_resp_map_vm_vproc[0]) || (mmio_resp_vm_eid[0]); 
assign mmio_resp_err = (&mmio_resp_config) || (&mmio_resp_gfrc) ||
                       (&mmio_resp_ac)     || (&mmio_resp_acs)  ||
                       (&mmio_resp_eid)    || (&mmio_resp_pmu) || (&mmio_resp_sfty) ||
                       (&mmio_resp_map_vm_vproc) || (&mmio_resp_vm_eid); 

// Generate request to each ARCSync feature
// If it's a 64-b access, it's divide to 2 32-b accesses except GFRC_READ register.
always_comb
begin : mmio_addr_PROC
  mmio_addr_check = 1'b0;
  mmio_addr       = gif_maddr_r[ARCSYNC_ADDR_WIDTH-1:0];
  mmio_wdata      = 32'b0;
  mmio_wdata_nxt  = mmio_wdata_r; 
  mmio_wen        = 1'b0; 
  mmio_wen_nxt    = mmio_wen_r;  
  mmio_ren        = 1'b0; 
  mmio_ren_nxt    = mmio_ren_r; 
  mmio_gfrc_read_64b = 1'b0;

  // Write burst is an invalid request. Send error response.
  if (write_burst_r)
    mmio_addr_check = 1'b0;
  // If the first-half of 64-b access is failed, not send out the second-half
  else if (mmio_st_2ND_REQ_cs && !gif_sresp_r[1])
  begin
    mmio_addr_check = 1'b1;
    mmio_addr       = gif_maddr_r[ARCSYNC_ADDR_WIDTH-1:0];
    mmio_wen        = mmio_wen_r && !mmio_sel_fail;
    mmio_wdata      = mmio_wdata_r;
    mmio_ren        = mmio_ren_r && !mmio_sel_fail;
  end 
  // Send out the request if it accesses one of the feature in ARCSync 
  //else if (gif_saccept && valid_req && (gif_mread || gif_mwrite))
  else if (mmio_st_CHK_COND0_cs && valid_req && (gif_mread_r || gif_mwrite_r))
  begin
    mmio_addr_check = 1'b1;

    // remap the GFRC RD for VMs to the normal GFRC RD addr
    // check that the 4k region matches to a valid VM
    // also check that the register offset within the 4k region matches GFRC LO or HI
    if (ARCSYNC_VIRT_MACHINES>0 &&
        gif_maddr_r[ARCSYNC_ADDR_WIDTH-1:12]>=(ARCSYNC_ADDR_VM0_EID>>12) &&
        gif_maddr_r[ARCSYNC_ADDR_WIDTH-1:12]<=((ARCSYNC_ADDR_VM0_EID>>12)+ARCSYNC_VIRT_MACHINES) &&
        (gif_maddr_r[11:0]==ARCSYNC_VM_GFRC_LO_OFFSET || gif_maddr_r[11:0]==ARCSYNC_VM_GFRC_HI_OFFSET))
    begin
      mmio_addr       = (gif_maddr_r[11:0]==ARCSYNC_VM_GFRC_LO_OFFSET) ? `ADDR_GFRC_READ_LO : `ADDR_GFRC_READ_HI ;
    end
    else
    begin
      mmio_addr       = gif_maddr_r[ARCSYNC_ADDR_WIDTH-1:0];
    end

    mmio_ren        = gif_mread_r  && !mmio_sel_fail;
    mmio_wen        = gif_mwrite_r && !mmio_sel_fail;
    mmio_wdata      = gif_maddr_r[2]? gif_mdata_r[63:32] : gif_mdata_r[31:0];
    mmio_gfrc_read_64b = gif_mread_r && access_gfrc_full;
    // Generate the second-half of 64-b request
    if (access_64b)
    begin  
      mmio_ren_nxt    = gif_mread_r;
      mmio_wen_nxt    = gif_mwrite_r;
      mmio_wdata_nxt  = gif_mdata_r[63:32];
    end  
  end
end // mmio_addr_PROC


assign mmio_AS_CFG_en = mmio_addr_check && ((mmio_addr==`ADDR_AS_BLD_CFG) || (mmio_addr==`ADDR_AS_NUM_CORE_C03) || (mmio_addr==`ADDR_AS_NUM_CORE_C47));

// cluster control register handling
for (genvar i=0; i<CLUSTER_NUM; i++)
begin: cl_control_status_asign_PROC
  assign CL_ENABLE[i] = {31'h0, mmio_cl_enable_r[i]};
  assign CL_GRP_CLK_EN[i] = {17'h0, 2'h0, mmio_cl_grp_clk_en_r[i][3], 2'h0, mmio_cl_grp_clk_en_r[i][2], 2'h0, mmio_cl_grp_clk_en_r[i][1], 2'h0, mmio_cl_grp_clk_en_r[i][0], 3'h0};
  assign CL_GRP_RESET[i] = {17'h0, 2'h0, mmio_cl_grp_rst_r[i][4], 2'h0, mmio_cl_grp_rst_r[i][3], 2'h0, mmio_cl_grp_rst_r[i][2], 2'h0, mmio_cl_grp_rst_r[i][1], 2'h0, mmio_cl_grp_rst_r[i][0]};
  assign CL_SM_ADDR_BASE[i] = {8'h0, mmio_csm_addr_base_r[i]};
  assign CL_PERIPH_ADDR_BASE[i] = {8'h0, mmio_per_addr_base_r[i]};
end: cl_control_status_asign_PROC

always_comb
begin: cluster_control_PROC
  logic [ARCSYNC_ADDR_WIDTH-1:0]  addr_cl_enable_base_addr;
  logic [ARCSYNC_ADDR_WIDTH-1:0]  addr_cl_grp_clk_en_base_addr;
  logic [ARCSYNC_ADDR_WIDTH-1:0]  addr_cl_grp_reset_base_addr;
  for (int unsigned i=0;i<CLUSTER_NUM; i++)
  begin: cl_control_base_addr_PROC

    addr_cl_enable_base_addr     = ADDR_CL_ENABLE     + 4*i;
    addr_cl_grp_clk_en_base_addr = ADDR_CL_GRP_CLK_EN + 4*i;
    addr_cl_grp_reset_base_addr  = ADDR_CL_GRP_RESET  + 4*i;
    // The request access cluster_control
    mmio_cl_enable_en[i] = mmio_addr_check && (mmio_addr==addr_cl_enable_base_addr);
    mmio_cl_grp_clk_en_en[i] = mmio_addr_check && (mmio_addr==addr_cl_grp_clk_en_base_addr);
    mmio_cl_grp_reset_en[i] = mmio_addr_check && (mmio_addr==addr_cl_grp_reset_base_addr);

    cl_enable_set[i] = mmio_cl_enable_en[i] && mmio_wen && (mmio_wdata[31:16] == 16'h5A5A) && (mmio_wdata[0] == 1'h1);
    cl_enable_clr[i] = mmio_cl_enable_en[i] && mmio_wen && (mmio_wdata[31:16] == 16'h5A5A) && (mmio_wdata[0] == 1'h0);

    // write {0x5A5A, grp_id} to disable group clock. write {0xA5A5, grp_id} to enable group clock.
    cl_grp_clk_en_set[i] = mmio_cl_grp_clk_en_en[i] && mmio_wen && cl_enable[i] && (mmio_wdata[31:16] == 16'hA5A5);
    cl_grp_clk_en_clr[i] = mmio_cl_grp_clk_en_en[i] && mmio_wen && cl_enable[i] && (mmio_wdata[31:16] == 16'h5A5A);

    cl_grp_clk_en_wen_valid_req[i] = mmio_cl_grp_clk_en_en[i] && mmio_wen && cl_enable[i] && 
                                     ((mmio_wdata[31:16] == 16'hA5A5) || (mmio_wdata[31:16] == 16'h5A5A)) &&
                                     ((mmio_wdata[5:3]==3'h1) || (mmio_wdata[8:6]==3'h2) || (mmio_wdata[11:9]==3'h3) || (mmio_wdata[14:12]==3'h4));

    // write {0x5A5A, grp_id} to assert reset. write {0xA5A5, grp_id} to de-assert reset.
    cl_grp_rst_set[i] = mmio_cl_grp_reset_en[i] && mmio_wen && cl_enable[i] && (mmio_wdata[31:16] == 16'h5A5A); 
    cl_grp_rst_clr[i] = mmio_cl_grp_reset_en[i] && mmio_wen && cl_enable[i] && (mmio_wdata[31:16] == 16'hA5A5);

    cl_grp_rst_wen_valid_req[i] = mmio_cl_grp_reset_en[i] && mmio_wen && cl_enable[i] && 
                                  ((mmio_wdata[31:16] == 16'h5A5A) || (mmio_wdata[31:16] == 16'hA5A5)) &&
                                  ((mmio_wdata[2:0]==3'h5) || (mmio_wdata[5:3]==3'h1) || (mmio_wdata[8:6]==3'h2) || (mmio_wdata[11:9]==3'h3) || (mmio_wdata[14:12]==3'h4));

    mmio_csm_addr_base_wen_valid_req[i]= mmio_csm_addr_base_en[i] & mmio_wen && cl_enable[i];
    mmio_per_addr_base_wen_valid_req[i]= mmio_per_addr_base_en[i] & mmio_wen && cl_enable[i];

  end: cl_control_base_addr_PROC
end: cluster_control_PROC

// update the cluster control register if it's written


always_comb
begin : cluster_control_upd_PROC
  for (int unsigned i=0;i<CLUSTER_NUM; i++)
  begin: cluster_control_upd_per_cl
    mmio_cl_enable_nxt[i] = mmio_cl_enable_r[i];
    mmio_cl_grp_clk_en_nxt[i] = mmio_cl_grp_clk_en_r[i];
    mmio_cl_grp_rst_nxt[i] = mmio_cl_grp_rst_r[i];

    if (cl_enable_set[i])
      mmio_cl_enable_nxt[i] = 1'b1;
    else if (cl_enable_clr[i])
      mmio_cl_enable_nxt[i] = 1'b0;

    if (cl_grp_clk_en_set[i] && (mmio_wdata[5:3]==3'h1) && npx_L1_grp_exist[i][0])
      mmio_cl_grp_clk_en_nxt[i][0] = 1'b1;
    else if (cl_grp_clk_en_clr[i] & (mmio_wdata[5:3]==3'h1) && npx_L1_grp_exist[i][0])
      mmio_cl_grp_clk_en_nxt[i][0] = 1'b0;

    if (cl_grp_clk_en_set[i] && (mmio_wdata[8:6]==3'h2) && npx_L1_grp_exist[i][1])
      mmio_cl_grp_clk_en_nxt[i][1] = 1'b1;
    else if (cl_grp_clk_en_clr[i] & (mmio_wdata[8:6]==3'h2) && npx_L1_grp_exist[i][1])
      mmio_cl_grp_clk_en_nxt[i][1] = 1'b0;

    if (cl_grp_clk_en_set[i] && (mmio_wdata[11:9]==3'h3) && npx_L1_grp_exist[i][2])
      mmio_cl_grp_clk_en_nxt[i][2] = 1'b1;
    else if (cl_grp_clk_en_clr[i] & (mmio_wdata[11:9]==3'h3) && npx_L1_grp_exist[i][2])
      mmio_cl_grp_clk_en_nxt[i][2] = 1'b0;

    if (cl_grp_clk_en_set[i] && (mmio_wdata[14:12]==3'h4) && npx_L1_grp_exist[i][3])
      mmio_cl_grp_clk_en_nxt[i][3] = 1'b1;
    else if (cl_grp_clk_en_clr[i] & (mmio_wdata[14:12]==3'h4) && npx_L1_grp_exist[i][3])
      mmio_cl_grp_clk_en_nxt[i][3] = 1'b0;

    if (cl_grp_rst_set[i] & (mmio_wdata[2:0]==3'h5) & npx_L2_grp_exist[i])
      mmio_cl_grp_rst_nxt[i][0] = 1'b1;
    else if (cl_grp_rst_clr[i] & (mmio_wdata[2:0]==3'h5) & npx_L2_grp_exist[i])
      mmio_cl_grp_rst_nxt[i][0] = 1'b0;

    if (cl_grp_rst_set[i] & (mmio_wdata[5:3]==3'h1) & npx_L1_grp_exist[i][0])
      mmio_cl_grp_rst_nxt[i][1] = 1'b1;
    else if (cl_grp_rst_clr[i] & (mmio_wdata[5:3]==3'h1) & npx_L1_grp_exist[i][0])
      mmio_cl_grp_rst_nxt[i][1] = 1'b0;

    if (cl_grp_rst_set[i] & (mmio_wdata[8:6]==3'h2) & npx_L1_grp_exist[i][1])
      mmio_cl_grp_rst_nxt[i][2] = 1'b1;
    else if (cl_grp_rst_clr[i] & (mmio_wdata[8:6]==3'h2) & npx_L1_grp_exist[i][1])
      mmio_cl_grp_rst_nxt[i][2] = 1'b0;

    if (cl_grp_rst_set[i] & (mmio_wdata[11:9]==3'h3) & npx_L1_grp_exist[i][2])
      mmio_cl_grp_rst_nxt[i][3] = 1'b1;
    else if (cl_grp_rst_clr[i] & (mmio_wdata[11:9]==3'h3) & npx_L1_grp_exist[i][2])
      mmio_cl_grp_rst_nxt[i][3] = 1'b0;

    if (cl_grp_rst_set[i] & (mmio_wdata[14:12]==3'h4) & npx_L1_grp_exist[i][3])
      mmio_cl_grp_rst_nxt[i][4] = 1'b1;
    else if (cl_grp_rst_clr[i] & (mmio_wdata[14:12]==3'h4) & npx_L1_grp_exist[i][3])
      mmio_cl_grp_rst_nxt[i][4] = 1'b0;
  end: cluster_control_upd_per_cl
end : cluster_control_upd_PROC



// csm/per sys base address handling
// set these group of register as part of mmio_sel_config
// if the request accesses the sys_base_addr register
// assert corresponding enable signal   
always_comb
begin : base_addr_PROC
  logic [ARCSYNC_ADDR_WIDTH-1:0]  addr_csm_base_addr; 
  logic [ARCSYNC_ADDR_WIDTH-1:0]  addr_per_base_addr; 
  for (int unsigned i=0;i<CLUSTER_NUM; i++)
  begin: base_addr_per_cl
    addr_csm_base_addr = ADDR_CSM_ADDR_BASE + 4*i;      
    addr_per_base_addr = ADDR_CL_PERIPH_ADDR_BASE + 4*i;
    // The request access CSM_CASE_ADDR
    mmio_csm_addr_base_en[i] = mmio_addr_check && (mmio_addr==addr_csm_base_addr);
    mmio_per_addr_base_en[i] = mmio_addr_check && (mmio_addr==addr_per_base_addr);
  end: base_addr_per_cl  
end : base_addr_PROC
// update the base address register if it's written
always_comb
begin : base_addr_upd_PROC
  for (int unsigned i=0;i<CLUSTER_NUM; i++)
  begin: base_addr_upd_per_cl
    mmio_csm_addr_base_nxt[i] = mmio_csm_addr_base_r[i];
    mmio_per_addr_base_nxt[i] = mmio_per_addr_base_r[i];
    if (mmio_csm_addr_base_wen_valid_req[i]) 
      mmio_csm_addr_base_nxt[i] = mmio_wdata[23:0];

    if (mmio_per_addr_base_wen_valid_req[i]) 
      mmio_per_addr_base_nxt[i] = mmio_wdata[23:0];
  end: base_addr_upd_per_cl
end : base_addr_upd_PROC

// get the base address and cluster control register value 
always_comb
begin : base_addr_cl_ctrl_read_PROC
  mmio_rdata_sys_base  = 32'h0;
  mmio_rdata_cl_ctrl = 32'h0;

  for (int unsigned i=0;i<CLUSTER_NUM; i++)
  begin: base_addr_cl_ctrl_read_per_cl
    arcsync_core_csm_addr_base[i] = mmio_csm_addr_base_r[i][BASE_ADDR_WIDTH-1-16:0];
    arcsync_core_periph_addr_base[i] = mmio_per_addr_base_r[i][BASE_ADDR_WIDTH-1-16:0];
    cl_enable[i]     = mmio_cl_enable_r[i];
    cl_grp_clk_en[i] = mmio_cl_grp_clk_en_r[i];
    cl_grp_rst[i]    = mmio_cl_grp_rst_r[i];

    if (((|mmio_csm_addr_base_en) || (|mmio_per_addr_base_en)) 
        && mmio_ren) 
      mmio_rdata_sys_base = mmio_rdata_sys_base | ({32{mmio_csm_addr_base_en[i]}} & CL_SM_ADDR_BASE[i])   
                          | ({32{mmio_per_addr_base_en[i]}} & CL_PERIPH_ADDR_BASE[i]);

    if ((|mmio_cl_enable_en) || (|mmio_cl_grp_clk_en_en) || (|mmio_cl_grp_reset_en ) && mmio_ren)
      mmio_rdata_cl_ctrl = mmio_rdata_cl_ctrl
                          | ({32{mmio_cl_enable_en[i]}} & CL_ENABLE[i])
                          | ({32{mmio_cl_grp_clk_en_en[i]}} & CL_GRP_CLK_EN[i])
                          | ({32{mmio_cl_grp_reset_en[i]}} & CL_GRP_RESET[i]);
  end: base_addr_cl_ctrl_read_per_cl
end : base_addr_cl_ctrl_read_PROC


if (ARCSYNC_VIRT_MACHINES>0)
begin: ADDR_VM_gen_PROC
  logic [ARCSYNC_VIRT_MACHINES-1:0] VM_EID_valid_range_tmp;
  logic [ARCSYNC_VIRT_MACHINES-1:0][ARCSYNC_ADDR_WIDTH-1:0] ADDR_VM_EID_SEND_EVENT_0  ;
  logic [ARCSYNC_VIRT_MACHINES-1:0][ARCSYNC_ADDR_WIDTH-1:0] ADDR_VM_EID_SEND_EVENT_MAX;
  logic [ARCSYNC_VIRT_MACHINES-1:0][ARCSYNC_ADDR_WIDTH-1:0] ADDR_VM_EID_RAISE_IRQ_0   ;
  logic [ARCSYNC_VIRT_MACHINES-1:0][ARCSYNC_ADDR_WIDTH-1:0] ADDR_VM_EID_ACK_IRQ_MAX   ;

  logic [ARCSYNC_VIRT_MACHINES-1:0] VM_AC_valid_range_tmp;
  logic [ARCSYNC_VIRT_MACHINES-1:0][ARCSYNC_ADDR_WIDTH-1:0] ADDR_VM_AC_NOTIFY_SRC;
  logic [ARCSYNC_VIRT_MACHINES-1:0][ARCSYNC_ADDR_WIDTH-1:0] ADDR_VM_AC_MAX;
  always_comb
  begin : mmio_vm_eid_PROC
    for (int unsigned i = 0; i<ARCSYNC_VIRT_MACHINES; i++)
    begin: mmio_sel_vm_eid
      ADDR_VM_EID_SEND_EVENT_0[i]   = ADDR_VM0_EID_SEND_EVENT_0 + (i * 4096);
      ADDR_VM_EID_SEND_EVENT_MAX[i] = ADDR_VM0_EID_SEND_EVENT_MAX + (i * 4096);
      ADDR_VM_EID_RAISE_IRQ_0[i]    = ADDR_VM0_EID_RAISE_IRQ_0 + (i * 4096);
      ADDR_VM_EID_ACK_IRQ_MAX[i]    = ADDR_VM0_EID_ACK_IRQ_MAX + (i * 4096);

      ADDR_VM_AC_NOTIFY_SRC[i]      = ADDR_VM0_AC_NOTIFY_SRC + (i * 4096);
      ADDR_VM_AC_MAX[i]             = ADDR_VM0_AC_MAX + (i * 4096);

      VM_EID_valid_range_tmp[i] = mmio_addr_check && (((mmio_addr >= ADDR_VM_EID_SEND_EVENT_0[i]) && (mmio_addr < ADDR_VM_EID_SEND_EVENT_MAX[i])) || 
                                                      ((mmio_addr >= ADDR_VM_EID_RAISE_IRQ_0[i])  && (mmio_addr < ADDR_VM_EID_ACK_IRQ_MAX[i])));

      VM_AC_valid_range_tmp[i] = mmio_addr_check && ((mmio_addr >= ADDR_VM_AC_NOTIFY_SRC[i]) && (mmio_addr < ADDR_VM_AC_MAX[i]));
    end : mmio_sel_vm_eid
  end : mmio_vm_eid_PROC

  assign mmio_sel_VM_EID_valid_range = |VM_EID_valid_range_tmp;
  assign mmio_sel_VM_AC_valid_range  = |VM_AC_valid_range_tmp;
end: ADDR_VM_gen_PROC
else
begin: sel_VM_asign0_PROC
  always_comb
  begin
    mmio_sel_VM_EID_valid_range = 1'b0;
    mmio_sel_VM_AC_valid_range  = 1'b0;
  end
end: sel_VM_asign0_PROC

// Request destination check
// 1st round classification
// Based on the mmio_addr, check the destination for the request
// If this is an undefined address, send error back
// 2nd round classification
// This is handled by each feature.
// If the address is for an undefined core, send error back
always_comb
begin : mmio_sel_PROC
  mmio_sel_config = 1'b0;
  mmio_sel_gfrc   = 1'b0; 
  mmio_sel_pmu    = 1'b0;
  mmio_sel_sfty    = 1'b0;   
  mmio_sel_acs    = 1'b0; 
  mmio_sel_eid    = 1'b0; 
  mmio_sel_ac     = 1'b0;
  mmio_sel_map_vm_vproc = 1'b0;
  mmio_sel_vm_eid = 1'b0;
  // check destination for mmio_addr 
  if (mmio_addr_check)
  begin
    if ((mmio_addr >= ARCSYNC_ADDR_CONFIG && mmio_addr <= ARCSYNC_ADDR_CONFIG_MAX)
       || (mmio_addr >= ADDR_CL_ENABLE && mmio_addr <= ADDR_CL_CONTROL_MAX)
       || (|mmio_csm_addr_base_en) || (|mmio_per_addr_base_en))
      mmio_sel_config = 1'b1;
    if (mmio_addr >= ARCSYNC_ADDR_GFRC && mmio_addr <= ARCSYNC_ADDR_GFRC_MAX)
      mmio_sel_gfrc = 1'b1;
    if ((mmio_addr >= ARCSYNC_ADDR_PMU_REGION_0 && mmio_addr <= ARCSYNC_ADDR_PMU_REGION_0_MAX) ||
        (mmio_addr >= ARCSYNC_ADDR_PMU_REGION_1 && mmio_addr <= ARCSYNC_ADDR_PMU_REGION_1_MAX))
      mmio_sel_pmu = 1'b1;
    if (mmio_addr >= ARCSYNC_ADDR_SFTY && mmio_addr <= ARCSYNC_ADDR_SFTY_MAX)
      mmio_sel_sfty = 1'b1; 
    if (mmio_addr >= ARCSYNC_ADDR_ACS && mmio_addr <= ARCSYNC_ADDR_ACS_MAX)
      mmio_sel_acs = 1'b1;
    // Currently, we only support one event and one irq so the format cannot be the same as others
    // else if (mmio_addr >= `ARCSYNC_ADDR_EID && mmio_addr <= `ARCSYNC_ADDR_EID_MAX)
    if ((mmio_addr >= ADDR_EID_SEND_EVENT_0 && mmio_addr < ADDR_EID_SEND_EVENT_MAX) || 
        (mmio_addr >= ADDR_EID_RAISE_IRQ_0  && mmio_addr < ADDR_EID_ACK_IRQ_MAX))
      mmio_sel_eid = 1'b1;
    if ((mmio_addr >= ARCSYNC_ADDR_AC && mmio_addr <= ARCSYNC_ADDR_AC_MAX) || 
        (mmio_addr >= ADDR_AC_CONFIG  && mmio_addr <= ADDR_AC_CONFIG_MAX) || 
        (mmio_addr >= ADDR_AC_CONTROL && mmio_addr <= ADDR_AC_CONTROL_MAX) ||
        mmio_sel_VM_AC_valid_range)
      mmio_sel_ac = 1'b1;
    if ((mmio_addr >= ARCSYNC_ADDR_VM_CONFIG) && (mmio_addr <= ARCSYNC_ADDR_VM_CONFIG_MAX)) // select MAP_VMx_VPROC table
      mmio_sel_map_vm_vproc = 1'b1;
    if (mmio_sel_VM_EID_valid_range)
      mmio_sel_vm_eid = 1'b1;
  end
end // mmio_sel_PROC  
assign mmio_sel_fail = mmio_addr_check && !mmio_sel_config && !mmio_sel_gfrc && !mmio_sel_pmu && !mmio_sel_sfty && !mmio_sel_acs && !mmio_sel_eid && !mmio_sel_ac && !mmio_sel_map_vm_vproc && !mmio_sel_vm_eid;

assign gif_svalid  = gif_svalid_r;
assign gif_sresp   = gif_sresp_r;
assign gif_sdata   = gif_sdata_r;

// ----------------------------------------------------------
//  MMIO operation state machine
// ----------------------------------------------------------

assign get_gif_m = (mmio_st_IDLE_cs | mmio_st_RESP_cs) & (gif_mread || gif_mwrite);
assign incr_gif_maddr_r = (mmio_st_CHK_COND0_cs && cond1 && access_64b) |
                          (mmio_st_WAIT_cs && mmio_resp_ack && access_64b);

always_ff @(posedge clk or posedge rst_a)
begin: gif_m_ff_PROC
  if (rst_a) 
  begin
    gif_maddr_r     <= {`ARCSYNC_REG_GS_AW{1'b0}};
    gif_mread_r     <= 1'b0;
    gif_mwrite_r    <= 1'b0;
    gif_msize_r     <= 3'h0;
    gif_mburst_r    <= 2'h0;
    gif_mlen_r      <= {`ARCSYNC_REG_GS_BW{1'b0}};
    gif_mlast_r     <= 1'b0;
    gif_mdata_r     <= {`ARCSYNC_REG_GS_DW{1'b0}};
    gif_mwstrb_r    <= {(`ARCSYNC_REG_GS_DW/8){1'b0}};
  end
  else if (get_gif_m)
  begin
    gif_maddr_r     <= gif_maddr; 
    gif_mread_r     <= gif_mread; 
    gif_mwrite_r    <= gif_mwrite;
    gif_msize_r     <= gif_msize; 
    gif_mburst_r    <= gif_mburst;
    gif_mlen_r      <= gif_mlen;  
    gif_mlast_r     <= gif_mlast; 
    gif_mdata_r     <= gif_mdata; 
    gif_mwstrb_r    <= gif_mwstrb;
  end
  else if (incr_gif_maddr_r)
  begin
    gif_maddr_r     <= gif_maddr_r + 32'd4;
  end
end

assign mmio_st_IDLE_cs      = (mmio_st_r==S_IDLE    );
assign mmio_st_CHK_COND0_cs = (mmio_st_r==S_CHK_COND0);
assign mmio_st_RESP_cs      = (mmio_st_r==S_RESP    );
assign mmio_st_2ND_REQ_cs   = (mmio_st_r==S_2ND_REQ );
assign mmio_st_WAIT_cs      = (mmio_st_r==S_WAIT    );
assign cond1 = mmio_resp_ack || mmio_sel_fail || (!valid_req);

always_comb
begin : mmio_fsm_PROC
  mmio_st_nxt = mmio_st_r;
  gif_saccept = 1'b1;
  gif_svalid_nxt  = gif_svalid_r;
  gif_sresp_nxt   = gif_sresp_r;
  gif_sdata_nxt   = gif_sdata_r;
  write_burst_nxt = write_burst_r;
  access_64b_nxt = access_64b_r;

  case (mmio_st_r)
    S_IDLE, S_RESP:
    begin
      // Write burst is an invalid request, send error
      if (write_burst_r)
      begin
        if (gif_mlast && gif_mwrite)
        begin
          write_burst_nxt = 1'b0;
          gif_svalid_nxt = 1'b1;
          mmio_st_nxt = S_IDLE;
        end  
      end
      // not accept new request if the old one is on-going
      else if (gif_svalid && !gif_mready)
        gif_saccept = 1'b0;
      else 
      begin   
        if (gif_mread || gif_mwrite)
        begin
          mmio_st_nxt = S_CHK_COND0;
          gif_svalid_nxt = 'b0;
        end  
        else 
        begin
          mmio_st_nxt = S_IDLE;
          gif_svalid_nxt = 'b0;
          gif_sresp_nxt  = 'b0;
          gif_sdata_nxt  = 'b0;
        end  
      end
    end

    // check gif_m*
    S_CHK_COND0:
    begin
      gif_saccept = 1'b0;

      // Send error back to that request, if
      // 1. It's an invalid request, including burst access 
      // 2. Requests is to those registers which don’t exist with undefined core index or undefined address. (e.g. one cluster is with 3 core but the request is to the 4th core)
      // 3. Return error to a 64-b access, if the first part is done successfully but the second part is fail. (note: the first part of write request is written to the register)
      // 4. The feature module returns an error to that request
      gif_sresp_nxt = {(mmio_sel_fail || !valid_req || mmio_resp_err), gif_mwrite_r};
      write_burst_nxt = write_burst;
      if (cond1)
      begin  
        gif_sdata_nxt = gif_maddr_r[2] ? {mmio_rdata, 32'b0} : {32'b0, mmio_rdata};
        gif_svalid_nxt = !write_burst;
        // handling second-half of 64-b access
        if (access_64b)
        begin  
          mmio_st_nxt = S_2ND_REQ; 
          gif_svalid_nxt = 1'b0;
        end  
        else
        begin
          // only GFRC_READ register could be accessed with 64-b request directly 
          if (access_gfrc_full) 
            gif_sdata_nxt[AXI_DATA_WIDTH-1:ARCSYNC_DATA_WIDTH] = mmio_rdata_gfrc_hi;
          mmio_st_nxt = S_RESP;
        end 
      end
      else 
      begin
        access_64b_nxt = access_64b;
        mmio_st_nxt = S_WAIT;
        gif_svalid_nxt = 1'b0;
      end  
    end

    // handling second-half of 64-b access
    S_2ND_REQ:
    begin
      gif_saccept = 1'b0;
      if (mmio_resp_ack || mmio_sel_fail || gif_sresp_r[1])
      begin  
        mmio_st_nxt = S_RESP;
        gif_svalid_nxt = 1'b1;
        gif_sresp_nxt  = gif_sresp_r | {(mmio_sel_fail || mmio_resp_err), 1'b0};
        gif_sdata_nxt[AXI_DATA_WIDTH-1:ARCSYNC_DATA_WIDTH] = mmio_sel_fail? {ARCSYNC_DATA_WIDTH{1'b0}}: mmio_rdata;
      end 
      else 
      begin  
        mmio_st_nxt = S_WAIT; 
        access_64b_nxt = 1'b0;
      end 
    end

    S_WAIT:
    begin
      gif_saccept = 1'b0;
      if (mmio_resp_ack)
      begin  
        gif_sdata_nxt = gif_maddr_r[2] ? {mmio_rdata, 32'b0} : {32'b0, mmio_rdata};
        gif_svalid_nxt = 1'b1;
        // handling second-half of 64-b access
        if (access_64b)
        begin  
          mmio_st_nxt = S_2ND_REQ; 
          gif_svalid_nxt = 1'b0;
        end 
        else 
          mmio_st_nxt = S_RESP;
      end  
    end  
    default : 
      mmio_st_nxt = S_IDLE;
  endcase
end // mmio_fsm_PROC

assign mmio_reg_en     =  (mmio_st_r != mmio_st_nxt) ||  (gif_mread || gif_mwrite) || gif_svalid_r;


assign mmio_cl_ctrl_wen = mmio_wen & ((|mmio_cl_enable_en) || (|mmio_cl_grp_clk_en_en) || (|mmio_cl_grp_reset_en));
assign mmio_sys_base_wen= mmio_wen & (((|mmio_csm_addr_base_en) || (|mmio_per_addr_base_en)));

always_ff @(posedge clk or posedge rst_a)
begin : mmio_ff_PROC
  if (rst_a) 
  begin
    gif_svalid_r <= 'b0;
    gif_sresp_r  <= 'b0;
    gif_sdata_r  <= 'b0;
    mmio_st_r    <= S_IDLE;
    mmio_wen_r   <= 'b0;
    mmio_wdata_r <= 'b0;
    mmio_ren_r   <= 'b0;
    write_burst_r<= 'b0;
    access_64b_r <= 'b0;
    mmio_cl_enable_r <= {CLUSTER_NUM{1'b1}};

    for (int i=0;i<CLUSTER_NUM; i++) // {
    begin
      mmio_cl_grp_rst_r[i][0] <= npx_L2_grp_exist[i];
      for (int j=0;j<4; j++) // {
      begin
        mmio_cl_grp_clk_en_r[i][j] <= npx_L1_grp_exist[i][j] & CL_GRP_CLK_EN_RST;
        mmio_cl_grp_rst_r[i][j+1] <= npx_L1_grp_exist[i][j];
      end // }
    end // }

    for (int i=0;i<CLUSTER_NUM; i++)
    begin
      mmio_csm_addr_base_r[i] <= {{BASE_ADDR_WIDTH-24{1'b0}}, `ARCSYNC_CSM_INIT_BASE};
      mmio_per_addr_base_r[i] <= {{BASE_ADDR_WIDTH-24{1'b0}}, `ARCSYNC_PERIPH_INIT_BASE};
    end
  end
  else
  begin
    if (mmio_reg_en)  
    begin  
      gif_svalid_r <= gif_svalid_nxt;
      gif_sresp_r  <= gif_sresp_nxt;
      gif_sdata_r  <= gif_sdata_nxt;
      mmio_st_r    <= mmio_st_nxt;
      mmio_wen_r   <= mmio_wen_nxt;
      mmio_wdata_r <= mmio_wdata_nxt;
      mmio_ren_r   <= mmio_ren_nxt;
      write_burst_r<= write_burst_nxt;
      access_64b_r <= access_64b_nxt;
    end  

    if (mmio_sys_base_wen)
    begin
      for (int i=0;i<CLUSTER_NUM; i++)
      begin
        mmio_csm_addr_base_r[i] <= mmio_csm_addr_base_nxt[i];
        mmio_per_addr_base_r[i] <= mmio_per_addr_base_nxt[i];
      end
    end

    if (mmio_cl_ctrl_wen)
    begin
      mmio_cl_enable_r <= mmio_cl_enable_nxt;
      mmio_cl_grp_clk_en_r <= mmio_cl_grp_clk_en_nxt;
      mmio_cl_grp_rst_r <= mmio_cl_grp_rst_nxt;
    end

  end
end  // mmio_ff_PROC  

//-------------------------------------------------------------------------------------------------------
// Properties
//-------------------------------------------------------------------------------------------------------
`ifdef FORMAL_ASSERT_ON
  `include "prop_arcsync_axi2reg.sv"
`endif
endmodule
