`include "nl2_cln_defines.v"

module nl2_new_dbank_axi2bnk
  #(
    parameter CMD_ID_SIZE    = 1,   // legal range: >= 1
    parameter WR_ID_SIZE     = 1,   // legal range: >= 1
    parameter CMD_ADDR_SIZE  = 32,  // legal range: >= 1
    parameter DATA_SIZE      = 128, // legal range: >= 8, power of 2
    parameter MULTICAST_SIZE = 1,    // legal range: >= 1
    parameter CTRL_CHANNELS  = 0,
    parameter BNK_ADDR_SIZE  = `nl2_CFG_BNK_ADDR_SIZE,
    parameter BNK_DATA_WIDTH = `nl2_DBANK_DATA_WIDTH,
    parameter BNK_IN_DATA_PIPE = 1,
    localparam BNK_ECC_ENABLE  = 1,
    // Extra bits
    // 1. Memory intialization
    // 2. scrub_enable   
    // 3. ecc_error
    // 4. wrap
    // 5. read
    // 6. excl
    // 7. excl_err
    localparam BNK_CMD_FW_SIZE = BNK_ADDR_SIZE + `nl2_CLN_CMD_BURST_SIZE + CMD_ID_SIZE + BNK_ECC_ENABLE + `nl2_IBP_CMD_DATA_SIZE + 7,
    localparam BNK_RD_FW_SIZE  = 5 + BNK_DATA_WIDTH + CMD_ID_SIZE, // {cmd_id, rd_ecc_dbe, rd_ecc_sbe,rd_last,rd_excl_ok,rd_data}
    localparam BNK_WR_FW_SIZE  = BNK_DATA_WIDTH/8 + BNK_DATA_WIDTH,  // {wr_data_mask, wr_data}
    localparam BNK_WRSP_FW_SIZE = WR_ID_SIZE + 3,  //{last, wr_id, dbe, sbe/wr_excl_okay}
//    localparam OUTSTANDING_ADR = $clog2(`CFG_TXC),
    localparam OUTSTANDING_ADR = 4 //FIXME
    )
(
input  logic                      axi_arvalid,
output logic                      axi_arready,
input  logic    [CMD_ID_SIZE-1:0] axi_arid,          
input  logic  [CMD_ADDR_SIZE-1:0] axi_araddr,
input  logic                [2:0] axi_arsize,
input  logic [`nl2_AXI_CMD_BURST_RNG] axi_arlen,
input  logic                [1:0] axi_arburst,
input  logic                      axi_arlock,
input  logic                [2:0] axi_arprot,
input  logic                [3:0] axi_arcache,
input  logic      [`nl2_AXI_USER_RNG] axi_aruser,
// Write command channel:
input  logic                      axi_awvalid,
output logic                      axi_awready,
input  logic     [WR_ID_SIZE-1:0] axi_awid,          
input  logic  [CMD_ADDR_SIZE-1:0] axi_awaddr,
input  logic                [2:0] axi_awsize,
input  logic [`nl2_AXI_CMD_BURST_RNG] axi_awlen,
input  logic                [1:0] axi_awburst,
input  logic                      axi_awlock,
input  logic                [2:0] axi_awprot,
input  logic                [3:0] axi_awcache,
input  logic      [`nl2_AXI_USER_RNG] axi_awuser,
// Read data channel:
output logic                      axi_rvalid,
input  logic                      axi_rready,
output logic      [DATA_SIZE-1:0] axi_rdata,
output logic                      axi_rlast,
output logic                [1:0] axi_rresp,
output logic    [CMD_ID_SIZE-1:0] axi_rid,
// write data channel:
input  logic                      axi_wvalid,
output logic                      axi_wready,
input  logic      [DATA_SIZE-1:0] axi_wdata,
input  logic    [DATA_SIZE/8-1:0] axi_wstrb,
input  logic                      axi_wlast,
// write response channel:
output logic     [WR_ID_SIZE-1:0] axi_bid,
output logic                      axi_bvalid,
output logic                [1:0] axi_bresp,
input  logic                      axi_bready,

// Bank command channel from dbank_bottom:
output                               phy_bnk_cmd_valid[2],
output         [BNK_CMD_FW_SIZE-1:0] phy_bnk_cmd_data[2],
input                                phy_bnk_cmd_accept[2],

// Bank write data channel from dbank_bottom:
output                               phy_bnk_wr_valid[1+CTRL_CHANNELS],
output          [BNK_WR_FW_SIZE-1:0] phy_bnk_wr_data[1+CTRL_CHANNELS],
input    logic                       phy_bnk_wr_accept[1+CTRL_CHANNELS],
// Bank read data channel to dbank_bottom:
input                                phy_bnk_rd_valid[1+CTRL_CHANNELS],
input           [BNK_RD_FW_SIZE-1:0] phy_bnk_rd_data[1+CTRL_CHANNELS],
output                               phy_bnk_rd_accept[1+CTRL_CHANNELS],
// Bank write response channel to dbank_bottom:
input                                phy_bnk_rsp_valid,
input         [BNK_WRSP_FW_SIZE-1:0] phy_bnk_rsp_data,
output                               phy_bnk_rsp_accept,

input logic                    [1:0] excl_err,
input logic                          cmd_ecc_enable,
input logic                          cmd_scrub_enable,
output logic                       init_done,
input  logic                       init_start,
input  logic                       disable_rst_init,
////////////////////////////////////////////////////////////////////////////////
// Misc:
input                             slv_ready,
input                             axi_clk,
input                             rst_a
);

/////////////////////////////////////////////////////////////////////////////////
//
// DEV command interface
logic                              ibp_cmd_valid[2];
logic                              ibp_cmd_accept[2];
logic            [CMD_ID_SIZE-1:0] ibp_cmd_id[2];
logic          [CMD_ADDR_SIZE-1:0] ibp_cmd_addr[2];
logic                              ibp_cmd_read[2];
logic                        [1:0] ibp_cmd_ar[2];  
logic                        [1:0] ibp_cmd_atomic[2];
logic         [`nl2_IBP_CMD_SPACE_RNG] ibp_cmd_space[2];
logic                              ibp_cmd_wrap[2];
logic                              ibp_cmd_fixed[2];
logic                        [2:0] ibp_cmd_data_size[2];
logic         [`nl2_CLN_CMD_BURST_RNG] ibp_cmd_burst_size[2];
logic                              ibp_cmd_excl[2];
logic                        [1:0] ibp_cmd_prot[2];
logic                        [3:0] ibp_cmd_cache[2];
logic                        [3:0] ibp_cmd_snoop[2];
logic                        [1:0] ibp_cmd_domain[2];
logic                        [2:0] ibp_cmd_rdomid[2];
// DEV write interface
logic                              ibp_wr_valid;
logic                              ibp_wr_accept;
logic          [DATA_SIZE-1:0]     ibp_wr_data;
logic          [DATA_SIZE/8-1:0]   ibp_wr_mask;
logic                              ibp_wr_last;
// DEV write response interface
logic                              ibp_wr_done;
logic                              ibp_wr_excl_okay;
logic                        [1:0] ibp_wr_bresp;
logic             [WR_ID_SIZE-1:0] ibp_wr_id;
logic                              ibp_wr_resp_accept;
// DEV read interface
logic                              ibp_rd_valid;
logic                              ibp_rd_accept;
logic              [DATA_SIZE-1:0] ibp_rd_data;
logic                              ibp_rd_last;
logic                              ibp_rd_excl_ok;
logic            [CMD_ID_SIZE-1:0] ibp_rd_id;
logic                              ibp_rd_sbe;
logic                              ibp_rd_dbe;
logic                              ibp_rd_err;


logic                      axi_arvalid_r;
logic    [CMD_ID_SIZE-1:0] axi_arid_r;          
logic  [CMD_ADDR_SIZE-1:0] axi_araddr_r;
logic                [2:0] axi_arsize_r;
logic [`nl2_AXI_CMD_BURST_RNG] axi_arlen_r;
logic                [1:0] axi_arburst_r;
logic                      axi_arlock_r;
logic                [2:0] axi_arprot_r;
logic                [3:0] axi_arcache_r;
logic      [`nl2_AXI_USER_RNG] axi_aruser_r;

logic                      axi_awvalid_r;
logic     [WR_ID_SIZE-1:0] axi_awid_r;          
logic  [CMD_ADDR_SIZE-1:0] axi_awaddr_r;
logic                [2:0] axi_awsize_r;
logic [`nl2_AXI_CMD_BURST_RNG] axi_awlen_r;
logic                [1:0] axi_awburst_r;
logic                      axi_awlock_r;
logic                [2:0] axi_awprot_r;
logic                [3:0] axi_awcache_r;
logic      [`nl2_AXI_USER_RNG] axi_awuser_r;

logic                      excl_err_r;

logic                      axi_wvalid_r;
logic                      axi_wready_r;
logic      [DATA_SIZE-1:0] axi_wdata_r;
logic    [DATA_SIZE/8-1:0] axi_wstrb_r;
logic                      axi_wlast_r;




logic                      rd_ecc_en_r;
logic                      wr_ecc_en_r;


always @(posedge axi_clk or posedge rst_a)
  begin : ecc_enable_PROC
    if (rst_a) begin
      rd_ecc_en_r        <=  'b0 ;
      wr_ecc_en_r        <=  'b0 ;
    end
    else begin

      // Capture the ECC enable value and preserve the value during the read transaction
      if (axi_arvalid && (!axi_arvalid_r || ibp_cmd_accept[0]) )
        rd_ecc_en_r        <=  cmd_ecc_enable  ;

      // Capture the ECC enable and preserve the value during the write transaction
      if (!axi_awvalid || ibp_cmd_accept[1] )
        wr_ecc_en_r        <=  cmd_ecc_enable  ;

    end
  end


always @(posedge axi_clk or posedge rst_a)
  begin : axi_arreg_PROC
    if (rst_a) begin
      axi_arvalid_r      <=  'b0 ; 
      axi_arid_r         <=  'b0 ; 
      axi_araddr_r       <=  'b0 ; 
      axi_arsize_r       <=  'b0 ; 
      axi_arlen_r        <=  'b0 ; 
      axi_arburst_r      <=  'b0 ; 
      axi_arlock_r       <=  'b0 ; 
      axi_arprot_r       <=  'b0 ; 
      axi_arcache_r      <=  'b0 ; 
      axi_aruser_r       <=  'b0 ;

    end
    else begin

      // Only capture the incoming AXI read command if the initialization is done
      if (init_done && (!axi_arvalid_r || ibp_cmd_accept[0]))
        axi_arvalid_r      <=  axi_arvalid ;

      if (init_done & axi_arvalid && (!axi_arvalid_r || ibp_cmd_accept[0]) ) begin
        axi_arid_r         <=  axi_arid        ;
        axi_araddr_r       <=  axi_araddr      ;
        axi_arsize_r       <=  axi_arsize      ;
        axi_arlen_r        <=  axi_arlen       ;
        axi_arburst_r      <=  axi_arburst     ;
        axi_arlock_r       <=  axi_arlock      ;
        axi_arprot_r       <=  axi_arprot      ;
        axi_arcache_r      <=  axi_arcache     ;
        axi_aruser_r       <=  axi_aruser      ;
      end

    end
  end // block: axi_arreg_PROC



always @(posedge axi_clk or posedge rst_a)
  begin : axi_awreg_PROC
    if (rst_a) begin
      axi_awvalid_r  <= 'b0 ; 
      axi_awid_r     <= 'b0 ;      
      axi_awaddr_r   <= 'b0 ; 
      axi_awsize_r   <= 'b0 ; 
      axi_awlen_r    <= 'b0 ; 
      axi_awburst_r  <= 'b0 ; 
      axi_awlock_r   <= 'b0 ; 
      axi_awprot_r   <= 'b0 ; 
      axi_awcache_r  <= 'b0 ; 
      axi_awuser_r   <= 'b0 ;
      excl_err_r     <= 'b0 ;
    end
    else begin

      // Only capture the incoming AXI read command if the initialization is done
      if (init_done && (!axi_awvalid_r || ibp_cmd_accept[1]))
        axi_awvalid_r      <=  axi_awvalid ;

      if (init_done & axi_awvalid && (!axi_awvalid_r || ibp_cmd_accept[1]) ) begin
        axi_awid_r     <=  axi_awid     ;     
        axi_awaddr_r   <=  axi_awaddr   ;
        axi_awsize_r   <=  axi_awsize   ;
        axi_awlen_r    <=  axi_awlen    ;
        axi_awburst_r  <=  axi_awburst  ;
        axi_awlock_r   <=  axi_awlock   ;
        axi_awprot_r   <=  axi_awprot   ;
        axi_awcache_r  <=  axi_awcache  ;
        axi_awuser_r   <=  axi_awuser   ;
        excl_err_r     <=  excl_err[1]  ;
      end

    end
  end

if (BNK_IN_DATA_PIPE == 1 ) 
begin: bnk_in_data_pipe_1_PROC

always @(posedge axi_clk or posedge rst_a)
  begin : axi_wdata_reg_PROC
    if (rst_a) begin
      axi_wvalid_r <= 'b0; 
      axi_wdata_r  <= 'b0; 
      axi_wstrb_r  <= 'b0; 
      axi_wlast_r  <= 'b0; 
    end
    else begin

      // Only capture the incoming AXI write data if the initialization is done
      if (init_done && (!axi_wvalid_r || ibp_wr_accept) )
        axi_wvalid_r  <=  axi_wvalid ;

      if (init_done && axi_wvalid && (!axi_wvalid_r || ibp_wr_accept) ) begin
        axi_wdata_r  <= axi_wdata  ; 
        axi_wstrb_r  <= axi_wstrb  ; 
        axi_wlast_r  <= axi_wlast  ; 
      end

    end
  end

end
else 
begin: bnk_in_data_pipe_0_PROC

     assign  axi_wvalid_r = axi_wvalid ; 
     assign  axi_wdata_r  = axi_wdata  ; 
     assign  axi_wstrb_r  = axi_wstrb  ; 
     assign  axi_wlast_r  = axi_wlast  ;

end


logic axi_arvalid_l1cg;
logic axi_awvalid_l1cg;
logic axi_wvalid_l1cg;
assign axi_arvalid_l1cg    = axi_arvalid_r  & slv_ready & init_done;
assign axi_awvalid_l1cg    = axi_awvalid_r  & slv_ready & init_done;
// Gate the write data channel if the write command has not been received.
assign axi_wvalid_l1cg     = axi_wvalid_r   & slv_ready & init_done;

/////////////////////////////////////////////////////////////////////////////////
// dbank init
/////////////////////////////////////////////////////////////////////////////////

typedef enum reg [1:0] {
  S_RESET,
  S_PENDING,
  S_GOING,
  S_DONE
} init_phase_t;
init_phase_t init_state;
wire                   init_pending;

assign init_done    = (init_state==S_DONE);
assign init_pending = (init_state==S_PENDING);

logic                  init_start_rise;

logic                  init_start_r;

always_ff @(posedge axi_clk or posedge rst_a) 
begin: init_start_r_PROC
  if (rst_a)
    init_start_r <= 'b0 ;
  else
    init_start_r <= init_start ;
end

// Rising edge detection
assign init_start_rise  =  init_start & ~init_start_r;


always_ff @(posedge axi_clk or posedge rst_a) 
begin: init_state_reg_PROC
  if (rst_a)
    init_state <= S_RESET;
  else if (init_state==S_RESET)  // send a cmd to triger sram init process
  begin
   if (disable_rst_init)
    init_state <= S_DONE;
   else
    init_state <= S_PENDING;
  end
//   else if (init_state==S_PENDING && phy_bnk_cmd_accept[1]) // the init cmd has been accepted
//     init_state <= S_GOING;
  else if (init_state==S_PENDING && phy_bnk_rd_valid[0])  // got the init done message
    init_state <= S_DONE;
  else if ( init_start_rise )
    init_state <= S_PENDING;

end 




//////////////////////////////////////////////////////////////////////////////
// Command channel forwarding:

always @*
begin: ibp_cmd_PROC
  ibp_cmd_valid[0] = axi_arvalid_l1cg;
  ibp_cmd_valid[1] = axi_awvalid_l1cg;
  ibp_cmd_read[0] = 1'b1;
  ibp_cmd_read[1] = 1'b0;
  ibp_cmd_addr[0] = axi_araddr_r;
  ibp_cmd_wrap[0] = (2'b10 == axi_arburst_r);
  ibp_cmd_fixed[0] = (2'b00 == axi_arburst_r);
  ibp_cmd_data_size[0] = axi_arsize_r;
  ibp_cmd_burst_size[0] = axi_arlen_r;
  ibp_cmd_excl[0] = axi_arlock_r;
  ibp_cmd_prot[0] = {axi_arprot_r[2], axi_arprot_r[0]};
  ibp_cmd_cache[0] = axi_arcache_r;
  ibp_cmd_id[0] = axi_arid_r;
  ibp_cmd_ar[0] = 2'b00;
  ibp_cmd_rdomid[0] = 3'b000;
  ibp_cmd_space[0] = ({3{axi_aruser_r == `nl2_AXI_USER_SIZE'd0}} & `nl2_IBP_CMD_SPACE_MEMORY)
                    |({3{axi_aruser_r == `nl2_AXI_USER_SIZE'd1}} & `nl2_IBP_CMD_SPACE_AUX)
                    |({3{axi_aruser_r == `nl2_AXI_USER_SIZE'd3}} & `nl2_IBP_CMD_SPACE_VIRTMEM)
                    |({3{axi_aruser_r == `nl2_AXI_USER_SIZE'd4}} & `nl2_IBP_CMD_SPACE_XSPC0)
                    |({3{axi_aruser_r == `nl2_AXI_USER_SIZE'd5}} & `nl2_IBP_CMD_SPACE_XSPC1)
                    |({3{axi_aruser_r == `nl2_AXI_USER_SIZE'd6}} & `nl2_IBP_CMD_SPACE_XSPC2);

  // Address is not propagated until the init is done. It could interfer with
  // memory initialization
  if ( init_done )
    ibp_cmd_addr[1] = axi_awaddr_r;
  else
    ibp_cmd_addr[1] = 'b0;
  ibp_cmd_wrap[1] = (2'b10 == axi_awburst_r);
  ibp_cmd_fixed[1] = (2'b00 == axi_awburst_r);
  ibp_cmd_data_size[1] = axi_awsize_r;
  ibp_cmd_burst_size[1] = axi_awlen_r;
  ibp_cmd_excl[1] = axi_awlock_r;
  ibp_cmd_prot[1] = {axi_awprot_r[2], axi_awprot_r[0]};
  ibp_cmd_cache[1] = axi_awcache_r;
  ibp_cmd_id[1] = axi_awid_r;
  ibp_cmd_ar[1] = 2'b00;
  ibp_cmd_rdomid[1] = 3'b000;
  ibp_cmd_space[1] = ({3{axi_awuser_r == `nl2_AXI_USER_SIZE'd0}} & `nl2_IBP_CMD_SPACE_MEMORY)
                    |({3{axi_awuser_r == `nl2_AXI_USER_SIZE'd1}} & `nl2_IBP_CMD_SPACE_AUX)
                    |({3{axi_awuser_r == `nl2_AXI_USER_SIZE'd3}} & `nl2_IBP_CMD_SPACE_VIRTMEM)
                    |({3{axi_awuser_r == `nl2_AXI_USER_SIZE'd4}} & `nl2_IBP_CMD_SPACE_XSPC0)
                    |({3{axi_awuser_r == `nl2_AXI_USER_SIZE'd5}} & `nl2_IBP_CMD_SPACE_XSPC1)
                    |({3{axi_awuser_r == `nl2_AXI_USER_SIZE'd6}} & `nl2_IBP_CMD_SPACE_XSPC2);

  axi_arready = init_done & (ibp_cmd_accept[0] | !axi_arvalid_r);
  axi_awready = init_done & (ibp_cmd_accept[1] | !axi_awvalid_r);

end

//////////////////////////////////////////////////////////////////////////////
// read channel forwarding:

always @*
begin: axi_read_PROC
  axi_rvalid    = ibp_rd_valid;
  ibp_rd_accept = axi_rready;
  axi_rdata     = ibp_rd_data;
  axi_rlast     = ibp_rd_last;
  axi_rid       = ibp_rd_id;
//  axi_rresp     = ibp_rd_dbe ? 2'b10 : {1'b0, ibp_rd_excl_ok};
//Exclusive read must return EXOKAY (this indicates the slave supports exclusive access)  
//  axi_rresp     = ibp_rd_excl_ok ? 2'b01 : {ibp_rd_dbe , 1'b0};

  // Check error first
  if ( ibp_rd_dbe | ibp_rd_err )
    axi_rresp     =  2'b10 ;
  else
    axi_rresp     =  {1'b0, ibp_rd_excl_ok};

end

//////////////////////////////////////////////////////////////////////////////
// write channel forwarding:

if (BNK_IN_DATA_PIPE == 1 ) 
begin: axi_wready_pipe_1_PROC
  assign  axi_wready   = init_done & (!axi_wvalid_r | ibp_wr_accept);
end
else 
begin: axi_wready_pipe_0_PROC
  assign  axi_wready   = ibp_wr_accept;
end

always @*
begin: ibp_wr_PROC
  ibp_wr_valid = axi_wvalid_l1cg;
  ibp_wr_data  = axi_wdata_r;
  ibp_wr_mask  = axi_wstrb_r;
  ibp_wr_last  = axi_wlast_r;
end

//////////////////////////////////////////////////////////////////////////////
// write response channel forwarding:

always @*
begin: write_response_PROC
  axi_bvalid = ibp_wr_done;
  ibp_wr_resp_accept = axi_bready;
  axi_bid = ibp_wr_id;
  axi_bresp = ibp_wr_bresp;
end

///////////////////////////////////////////////////////////////////////
// synchronous CMD channel
///////////////////////////////////////////////////////////////////////
// Cmd_err asserted if AxBURST != INCR || WRAP, or internal fatal error detected
//TODO bus_ecc_err need to add
logic [1:0] cmd_err;
assign cmd_err[0] = axi_arvalid_r && init_done && (axi_arburst_r == 2'b00) | (axi_arburst_r == 2'b11);
assign cmd_err[1] = axi_awvalid_r && init_done && (axi_awburst_r == 2'b00) | (axi_awburst_r == 2'b11);

assign phy_bnk_cmd_data[0]  =  {1'b0, ibp_cmd_id[0],rd_ecc_en_r,cmd_scrub_enable,cmd_err[0],ibp_cmd_addr[0],ibp_cmd_burst_size[0],ibp_cmd_data_size[0],ibp_cmd_wrap[0],ibp_cmd_read[0],ibp_cmd_excl[0],excl_err[0]};
assign phy_bnk_cmd_data[1]  =  {init_pending,ibp_cmd_id[1],wr_ecc_en_r,cmd_scrub_enable,cmd_err[1],ibp_cmd_addr[1],ibp_cmd_burst_size[1],ibp_cmd_data_size[1],ibp_cmd_wrap[1],ibp_cmd_read[1],ibp_cmd_excl[1],excl_err_r};
assign phy_bnk_cmd_valid[0] = (ibp_cmd_valid[0] && slv_ready);
assign phy_bnk_cmd_valid[1] = (ibp_cmd_valid[1] && slv_ready)
                           | init_pending
                         ;
assign ibp_cmd_accept[0]    = (phy_bnk_cmd_accept[0] && slv_ready);
assign ibp_cmd_accept[1]    = (phy_bnk_cmd_accept[1] && slv_ready);


///////////////////////////////////////////////////////////////////////
// Synchronous Read channel
///////////////////////////////////////////////////////////////////////

  assign phy_bnk_rd_accept[0] = ibp_rd_accept;
  assign ibp_rd_valid = phy_bnk_rd_valid[0] & init_done;
  
  assign {ibp_rd_dbe,
          ibp_rd_sbe,
          ibp_rd_last,
          ibp_rd_err,
          ibp_rd_excl_ok,
          ibp_rd_data} = phy_bnk_rd_data[0][BNK_RD_FW_SIZE-CMD_ID_SIZE-1:0];
  if (CMD_ID_SIZE > 0)
    assign ibp_rd_id = phy_bnk_rd_data[0][BNK_RD_FW_SIZE-1:BNK_RD_FW_SIZE-CMD_ID_SIZE];
  else
    assign ibp_rd_id = 1'b0;

///////////////////////////////////////////////////////////////////////
// Synchronous Write channel
///////////////////////////////////////////////////////////////////////
  assign phy_bnk_wr_valid[0] = ibp_wr_valid && slv_ready;
  assign phy_bnk_wr_data[0]  = {ibp_wr_mask, ibp_wr_data};
  // Gate the write data channel if the write command has not been received.
  assign ibp_wr_accept       = phy_bnk_wr_accept[0] & slv_ready & init_done;

///////////////////////////////////////////////////////////////////////
// Write response channel
///////////////////////////////////////////////////////////////////////

  // Sticky bit error for RMW ECC dbe
  logic       wr_ecc_err;

  always @(posedge axi_clk or posedge rst_a)
    begin : wr_err_reg_PROC
      if (rst_a)
        wr_ecc_err  <= 'b0 ;
      else begin
        if ( phy_bnk_rsp_valid && phy_bnk_rsp_data[BNK_WRSP_FW_SIZE-1] && ibp_wr_resp_accept)
          wr_ecc_err  <= 'b0 ;
        else if (phy_bnk_rsp_valid && !phy_bnk_rsp_data[BNK_WRSP_FW_SIZE-1] && phy_bnk_rsp_data[1])
          wr_ecc_err  <= 1'b1 ;
      end
    end

  // Write command error
  logic ibp_wr_cmd_err;

  assign ibp_wr_done         = phy_bnk_rsp_valid & phy_bnk_rsp_data[BNK_WRSP_FW_SIZE-1];
  assign ibp_wr_cmd_err      = ibp_wr_done & phy_bnk_rsp_data[1];
  assign ibp_wr_excl_okay    = ibp_wr_done & phy_bnk_rsp_data[0];
  assign ibp_wr_bresp        = wr_ecc_err | ibp_wr_cmd_err ? 2'b10 : {1'b0,ibp_wr_excl_okay};
if (WR_ID_SIZE > 0)
  assign ibp_wr_id           = phy_bnk_rsp_data[BNK_WRSP_FW_SIZE-2 -: WR_ID_SIZE];
else
  assign ibp_wr_id           = 1'b0;

  // Backpressure the interface only for the last write response 
  // and if there is backpressure on the AXI interface
  assign phy_bnk_rsp_accept = (phy_bnk_rsp_valid &  phy_bnk_rsp_data[BNK_WRSP_FW_SIZE-1] & ibp_wr_resp_accept) | 
                              (phy_bnk_rsp_valid & ~phy_bnk_rsp_data[BNK_WRSP_FW_SIZE-1]);

///////////////////////////////////////////////////////////////////////


endmodule // new_dbank_axi2bnk
