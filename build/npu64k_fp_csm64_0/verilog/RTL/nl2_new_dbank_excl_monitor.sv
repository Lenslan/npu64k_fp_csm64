module nl2_new_dbank_excl_monitor
#(  
  parameter CMD_ID_SIZE    = 1,   // legal range: >= 1
  parameter WR_ID_SIZE     = 1,   // legal range: >= 1
  parameter CMD_ADDR_SIZE  = 32   // legal range: >= 1
 )
(  
 input logic                     axi_arvalid,
 input logic                     axi_arready,
 input logic                     axi_arlock,
 input logic [CMD_ID_SIZE-1:0]   axi_arid,
 input logic [CMD_ADDR_SIZE-1:0] axi_araddr,

 input logic                     axi_awvalid,
 input logic                     axi_awready,
 input logic                     axi_awlock,
 input logic [WR_ID_SIZE-1:0]    axi_awid,
 input logic [CMD_ADDR_SIZE-1:0] axi_awaddr,

 output logic [1:0]              excl_err,
 input logic                     axi_clk,
 input logic                     rst_a
);
//////////////////////////////////////////////////////////////////////////////
//exclusive monitor 
logic [CMD_ID_SIZE-1:0]   excl_mon_cmd_id_r;
logic [CMD_ADDR_SIZE-8:0] excl_mon_addr_r;

logic                     excl_moni_valid;
logic                     excl_moni_clear;
logic                     excl_moni_match;

logic                      axi_awvalid_r;
logic  [CMD_ADDR_SIZE-1:0] axi_awaddr_r;
logic                      axi_awlock_r;

logic                      rd_latch;

  // excl monitor is valid when an exclusive read transaction is accepted on the interface
  // It is cleared when write transaction is matching the address the of the exclusive monitor and
  // 
  always @(posedge axi_clk or posedge rst_a)
  begin:excl_monitor_valid_PROC
    if (rst_a)
      excl_moni_valid    <= 1'b0;
    else if (excl_moni_clear)
      excl_moni_valid    <= 1'b0;
    else if (axi_arvalid && axi_arlock && axi_arready)
      excl_moni_valid    <= 1'b1;  
  end

  always @(posedge axi_clk or posedge rst_a)
  begin:excl_monitor_regs_PROC
    if (rst_a)
      begin
        excl_mon_cmd_id_r    <=  'b0;
        excl_mon_addr_r      <=  'b0;
      end
    else if (axi_arvalid && axi_arlock && axi_arready)
      begin
        excl_mon_cmd_id_r    <=  axi_arid;
        excl_mon_addr_r      <=  axi_araddr[CMD_ADDR_SIZE-1:7];
      end
  end


  // Capture the current write transaction in process
  always @(posedge axi_clk or posedge rst_a)
  begin : axi_awreg_PROC
    if (rst_a) begin
      axi_awvalid_r    <= 'b0 ; 
      axi_awaddr_r     <= 'b0 ; 
      axi_awlock_r     <= 'b0 ; 
    end
    else begin
      
      if (axi_awready)
        axi_awvalid_r  <=  axi_awvalid ;

       if (axi_awvalid && axi_awready) begin
        axi_awaddr_r   <=  axi_awaddr   ;
        axi_awlock_r   <=  axi_awlock   ;
      end

    end
  end


  // rd_latch is asserted on a read exclusive access
  // and deasserted on the next assertion of axi_arready
  always @(posedge axi_clk or posedge rst_a)
  begin: rd_latch_PROC
    if (rst_a)
      rd_latch    <= 1'b0;
    else if (axi_arvalid && axi_arlock && axi_arready)
      rd_latch    <= 1'b1;
    else if (axi_arready)
      rd_latch    <= 1'b0;
  end


// Exclusive Monitor match the write transaction on the following condition:
// 1. Match on cmd_id
// 2. Match on write  address
// If the the read ID is wider than the write ID, check that MSB are zero.

// Exclusive Monitor is clearead on the following condition:
// 1. Not an exclusive or current processing an exclusive read
// 2. Match on write address

if ( CMD_ID_SIZE > WR_ID_SIZE ) 
begin: excl_moni_match_nequal_PROC
  // CMD_ID_SIZE is wider than WR_ID_SIZE
  
  assign excl_moni_match =  (excl_mon_cmd_id_r[CMD_ID_SIZE-1:WR_ID_SIZE] == 'b0) && 
                            (excl_mon_cmd_id_r[WR_ID_SIZE-1:0] == axi_awid) && 
                            (excl_mon_addr_r                   == axi_awaddr[CMD_ADDR_SIZE-1:7]) ;

  assign excl_moni_clear =  axi_awvalid_r &&
                            (!axi_awlock_r || rd_latch) && 
                            (excl_mon_addr_r   == axi_awaddr_r[CMD_ADDR_SIZE-1:7]) ;

end
else 
begin: excl_moni_match_equal_PROC
  // CMD_ID_SIZE and WR_ID_SIZE equal

  assign excl_moni_match =  (excl_mon_cmd_id_r == axi_awid) && 
                            (excl_mon_addr_r   == axi_awaddr[CMD_ADDR_SIZE-1:7]) ;

  assign excl_moni_clear =  axi_awvalid_r &&
                            (!axi_awlock_r || rd_latch) && 
                            (excl_mon_addr_r   == axi_awaddr_r[CMD_ADDR_SIZE-1:7]) ;

end


  // This signal is registered in axi2bnk module before transmitted to dbank_top
  always_comb
  begin:excl_err_PROC
    excl_err = 2'b00;
  if(axi_awlock && axi_awvalid && !excl_moni_valid)
    excl_err = 2'b10;
  else if(axi_awlock && axi_awvalid && excl_moni_valid)
    excl_err = {!excl_moni_match,1'b0};
  end



endmodule  //new_dbank_excl_monitor
