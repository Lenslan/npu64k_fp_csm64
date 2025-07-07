// Library ARCv2HS-3.5.999999999
// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_dmp_ibp_buf # (
  parameter WIDTH = 32
)
  (
  ////////// FIFO inputs /////////////////////////////////////////////////////////
  //
  input                  i_valid,
  output                 i_ready,
  input  [WIDTH-1:0]     i_data,
  
  ////////// FIFO outputs /////////////////////////////////////////////////////////
  //
  output                 o_valid,
  input                  o_ready,
  output [WIDTH-1:0]     o_data,

  ////////// General input signals /////////////////////////////////////////////
  //
  input                  clk,
  input                  rst_a
);

// Local declarations
//

reg               valid_r;         
reg               valid_nxt;       
reg               valid_next;       
reg               valid_cg0;       

reg  [WIDTH-1:0]  data_r;          
reg               data_cg0;

reg               wr_en;
reg               rd_en;

//////////////////////////////////////////////////////////////////////////////
//                                                                          
//  Determine the effective write into the FIFO or read from the FIFO
//                                                                          
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wr_rd_PROC
  // We write into the FIFO when there is incoming valid data and the
  // FIFO is able to take it
  //
  wr_en = i_valid & i_ready;
  
  // We read from the FIFO when the FIFO is presenting valid data that
  // can be consumed
  //
  rd_en = o_valid & o_ready;
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          
//  Compute the validity state of the FIFO
//                                                                          
//////////////////////////////////////////////////////////////////////////////
always @*
begin : valid_PROC
  
  // Enable the clock gate when we read or write
  //
  valid_cg0 = wr_en | rd_en;
  
  // Determing next state of the valid bits
  //
  valid_nxt = valid_r;
  
  case ({wr_en, rd_en})
  2'b1_0:  valid_nxt = 1'b1; // write
  2'b0_1:  valid_nxt = 1'b0; // read
  default: valid_nxt = valid_r;
  endcase
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Clock gate for the FIFO
//                                                                          
//////////////////////////////////////////////////////////////////////////////
always @*
begin : data_cg0_PROC
  
  // This clock gate only enables the entry we are effectively writing data
  //
  data_cg0 = i_valid & i_ready;
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Synchronous processes
//
///////////////////////////////////////////////////////////////////////////////
always @*
begin : valid_commb_PROC
  valid_next = valid_r;
  begin
    if (valid_cg0 == 1'b1)
    begin
      valid_next = valid_nxt;
    end
  end
end

always @(posedge clk or posedge rst_a)
begin : valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    valid_r   <= 1'b0;
  end
  else
  begin
    valid_r <= valid_next;
  end
end


// leda NTL_RST03 off
// leda S_1C_R off
// leda G_551_1_K off
// LMD: A flipflop without reset
// LJ:  Data path signals that dont require a reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
// KS: Conditional reset datapath when safety enabled
always @(posedge clk)
begin : data_reg_PROC
  if (data_cg0 == 1'b1)
  begin
    data_r  <= i_data;
  end
end
// leda S_1C_R on
// leda NTL_RST03 on
// leda G_551_1_K on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Output assignments
//
///////////////////////////////////////////////////////////////////////////////
assign o_valid = valid_r;
assign o_data  = data_r;

assign i_ready =  (valid_r == 1'b0)
                | rd_en;

endmodule // alb_dmp_ibp_buf


