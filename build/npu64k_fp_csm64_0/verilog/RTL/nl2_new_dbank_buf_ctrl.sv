`include "nl2_cln_defines.v"

module nl2_new_dbank_buf_ctrl
  #(
    parameter N_SRAM        = 4, // legal range: {2,4}
    parameter N_NARROW      = 4,
    parameter BNK_ADDR_SIZE = 10,
    parameter BNK_DATA_WIDTH= 8,
    parameter BNK_ECC_WIDTH = 4,
    parameter SRAM_SEL_MSB  = 7,
    parameter SRAM_SEL_LSB  = 6,
    parameter CMD_ID_SIZE   = 1,
    parameter RMW_ECC_PIPE  = 1,
    parameter BLOCK_ADDR_SIZE = `nl2_SRAM_BLOCK_ADDR_SIZE,
    parameter INTERLEAVE_ADR = $clog2(`nl2_CFG_SCM_INTERLEAVE),
    // The following is immutable:
    localparam BNK_MASK_WIDTH = BNK_DATA_WIDTH/8,
    localparam BNK_MASK_WIDTH_NARROW = BNK_MASK_WIDTH/N_NARROW,
    localparam BNK_RAW_MASK_WIDTH_NARROW  = `nl2_DBANK_MASK_WIDTH_NARROW
    )
(
// spyglass disable_block W240 
// SMD: declared but not read
// SJ: Do not care the warning of "declared but not read"  
input                                 wr_done,
input                                 rd_done,
input                                 do_rd,
// spyglass enable_block W240 
input                                 do_wr,
input                                 do_scrub,
input                                 init_going,

// to dbank_wr_ctrl
output                                wdata_out_scrub,
output                                wdata_out_valid,
input                                 wdata_out_accept,
output            [BNK_ECC_WIDTH-1:0] wdata_out_ecc,
output           [BNK_DATA_WIDTH-1:0] wdata_out_data,
output [BNK_RAW_MASK_WIDTH_NARROW-1:0] wdata_out_mask[N_NARROW-1:0],
output                                wdata_out_rmw_req,
output                                wdata_out_err,
input                                 wdata_rmw_read,

// to dbank_rd_ctrl
input                                 rdata_in_ecc_en,
input                                 rdata_in_valid,
input                                 rdata_in_excl_ok,
input                                 rdata_in_tag_err,
input               [CMD_ID_SIZE-1:0] rdata_in_id,
input                                 rdata_in_last,
input             [BNK_ECC_WIDTH-1:0] rdata_in_ecc,
input            [BNK_DATA_WIDTH-1:0] rdata_in_data,
input           [BLOCK_ADDR_SIZE-1:0] rdata_in_block_addr,
input                    [N_SRAM-1:0] rdata_in_sram_sel,

// Bank write data channel from dbank_bottom:
input                                 wdata_in_scrub,
input                                 wdata_in_ecc_en,
input                                 wdata_in_valid,
output                                wdata_in_accept,
input            [BNK_MASK_WIDTH-1:0] wdata_in_mask,
input            [BNK_DATA_WIDTH-1:0] wdata_in_data,
input           [BLOCK_ADDR_SIZE-1:0] wdata_in_block_addr,

// Bank read data channel to dbank_bottom:
input                                 rdata_out_accept,
output                                rdata_out_valid,
output                                rdata_out_last,
output              [CMD_ID_SIZE-1:0] rdata_out_rd_id,
output                                rdata_out_sbe,
output                                rdata_out_dbe,
output                                rdata_out_err,
output                                rdata_out_rmw,
output                                rdata_out_excl_ok,
output           [BNK_DATA_WIDTH-1:0] rdata_out_data,

output                                rmw_out_sbe,
output                                rmw_out_dbe,
 
output                                rdata_out_scrub_req,
output                   [N_SRAM-1:0] rdata_out_sram_sel,
output          [BLOCK_ADDR_SIZE-1:0] rdata_out_block_addr,

output                               buf_idle,
// Misc:
input                                dbank_ctrl_clk,
input                                rst_a
);


reg                         rbuf_ecc_en;
reg                         rbuf_valid;
reg    [BNK_DATA_WIDTH-1:0] rbuf_data;
reg   [BLOCK_ADDR_SIZE-1:0] rbuf_block_addr;
reg            [N_SRAM-1:0] rbuf_sram_sel;
reg       [CMD_ID_SIZE-1:0] rbuf_rd_id;
reg                         rbuf_tag_err;
reg                         rbuf_excl_ok;
reg                         rbuf_last;
reg     [BNK_ECC_WIDTH-1:0] rbuf_ecc;
reg      [RMW_ECC_PIPE:0]   rbuf_for_rmw;
reg                         wbuf_rmw_req;
reg                         wbuf_valid;
reg    [BNK_DATA_WIDTH-1:0] wbuf_data;
reg     [BNK_ECC_WIDTH-1:0] wbuf_ecc;
reg    [BNK_MASK_WIDTH-1:0] wbuf_mask;
reg                         wbuf_sbe;
reg                         wbuf_err;
reg                         wbuf_scrub;

`include "nl2_new_dbnk_ecc_func.sv"
always @(posedge dbank_ctrl_clk or posedge rst_a)
begin: rbuf_PROC
  if (rst_a)
  begin
    rbuf_valid   <= 1'b0;
    rbuf_data    <= {BNK_DATA_WIDTH{1'b0}};
    rbuf_block_addr <= {BLOCK_ADDR_SIZE{1'b0}};
    rbuf_sram_sel   <= {N_SRAM{1'b0}};
    rbuf_ecc     <= {N_NARROW{ new_dbnk_ecc_enc( .data_in({BNK_DATA_WIDTH/N_NARROW{1'b0}})) }};
    rbuf_last    <= 1'b0;
    rbuf_rd_id   <=  'b0;
    rbuf_tag_err <= 1'b0;   
    rbuf_excl_ok <= 1'b0;
    rbuf_ecc_en  <= 1'b0;
  end
  else
  begin
    if (rdata_in_valid)
    begin
      rbuf_valid   <= 1'b1;
      rbuf_data    <= rdata_in_data;
      rbuf_block_addr <= rdata_in_block_addr;
      rbuf_sram_sel   <= rdata_in_sram_sel;
      rbuf_ecc     <= rdata_in_ecc;
      rbuf_last    <= rdata_in_last;
      rbuf_rd_id   <= rdata_in_id;
      rbuf_tag_err <= rdata_in_tag_err;
      rbuf_excl_ok <= rdata_in_excl_ok;
      rbuf_ecc_en  <= rdata_in_ecc_en;
    end
    else if (wdata_rmw_read) begin
      rbuf_valid      <= 1'b0;
      rbuf_data       <= rdata_in_data;
      rbuf_block_addr <= wdata_in_block_addr;
      rbuf_sram_sel   <= {N_SRAM{1'b0}};
      rbuf_ecc        <= rdata_in_ecc;
      rbuf_last       <= 1'b0;
      rbuf_rd_id      <=  'b0;
      rbuf_tag_err    <= 1'b0;
      rbuf_excl_ok    <= 1'b0;
      rbuf_ecc_en     <= 1'b1;
    end // if (rdata_out_accept)
    else begin
      rbuf_valid   <= 1'b0;
    end

  end
end // block: rbuf_PROC

if ( RMW_ECC_PIPE ) 
begin: rbuf_for_rmw_reg_PROC

  always @(posedge dbank_ctrl_clk or posedge rst_a)
    begin: rbuf_rmw_PROC
      if (rst_a) begin
        rbuf_for_rmw <= 'b0 ;
      end
      else begin
        rbuf_for_rmw <= {rbuf_for_rmw[0], wdata_rmw_read};
      end
    end

end
else 
begin: rbuf_for_rmw_PROC

 always @(posedge dbank_ctrl_clk or posedge rst_a)
    begin: rbuf_rmw_PROC
      if (rst_a) begin
        rbuf_for_rmw <= 'b0 ;
      end
      else begin
        rbuf_for_rmw <=  wdata_rmw_read;
      end
    end
      
end




wire  [BNK_ECC_WIDTH-1:0] corrected_ecc;
wire [BNK_DATA_WIDTH-1:0] corrected_data;

wire                single_err;
wire                double_err;
wire                unknown_err;
wire                addr_err;
wire [N_NARROW-1:0] i_single_err;
wire [N_NARROW-1:0] i_double_err;
wire [N_NARROW-1:0] i_unknown_err;
wire [N_NARROW-1:0] i_addr_err;

assign i_addr_err = 0;

for (genvar i=0; i<N_NARROW; i++) begin: g_dec
  nl2_new_dbnk_ecc_decoder u_new_dbnk_ecc_decoder
  (.enable     (rbuf_ecc_en),
   .data_in    (rbuf_data[`nl2_WIDTH_NARROW*i+:`nl2_WIDTH_NARROW]),
   .ecc_in     (rbuf_ecc[`nl2_DBANK_ECC_WIDTH_NARROW*i+:`nl2_DBANK_ECC_WIDTH_NARROW]),
   .ecc_out    (corrected_ecc[`nl2_DBANK_ECC_WIDTH_NARROW*i+:`nl2_DBANK_ECC_WIDTH_NARROW]),
   .data_out   (corrected_data[`nl2_WIDTH_NARROW*i+:`nl2_WIDTH_NARROW]),
   .single_err (i_single_err[i]),
   .double_err (i_double_err[i]),
   .unknown_err(i_unknown_err[i])
  );
end: g_dec

assign single_err = (i_single_err != '0);
assign double_err = (i_double_err != '0);
assign unknown_err = (i_unknown_err != '0);
assign addr_err = (i_addr_err != 0);

assign rdata_out_valid   = rbuf_valid;
assign rdata_out_data    = corrected_data;
assign rdata_out_last    = rbuf_last;
assign rdata_out_rmw     = rbuf_for_rmw[0];
assign rdata_out_excl_ok = rbuf_excl_ok;
assign rdata_out_rd_id   = rbuf_rd_id;
assign rdata_out_err     = double_err | unknown_err | addr_err | rbuf_tag_err;
assign rdata_out_sbe     = single_err & !rbuf_tag_err;
assign rdata_out_dbe     = (double_err | unknown_err | addr_err) & !rbuf_tag_err;
   
    
assign rdata_out_scrub_req  = rdata_out_valid & rdata_out_sbe & !rdata_out_dbe ;
assign rdata_out_sram_sel   = rbuf_sram_sel;
assign rdata_out_block_addr = rbuf_block_addr;


logic [BNK_DATA_WIDTH-1:0]   rmw_corrected_data_r;
logic                        rmw_single_err;
logic                        rmw_double_err;
logic                        rmw_unknown_err;
logic                        rmw_addr_err;

if ( RMW_ECC_PIPE ) 
begin: rmw_ecc_pipe_1_reg_PROC

  always @(posedge dbank_ctrl_clk or posedge rst_a)
    begin: rmw_pipe_PROC
      if (rst_a) begin
        rmw_corrected_data_r <= 'b0 ;
        rmw_single_err       <= 'b0 ; 
        rmw_double_err       <= 'b0 ; 
        rmw_unknown_err      <= 'b0 ; 
        rmw_addr_err         <= 'b0 ; 
      end
      else begin
        if ( rbuf_for_rmw[0] ) begin
          rmw_corrected_data_r <= corrected_data ;
          rmw_single_err       <= single_err  ; 
          rmw_double_err       <= double_err  ; 
          rmw_unknown_err      <= unknown_err ; 
          rmw_addr_err         <= addr_err    ; 
        end

      end
    end

end
else 
begin: rmw_ecc_pipe_0_reg_PROC
  assign  rmw_corrected_data_r = corrected_data ;
  assign  rmw_single_err       = single_err  ; 
  assign  rmw_double_err       = double_err  ; 
  assign  rmw_unknown_err      = unknown_err ; 
  assign  rmw_addr_err         = addr_err    ; 
end


// TBD : Fix tag error for write command
assign rmw_out_dbe     = rbuf_for_rmw[0] & (double_err | unknown_err | addr_err);
assign rmw_out_sbe     = rbuf_for_rmw[0] &  single_err ;

reg    [BNK_DATA_WIDTH-1:0] wdata_pre;
always @*
begin: wdata_pre_PROC
  wdata_pre = wdata_in_data;
  if (rbuf_for_rmw[RMW_ECC_PIPE])
  begin
// spyglass disable_block SelfDeterminedExpr-ML
// SMD: self determined expression
// SJ: No care about the warning
    for (integer i = 0; i < BNK_MASK_WIDTH; i = i + 1)
      wdata_pre[i*8 +: 8] = wbuf_mask[i] ? wbuf_data[i*8 +: 8] : rmw_corrected_data_r[i*8 +: 8];
  end
  else if (init_going) begin
    wdata_pre = {BNK_DATA_WIDTH{1'b0}};
  end
// spyglass enable_block SelfDeterminedExpr-ML
end

// Check if all the bytes of the data segment is written
// If one data segment is partially written, it will trigger Read-Modify-Write
function automatic rmw_check;
input [BNK_MASK_WIDTH-1:0]        wdata_mask;
begin
logic rmw = 1'b0;
logic [BNK_MASK_WIDTH_NARROW-1:0] seg_wmask;

  for (int i=0; i<N_NARROW; i++) begin
                // spyglass disable_block SelfDeterminedExpr-ML
                // SMD: Self determined expression found in module
                // SJ: Do not care about the warning
    seg_wmask = wdata_mask[i*BNK_MASK_WIDTH_NARROW +: BNK_MASK_WIDTH_NARROW];
                // spyglass enable_block SelfDeterminedExpr-ML
    rmw  |=  (|(~seg_wmask)) & (|seg_wmask) ;
  end

  rmw_check = rmw;
  
end
endfunction



// ECC encoded the incoming data as this address was zero.
// The address will be added to the ECC computation on following stage.
wire [BLOCK_ADDR_SIZE-1:0] null_addr;
wire [BNK_DATA_WIDTH-1:0]  null_data;
assign null_addr  = 'b0 ;
assign null_data  = 'b0 ;
// assign inv_mask   = {N_NARROW{( 'b11 << (`DBANK_ECC_WIDTH_NARROW-3))}}; // Invert 2 MSBs before parity
// assign inv_mask   = {N_NARROW{9'h0c0}};

wire [BNK_ECC_WIDTH-1:0] encoded_ecc;
for (genvar i=0; i<N_NARROW; i++) begin: g_enc
  nl2_new_dbnk_ecc_encoder u_dnk_ecc_encoder
  (.data_in    (wdata_pre[`nl2_WIDTH_NARROW*i+:`nl2_WIDTH_NARROW]),
   .ecc        (encoded_ecc[`nl2_DBANK_ECC_WIDTH_NARROW*i+:`nl2_DBANK_ECC_WIDTH_NARROW])
  );


end: g_enc


always @(posedge dbank_ctrl_clk or posedge rst_a)
begin: wbuf_PROC
  if (rst_a)
  begin
    wbuf_valid   <= 1'b0;
    wbuf_data    <= {BNK_DATA_WIDTH{1'b0}};
    wbuf_ecc     <= {N_NARROW{ new_dbnk_ecc_enc( .data_in({BNK_DATA_WIDTH/N_NARROW{1'b0}})) }};
    wbuf_mask    <= {BNK_MASK_WIDTH{1'b1}};
    wbuf_sbe     <= 1'b0;
    wbuf_err     <= 1'b0;
    wbuf_rmw_req <= 1'b0;
    wbuf_scrub   <= 1'b0;
  end
  else
  begin
    if (wdata_in_valid & wdata_in_accept)
    begin
      wbuf_scrub   <= wdata_in_scrub;
      wbuf_valid   <= 1'b1;
      wbuf_data    <= wdata_pre;
      wbuf_ecc     <= encoded_ecc;
      wbuf_mask    <= wdata_in_mask;
      wbuf_sbe     <= 1'b0;
      wbuf_err     <= 1'b0;
// spyglass disable_block Ac_conv01
// SMD: synchronizers converge on combinational gate
// SJ:  functionally independent signals
      wbuf_rmw_req <= wdata_in_ecc_en & rmw_check(wdata_in_mask);
// spyglass enable_block Ac_conv01
    end
    else if (rbuf_for_rmw[RMW_ECC_PIPE])
    begin
// spyglass disable_block Ac_unsync02 Ac_glitch04
// SMD: Unsynchronized Crossing
// SJ:  static
      wbuf_scrub   <= 1'b0;
      wbuf_data    <= wdata_pre;
      wbuf_ecc     <= encoded_ecc;
      wbuf_mask    <= {BNK_MASK_WIDTH{1'b1}};
// spyglass enable_block Ac_unsync02 Ac_glitch04
      wbuf_sbe     <= rmw_single_err;
      wbuf_err     <= rmw_double_err | rmw_unknown_err | rmw_addr_err;
      wbuf_rmw_req <= 1'b0;
    end
    else if (wdata_out_accept | init_going)
    begin
// spyglass disable_block Ac_conv01 Ac_unsync01 Ac_unsync02 Ac_glitch04
// SMD: Unsynchronized Crossing
// SJ:  static
      wbuf_scrub   <= 1'b0;
      wbuf_valid   <= 1'b0;
      wbuf_ecc     <= encoded_ecc;
      wbuf_data    <= {BNK_DATA_WIDTH{1'b0}};
      wbuf_mask    <= {BNK_MASK_WIDTH{1'b0}};
      wbuf_sbe     <= 1'b0;
      wbuf_err     <= 1'b0;
      wbuf_rmw_req <= 1'b0;
// spyglass enable_block Ac_conv01 Ac_unsync01 Ac_unsync02 Ac_glitch04
    end
  end
end

logic   [N_NARROW-1:0] wr_ecc_en;


for (genvar i=0; i<N_NARROW; i++) begin: g_msk
  assign wr_ecc_en[i]      = wdata_in_ecc_en & (&wbuf_mask[i*BNK_MASK_WIDTH_NARROW+:BNK_MASK_WIDTH_NARROW]);
  assign wdata_out_mask[i] = {{(BNK_RAW_MASK_WIDTH_NARROW-BNK_MASK_WIDTH_NARROW){wr_ecc_en[i]}}, 
                                wbuf_mask[i*BNK_MASK_WIDTH_NARROW+:BNK_MASK_WIDTH_NARROW]};
end: g_msk

assign wdata_out_scrub = wbuf_scrub;
assign wdata_out_valid = wbuf_valid & ~wbuf_scrub; // Invalidate valid flag for 
assign wdata_out_err   = wbuf_err;
assign wdata_out_ecc   = wbuf_ecc; // Adding address to the ECC computation
assign wdata_out_data  = wbuf_data;
assign wdata_out_rmw_req = wbuf_rmw_req;
assign wdata_in_accept = (!wbuf_valid & (do_wr | do_scrub)) | wdata_out_accept;
assign buf_idle        = !wbuf_valid & !rbuf_valid & (~|rbuf_for_rmw);

endmodule // new_dbank_buf_ctrl
