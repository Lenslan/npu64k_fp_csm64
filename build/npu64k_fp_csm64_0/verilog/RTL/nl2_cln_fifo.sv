module nl2_cln_fifo
  #(parameter WIDTH = 1,
    parameter DEPTH = 2,          // DEPTH >= 2
    parameter FULL_THRESHOLD = 1) // FULL_THRESHOLD >= 1
  (output             fifo_full,
   output             fifo_head_valid,
   output [WIDTH-1:0] fifo_head_data,
   input  [WIDTH-1:0] fifo_in,
   input              push,
   input              pop,
   
   input              clk,
   input              rst_a
   );

reg [DEPTH-1:0] fifo_valid;
reg [WIDTH-1:0] fifo_data [DEPTH-1:0];

// Bits in the msb side of the valid vector are inspected to determine if FULL_THRESHOLD more elements can be written to the fifo before it is full.
assign fifo_full = |fifo_valid[DEPTH-1 -: FULL_THRESHOLD];
assign fifo_head_data = fifo_data[0];
assign fifo_head_valid = fifo_valid[0];

wire [DEPTH-1:0] fifo_last_valid;
wire [DEPTH-1:0] fifo_first_free;

assign fifo_last_valid =  fifo_valid & ~{1'b0, fifo_valid[DEPTH-1:1]};
assign fifo_first_free = ~fifo_valid &  {fifo_valid[DEPTH-2:0], 1'b1};

wire [DEPTH-1:0] shift; // if shift[i]==1 then load from entry[i+1]

assign shift = fifo_valid & {DEPTH{pop}};

// spyglass disable_block Ac_unsync02
// SMD: Unsynchronized Crossing
// SJ:  static enable
// spyglass disable_block Reset_sync02
// SMD: Reset signal is asynchronously to clock signal. Domain mismatch
// SJ:  constraint to be synchronous
// spyglass disable_block Ar_unsync01
// SMD: Reset signal is unsynchronized. Domain mismatch
// SJ:  constraint to be synchronous
// spyglass disable_block Ar_asyncdeassert01
// SMD: Reset signal is asynchronously de-asserted relative to clock signal. Domain mismatch
// SJ:  constraint to be synchronous
always @(posedge clk or posedge rst_a)
begin
  if (rst_a)
  begin: fifo_RESET
    integer i;
    fifo_valid <= {DEPTH{1'b0}};
    for (i=0; i<DEPTH; i=i+1)
      fifo_data[i] <= {WIDTH{1'b0}};
  end
  else
  begin: fifo_PROC
    integer i;
// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self determined expression
// SJ: Operand iterator can be predetermined
// spyglass disable_block W527
// SMD: Potential dangling statement
// SJ: 
// spyglass disable_block Ac_glitch04
// SMD: destination can glitch
// SJ:  static 
    for (i=0; i<DEPTH; i=i+1)
      if (push & !pop & fifo_first_free[i] ||
          push &  pop & fifo_last_valid[i])
        {fifo_valid[i], fifo_data[i]} <= {1'b1, fifo_in};
      else if (shift[i])
      begin
        if (i<DEPTH-1)
// spyglass disable_block Ac_conv01 Ac_conv02 Ac_conv03
// SMD: same-domain signals that are synchronized in the same destination domain and converge before sequential elements
// SJ:  static
          {fifo_valid[i], fifo_data[i]} <= {fifo_valid[i+1], fifo_data[i+1]};
// spyglass enable_block Ac_conv01 Ac_conv02 Ac_conv03
        else begin
          fifo_valid[i] <= 1'b0;
          fifo_data[i] <= {WIDTH{1'b0}};          
        end
      end
// spyglass enable_block W527
// spyglass enable_block SelfDeterminedExpr-ML
  end
// spyglass enable_block Ac_glitch04
end
// spyglass enable_block Reset_sync02
// spyglass enable_block Ar_unsync01
// spyglass enable_block Ar_asyncdeassert01
// spyglass enable_block Ac_unsync02

endmodule // cln_fifo
