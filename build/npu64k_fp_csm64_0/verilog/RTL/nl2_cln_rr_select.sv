module nl2_cln_rr_select #(
  parameter LENGTH = 2,                 // length of bit-vector to select from 
  parameter ADDR   = $clog2(LENGTH)     // size of pointer into input vector
)(
  output reg  [LENGTH-1:0] unitary_out, // one-hot vector of selected index
  output reg    [ADDR-1:0] binary_out,  // binary encoding of selected index
  input       [LENGTH-1:0] valid_in,    // input vector of valids to select from
  input                    next,        // signal to increment to the next valid entry
  
  input                    clk,
  input                    rst_a
);

  reg [ADDR-1:0] pivot;
  reg            match;
  reg [ADDR-1:0] match_idx;

  always @*
  begin: select_PROC
// spyglass disable_block Ac_conv01 Ac_conv02
// SMD: synchronizers converge on combinational gate
// SJ:  functionally independent signals
    match       = 1'b0;
    match_idx   =  'b0;
// spyglass enable_block Ac_conv01 Ac_conv02
    unitary_out =  'b0;
    binary_out  =  'b0;

    // First pass, only consider candidates up to the pivot
// spyglass disable_block Ac_conv01
// SMD: synchronizers converge on combinational gate
// SJ:  functionally independent signals
    for (int i=LENGTH-1; i>=0; i--)
    begin
      if (i <= pivot)
        if (valid_in[i])
        begin
          match     = 1'b1;
          match_idx = i;
        end
    end
    // Second pass, only consider candidates starting from the RR index
    for (int i=LENGTH-1; i>=0; i--)
    begin
      if (i > pivot)
        if (valid_in[i])
        begin
          match     = 1'b1;
          match_idx = i;
        end
    end
// spyglass enable_block Ac_conv01

    if (match)
    begin
      binary_out             = match_idx;
      unitary_out[match_idx] = 1'b1;
    end
  end

// spyglass disable_block Ac_unsync02 Ac_glitch04
// SMD: Unsynchronized Crossing
// SJ:  static enable
  always @(posedge clk or posedge rst_a)
  begin: rr_idx_PROC
    if (rst_a)
      pivot <= LENGTH-1;
    else
    begin
      if (next && match)
        pivot <= match_idx;
    end
  end
// spyglass enable_block Ac_unsync02 Ac_glitch04
endmodule    
