// Library ARC_Trace-3.0.999999999

`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"

module npuarc_arct_cti_pipeline # (
  parameter WIDTH  = 8,
  parameter STAGES = 2
)
(
  input  [WIDTH-1:0] din,
  output [WIDTH-1:0] dout,
  input              clk
);

reg [WIDTH-1:0] pipeline [0:STAGES-1];

// spyglass disable_block STARC-2.3.4.3
// SMD: Register with no reset/set
// SJ: flops used as pipeline without reset
always @(posedge clk)
begin : cti_pipeline_PROC
  integer i;
  pipeline[0] <= din;
  for (i=0; i < STAGES-1; i=i+1)
  begin
    pipeline[i+1] <= pipeline[i];
  end
end
// spyglass enable_block STARC-2.3.4.3

assign dout = pipeline[STAGES-1];

endmodule
