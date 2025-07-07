`include "tb_defines.sv"
module swe_arb_tb
#(
   parameter int NUM_TRACE_SRC = 5 // number of source trace
 , parameter int DW = 32
 , parameter string TB_GEN_TRACE_FLAG = "TB_GEN_SWE"
)
(
  input logic clk,
  input logic rst_a,
  input  logic [NUM_TRACE_SRC-1:0]         trace_cdc_valid,   
  input  logic [NUM_TRACE_SRC-1:0]         trace_valid,
  input  logic [NUM_TRACE_SRC-1:0][DW-1:0] trace_id,
  input  logic [NUM_TRACE_SRC-1:0]         trace_accept,
  input  logic                             rtt_swe_val,
  input  logic [DW:0]                      rtt_swe_data,
  input  logic [7:0]                       rtt_swe_ext,
  input  logic [7:0]                       ref_swe_ext,
  output logic [NUM_TRACE_SRC-1:0]         o_trace_valid,
  output logic [NUM_TRACE_SRC-1:0][DW-1:0] o_trace_id,
  output logic [NUM_TRACE_SRC-1:0]         swe_gen_en,
  output logic                             host_sys_cfg_done
);

  //logic [NUM_TRACE_SRC-1:0] swe_gen_en; //enable flag to generate SWE event
  logic test_en;
  logic [NUM_TRACE_SRC-1:0] valid_en1;
  logic [NUM_TRACE_SRC-1:0] valid_en2;
  logic [NUM_TRACE_SRC-1:0] valid_en3;
  logic [NUM_TRACE_SRC-1:0] valid_en4;
  logic [NUM_TRACE_SRC-1:0][DW-1:0] trace_data;
  logic [NUM_TRACE_SRC-1:0] valid_edge0;
  logic [NUM_TRACE_SRC-1:0] valid_edge1;
  logic [NUM_TRACE_SRC-1:0] valid_edge;

  assign valid_edge0 = trace_valid & ~(trace_valid & valid_en1); // get first edge of 5 cycle valid
  
`ifndef TB_HOST
  assign host_sys_cfg_done = 1'b1;
`else
  assign host_sys_cfg_done = `TB_HOST.host_done;
`endif

  for (genvar i = 0; i<NUM_TRACE_SRC; i++)
  begin
    npu_fifo
    #(.SIZE   ( 1 ),
      .DWIDTH ( DW    ),
      .FRCVAL ( 1'b0  ),
      .FRCACC ( 1'b0  )
      )
    u_tb_trace_fifo
      (
       .clk          ( clk          ),
       .rst_a        ( rst_a        ),
       .valid_write  ( valid_edge[i]),
       .accept_write ( ),
       .data_write   (trace_id[i] ),
       .valid_read   ( ),
       .accept_read  (trace_accept[i]),
       .data_read    (trace_data[i] )
       );
  end

  generate
    genvar i;
    // set enable flag to control trace event generation
    for(i=0;i<NUM_TRACE_SRC;i++) begin: force_en_GEN
      always_ff @(posedge clk or posedge rst_a) begin
        if (rst_a == 1'b1) begin
          swe_gen_en[i] <= 0;
        end
        else if(valid_en4[i]) begin
          swe_gen_en[i] <= 0; //release force once accepted
        end
        else begin
          if(!swe_gen_en[i] & test_en)  begin
              swe_gen_en[i] <= ($urandom & 31); // randomly generate swe event 
          end
        end
      end
    end: force_en_GEN

    // keep valid for 5 cycles
    for(i=0;i<NUM_TRACE_SRC;i++) begin: buffer_en_GEN
      always_ff @(posedge clk or posedge rst_a) begin
        if (rst_a == 1'b1) begin
          valid_en1[i] <= 0;
          valid_en2[i] <= 0;
          valid_en3[i] <= 0;
          valid_en4[i] <= 0;
          valid_edge[i]  <= '0;
          valid_edge1[i] <= '0;
        end
        else begin
          valid_en1[i] <= trace_valid[i];
          valid_en2[i] <= valid_en1[i];
          valid_en3[i] <= valid_en2[i];
          valid_en4[i] <= valid_en3[i];
          valid_edge1[i] <= valid_edge0[i];
          valid_edge[i] <= valid_edge1[i];  // get valid edge for skid/fifo
        end
      end
    end: buffer_en_GEN

    // generate trace event 
    for(i=0;i<NUM_TRACE_SRC;i++)begin: trc_gen_GEN
      always @(*) begin
        if (swe_gen_en[i]) begin
          o_trace_valid[i] = 1;
          o_trace_id[i]={$urandom,$urandom};
        end
        else begin
          o_trace_valid[i] = 0;
          o_trace_id[i] = 0;
        end
      end
    end: trc_gen_GEN

    // checkers
    for(i=0;i<NUM_TRACE_SRC;i++)begin: assert_GEN
/*      // check cycles of valid
      property trace_vld_prop;
         @(posedge clk) disable iff(rst_a !==0) $rose(trace_valid[i]) |-> ##5 $fell(trace_valid[i]) ;
      endproperty
      //check accept
      property trace_acp_prop;
         @(posedge clk) disable iff(rst_a !==0) $rose(trace_valid[i]) |-> ##4 $rose(trace_accept[i]) ##1 $fell(trace_accept[i]);
      endproperty
      // check trace id
      property trace_data_prop;
         @(posedge clk) disable iff(rst_a !==0) $rose(trace_valid[i]) |-> ##5 (trace_id[i] == $past(trace_id[i], 5));
      endproperty

      ast_trc_vld: assert property(trace_vld_prop) else $error("trace_valid should keeep 5 cycles");
      ast_trc_acp: assert property(trace_acp_prop) else $error("trace_accept should be asserted before trace_valid drop");
      ast_trc_dat: assert property(trace_data_prop) else $error("trace_id should keeep 5 cycles when trace_valid is asserted");
*/
      // check arb
      property rtt_swe_vld_prop;
        @(posedge clk) disable iff(rst_a !==0) (trace_accept[i] & trace_valid[i]) |-> (rtt_swe_val==1);
      endproperty
      // check arb output data equal with fifo output
      property rtt_swe_dat_prop;
        @(posedge clk) disable iff(rst_a !==0) (trace_accept[i] & trace_valid[i]) |-> (rtt_swe_data[DW:0]=={trace_data[i][DW-1:31],1'b0,trace_data[i][30:0]});
      endproperty
      
      //check cdc valid signal
      property cdc_vld_prop;
        @(posedge clk) disable iff(rst_a !==0) (valid_edge0[i]) |-> ##2 (trace_cdc_valid[i]==1);
      endproperty
      
      ast_swe_vld: assert property(rtt_swe_vld_prop) else $fatal("rtt_swe_val is not asserted when trace_accept[i] asserted");
      ast_swe_dat: assert property(rtt_swe_dat_prop) else $fatal("rtt_swe_data is not expected");
      ast_swe_cdc: assert property(cdc_vld_prop) else $fatal("rtt_swe_cdc is not expected");
    end: assert_GEN
  endgenerate

  property rtt_swe_valid_cycles_prop;
     @(posedge clk) disable iff(rst_a !==0) $rose(rtt_swe_val) |-> ##5 $fell(rtt_swe_val);
  endproperty
  ast_rtt_valid: assert property(rtt_swe_valid_cycles_prop) else $fatal("rtt_swe_valid is not asserted 5 cycles");

  property rtt_swe_ext_prop;
     @(posedge clk) disable iff(rst_a !==0) (1) |-> (rtt_swe_ext == ref_swe_ext);
  endproperty
  ast_rtt_ext: assert property(rtt_swe_ext_prop) else $fatal("rtt_swe_ext is not expected");

  integer k;

  initial begin
    test_en=0;
    wait (host_sys_cfg_done);
    repeat (300) @(posedge clk);
    test_en = get_value_from_plusargs(TB_GEN_TRACE_FLAG);

    if(test_en) begin 
      int num = $urandom_range(20000, 30000);
      // block atb parser to avoid failure because of large number of entry over 40
      //for (k=0;k<40;k++) begin
        force `TB_TOP.i_rtt_tb.parser_din = '{default:'0};
      //end
      repeat (num) @(posedge clk);
      test_en= 0;
      repeat (300) @(posedge clk);

      // check all traces are handled
      assert (~|swe_gen_en);

    end
  end

endmodule
