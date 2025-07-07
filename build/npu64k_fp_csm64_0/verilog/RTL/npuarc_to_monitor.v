// Library ARCv2HS-3.5.999999999
module npuarc_to_monitor #(
parameter TO_EN        = 1,                  // timeout monitor enable (0: disable, 1:enable)
parameter TO_CNT_WIDTH = 4,                  // timeout counter width
parameter TO_MAX_VAL   = 2**TO_CNT_WIDTH -1  // timeout max value setting
) (
input  clk,        // clock source 
input  rst_a,      // async reset, active high
input  clk_en,     // clock enable
input  to_start,   // timeout monitor start setting, start timeout counter (detect rising edge)
input  to_end,     // timeout monitor end setting, reset timeout counter (detect rising edge)
output to_flag     // timeout trigger status, once triggered will be sticky till receive to_end
);
reg                    to_en;         // timeout monitor enable
reg                     to_start_r;
reg                     to_end_r;
wire                    to_start_rise; // to_start rising edge detect
wire                    to_end_rise;   // to_end rising edge detect
reg                     to_trig_r;
wire                    to_trig_r_nxt;
wire                    to_trig;       // timeout counter trigger (level signal)
reg  [TO_CNT_WIDTH-1:0] to_cnt_r;      // timeout counter (destination domain)
wire  [TO_CNT_WIDTH-1:0] to_cnt_nxt;
wire                    to_cnt_cg0;    // timeout counter clock gating
wire                    to_max_val_eql_zero;
wire                    to_en_clk_en;  // both timeout monitor enable and clock enable

assign to_en_clk_en = to_en & clk_en;

always @(posedge clk or  posedge rst_a)
begin
  if (rst_a == 1'b1)
  begin
     to_start_r <= 1'b0;
     to_end_r <= 1'b0;
     to_en <= 1'b1;
  end
  else if (to_en_clk_en)
  begin
     to_start_r <= to_start;
     to_end_r <= to_end;
     to_en <= TO_EN;
  end
end

assign to_start_rise = ({to_start_r,to_start} == 2'b01);
assign to_end_rise = ({to_end_r,to_end} == 2'b01);

assign to_trig_r_nxt = to_end_rise? 1'b0: (to_start_rise? 1'b1 : to_trig_r);
always @(posedge clk or posedge rst_a)
begin
  if (rst_a == 1'b1)
  begin
     to_trig_r <= 1'b0;
  end
  else if (to_en_clk_en)
  begin
     to_trig_r <= to_trig_r_nxt;
  end
end
assign to_trig      = to_trig_r_nxt;

assign to_cnt_nxt = to_trig? ((to_flag)? to_cnt_r : to_cnt_r + 1'b1): {TO_CNT_WIDTH{1'b0}};
assign to_cnt_cg0 = to_en_clk_en & (|(to_cnt_r^to_cnt_nxt));
always @(posedge clk or posedge rst_a)
begin: timeout_counter_reg_PROC
  if (rst_a == 1'b1)
  begin
    to_cnt_r  <= {TO_CNT_WIDTH{1'b0}};
  end
  else if (to_cnt_cg0)
  begin
    to_cnt_r  <= to_cnt_nxt;
  end
end //timeout_counter_reg_PROC
assign to_max_val_eql_zero = &(~to_cnt_r);
assign to_flag = (to_cnt_r == TO_MAX_VAL) && ~to_max_val_eql_zero;


endmodule
