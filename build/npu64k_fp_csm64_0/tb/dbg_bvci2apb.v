`include "npuarc_defines.v"

module dbg_bvci2apb (
  input                         clk,
  input                         rst_a,
  input                         pclkdbg_en,
   
  input                         presetdbgn,

  input                         dbg_cmdval,     // |cmdval| from JTAG
  output                        dbg_cmdack,     // BVCI |cmd| acknowledge
  input       [`npuarc_DBG_ADDR_RANGE] dbg_address,    // |addres|s from JTAG
  input       [`npuarc_DBG_BE_RANGE]   dbg_be,         // |be| from JTAG
  input       [`npuarc_DBG_CMD_RANGE]  dbg_cmd,        // |cmd| from JTAG
  input       [`npuarc_DBG_DATA_RANGE] dbg_wdata,      // |wdata| from JTAG

  input                         dbg_rspack,     // |rspack| from JTAG
  output                        dbg_rspval,     // BVCI response valid
  output      [`npuarc_DBG_DATA_RANGE] dbg_rdata,      // BVCI response EOP
  output                        dbg_reop,       // BVCI response error
  output                        dbg_rerr,       // BVCI data to Debug host


  output reg                    pseldbg,
  output reg [31:2]             paddrdbg,
  output reg                    pwritedbg,
  output reg                    penabledbg,
  output reg [31:0]             pwdatadbg,

  input [31:0]                  prdatadbg,
  input                         preadydbg,
  input                         pslverrdbg
);

//probably only works with pclk_en true (PCLK = CPU CLK)

assign dbg_rdata = prdatadbg;
assign dbg_rerr = pslverrdbg;
assign dbg_reop = 1'b1;

reg [1:0] dbg_trans_state_r;
reg [1:0] dbg_trans_state_nxt;
reg i_write_r, i_write_nxt;
reg i_cmd_en;
reg reset_done_r;
reg i_dbg_cmdack, i_dbg_rspval;

reg [3:0] i_del_cycles = 4'h3;
reg [3:0] i_del_cycles_r;

assign dbg_cmdack = i_dbg_cmdack & pclkdbg_en;
assign dbg_rspval = i_dbg_rspval & pclkdbg_en;

always @(posedge clk or posedge rst_a)
begin : reset_done_PROC
  if (rst_a == 1'b1)
    reset_done_r  <=  1'b0;
  else
    reset_done_r  <=  1'b1;
end

//state machine for BVCI2APB
always @*
begin //{
  //defaults
  pseldbg = 1'b0;
  pwritedbg = 1'b0;
  penabledbg = 1'b0;
  i_dbg_cmdack = 1'b0;
  i_dbg_rspval = 1'b0;
  i_write_nxt = 1'b0;
  i_cmd_en = 1'b0;
  dbg_trans_state_nxt = 2'b00;

  if (dbg_address[31:8] == 24'hffff00)
  begin //{
  case (dbg_trans_state_r)
    2'b00: // IDLE
    begin //{
	  if (dbg_cmdval == 1'b1)
      begin //{
		if (dbg_cmd == 2'b01)
			i_write_nxt = 1'b0;
		else if (dbg_cmd == 2'b10)
			i_write_nxt = 1'b1;
		i_cmd_en = 1'b1;
		if (reset_done_r & pclkdbg_en == 1'b1)
		begin
		  i_dbg_cmdack = 1'b1;
		  dbg_trans_state_nxt = 2'b01;
		end
		else
		  dbg_trans_state_nxt = 2'b00;
     end //}
	end //}

    2'b01: // SETUP
    begin //{
	  i_write_nxt = i_write_r;
	  pseldbg = 1'b1;
	  pwritedbg = i_write_r;
      if (pclkdbg_en == 1'b1)
	    dbg_trans_state_nxt = 2'b10;
    end //}

    2'b10: // ACCESS
    begin //{
	  i_write_nxt = i_write_r;
	  pseldbg = 1'b1;
	  penabledbg = 1'b1;
	  pwritedbg = i_write_r;
	  if (preadydbg == 1'b1)
	  begin //{
        i_dbg_rspval = 1'b1;
 	    if (dbg_cmdval == 1'b0 & pclkdbg_en == 1'b1)
	    begin //{
            //dbg_trans_state_nxt = 2'b00;
            dbg_trans_state_nxt = 2'b11;
		end //}
		else if (pclkdbg_en == 1'b1)
		begin //{
			if (dbg_cmd == 2'b01)
			  i_write_nxt = 1'b0;
			else if (dbg_cmd == 2'b10)
			  i_write_nxt = 1'b1;
            i_cmd_en = 1'b1;
			i_dbg_cmdack = 1'b1;
			dbg_trans_state_nxt = 2'b01;
		end //}
	  end //}
      else
          dbg_trans_state_nxt = 2'b10;
    end //}

    2'b11: // DELAY
    begin
      if (i_del_cycles_r != 4'h0)
      begin
        i_del_cycles = i_del_cycles_r - 1;
        dbg_trans_state_nxt = 2'b11;
      end
      else
      begin
        i_del_cycles = 4'h3;
        dbg_trans_state_nxt = 2'b00;
      end
    end
  endcase
  end //}
end //}

always @(posedge clk or posedge rst_a)
begin //{
	if (rst_a == 1'b1)
    begin
		dbg_trans_state_r <= 2'b00;
        i_del_cycles_r <= 4'h0;
    end
	else if (pclkdbg_en == 1'b1)
    begin
		dbg_trans_state_r <= dbg_trans_state_nxt;
        i_del_cycles_r <= i_del_cycles;
    end
end //}

always @(posedge clk or posedge rst_a)
begin //{
	if (rst_a == 1'b1)
		i_write_r <= 1'b0;
	else
		i_write_r <= i_write_nxt;
end //}

always @(posedge clk or posedge rst_a)
begin //{
	if (rst_a == 1'b1)
	begin
		paddrdbg <= 30'b0; // may need translation & registering?
		pwdatadbg <= 32'b0; // needs to be sampled, and write
	end
	else if (i_cmd_en == 1'b1)
	begin
		paddrdbg <= dbg_address[31:2]; 
		pwdatadbg <= dbg_wdata;
	end
end//}

endmodule
