module npu_rtt_tb (
    // CoreSight interface per core
    output                     atclken,
    output                     atresetn,
    output logic              atready,
    input [`ATDATA_WIDTH-1:0] atdata,
    input [3-1:0] atbytes,
    input [6:0]               atid,
    input                     atvalid,

    output      logic         afvalid,
    input                     afready,
    output      logic         syncreq,

    output reg                swe_atready,
    input [`SWE_ATDATA_WIDTH-1:0]              swe_atdata,
    input [3-1:0]              swe_atbytes,
    input [6:0]               swe_atid,
    input                     swe_atvalid,

    output   logic            swe_afvalid,
    input                     swe_afready,
    output   logic            swe_syncreq,
    output   logic            cti_trace_start,
    output   logic            cti_trace_stop,

    /////////////////////////////////////////
    // APB Interface
    /////////////////////////////////////////
    input                     arct0_preadydbg,
    input [31:0]              arct0_prdatadbg,
    input                     arct0_pslverrdbg,

    output reg [31:2]         arct0_paddrdbg,
    output reg                arct0_pseldbg,
    output reg                arct0_penabledbg,
    output reg                arct0_pwritedbg,
    output reg [31:0]         arct0_pwdatadbg,

    //output                    arct0_dbgen,
    //output                    arct0_niden,
    //output                    arct0_dbg_prot_sel,


    output  [3:0]              bri4tb_awid,
    output  reg [40-1:0]       bri4tb_awaddr,
    output  reg [3:0]          bri4tb_awlen,
    output  reg [2:0]          bri4tb_awsize,
    output  reg [1:0]          bri4tb_awburst,
//    output  [1:0]       rtt_tb_awlock,
    output  [3:0]              bri4tb_awcache,
    output  [2:0]              bri4tb_awprot,
    output  reg                bri4tb_awvalid,
    output  [3:0]              bri4tb_wid,
    output  reg [32-1:0]       bri4tb_wdata,
    output  reg [32/8-1:0]        bri4tb_wstrb,
    output  reg                bri4tb_wlast,
    output  reg                bri4tb_wvalid,
    output                     bri4tb_bready,
    output  [3:0]              bri4tb_arid,
    output  [40-1:0]           bri4tb_araddr,
    output  [3:0]              bri4tb_arlen,
    output  [2:0]              bri4tb_arsize,
    output  [1:0]              bri4tb_arburst,
//    output  [1:0]            rtt_tb_arlock,
    output  [3:0]              bri4tb_arcache,
    output  [2:0]              bri4tb_arprot,
    output                     bri4tb_arvalid,
    output                     bri4tb_rready,

    input  [3:0]               bri4tb_bid,
    input                      bri4tb_awready,
    input                      bri4tb_wready,
    input [1:0]                bri4tb_bresp,
    input                      bri4tb_bvalid,
//leda NTL_CON13C off
//leda NTL_CON37 off
    input  [3:0]               bri4tb_rid,
    input                      bri4tb_arready,
    input [32-1:0]  bri4tb_rdata,
    input                      bri4tb_rlast,
    input                      bri4tb_rvalid,
    input [1:0]                bri4tb_rresp,
    input                      mbus_clk_en,


    input                      rst_a,
    input                      clk,



//---------------------------------------------------------

    input                      rtt_clk
);


wire [31:0] trace_mem_base_addr;

///////////////////////////////////////////////////
// Tie UnusedSignals to 0
///////////////////////////////////////////////////
assign bri4tb_awid    =0;
assign bri4tb_awcache =0;
assign bri4tb_awprot  =0;
assign bri4tb_wid     =0;
assign bri4tb_bready  =1;

assign bri4tb_arid    =0;
assign bri4tb_arlen   =0;
assign bri4tb_arburst =0;
assign bri4tb_arcache =0;
assign bri4tb_arprot  =0;
assign bri4tb_rready  =1;



assign bri4tb_araddr  =0;
assign bri4tb_arvalid =0;
assign bri4tb_arsize  =0;


///////////////////////////////////////////////////
// CCT Tests
///////////////////////////////////////////////////
wire         freeze_cct_en;
assign freeze_cct_en=1'b0;
///////////////////////////////////////////////////

// dummy signal
wire dummy_sig;
assign dummy_sig=1'b0;

// MSS Data
reg        tb_we;
reg [31:0] tb_waddr;
reg [31:0] tb_wdata;

///////////////////////////////////////////////////




///////////////////////////////////////////////////
// Tie UnusedSignals to 0
///////////////////////////////////////////////////


///////////////////////////////////////////////////
// CoreSight Ratio
///////////////////////////////////////////////////

reg  [31:0] trace_mem_ofs;
reg  [31:0] trace_mem_ptr;

///////////////////////////////////////////////////
// CoreSight Slave Interface
///////////////////////////////////////////////////
reg [`ATDATA_WIDTH-1:0] trace_data_buffer [63:0];
reg [`ATDATA_WIDTH-1:0] trace_data_buffer_din [39:0];
reg [5:0]  trace_data_buffer_wr_ptr;
reg [5:0]  trace_data_buffer_rd_ptr;
reg [5:0]  trace_data_buffer_diff_ptr;
reg        trace_data_buffer_empty;
reg        trace_data_buffer_full;
reg        trace_data_buffer_al_full;
wire       trace_data_buffer_wen;
reg        trace_data_buffer_ren;

// {
reg [`SWE_ATDATA_WIDTH-1:0] swe_trace_data_buffer [63:0];
reg [`SWE_ATDATA_WIDTH-1:0] swe_trace_data_buffer_din [39:0];
reg [5:0]  swe_trace_data_buffer_wr_ptr;
reg [5:0]  swe_trace_data_buffer_rd_ptr;
reg [5:0]  swe_trace_data_buffer_diff_ptr;
reg        swe_trace_data_buffer_empty;
reg        swe_trace_data_buffer_full;
reg        swe_trace_data_buffer_al_full;
wire       swe_trace_data_buffer_wen;
wire       swe_trace_data_buffer_ren;
//}


assign atresetn = ~rst_a;


reg [`ATDATA_WIDTH-1:0] atdata_reg;
assign trace_data_buffer_wen = (atclken && atready && atvalid);

//always@(posedge rtt_clk, negedge atresetn)
//  begin
//    if (atresetn == 1'b0)
//      begin
//        atready <= 1'b0;
//      end
//    else
//      begin
//        if (freeze_cct_en == 1'b1)
//          begin
//            atready <= 1'b0;
//          end
//        else if ((trace_data_buffer_diff_ptr == 62) && (trace_data_buffer_wen == 1'b1))
//          begin
//            atready <= 1'b0;
//          end
//        else if ((trace_data_buffer_diff_ptr == 63) && (trace_data_buffer_ren == 1'b1))
//          begin
//            atready <= 1'b1;
//          end
//        else if (trace_data_buffer_diff_ptr == 63)
//          begin
//            atready <= 1'b0;
//          end
//        else
//          begin
//            atready <= 1'b1;
//          end
//      end
//  end

always@(posedge rtt_clk, negedge atresetn)
  begin
    if (atresetn == 1'b0)
      begin
        trace_data_buffer_wr_ptr   <= 0;
        trace_data_buffer_diff_ptr <= 0;
        trace_data_buffer_full     <= 0;
        trace_data_buffer_al_full  <= 0;
        trace_data_buffer_empty    <= 1;
      end
    else
      begin
        if (atready && atvalid && atclken && (!(&atdata[(`ATDATA_WIDTH/2-1):0])))
          begin
            trace_data_buffer[trace_data_buffer_wr_ptr] <= {2'h0,atdata[63:49],atdata[47:33],2'h0,atdata[31:17],atdata[15:1]};
            atdata_reg <= {2'h0,atdata[63:49],atdata[47:33],2'h0,atdata[31:17],atdata[15:1]};
            trace_data_buffer_din[trace_data_buffer_wr_ptr] <= atdata;
            trace_data_buffer_wr_ptr                           <= trace_data_buffer_wr_ptr + 1;
          end

        if ((trace_data_buffer_wen == 1'b1) && (trace_data_buffer_ren == 1'b1))
          begin
            trace_data_buffer_diff_ptr <= trace_data_buffer_diff_ptr;
          end
        else if ((trace_data_buffer_wen == 1'b1) && (trace_data_buffer_ren == 1'b0))
          begin
            trace_data_buffer_diff_ptr <= trace_data_buffer_diff_ptr + 1;
          end
        else if ((trace_data_buffer_wen == 1'b0) && (trace_data_buffer_ren == 1'b1))
          begin
            trace_data_buffer_diff_ptr <= trace_data_buffer_diff_ptr - 1;
          end


        if ((trace_data_buffer_diff_ptr == 62) && (trace_data_buffer_wen == 1'b1) && (trace_data_buffer_ren == 1'b1))
          begin
            trace_data_buffer_full <= 1'b0;
          end
        else if ((trace_data_buffer_diff_ptr == 62) && (trace_data_buffer_wen == 1'b1))
          begin
            trace_data_buffer_full <= 1'b1;
          end
        else if ((trace_data_buffer_diff_ptr == 63) && (trace_data_buffer_ren == 1'b1))
          begin
            trace_data_buffer_full <= 1'b0;
          end

        if ((trace_data_buffer_diff_ptr == 1) && (trace_data_buffer_wen == 1'b1) && (trace_data_buffer_ren == 1'b1))
          begin
            trace_data_buffer_empty <= 1'b0;
          end
        else if ((trace_data_buffer_diff_ptr == 1) && (trace_data_buffer_ren == 1'b1))
          begin
            trace_data_buffer_empty <= 1'b1;
          end
        else if ((trace_data_buffer_diff_ptr == 0) && (trace_data_buffer_wen == 1'b1))
          begin
            trace_data_buffer_empty <= 1'b0;
          end
      end
  end

// {


reg [`ATDATA_WIDTH-1:0] swe_atdata_reg;
assign swe_trace_data_buffer_wen = (atclken && swe_atready && swe_atvalid);
assign swe_trace_data_buffer_ren = 1'b0;

//always@(posedge rtt_clk, negedge atresetn)
//  begin
//    if (atresetn == 1'b0)
//      begin
//        swe_atready <= 1'b0;
//      end
//    else
//      begin
//        if (freeze_cct_en == 1'b1)
//          begin
//            swe_atready <= 1'b0;
//          end
//        else if ((swe_trace_data_buffer_diff_ptr == 62) && (swe_trace_data_buffer_wen == 1'b1))
//          begin
//            swe_atready <= 1'b0;
//          end
//        else if ((swe_trace_data_buffer_diff_ptr == 63) && (swe_trace_data_buffer_ren == 1'b1))
//          begin
//            swe_atready <= 1'b1;
//          end
//        else if (swe_trace_data_buffer_diff_ptr == 63)
//          begin
//            swe_atready <= 1'b0;
//          end
//        else
//          begin
//            swe_atready <= 1'b1;
//          end
//      end
//  end

always@(posedge rtt_clk, negedge atresetn)
  begin
    if (atresetn == 1'b0)
      begin
        swe_trace_data_buffer_wr_ptr   <= 0;
        swe_trace_data_buffer_diff_ptr <= 0;
        swe_trace_data_buffer_full     <= 0;
        swe_trace_data_buffer_al_full  <= 0;
        swe_trace_data_buffer_empty    <= 1;
      end
    else
      begin
        if (swe_atready && swe_atvalid && atclken && (!(&swe_atdata[(`SWE_ATDATA_WIDTH/2-1):0])))
          begin
            swe_trace_data_buffer[swe_trace_data_buffer_wr_ptr] <= {2'h0,swe_atdata[63:49],swe_atdata[47:33],2'h0,swe_atdata[31:17],swe_atdata[15:1]};
            swe_atdata_reg <= {2'h0,swe_atdata[63:49],swe_atdata[47:33],2'h0,swe_atdata[31:17],swe_atdata[15:1]};
            swe_trace_data_buffer_din[swe_trace_data_buffer_wr_ptr] <= swe_atdata;
            swe_trace_data_buffer_wr_ptr                           <= swe_trace_data_buffer_wr_ptr + 1;
          end

        if ((swe_trace_data_buffer_wen == 1'b1) && (swe_trace_data_buffer_ren == 1'b1))
          begin
            swe_trace_data_buffer_diff_ptr <= swe_trace_data_buffer_diff_ptr;
          end
        else if ((swe_trace_data_buffer_wen == 1'b1) && (swe_trace_data_buffer_ren == 1'b0))
          begin
            swe_trace_data_buffer_diff_ptr <= swe_trace_data_buffer_diff_ptr + 1;
          end
        else if ((swe_trace_data_buffer_wen == 1'b0) && (swe_trace_data_buffer_ren == 1'b1))
          begin
            swe_trace_data_buffer_diff_ptr <= swe_trace_data_buffer_diff_ptr - 1;
          end


        if ((swe_trace_data_buffer_diff_ptr == 62) && (swe_trace_data_buffer_wen == 1'b1) && (swe_trace_data_buffer_ren == 1'b1))
          begin
            swe_trace_data_buffer_full <= 1'b0;
          end
        else if ((swe_trace_data_buffer_diff_ptr == 62) && (swe_trace_data_buffer_wen == 1'b1))
          begin
            swe_trace_data_buffer_full <= 1'b1;
          end
        else if ((swe_trace_data_buffer_diff_ptr == 63) && (swe_trace_data_buffer_ren == 1'b1))
          begin
            swe_trace_data_buffer_full <= 1'b0;
          end

        if ((swe_trace_data_buffer_diff_ptr == 1) && (swe_trace_data_buffer_wen == 1'b1) && (swe_trace_data_buffer_ren == 1'b1))
          begin
            swe_trace_data_buffer_empty <= 1'b0;
          end
        else if ((swe_trace_data_buffer_diff_ptr == 1) && (swe_trace_data_buffer_ren == 1'b1))
          begin
            swe_trace_data_buffer_empty <= 1'b1;
          end
        else if ((swe_trace_data_buffer_diff_ptr == 0) && (swe_trace_data_buffer_wen == 1'b1))
          begin
            swe_trace_data_buffer_empty <= 1'b0;
          end
      end
  end
//}

wire [2:0] atb_clk_ratio_tb;
assign atb_clk_ratio_tb=`RTT_ATB_RATIO -1;
reg  [2:0] atb_clk_en_cntr;

assign atclken  = (atb_clk_ratio_tb == 0)? 1: (atb_clk_en_cntr == atb_clk_ratio_tb);

always@(posedge rtt_clk or posedge rst_a)
  begin
    if (rst_a == 1'b1)
      begin
        atb_clk_en_cntr <= 3'b0;
      end
    else
      begin
        if (atb_clk_en_cntr == atb_clk_ratio_tb)
          begin
            atb_clk_en_cntr <= 3'b0;
          end
        else
          begin
            atb_clk_en_cntr <= atb_clk_en_cntr + 1;
          end
      end
  end




////////////////////////////////////////////////////////////////////////
// External Interface
////////////////////////////////////////////////////////////////////////


assign trace_mem_base_addr=32'd2147483648;

reg [1:0] axi_state;

localparam IDLE_STATE= 2'b00;
localparam AWREADY_STATE= 2'b01;
localparam WREADY_STATE= 2'b10;

`define CS_TRACE_SIZE 9

always@(posedge clk, posedge rst_a)
begin
    if (rst_a == 1'b1)
    begin
      bri4tb_awaddr <= trace_mem_base_addr;
      trace_mem_ofs <= 0;
      trace_mem_ptr <= 0;
      trace_data_buffer_rd_ptr   <= 0;


      bri4tb_awlen <= 4'd0;
      bri4tb_awsize <= 3'd0;
      bri4tb_awburst <= 2'd0;
      bri4tb_awvalid <= 1'b0;

      bri4tb_wdata <= 32'd0;
      bri4tb_wstrb <= 4'd0;
      bri4tb_wlast <= 1'b0;
      bri4tb_wvalid <= 1'b0;

      axi_state <= IDLE_STATE;
    end

    else if (mbus_clk_en == 1'b1)
    begin
      bri4tb_awlen <= 4'd0;
      bri4tb_awsize <= 3'd2;
      bri4tb_wstrb <= 4'b1111;
      bri4tb_awburst <= 2'd1;


      case (axi_state)
      IDLE_STATE:
        begin
          bri4tb_awvalid <= 1'b0;
          bri4tb_wlast   <= 1'b0;
          bri4tb_wvalid  <= 1'b0;
          if (
               (trace_data_buffer_empty == 0) ||
               0)
              begin
                bri4tb_awvalid <= 1'b1;
                      axi_state <= AWREADY_STATE;
             if (trace_data_buffer_empty == 0)
               begin
                 bri4tb_awaddr <= trace_mem_base_addr + trace_mem_ofs + trace_mem_ptr;
                end


              end
           else
             begin
               bri4tb_awvalid <= 1'b0;
             end
               end

            AWREADY_STATE:
        begin
          if (bri4tb_awready)
            begin
              bri4tb_awvalid <= 1'b0;
              bri4tb_wvalid  <= 1'b1;
              bri4tb_wlast <= 1'b1;
             if (dummy_sig == 1'b1)
               begin
                 bri4tb_awvalid <= 1'b1;
                       axi_state      <= AWREADY_STATE;
               end
             else if (trace_data_buffer_empty == 0)
               begin
                 trace_mem_ptr <= trace_mem_ptr + 8;
                 bri4tb_wdata   <= trace_data_buffer[trace_data_buffer_rd_ptr][31:0];
                 trace_data_buffer_rd_ptr <= trace_data_buffer_rd_ptr + 1;
              end
                   axi_state <= WREADY_STATE;
           end
        end

            WREADY_STATE:
         begin
           if (bri4tb_wready)
                   begin
                    bri4tb_wvalid <= 1'b0;
              bri4tb_wlast <= 1'b0;
              if (dummy_sig == 1'b1)
                begin
                  bri4tb_awvalid <= 1'b1;
                        axi_state      <= AWREADY_STATE;
                end
              else if (
                  (trace_data_buffer_empty == 0) ||
                  0)
                begin
                  bri4tb_awvalid <= 1'b1;
                        axi_state <= AWREADY_STATE;
                  if (trace_data_buffer_empty == 0)
                    begin
                      bri4tb_awaddr <= trace_mem_base_addr + trace_mem_ofs + trace_mem_ptr;
                     end
                end
                  else
              begin
                      axi_state <= IDLE_STATE;
                end
            end
          end

           default:
        begin
          bri4tb_awvalid <= 1'b0;
          bri4tb_wlast <= 1'b0;
          bri4tb_wvalid  <= 1'b0;
         end
     endcase
    end
end

always@*
  begin
    trace_data_buffer_ren = 0;
   if (trace_data_buffer_empty == 0)
     begin
       trace_data_buffer_ren = ((axi_state == AWREADY_STATE) && (bri4tb_awready == 1'b1) && (mbus_clk_en == 1'b1) && (trace_data_buffer_empty == 1'b0));
    end
  end




//---------------------------------------------------------



reg start_swe_test,stop_swe_test,swe_trace_generation_enable;
reg [5:0] start_cntr,stop_cntr;
reg [5:0] db_reg_apbic;
reg [8:0] apbic_start_cnt;
wire       apbic_test_en;
logic       all_reset_done;


assign        apbic_test_en = db_reg_apbic != 6'd58 && apbic_start_cnt[8];
           



 

initial
begin

  all_reset_done = 0;
  wait(`NPU_TOP.sl15_rst_a == 0);
  all_reset_done = 1 ;

end



always@(posedge rtt_clk or posedge rst_a)
  begin
    if (rst_a == 1'b1)
      begin
        start_swe_test     <= 1'b0;
        stop_swe_test      <= 1'b0;
        start_cntr         <= 6'b0;
        stop_cntr          <= 6'b0;
        apbic_start_cnt    <= 6'd0;
        swe_trace_generation_enable <= 1'b0;
      end
    else
      begin
        if(apbic_start_cnt[8] == 1'b0 && all_reset_done)
          apbic_start_cnt    <= apbic_start_cnt + 1;
        if(!apbic_test_en && all_reset_done)
          start_cntr <= start_cntr + 1;
        if ((start_cntr[5] == 1'b1))
          begin
            start_swe_test <= 1'b1;
            start_cntr     <= 1'b0;
          end

        if (swe_atvalid == 1'b1)
          begin
            swe_trace_generation_enable <= 1'b1;
          end

        if ((stop_swe_test == 1'b0) && (swe_trace_generation_enable == 1'b1))
          begin
            if (`NPU_TOP.u_npu_core.u_npu_core_pd.u_l2arc_grp.u_rtt.u_rtt_swe_prdcr_top.u_rtt_encapsulation_top.msg_seq_order_q_wr_ptr == 'd7)
              begin
                stop_swe_test <= 1'b1;
              end
          end
      end
  end  

reg apb_wr_swe_prdcr_sel,swe_prdcr_disable,apb_wr_swe_flush;
reg [1:0] swe_programming_seq,db_reg,wr_filter_reg;
reg flush_complete;
logic [63:0] tcode_dout;
logic [255:0] tcode_dout_long;
assign tcode_dout = tcode_dout_long[63:0];
wire [31:0] addr,wdata;
assign addr = (flush_complete && wr_filter_reg != 2'd2) ? (32'h40 + wr_filter_reg) :  32'h1_0077;
assign wdata = (flush_complete && wr_filter_reg != 2'd2) ? (wr_filter_reg == 2'd0) ? tcode_dout[31:0] : tcode_dout[63:32] : {{15{1'b0}},{17{1'b1}}}; 

//assign arct0_dbgen = 0;
//assign arct0_niden = 0;
initial
begin
        arct0_paddrdbg       =0;
        arct0_pwritedbg      =0;
        arct0_pseldbg        =0;
        arct0_penabledbg     =0;
        arct0_pwdatadbg      =0;
        apb_wr_swe_prdcr_sel =0;
        swe_prdcr_disable    =0;
        apb_wr_swe_flush     =0;
        swe_programming_seq  =0;
        db_reg               =0;
        wr_filter_reg        =0;
        db_reg_apbic         =0;               
end



//===================================================
// Coverage for Debug APB
//===================================================
int total_clients = 1  + `NPU_HAS_L2ARC  + `DUO_L2ARC +  (`NPU_NUM_GRP * `NPU_NUM_SLC_PER_GRP);
parameter bit [31:0]  IDR        = 32'hDFC;
parameter bit [31:0]  ITCTRL     = 32'hF00;
parameter bit [31:0]  CLAIMSET   = 32'hFA0;
parameter bit [31:0]  CLAIMCLR   = 32'hFA4;
parameter bit [31:0]  DEVAFF0    = 32'hFA8;
parameter bit [31:0]  DEVAFF1    = 32'hFAC;
parameter bit [31:0]  LAR        = 32'hFB0;
parameter bit [31:0]  LSR        = 32'hFB4;
parameter bit [31:0]  AUTHSTATUS = 32'hFB8;
parameter bit [31:0]  DEVARCH    = 32'hFBC;
parameter bit [31:0]  DEVID2     = 32'hFC0;
parameter bit [31:0]  DEVID1     = 32'hFC4;
parameter bit [31:0]  DEVID      = 32'hFC8;
parameter bit [31:0]  DEVTYPE    = 32'hFCC;
parameter bit [31:0]  PIDR4      = 32'hFD0;
parameter bit [31:0]  PIDR5      = 32'hFD4;
parameter bit [31:0]  PIDR6      = 32'hFD8;
parameter bit [31:0]  PIDR7      = 32'hFDC;
parameter bit [31:0]  PIDR0      = 32'hFE0;
parameter bit [31:0]  PIDR1      = 32'hFE4;
parameter bit [31:0]  PIDR2      = 32'hFE8;
parameter bit [31:0]  PIDR3      = 32'hFEC;
parameter bit [31:0]  CIDR0      = 32'hFF0;
parameter bit [31:0]  CIDR1      = 32'hFF4;
parameter bit [31:0]  CIDR2      = 32'hFF8;
parameter bit [31:0]  CIDR3      = 32'hFFC;
covergroup dbg_apb_cov @ (posedge clk);
 dbg_apb_top_offset_regs_rd: coverpoint  `ARCHIPELAGO.arct0_paddrdbg {
                                    bins top_offset_addr = {0};
                                    bins trace_offset_addr = {1};
                                    bins l2_0_offset_addr  = {2};
                                    bins l2_1_offset_addr  = {3};
                                     bins l1_0_offset_addr = {4};
                                     bins l1_1_offset_addr = {5};
                                     bins l1_2_offset_addr = {6};
                                     bins l1_3_offset_addr = {7};
                                     bins l1_4_offset_addr = {8};
                                     bins l1_5_offset_addr = {9};
                                     bins l1_6_offset_addr = {10};
                                     bins l1_7_offset_addr = {11};
                                     bins l1_8_offset_addr = {12};
                                     bins l1_9_offset_addr = {13};
                                     bins l1_10_offset_addr = {14};
                                     bins l1_11_offset_addr = {15};
                                     bins l1_12_offset_addr = {16};
                                     bins l1_13_offset_addr = {17};
                                     bins l1_14_offset_addr = {18};
                                     bins l1_15_offset_addr = {19};
                                    bins undefined_offset = {total_clients};
                                 }

  dbg_apb_top_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd0,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd0,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd0,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd0,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd0,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd0,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd0,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd0,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd0,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd0,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd0,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd0,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd0,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd0,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd0,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd0,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd0,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd0,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd0,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd0,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd0,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd0,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd0,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd0,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd0,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd0,CIDR3[11:2]}};
                                }
  dbg_apb_trace_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd1,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd1,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd1,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd1,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd1,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd1,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd1,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd1,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd1,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd1,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd1,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd1,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd1,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd1,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd1,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd1,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd1,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd1,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd1,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd1,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd1,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd1,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd1,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd1,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd1,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd1,CIDR3[11:2]}};
                                }
  dbg_apb_l2_0_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd2,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd2,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd2,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd2,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd2,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd2,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd2,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd2,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd2,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd2,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd2,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd2,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd2,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd2,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd2,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd2,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd2,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd2,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd2,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd2,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd2,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd2,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd2,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd2,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd2,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd2,CIDR3[11:2]}};
                                }
  dbg_apb_l2_1_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd3,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd3,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd3,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd3,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd3,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd3,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd3,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd3,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd3,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd3,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd3,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd3,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd3,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd3,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd3,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd3,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd3,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd3,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd3,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd3,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd3,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd3,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd3,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd3,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd3,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd3,CIDR3[11:2]}};
                                }
  dbg_apb_l1_0_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd4,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd4,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd4,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd4,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd4,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd4,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd4,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd4,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd4,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd4,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd4,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd4,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd4,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd4,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd4,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd4,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd4,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd4,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd4,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd4,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd4,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd4,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd4,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd4,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd4,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd4,CIDR3[11:2]}};
                                }
  dbg_apb_l1_1_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd5,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd5,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd5,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd5,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd5,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd5,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd5,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd5,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd5,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd5,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd5,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd5,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd5,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd5,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd5,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd5,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd5,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd5,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd5,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd5,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd5,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd5,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd5,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd5,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd5,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd5,CIDR3[11:2]}};
                                }
  dbg_apb_l1_2_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd6,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd6,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd6,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd6,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd6,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd6,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd6,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd6,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd6,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd6,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd6,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd6,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd6,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd6,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd6,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd6,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd6,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd6,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd6,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd6,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd6,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd6,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd6,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd6,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd6,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd6,CIDR3[11:2]}};
                                }
  dbg_apb_l1_3_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd7,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd7,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd7,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd7,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd7,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd7,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd7,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd7,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd7,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd7,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd7,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd7,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd7,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd7,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd7,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd7,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd7,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd7,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd7,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd7,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd7,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd7,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd7,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd7,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd7,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd7,CIDR3[11:2]}};
                                }
  dbg_apb_l1_4_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd8,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd8,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd8,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd8,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd8,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd8,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd8,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd8,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd8,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd8,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd8,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd8,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd8,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd8,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd8,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd8,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd8,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd8,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd8,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd8,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd8,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd8,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd8,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd8,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd8,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd8,CIDR3[11:2]}};
                                }
  dbg_apb_l1_5_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd9,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd9,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd9,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd9,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd9,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd9,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd9,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd9,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd9,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd9,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd9,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd9,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd9,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd9,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd9,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd9,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd9,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd9,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd9,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd9,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd9,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd9,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd9,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd9,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd9,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd9,CIDR3[11:2]}};
                                }
  dbg_apb_l1_6_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd10,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd10,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd10,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd10,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd10,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd10,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd10,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd10,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd10,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd10,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd10,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd10,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd10,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd10,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd10,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd10,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd10,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd10,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd10,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd10,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd10,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd10,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd10,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd10,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd10,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd10,CIDR3[11:2]}};
                                }
  dbg_apb_l1_7_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd11,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd11,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd11,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd11,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd11,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd11,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd11,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd11,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd11,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd11,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd11,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd11,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd11,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd11,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd11,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd11,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd11,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd11,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd11,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd11,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd11,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd11,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd11,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd11,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd11,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd11,CIDR3[11:2]}};
                                }
  dbg_apb_l1_8_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd12,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd12,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd12,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd12,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd12,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd12,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd12,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd12,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd12,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd12,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd12,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd12,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd12,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd12,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd12,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd12,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd12,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd12,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd12,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd12,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd12,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd12,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd12,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd12,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd12,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd12,CIDR3[11:2]}};
                                }
  dbg_apb_l1_9_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd13,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd13,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd13,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd13,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd13,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd13,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd13,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd13,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd13,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd13,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd13,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd13,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd13,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd13,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd13,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd13,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd13,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd13,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd13,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd13,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd13,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd13,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd13,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd13,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd13,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd13,CIDR3[11:2]}};
                                }
  dbg_apb_l1_10_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd14,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd14,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd14,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd14,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd14,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd14,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd14,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd14,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd14,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd14,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd14,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd14,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd14,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd14,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd14,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd14,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd14,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd14,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd14,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd14,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd14,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd14,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd14,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd14,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd14,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd14,CIDR3[11:2]}};
                                }
  dbg_apb_l1_11_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd15,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd15,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd15,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd15,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd15,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd15,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd15,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd15,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd15,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd15,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd15,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd15,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd15,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd15,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd15,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd15,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd15,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd15,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd15,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd15,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd15,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd15,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd15,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd15,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd15,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd15,CIDR3[11:2]}};
                                }
  dbg_apb_l1_12_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd16,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd16,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd16,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd16,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd16,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd16,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd16,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd16,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd16,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd16,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd16,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd16,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd16,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd16,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd16,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd16,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd16,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd16,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd16,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd16,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd16,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd16,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd16,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd16,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd16,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd16,CIDR3[11:2]}};
                                }
  dbg_apb_l1_13_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd17,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd17,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd17,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd17,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd17,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd17,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd17,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd17,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd17,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd17,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd17,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd17,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd17,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd17,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd17,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd17,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd17,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd17,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd17,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd17,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd17,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd17,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd17,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd17,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd17,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd17,CIDR3[11:2]}};
                                }
  dbg_apb_l1_14_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd18,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd18,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd18,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd18,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd18,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd18,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd18,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd18,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd18,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd18,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd18,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd18,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd18,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd18,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd18,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd18,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd18,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd18,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd18,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd18,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd18,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd18,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd18,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd18,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd18,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd18,CIDR3[11:2]}};
                                }
  dbg_apb_l1_15_rom_table_rd: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  bins IDR_RD        = {{2'b0,20'd19,IDR[11:2]}};
                                  bins ITCTRL_RD     = {{2'b0,20'd19,ITCTRL[11:2]}};
                                  bins CLAIMSET_RD   = {{2'b0,20'd19,CLAIMSET[11:2]}};
                                  bins CLAIMCLR_RD   = {{2'b0,20'd19,CLAIMCLR[11:2]}};
                                  bins DEVAFF0_RD    = {{2'b0,20'd19,DEVAFF0[11:2]}};
                                  bins DEVAFF1_RD    = {{2'b0,20'd19,DEVAFF1[11:2]}};
                                  bins LAR_RD        = {{2'b0,20'd19,LAR[11:2]}};
                                  bins LSR_RD        = {{2'b0,20'd19,LSR[11:2]}};
                                  bins AUTHSTATUS_RD = {{2'b0,20'd19,AUTHSTATUS[11:2]}};
                                  bins DEVARCH_RD    = {{2'b0,20'd19,DEVARCH[11:2]}};
                                  bins DEVID2_RD     = {{2'b0,20'd19,DEVID2[11:2]}};
                                  bins DEVID1_RD     = {{2'b0,20'd19,DEVID1[11:2]}};
                                  bins DEVID_RD      = {{2'b0,20'd19,DEVID[11:2]}};
                                  bins DEVTYPE_RD    = {{2'b0,20'd19,DEVTYPE[11:2]}};
                                  bins PIDR4_RD      = {{2'b0,20'd19,PIDR4[11:2]}};
                                  bins PIDR5_RD      = {{2'b0,20'd19,PIDR5[11:2]}};
                                  bins PIDR6_RD      = {{2'b0,20'd19,PIDR6[11:2]}};
                                  bins PIDR7_RD      = {{2'b0,20'd19,PIDR7[11:2]}};
                                  bins PIDR0_RD      = {{2'b0,20'd19,PIDR0[11:2]}};
                                  bins PIDR1_RD      = {{2'b0,20'd19,PIDR1[11:2]}};
                                  bins PIDR2_RD      = {{2'b0,20'd19,PIDR2[11:2]}};
                                  bins PIDR3_RD      = {{2'b0,20'd19,PIDR3[11:2]}};
                                  bins CIDR0_RD      = {{2'b0,20'd19,CIDR0[11:2]}};
                                  bins CIDR1_RD      = {{2'b0,20'd19,CIDR1[11:2]}};
                                  bins CIDR2_RD      = {{2'b0,20'd19,CIDR2[11:2]}};
                                  bins CIDR3_RD      = {{2'b0,20'd19,CIDR3[11:2]}};
                                }
  dbg_apb_slave_error: coverpoint `ARCHIPELAGO.arct0_pslverrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg) ;

  dbg_apb_write_read: coverpoint `ARCHIPELAGO.arct0_pwritedbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
    bins WRITE  = {1};
    bins READ   = {0};
  }
  
  dbg_apb_write_data: coverpoint `ARCHIPELAGO.arct0_pwdatadbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
    bins DB_CMB_CORE_WR = {'h1};
    bins DB_CMB_CORE_RD = {'h5};
  }
  dbg_apb_l2_0_addr_access: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  
    bins DB_ADDR            = {{2'b0,20'd2,10'b10}};
    bins DB_CMD             = {{2'b0,20'd2,10'b01}};
    bins DB_DATA            = {{2'b0,20'd2,10'b11}};
    bins DB_STAT            = {{2'b0,20'd2,10'b00}};
  }
  dbg_apb_l2_0_core_wr_rd : cross dbg_apb_l2_0_addr_access,dbg_apb_write_read, dbg_apb_write_data {
    ignore_bins ig1 = (binsof(dbg_apb_l2_0_addr_access) intersect {{2'b0,20'd2,10'b00},{2'b0,20'd2,10'b10},{2'b0,20'd2,10'b11}});
    ignore_bins ig2 = (binsof(dbg_apb_write_read) intersect {0});
  }
  
  dbg_apb_l2_1_addr_access: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  
    bins DB_ADDR            = {{2'b0,20'd3,10'b10}};
    bins DB_CMD             = {{2'b0,20'd3,10'b01}};
    bins DB_DATA            = {{2'b0,20'd3,10'b11}};
    bins DB_STAT            = {{2'b0,20'd3,10'b00}};
  }
  dbg_apb_l2_1_core_wr_rd : cross dbg_apb_l2_1_addr_access,dbg_apb_write_read, dbg_apb_write_data {
    ignore_bins ig1 = (binsof(dbg_apb_l2_1_addr_access) intersect {{2'b0,20'd3,10'b00},{2'b0,20'd3,10'b10},{2'b0,20'd3,10'b11}});
    ignore_bins ig2 = (binsof(dbg_apb_write_read) intersect {0});
  }
  
  dbg_apb_l1_0_addr_access: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  
    bins DB_ADDR            = {{2'b0,20'd4,10'b10}};
    bins DB_CMD             = {{2'b0,20'd4,10'b01}};
    bins DB_DATA            = {{2'b0,20'd4,10'b11}};
    bins DB_STAT            = {{2'b0,20'd4,10'b00}};
  }
  dbg_apb_l1_0_core_wr_rd : cross dbg_apb_l1_0_addr_access,dbg_apb_write_read, dbg_apb_write_data {
    ignore_bins ig1 = (binsof(dbg_apb_l1_0_addr_access) intersect {{2'b0,20'd4,10'b00},{2'b0,20'd4,10'b10},{2'b0,20'd4,10'b11}});
    ignore_bins ig2 = (binsof(dbg_apb_write_read) intersect {0});
  }
  
  dbg_apb_l1_1_addr_access: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  
    bins DB_ADDR            = {{2'b0,20'd5,10'b10}};
    bins DB_CMD             = {{2'b0,20'd5,10'b01}};
    bins DB_DATA            = {{2'b0,20'd5,10'b11}};
    bins DB_STAT            = {{2'b0,20'd5,10'b00}};
  }
  dbg_apb_l1_1_core_wr_rd : cross dbg_apb_l1_1_addr_access,dbg_apb_write_read, dbg_apb_write_data {
    ignore_bins ig1 = (binsof(dbg_apb_l1_1_addr_access) intersect {{2'b0,20'd5,10'b00},{2'b0,20'd5,10'b10},{2'b0,20'd5,10'b11}});
    ignore_bins ig2 = (binsof(dbg_apb_write_read) intersect {0});
  }
  
  dbg_apb_l1_2_addr_access: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  
    bins DB_ADDR            = {{2'b0,20'd6,10'b10}};
    bins DB_CMD             = {{2'b0,20'd6,10'b01}};
    bins DB_DATA            = {{2'b0,20'd6,10'b11}};
    bins DB_STAT            = {{2'b0,20'd6,10'b00}};
  }
  dbg_apb_l1_2_core_wr_rd : cross dbg_apb_l1_2_addr_access,dbg_apb_write_read, dbg_apb_write_data {
    ignore_bins ig1 = (binsof(dbg_apb_l1_2_addr_access) intersect {{2'b0,20'd6,10'b00},{2'b0,20'd6,10'b10},{2'b0,20'd6,10'b11}});
    ignore_bins ig2 = (binsof(dbg_apb_write_read) intersect {0});
  }
  
  dbg_apb_l1_3_addr_access: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  
    bins DB_ADDR            = {{2'b0,20'd7,10'b10}};
    bins DB_CMD             = {{2'b0,20'd7,10'b01}};
    bins DB_DATA            = {{2'b0,20'd7,10'b11}};
    bins DB_STAT            = {{2'b0,20'd7,10'b00}};
  }
  dbg_apb_l1_3_core_wr_rd : cross dbg_apb_l1_3_addr_access,dbg_apb_write_read, dbg_apb_write_data {
    ignore_bins ig1 = (binsof(dbg_apb_l1_3_addr_access) intersect {{2'b0,20'd7,10'b00},{2'b0,20'd7,10'b10},{2'b0,20'd7,10'b11}});
    ignore_bins ig2 = (binsof(dbg_apb_write_read) intersect {0});
  }
  
  dbg_apb_l1_4_addr_access: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  
    bins DB_ADDR            = {{2'b0,20'd8,10'b10}};
    bins DB_CMD             = {{2'b0,20'd8,10'b01}};
    bins DB_DATA            = {{2'b0,20'd8,10'b11}};
    bins DB_STAT            = {{2'b0,20'd8,10'b00}};
  }
  dbg_apb_l1_4_core_wr_rd : cross dbg_apb_l1_4_addr_access,dbg_apb_write_read, dbg_apb_write_data {
    ignore_bins ig1 = (binsof(dbg_apb_l1_4_addr_access) intersect {{2'b0,20'd8,10'b00},{2'b0,20'd8,10'b10},{2'b0,20'd8,10'b11}});
    ignore_bins ig2 = (binsof(dbg_apb_write_read) intersect {0});
  }
  
  dbg_apb_l1_5_addr_access: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  
    bins DB_ADDR            = {{2'b0,20'd9,10'b10}};
    bins DB_CMD             = {{2'b0,20'd9,10'b01}};
    bins DB_DATA            = {{2'b0,20'd9,10'b11}};
    bins DB_STAT            = {{2'b0,20'd9,10'b00}};
  }
  dbg_apb_l1_5_core_wr_rd : cross dbg_apb_l1_5_addr_access,dbg_apb_write_read, dbg_apb_write_data {
    ignore_bins ig1 = (binsof(dbg_apb_l1_5_addr_access) intersect {{2'b0,20'd9,10'b00},{2'b0,20'd9,10'b10},{2'b0,20'd9,10'b11}});
    ignore_bins ig2 = (binsof(dbg_apb_write_read) intersect {0});
  }
  
  dbg_apb_l1_6_addr_access: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  
    bins DB_ADDR            = {{2'b0,20'd10,10'b10}};
    bins DB_CMD             = {{2'b0,20'd10,10'b01}};
    bins DB_DATA            = {{2'b0,20'd10,10'b11}};
    bins DB_STAT            = {{2'b0,20'd10,10'b00}};
  }
  dbg_apb_l1_6_core_wr_rd : cross dbg_apb_l1_6_addr_access,dbg_apb_write_read, dbg_apb_write_data {
    ignore_bins ig1 = (binsof(dbg_apb_l1_6_addr_access) intersect {{2'b0,20'd10,10'b00},{2'b0,20'd10,10'b10},{2'b0,20'd10,10'b11}});
    ignore_bins ig2 = (binsof(dbg_apb_write_read) intersect {0});
  }
  
  dbg_apb_l1_7_addr_access: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  
    bins DB_ADDR            = {{2'b0,20'd11,10'b10}};
    bins DB_CMD             = {{2'b0,20'd11,10'b01}};
    bins DB_DATA            = {{2'b0,20'd11,10'b11}};
    bins DB_STAT            = {{2'b0,20'd11,10'b00}};
  }
  dbg_apb_l1_7_core_wr_rd : cross dbg_apb_l1_7_addr_access,dbg_apb_write_read, dbg_apb_write_data {
    ignore_bins ig1 = (binsof(dbg_apb_l1_7_addr_access) intersect {{2'b0,20'd11,10'b00},{2'b0,20'd11,10'b10},{2'b0,20'd11,10'b11}});
    ignore_bins ig2 = (binsof(dbg_apb_write_read) intersect {0});
  }
  
  dbg_apb_l1_8_addr_access: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  
    bins DB_ADDR            = {{2'b0,20'd12,10'b10}};
    bins DB_CMD             = {{2'b0,20'd12,10'b01}};
    bins DB_DATA            = {{2'b0,20'd12,10'b11}};
    bins DB_STAT            = {{2'b0,20'd12,10'b00}};
  }
  dbg_apb_l1_8_core_wr_rd : cross dbg_apb_l1_8_addr_access,dbg_apb_write_read, dbg_apb_write_data {
    ignore_bins ig1 = (binsof(dbg_apb_l1_8_addr_access) intersect {{2'b0,20'd12,10'b00},{2'b0,20'd12,10'b10},{2'b0,20'd12,10'b11}});
    ignore_bins ig2 = (binsof(dbg_apb_write_read) intersect {0});
  }
  
  dbg_apb_l1_9_addr_access: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  
    bins DB_ADDR            = {{2'b0,20'd13,10'b10}};
    bins DB_CMD             = {{2'b0,20'd13,10'b01}};
    bins DB_DATA            = {{2'b0,20'd13,10'b11}};
    bins DB_STAT            = {{2'b0,20'd13,10'b00}};
  }
  dbg_apb_l1_9_core_wr_rd : cross dbg_apb_l1_9_addr_access,dbg_apb_write_read, dbg_apb_write_data {
    ignore_bins ig1 = (binsof(dbg_apb_l1_9_addr_access) intersect {{2'b0,20'd13,10'b00},{2'b0,20'd13,10'b10},{2'b0,20'd13,10'b11}});
    ignore_bins ig2 = (binsof(dbg_apb_write_read) intersect {0});
  }
  
  dbg_apb_l1_10_addr_access: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  
    bins DB_ADDR            = {{2'b0,20'd14,10'b10}};
    bins DB_CMD             = {{2'b0,20'd14,10'b01}};
    bins DB_DATA            = {{2'b0,20'd14,10'b11}};
    bins DB_STAT            = {{2'b0,20'd14,10'b00}};
  }
  dbg_apb_l1_10_core_wr_rd : cross dbg_apb_l1_10_addr_access,dbg_apb_write_read, dbg_apb_write_data {
    ignore_bins ig1 = (binsof(dbg_apb_l1_10_addr_access) intersect {{2'b0,20'd14,10'b00},{2'b0,20'd14,10'b10},{2'b0,20'd14,10'b11}});
    ignore_bins ig2 = (binsof(dbg_apb_write_read) intersect {0});
  }
  
  dbg_apb_l1_11_addr_access: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  
    bins DB_ADDR            = {{2'b0,20'd15,10'b10}};
    bins DB_CMD             = {{2'b0,20'd15,10'b01}};
    bins DB_DATA            = {{2'b0,20'd15,10'b11}};
    bins DB_STAT            = {{2'b0,20'd15,10'b00}};
  }
  dbg_apb_l1_11_core_wr_rd : cross dbg_apb_l1_11_addr_access,dbg_apb_write_read, dbg_apb_write_data {
    ignore_bins ig1 = (binsof(dbg_apb_l1_11_addr_access) intersect {{2'b0,20'd15,10'b00},{2'b0,20'd15,10'b10},{2'b0,20'd15,10'b11}});
    ignore_bins ig2 = (binsof(dbg_apb_write_read) intersect {0});
  }
  
  dbg_apb_l1_12_addr_access: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  
    bins DB_ADDR            = {{2'b0,20'd16,10'b10}};
    bins DB_CMD             = {{2'b0,20'd16,10'b01}};
    bins DB_DATA            = {{2'b0,20'd16,10'b11}};
    bins DB_STAT            = {{2'b0,20'd16,10'b00}};
  }
  dbg_apb_l1_12_core_wr_rd : cross dbg_apb_l1_12_addr_access,dbg_apb_write_read, dbg_apb_write_data {
    ignore_bins ig1 = (binsof(dbg_apb_l1_12_addr_access) intersect {{2'b0,20'd16,10'b00},{2'b0,20'd16,10'b10},{2'b0,20'd16,10'b11}});
    ignore_bins ig2 = (binsof(dbg_apb_write_read) intersect {0});
  }
  
  dbg_apb_l1_13_addr_access: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  
    bins DB_ADDR            = {{2'b0,20'd17,10'b10}};
    bins DB_CMD             = {{2'b0,20'd17,10'b01}};
    bins DB_DATA            = {{2'b0,20'd17,10'b11}};
    bins DB_STAT            = {{2'b0,20'd17,10'b00}};
  }
  dbg_apb_l1_13_core_wr_rd : cross dbg_apb_l1_13_addr_access,dbg_apb_write_read, dbg_apb_write_data {
    ignore_bins ig1 = (binsof(dbg_apb_l1_13_addr_access) intersect {{2'b0,20'd17,10'b00},{2'b0,20'd17,10'b10},{2'b0,20'd17,10'b11}});
    ignore_bins ig2 = (binsof(dbg_apb_write_read) intersect {0});
  }
  
  dbg_apb_l1_14_addr_access: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  
    bins DB_ADDR            = {{2'b0,20'd18,10'b10}};
    bins DB_CMD             = {{2'b0,20'd18,10'b01}};
    bins DB_DATA            = {{2'b0,20'd18,10'b11}};
    bins DB_STAT            = {{2'b0,20'd18,10'b00}};
  }
  dbg_apb_l1_14_core_wr_rd : cross dbg_apb_l1_14_addr_access,dbg_apb_write_read, dbg_apb_write_data {
    ignore_bins ig1 = (binsof(dbg_apb_l1_14_addr_access) intersect {{2'b0,20'd18,10'b00},{2'b0,20'd18,10'b10},{2'b0,20'd18,10'b11}});
    ignore_bins ig2 = (binsof(dbg_apb_write_read) intersect {0});
  }
  
  dbg_apb_l1_15_addr_access: coverpoint `ARCHIPELAGO.arct0_paddrdbg iff (`ARCHIPELAGO.arct0_penabledbg && `ARCHIPELAGO.arct0_pseldbg && `ARCHIPELAGO.arct0_preadydbg && !`ARCHIPELAGO.arct0_pslverrdbg) {
                                  
    bins DB_ADDR            = {{2'b0,20'd19,10'b10}};
    bins DB_CMD             = {{2'b0,20'd19,10'b01}};
    bins DB_DATA            = {{2'b0,20'd19,10'b11}};
    bins DB_STAT            = {{2'b0,20'd19,10'b00}};
  }
  dbg_apb_l1_15_core_wr_rd : cross dbg_apb_l1_15_addr_access,dbg_apb_write_read, dbg_apb_write_data {
    ignore_bins ig1 = (binsof(dbg_apb_l1_15_addr_access) intersect {{2'b0,20'd19,10'b00},{2'b0,20'd19,10'b10},{2'b0,20'd19,10'b11}});
    ignore_bins ig2 = (binsof(dbg_apb_write_read) intersect {0});
  }
  
  
endgroup
dbg_apb_cov dbg_apb_cov_inst;
initial dbg_apb_cov_inst = new(); 
//===================================================

wire start_parsing;
assign start_parsing = (`NPU_TOP.u_npu_core.u_npu_core_pd.u_l2arc_grp.u_rtt.flush_done) || (`NPU_TOP.u_npu_core.u_npu_core_pd.u_l2arc_grp.u_rtt.swe_flush_done) ;  

reg [31:0] parser_din [39:0];


logic atvalid_r;
logic swe_atvalid_r;
logic push_data;
logic push_data_r;
logic normal_push;
logic swe_push;

logic [16-1:0] swe_tcode_pass;
assign swe_tcode_pass[0] = tcode_dout_long[15:0] == 16'h073d;
      assign swe_tcode_pass[1] = tcode_dout_long[(1+2)*8-1:(1+1)*8] == 8'h07;
      assign swe_tcode_pass[2] = tcode_dout_long[(2+2)*8-1:(2+1)*8] == 8'h07;
      assign swe_tcode_pass[3] = tcode_dout_long[(3+2)*8-1:(3+1)*8] == 8'h07;
      assign swe_tcode_pass[4] = tcode_dout_long[(4+2)*8-1:(4+1)*8] == 8'h07;
      assign swe_tcode_pass[5] = tcode_dout_long[(5+2)*8-1:(5+1)*8] == 8'h07;
      assign swe_tcode_pass[6] = tcode_dout_long[(6+2)*8-1:(6+1)*8] == 8'h07;
      assign swe_tcode_pass[7] = tcode_dout_long[(7+2)*8-1:(7+1)*8] == 8'h07;
      assign swe_tcode_pass[8] = tcode_dout_long[(8+2)*8-1:(8+1)*8] == 8'h07;
      assign swe_tcode_pass[9] = tcode_dout_long[(9+2)*8-1:(9+1)*8] == 8'h07;
      assign swe_tcode_pass[10] = tcode_dout_long[(10+2)*8-1:(10+1)*8] == 8'h07;
      assign swe_tcode_pass[11] = tcode_dout_long[(11+2)*8-1:(11+1)*8] == 8'h07;
      assign swe_tcode_pass[12] = tcode_dout_long[(12+2)*8-1:(12+1)*8] == 8'h07;
      assign swe_tcode_pass[13] = tcode_dout_long[(13+2)*8-1:(13+1)*8] == 8'h07;
      assign swe_tcode_pass[14] = tcode_dout_long[(14+2)*8-1:(14+1)*8] == 8'h07;
      assign swe_tcode_pass[15] = tcode_dout_long[(15+2)*8-1:(15+1)*8] == 8'h07;

assign normal_push = (atvalid_r && !atvalid);
assign swe_push    = (swe_atvalid_r && !swe_atvalid);
assign  push_data = normal_push || swe_push;

  always @(posedge `NPU_TOP.u_npu_core.u_npu_core_pd.u_l2arc_grp.u_rtt.rtt_clk)
begin
atvalid_r <= atvalid;
swe_atvalid_r <= swe_atvalid;
push_data_r <= push_data;
end 






always@*
begin
if(normal_push)
  begin
      parser_din[0] = trace_data_buffer_din[0][31:0];
      parser_din[1] = trace_data_buffer_din[0][63:32];
      parser_din[2] = trace_data_buffer_din[1][31:0];
      parser_din[3] = trace_data_buffer_din[1][63:32];
      parser_din[4] = trace_data_buffer_din[2][31:0];
      parser_din[5] = trace_data_buffer_din[2][63:32];
      parser_din[6] = trace_data_buffer_din[3][31:0];
      parser_din[7] = trace_data_buffer_din[3][63:32];
      parser_din[8] = trace_data_buffer_din[4][31:0];
      parser_din[9] = trace_data_buffer_din[4][63:32];
      parser_din[10] = trace_data_buffer_din[5][31:0];
      parser_din[11] = trace_data_buffer_din[5][63:32];
      parser_din[12] = trace_data_buffer_din[6][31:0];
      parser_din[13] = trace_data_buffer_din[6][63:32];
      parser_din[14] = trace_data_buffer_din[7][31:0];
      parser_din[15] = trace_data_buffer_din[7][63:32];
      parser_din[16] = trace_data_buffer_din[8][31:0];
      parser_din[17] = trace_data_buffer_din[8][63:32];
      parser_din[18] = trace_data_buffer_din[9][31:0];
      parser_din[19] = trace_data_buffer_din[9][63:32];                              
      parser_din[20] = trace_data_buffer_din[10][31:0];
      parser_din[21] = trace_data_buffer_din[10][63:32];
      parser_din[22] = trace_data_buffer_din[11][31:0];
      parser_din[23] = trace_data_buffer_din[11][63:32];
      parser_din[24] = trace_data_buffer_din[12][31:0];
      parser_din[25] = trace_data_buffer_din[12][63:32];
      parser_din[26] = trace_data_buffer_din[13][31:0];
      parser_din[27] = trace_data_buffer_din[13][63:32];
      parser_din[28] = trace_data_buffer_din[14][31:0];
      parser_din[29] = trace_data_buffer_din[14][63:32];
      parser_din[30] = trace_data_buffer_din[15][31:0];
      parser_din[31] = trace_data_buffer_din[15][63:32];
      parser_din[32] = trace_data_buffer_din[16][31:0];
      parser_din[33] = trace_data_buffer_din[16][63:32];
      parser_din[34] = trace_data_buffer_din[17][31:0];
      parser_din[35] = trace_data_buffer_din[17][63:32];
      parser_din[36] = trace_data_buffer_din[18][31:0];
      parser_din[37] = trace_data_buffer_din[18][63:32];
      parser_din[38] = trace_data_buffer_din[19][31:0];
      parser_din[39] = trace_data_buffer_din[19][63:32];                               
  end

if(swe_push)
  begin
      parser_din[0] = swe_trace_data_buffer_din[0][31:0];
      parser_din[1] = swe_trace_data_buffer_din[0][63:32];
      parser_din[2] = swe_trace_data_buffer_din[1][31:0];
      parser_din[3] = swe_trace_data_buffer_din[1][63:32];
      parser_din[4] = swe_trace_data_buffer_din[2][31:0];
      parser_din[5] = swe_trace_data_buffer_din[2][63:32];
      parser_din[6] = swe_trace_data_buffer_din[3][31:0];
      parser_din[7] = swe_trace_data_buffer_din[3][63:32];
      parser_din[8] = swe_trace_data_buffer_din[4][31:0];
      parser_din[9] = swe_trace_data_buffer_din[4][63:32];
      parser_din[10] = swe_trace_data_buffer_din[5][31:0];
      parser_din[11] = swe_trace_data_buffer_din[5][63:32];
      parser_din[12] = swe_trace_data_buffer_din[6][31:0];
      parser_din[13] = swe_trace_data_buffer_din[6][63:32];
      parser_din[14] = swe_trace_data_buffer_din[7][31:0];
      parser_din[15] = swe_trace_data_buffer_din[7][63:32];
      parser_din[16] = swe_trace_data_buffer_din[8][31:0];
      parser_din[17] = swe_trace_data_buffer_din[8][63:32];
      parser_din[18] = swe_trace_data_buffer_din[9][31:0];
      parser_din[19] = swe_trace_data_buffer_din[9][63:32];                               
      parser_din[20] = swe_trace_data_buffer_din[10][31:0];
      parser_din[21] = swe_trace_data_buffer_din[10][63:32];
      parser_din[22] = swe_trace_data_buffer_din[11][31:0];
      parser_din[23] = swe_trace_data_buffer_din[11][63:32];
      parser_din[24] = swe_trace_data_buffer_din[12][31:0];
      parser_din[25] = swe_trace_data_buffer_din[12][63:32];
      parser_din[26] = swe_trace_data_buffer_din[13][31:0];
      parser_din[27] = swe_trace_data_buffer_din[13][63:32];
      parser_din[28] = swe_trace_data_buffer_din[14][31:0];
      parser_din[29] = swe_trace_data_buffer_din[14][63:32];
      parser_din[30] = swe_trace_data_buffer_din[15][31:0];
      parser_din[31] = swe_trace_data_buffer_din[15][63:32];
      parser_din[32] = swe_trace_data_buffer_din[16][31:0];
      parser_din[33] = swe_trace_data_buffer_din[16][63:32];
      parser_din[34] = swe_trace_data_buffer_din[17][31:0];
      parser_din[35] = swe_trace_data_buffer_din[17][63:32];
      parser_din[36] = swe_trace_data_buffer_din[18][31:0];
      parser_din[37] = swe_trace_data_buffer_din[18][63:32];
      parser_din[38] = swe_trace_data_buffer_din[19][31:0];
      parser_din[39] = swe_trace_data_buffer_din[19][63:32];                                
  end  
end

always@(posedge rtt_clk or posedge rst_a)
  begin
    if (rst_a == 1'b1)
      begin
        flush_complete <= 1'b0;
      end
    else
      begin
       if((`NPU_TOP.u_npu_core.u_npu_core_pd.u_l2arc_grp.u_rtt.flush_done) || (`NPU_TOP.u_npu_core.u_npu_core_pd.u_l2arc_grp.u_rtt.swe_flush_done))
        flush_complete <= 1'b1;
      end
  end


always @(posedge push_data_r or negedge push_data_r or posedge start_parsing) begin rtt_atb_parser((push_data_r||start_parsing),parser_din,tcode_dout_long); end

initial begin
   cti_trace_start = 1'b0;
   cti_trace_stop =  1'b0;
   syncreq=1'b0;
   afvalid=1'b0;
    wait(`NPU_TOP.u_npu_core.u_npu_core_pd.u_l2arc_grp.u_rtt.u_rtt_small_prdcr_regs.rtt_pr_sel);
  cti_trace_start = 1'b1;
  @(posedge rtt_clk);
  @(posedge rtt_clk);
  afvalid=1'b1;
  wait(afready);
  afvalid=1'b0; 
  cti_trace_start = 1'b0;
  @(posedge rtt_clk);
  @(posedge rtt_clk);
  syncreq = 1'b1;
  repeat(4) @(posedge rtt_clk);
  syncreq = 1'b0;
    wait(`NPU_TOP.u_npu_core.u_npu_core_pd.u_l2arc_grp.u_rtt.u_rtt_small_prdcr_regs.rtt_pr_sel==1'b0);
  cti_trace_stop = 1'b1;

  @(posedge rtt_clk);
  @(posedge rtt_clk);
  cti_trace_stop = 1'b0;

end

initial begin

   swe_syncreq=1'b0;
   swe_afvalid=1'b0;
    wait(|`NPU_TOP.u_npu_core.u_npu_core_pd.u_l2arc_grp.u_rtt.u_rtt_swe_prdcr_regs.swe_prdcr_sel);
  swe_afvalid=1'b1;
  wait(swe_afready);
  swe_afvalid=1'b0;

  swe_syncreq=1'b1;
  repeat(4) @(posedge rtt_clk);
  swe_syncreq=1'b0;


end


  always @(posedge `NPU_TOP.u_npu_core.u_npu_core_pd.u_l2arc_grp.u_rtt.rtt_clk)
begin
  if (atclken) begin
    if(syncreq || swe_syncreq)  
      begin
        atready <= 1;
        swe_atready <= 1;
      end
    else if ($random > 0) begin
      atready <= 1;
      swe_atready <= 1;
    end
    else begin
      atready <= 0;
      swe_atready <= 0;
    end
  end
end


//Add assertion to check to rtt swe valid pulse width
property check_pulse_width_SWEIF0;
  @(posedge rtt_clk)
  disable iff(rst_a == 1'b1)
  $rose (`L2ARC_GRP.u_rtt.sl0_alt_rtt_swe_val)  |=>  $fell(`L2ARC_GRP.u_rtt.sl0_alt_rtt_swe_val);
endproperty

ASSERT_PULSE_CHECK_SWE_IF0: assert property (check_pulse_width_SWEIF0)
else begin
      $fatal("RTT SWE IF'p pulse width violation at time %t", $time);  
  end                     
property check_pulse_width_SWEIF1;
  @(posedge rtt_clk)
  disable iff(rst_a == 1'b1)
  $rose (`L2ARC_GRP.u_rtt.sl1_alt_rtt_swe_val)  |=>  $fell(`L2ARC_GRP.u_rtt.sl1_alt_rtt_swe_val);
endproperty

ASSERT_PULSE_CHECK_SWE_IF1: assert property (check_pulse_width_SWEIF1)
else begin
      $fatal("RTT SWE IF'p pulse width violation at time %t", $time);  
  end                     
property check_pulse_width_SWEIF2;
  @(posedge rtt_clk)
  disable iff(rst_a == 1'b1)
  $rose (`L2ARC_GRP.u_rtt.sl2_alt_rtt_swe_val)  |=>  $fell(`L2ARC_GRP.u_rtt.sl2_alt_rtt_swe_val);
endproperty

ASSERT_PULSE_CHECK_SWE_IF2: assert property (check_pulse_width_SWEIF2)
else begin
      $fatal("RTT SWE IF'p pulse width violation at time %t", $time);  
  end                     
property check_pulse_width_SWEIF3;
  @(posedge rtt_clk)
  disable iff(rst_a == 1'b1)
  $rose (`L2ARC_GRP.u_rtt.sl3_alt_rtt_swe_val)  |=>  $fell(`L2ARC_GRP.u_rtt.sl3_alt_rtt_swe_val);
endproperty

ASSERT_PULSE_CHECK_SWE_IF3: assert property (check_pulse_width_SWEIF3)
else begin
      $fatal("RTT SWE IF'p pulse width violation at time %t", $time);  
  end                     
property check_pulse_width_SWEIF4;
  @(posedge rtt_clk)
  disable iff(rst_a == 1'b1)
  $rose (`L2ARC_GRP.u_rtt.sl4_alt_rtt_swe_val)  |=>  $fell(`L2ARC_GRP.u_rtt.sl4_alt_rtt_swe_val);
endproperty

ASSERT_PULSE_CHECK_SWE_IF4: assert property (check_pulse_width_SWEIF4)
else begin
      $fatal("RTT SWE IF'p pulse width violation at time %t", $time);  
  end                     
property check_pulse_width_SWEIF5;
  @(posedge rtt_clk)
  disable iff(rst_a == 1'b1)
  $rose (`L2ARC_GRP.u_rtt.sl5_alt_rtt_swe_val)  |=>  $fell(`L2ARC_GRP.u_rtt.sl5_alt_rtt_swe_val);
endproperty

ASSERT_PULSE_CHECK_SWE_IF5: assert property (check_pulse_width_SWEIF5)
else begin
      $fatal("RTT SWE IF'p pulse width violation at time %t", $time);  
  end                     
property check_pulse_width_SWEIF6;
  @(posedge rtt_clk)
  disable iff(rst_a == 1'b1)
  $rose (`L2ARC_GRP.u_rtt.sl6_alt_rtt_swe_val)  |=>  $fell(`L2ARC_GRP.u_rtt.sl6_alt_rtt_swe_val);
endproperty

ASSERT_PULSE_CHECK_SWE_IF6: assert property (check_pulse_width_SWEIF6)
else begin
      $fatal("RTT SWE IF'p pulse width violation at time %t", $time);  
  end                     
property check_pulse_width_SWEIF7;
  @(posedge rtt_clk)
  disable iff(rst_a == 1'b1)
  $rose (`L2ARC_GRP.u_rtt.sl7_alt_rtt_swe_val)  |=>  $fell(`L2ARC_GRP.u_rtt.sl7_alt_rtt_swe_val);
endproperty

ASSERT_PULSE_CHECK_SWE_IF7: assert property (check_pulse_width_SWEIF7)
else begin
      $fatal("RTT SWE IF'p pulse width violation at time %t", $time);  
  end                     
property check_pulse_width_SWEIF8;
  @(posedge rtt_clk)
  disable iff(rst_a == 1'b1)
  $rose (`L2ARC_GRP.u_rtt.sl8_alt_rtt_swe_val)  |=>  $fell(`L2ARC_GRP.u_rtt.sl8_alt_rtt_swe_val);
endproperty

ASSERT_PULSE_CHECK_SWE_IF8: assert property (check_pulse_width_SWEIF8)
else begin
      $fatal("RTT SWE IF'p pulse width violation at time %t", $time);  
  end                     
property check_pulse_width_SWEIF9;
  @(posedge rtt_clk)
  disable iff(rst_a == 1'b1)
  $rose (`L2ARC_GRP.u_rtt.sl9_alt_rtt_swe_val)  |=>  $fell(`L2ARC_GRP.u_rtt.sl9_alt_rtt_swe_val);
endproperty

ASSERT_PULSE_CHECK_SWE_IF9: assert property (check_pulse_width_SWEIF9)
else begin
      $fatal("RTT SWE IF'p pulse width violation at time %t", $time);  
  end                     
property check_pulse_width_SWEIF10;
  @(posedge rtt_clk)
  disable iff(rst_a == 1'b1)
  $rose (`L2ARC_GRP.u_rtt.sl10_alt_rtt_swe_val)  |=>  $fell(`L2ARC_GRP.u_rtt.sl10_alt_rtt_swe_val);
endproperty

ASSERT_PULSE_CHECK_SWE_IF10: assert property (check_pulse_width_SWEIF10)
else begin
      $fatal("RTT SWE IF'p pulse width violation at time %t", $time);  
  end                     
property check_pulse_width_SWEIF11;
  @(posedge rtt_clk)
  disable iff(rst_a == 1'b1)
  $rose (`L2ARC_GRP.u_rtt.sl11_alt_rtt_swe_val)  |=>  $fell(`L2ARC_GRP.u_rtt.sl11_alt_rtt_swe_val);
endproperty

ASSERT_PULSE_CHECK_SWE_IF11: assert property (check_pulse_width_SWEIF11)
else begin
      $fatal("RTT SWE IF'p pulse width violation at time %t", $time);  
  end                     
property check_pulse_width_SWEIF12;
  @(posedge rtt_clk)
  disable iff(rst_a == 1'b1)
  $rose (`L2ARC_GRP.u_rtt.sl12_alt_rtt_swe_val)  |=>  $fell(`L2ARC_GRP.u_rtt.sl12_alt_rtt_swe_val);
endproperty

ASSERT_PULSE_CHECK_SWE_IF12: assert property (check_pulse_width_SWEIF12)
else begin
      $fatal("RTT SWE IF'p pulse width violation at time %t", $time);  
  end                     
property check_pulse_width_SWEIF13;
  @(posedge rtt_clk)
  disable iff(rst_a == 1'b1)
  $rose (`L2ARC_GRP.u_rtt.sl13_alt_rtt_swe_val)  |=>  $fell(`L2ARC_GRP.u_rtt.sl13_alt_rtt_swe_val);
endproperty

ASSERT_PULSE_CHECK_SWE_IF13: assert property (check_pulse_width_SWEIF13)
else begin
      $fatal("RTT SWE IF'p pulse width violation at time %t", $time);  
  end                     
property check_pulse_width_SWEIF14;
  @(posedge rtt_clk)
  disable iff(rst_a == 1'b1)
  $rose (`L2ARC_GRP.u_rtt.sl14_alt_rtt_swe_val)  |=>  $fell(`L2ARC_GRP.u_rtt.sl14_alt_rtt_swe_val);
endproperty

ASSERT_PULSE_CHECK_SWE_IF14: assert property (check_pulse_width_SWEIF14)
else begin
      $fatal("RTT SWE IF'p pulse width violation at time %t", $time);  
  end                     
property check_pulse_width_SWEIF15;
  @(posedge rtt_clk)
  disable iff(rst_a == 1'b1)
  $rose (`L2ARC_GRP.u_rtt.sl15_alt_rtt_swe_val)  |=>  $fell(`L2ARC_GRP.u_rtt.sl15_alt_rtt_swe_val);
endproperty

ASSERT_PULSE_CHECK_SWE_IF15: assert property (check_pulse_width_SWEIF15)
else begin
      $fatal("RTT SWE IF'p pulse width violation at time %t", $time);  
  end                     

endmodule

