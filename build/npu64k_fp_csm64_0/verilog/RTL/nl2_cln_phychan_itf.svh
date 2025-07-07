`ifndef CLN_PHYCHAN_ITF_INCLUDED_
`define CLN_PHYCHAN_ITF_INCLUDED_

`include "nl2_cln_phychan_def.v"

// Physical channel sender interface
//
interface cln_phychan_snd
  # (parameter  DATA_WIDTH  = 1,
     parameter  NCHAN       = 1,
     parameter  CRDSZ       = `CLOG2_MAX_VCHAN_FIFO_DEPTH_X 
     );

  localparam VCHAN_ID_SZ = NCHAN < 2 ? 1 : $clog2(NCHAN);

  logic  [DATA_WIDTH-1:0] payload;           // data cell to be transferred
  logic [VCHAN_ID_SZ-1:0] chan_id;           // channel identifier
  logic                   valid;             // data cell is valid
  logic                   accept;            // channel accepts data cells
  logic                   accept2;           // channel accepts at least 2 data cells
  logic                   accept2_next;      // next value of accept2
  logic       [CRDSZ-1:0] credit[NCHAN];     // accumulated credits received

  modport upstream (output payload, chan_id, valid, input accept, accept2, accept2_next, credit);
  modport downstream (input payload, chan_id, valid, output accept, accept2, accept2_next, credit);
endinterface // cln_phychan_snd


// Physical channel receiver interface
//
interface cln_phychan_rcv
  # (parameter DATA_WIDTH  = 1,
     parameter NCHAN       = 1 
     );

  localparam VCHAN_ID_SZ = NCHAN < 2 ? 1 : $clog2(NCHAN);

  logic  [DATA_WIDTH-1:0] payload;          // channel data cell
  logic [VCHAN_ID_SZ-1:0] chan_id;          // channel identifier
  logic                   clk_payload;      // clock for payload and chan_id
  logic                   en_payload;       // synchronous w.r.t clk_payload
  logic                   rst_payload;      // reset for payload
  logic                   credit_up[NCHAN]; // setup-hold w.r.t. posedge clk

  modport upstream (output payload, chan_id, clk_payload, en_payload, rst_payload, input credit_up);
  modport downstream (input payload, chan_id, clk_payload, en_payload, rst_payload, output credit_up);
endinterface // cln_phychan_rcv


`ifdef CFG_PHYCHAN_SOURCE_SYNCHRONOUS // {
   `ifdef CFG_PHYCHAN_SRCSYN_SPLT // {
interface cln_phychan_srcrcv
  # (parameter DATA_WIDTH  = 1,
     parameter NCHAN       = 1 
     );

localparam VCHAN_ID_SZ = NCHAN < 2 ? 1 : $clog2(NCHAN);
localparam PHY_WIDTH   = VCHAN_ID_SZ + DATA_WIDTH;
localparam SUBCHAN_NUM = (PHY_WIDTH+`nl2_CLN_SRCSYN_SUBCHAN_SIZE-1)/`nl2_CLN_SRCSYN_SUBCHAN_SIZE;
localparam PHY_WIDTH_F   = PHY_WIDTH-VCHAN_ID_SZ;
localparam SUBCHAN_F_NUM = (PHY_WIDTH_F+`nl2_CLN_SRCSYN_SUBCHAN_SIZE-1)/`nl2_CLN_SRCSYN_SUBCHAN_SIZE;

  fw_srcrcv_s             fw_srcrcv[SUBCHAN_F_NUM]; // struct of channel data cell and clock for payload&chan_id
  logic [VCHAN_ID_SZ-1:0] chan_id;          // channel identifier
  logic                   en_payload;       // synchronous w.r.t clk_payload
  logic                   rst_payload;      // reset for payload
  logic                   credit_up[NCHAN]; // setup-hold w.r.t. posedge clk

  modport upstream (output fw_srcrcv, chan_id, en_payload, rst_payload, input credit_up);
  modport downstream (input fw_srcrcv, chan_id, en_payload, rst_payload, output credit_up);
endinterface // cln_phychan_srcrcv

interface cln_phychan_srcsyn
  # (parameter DATA_WIDTH  = 1,
     parameter NCHAN       = 1 
     );

localparam VCHAN_ID_SZ = NCHAN < 2 ? 1 : $clog2(NCHAN);
localparam PHY_WIDTH   = VCHAN_ID_SZ + DATA_WIDTH;
localparam SUBCHAN_NUM = (PHY_WIDTH+`nl2_CLN_SRCSYN_SUBCHAN_SIZE-1)/`nl2_CLN_SRCSYN_SUBCHAN_SIZE;

  fw_subchan_s       [SUBCHAN_NUM-1:0]   fw_subchan;
  logic                                  fw_rst;
  logic              [NCHAN-1:0]         bk_strb;
  logic                                  bk_rst;

modport upstream (output fw_subchan, fw_rst, input bk_strb, bk_rst);
modport downstream (input fw_subchan, fw_rst, output bk_strb, bk_rst);
endinterface // cln_phychan_srcsyn

interface cln_phychan_srcsyn2
  # (parameter DATA_WIDTH  = 1,
     parameter NCHAN       = 1 
     );

localparam VCHAN_ID_SZ = NCHAN < 2 ? 1 : $clog2(NCHAN);
localparam PHY_WIDTH   = VCHAN_ID_SZ + DATA_WIDTH;
localparam SUBCHAN_NUM = (PHY_WIDTH+`nl2_CLN_SRCSYN_SUBCHAN_SIZE-1)/`nl2_CLN_SRCSYN_SUBCHAN_SIZE;
localparam CHAN_WIDTH  = SUBCHAN_NUM * `nl2_CLN_SRCSYN_SUBCHAN_SIZE;
  reg   [`nl2_CLN_SRCSYN_SUBCHAN_SIZE*SUBCHAN_NUM-1:0]   fw_data;
  logic [SUBCHAN_NUM-1:0]                fw_strb;
  logic                                  fw_rst;
  logic [NCHAN-1:0]                      bk_strb;
  logic                                  bk_rst;

modport upstream (output fw_data, fw_strb, fw_rst, input bk_strb, bk_rst);
  modport downstream (input fw_data, fw_strb, fw_rst, output bk_strb, bk_rst);
endinterface // cln_phychan_srcsyn2

    `else//}{
interface cln_phychan_srcsyn
  # (parameter DATA_WIDTH  = 1,
     parameter NCHAN       = 1 
     );

  localparam VCHAN_ID_SZ = NCHAN < 2 ? 1 : $clog2(NCHAN);

  logic [DATA_WIDTH+VCHAN_ID_SZ-1:0] fw_data;
  logic                              fw_strb;
  logic                              fw_rst;
  logic                  [NCHAN-1:0] bk_strb;
  logic                              bk_rst;


  modport upstream (output fw_data, fw_strb, fw_rst, input bk_strb, bk_rst);
  modport downstream (input fw_data, fw_strb, fw_rst, output bk_strb, bk_rst);
endinterface // cln_phychan
    `endif // }
`endif // } CFG_PHYCHAN_SOURCE_SYNCHRONOUS


`ifdef CFG_PHYCHAN_ASYNC_FIFO // {
interface cln_phychan_asfifo
  # (parameter DATA_WIDTH  = 1,
     parameter NCHAN       = 1,
     parameter CRDSZ       = `CLOG2_MAX_VCHAN_FIFO_DEPTH_X
     );

  localparam VCHAN_ID_SZ = NCHAN < 2 ? 1 : $clog2(NCHAN);

  logic [DATA_WIDTH+VCHAN_ID_SZ-1:0] data_read;
  logic   [`ASYNC_FIFO_SIZE_CL2_X:0] wpnt;
  logic   [`ASYNC_FIFO_SIZE_CL2_X:0] rpnt;
  logic     [`ASYNC_FIFO_SIZE_X-1:0] rpnt_comb;
  logic            [NCHAN*CRDSZ-1:0] credit;

  modport upstream (output data_read, wpnt, input rpnt, rpnt_comb, credit);
  modport downstream (input data_read, wpnt, output rpnt, rpnt_comb, credit);
endinterface // cln_phychan
`endif //  } CFG_PHYCHAN_ASYNC_FIFO


`ifdef CFG_PHYCHAN_SYNCHRONOUS // {
interface cln_phychan_synchronous
  # (parameter DATA_WIDTH  = 1,
     parameter NCHAN       = 1,
     parameter CRDSZ       = `CLOG2_MAX_VCHAN_FIFO_DEPTH_X
     );

  localparam VCHAN_ID_SZ = NCHAN < 2 ? 1 : $clog2(NCHAN);
   
  logic                              valid;
  logic                              clk_payload;
  logic [DATA_WIDTH+VCHAN_ID_SZ-1:0] data;
  logic            [NCHAN*CRDSZ-1:0] credit;

  modport upstream (output valid, data, clk_payload, input credit);
  modport downstream (input valid, data, clk_payload, output credit);
endinterface // cln_phychan
`endif // } CFG_PHYCHAN_SYNCHRONOUS

`endif // CLN_PHYCHAN_ITF_INCLUDED_
