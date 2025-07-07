/*
 * Copyright (C) 2021-2023 Synopsys, Inc. All rights reserved.
 *
 * SYNOPSYS CONFIDENTIAL - This is an unpublished, confidential, and
 * proprietary work of Synopsys, Inc., and may be subject to patent,
 * copyright, trade secret, and other legal or contractual protection.
 * This work may be used only pursuant to the terms and conditions of a
 * written license agreement with Synopsys, Inc. All other use, reproduction,
 * distribution, or disclosure of this work is strictly prohibited.
 *
 * The entire notice above must be reproduced on all authorized copies.
 */

`include "npu_macros.svh"


`include "npu_defines.v"
module npu_pdm_cdc_resync
  import npu_types::*;
(
  // power domain
  input  logic                sl0nl1arc_isolate_n,
  input  logic                sl0nl1arc_isolate,
  input  logic                sl0nl1arc_pd_mem,
  input  logic                sl0nl1arc_pd_logic,
  output logic                sl0nl1arc_isolate_n_sync,
  output logic                sl0nl1arc_isolate_sync,
  output logic                sl0nl1arc_pd_mem_sync,
  output logic                sl0nl1arc_pd_logic_sync,
  input  logic                sl0nl1arc_clk,
  input  logic                sl0nl1arc_rst_a,
  input  logic                sl1nl1arc_isolate_n,
  input  logic                sl1nl1arc_isolate,
  input  logic                sl1nl1arc_pd_mem,
  input  logic                sl1nl1arc_pd_logic,
  output logic                sl1nl1arc_isolate_n_sync,
  output logic                sl1nl1arc_isolate_sync,
  output logic                sl1nl1arc_pd_mem_sync,
  output logic                sl1nl1arc_pd_logic_sync,
  input  logic                sl1nl1arc_clk,
  input  logic                sl1nl1arc_rst_a,
  input  logic                sl2nl1arc_isolate_n,
  input  logic                sl2nl1arc_isolate,
  input  logic                sl2nl1arc_pd_mem,
  input  logic                sl2nl1arc_pd_logic,
  output logic                sl2nl1arc_isolate_n_sync,
  output logic                sl2nl1arc_isolate_sync,
  output logic                sl2nl1arc_pd_mem_sync,
  output logic                sl2nl1arc_pd_logic_sync,
  input  logic                sl2nl1arc_clk,
  input  logic                sl2nl1arc_rst_a,
  input  logic                sl3nl1arc_isolate_n,
  input  logic                sl3nl1arc_isolate,
  input  logic                sl3nl1arc_pd_mem,
  input  logic                sl3nl1arc_pd_logic,
  output logic                sl3nl1arc_isolate_n_sync,
  output logic                sl3nl1arc_isolate_sync,
  output logic                sl3nl1arc_pd_mem_sync,
  output logic                sl3nl1arc_pd_logic_sync,
  input  logic                sl3nl1arc_clk,
  input  logic                sl3nl1arc_rst_a,
  input  logic                sl4nl1arc_isolate_n,
  input  logic                sl4nl1arc_isolate,
  input  logic                sl4nl1arc_pd_mem,
  input  logic                sl4nl1arc_pd_logic,
  output logic                sl4nl1arc_isolate_n_sync,
  output logic                sl4nl1arc_isolate_sync,
  output logic                sl4nl1arc_pd_mem_sync,
  output logic                sl4nl1arc_pd_logic_sync,
  input  logic                sl4nl1arc_clk,
  input  logic                sl4nl1arc_rst_a,
  input  logic                sl5nl1arc_isolate_n,
  input  logic                sl5nl1arc_isolate,
  input  logic                sl5nl1arc_pd_mem,
  input  logic                sl5nl1arc_pd_logic,
  output logic                sl5nl1arc_isolate_n_sync,
  output logic                sl5nl1arc_isolate_sync,
  output logic                sl5nl1arc_pd_mem_sync,
  output logic                sl5nl1arc_pd_logic_sync,
  input  logic                sl5nl1arc_clk,
  input  logic                sl5nl1arc_rst_a,
  input  logic                sl6nl1arc_isolate_n,
  input  logic                sl6nl1arc_isolate,
  input  logic                sl6nl1arc_pd_mem,
  input  logic                sl6nl1arc_pd_logic,
  output logic                sl6nl1arc_isolate_n_sync,
  output logic                sl6nl1arc_isolate_sync,
  output logic                sl6nl1arc_pd_mem_sync,
  output logic                sl6nl1arc_pd_logic_sync,
  input  logic                sl6nl1arc_clk,
  input  logic                sl6nl1arc_rst_a,
  input  logic                sl7nl1arc_isolate_n,
  input  logic                sl7nl1arc_isolate,
  input  logic                sl7nl1arc_pd_mem,
  input  logic                sl7nl1arc_pd_logic,
  output logic                sl7nl1arc_isolate_n_sync,
  output logic                sl7nl1arc_isolate_sync,
  output logic                sl7nl1arc_pd_mem_sync,
  output logic                sl7nl1arc_pd_logic_sync,
  input  logic                sl7nl1arc_clk,
  input  logic                sl7nl1arc_rst_a,
  input  logic                sl8nl1arc_isolate_n,
  input  logic                sl8nl1arc_isolate,
  input  logic                sl8nl1arc_pd_mem,
  input  logic                sl8nl1arc_pd_logic,
  output logic                sl8nl1arc_isolate_n_sync,
  output logic                sl8nl1arc_isolate_sync,
  output logic                sl8nl1arc_pd_mem_sync,
  output logic                sl8nl1arc_pd_logic_sync,
  input  logic                sl8nl1arc_clk,
  input  logic                sl8nl1arc_rst_a,
  input  logic                sl9nl1arc_isolate_n,
  input  logic                sl9nl1arc_isolate,
  input  logic                sl9nl1arc_pd_mem,
  input  logic                sl9nl1arc_pd_logic,
  output logic                sl9nl1arc_isolate_n_sync,
  output logic                sl9nl1arc_isolate_sync,
  output logic                sl9nl1arc_pd_mem_sync,
  output logic                sl9nl1arc_pd_logic_sync,
  input  logic                sl9nl1arc_clk,
  input  logic                sl9nl1arc_rst_a,
  input  logic                sl10nl1arc_isolate_n,
  input  logic                sl10nl1arc_isolate,
  input  logic                sl10nl1arc_pd_mem,
  input  logic                sl10nl1arc_pd_logic,
  output logic                sl10nl1arc_isolate_n_sync,
  output logic                sl10nl1arc_isolate_sync,
  output logic                sl10nl1arc_pd_mem_sync,
  output logic                sl10nl1arc_pd_logic_sync,
  input  logic                sl10nl1arc_clk,
  input  logic                sl10nl1arc_rst_a,
  input  logic                sl11nl1arc_isolate_n,
  input  logic                sl11nl1arc_isolate,
  input  logic                sl11nl1arc_pd_mem,
  input  logic                sl11nl1arc_pd_logic,
  output logic                sl11nl1arc_isolate_n_sync,
  output logic                sl11nl1arc_isolate_sync,
  output logic                sl11nl1arc_pd_mem_sync,
  output logic                sl11nl1arc_pd_logic_sync,
  input  logic                sl11nl1arc_clk,
  input  logic                sl11nl1arc_rst_a,
  input  logic                sl12nl1arc_isolate_n,
  input  logic                sl12nl1arc_isolate,
  input  logic                sl12nl1arc_pd_mem,
  input  logic                sl12nl1arc_pd_logic,
  output logic                sl12nl1arc_isolate_n_sync,
  output logic                sl12nl1arc_isolate_sync,
  output logic                sl12nl1arc_pd_mem_sync,
  output logic                sl12nl1arc_pd_logic_sync,
  input  logic                sl12nl1arc_clk,
  input  logic                sl12nl1arc_rst_a,
  input  logic                sl13nl1arc_isolate_n,
  input  logic                sl13nl1arc_isolate,
  input  logic                sl13nl1arc_pd_mem,
  input  logic                sl13nl1arc_pd_logic,
  output logic                sl13nl1arc_isolate_n_sync,
  output logic                sl13nl1arc_isolate_sync,
  output logic                sl13nl1arc_pd_mem_sync,
  output logic                sl13nl1arc_pd_logic_sync,
  input  logic                sl13nl1arc_clk,
  input  logic                sl13nl1arc_rst_a,
  input  logic                sl14nl1arc_isolate_n,
  input  logic                sl14nl1arc_isolate,
  input  logic                sl14nl1arc_pd_mem,
  input  logic                sl14nl1arc_pd_logic,
  output logic                sl14nl1arc_isolate_n_sync,
  output logic                sl14nl1arc_isolate_sync,
  output logic                sl14nl1arc_pd_mem_sync,
  output logic                sl14nl1arc_pd_logic_sync,
  input  logic                sl14nl1arc_clk,
  input  logic                sl14nl1arc_rst_a,
  input  logic                sl15nl1arc_isolate_n,
  input  logic                sl15nl1arc_isolate,
  input  logic                sl15nl1arc_pd_mem,
  input  logic                sl15nl1arc_pd_logic,
  output logic                sl15nl1arc_isolate_n_sync,
  output logic                sl15nl1arc_isolate_sync,
  output logic                sl15nl1arc_pd_mem_sync,
  output logic                sl15nl1arc_pd_logic_sync,
  input  logic                sl15nl1arc_clk,
  input  logic                sl15nl1arc_rst_a,
  //
  input                       test_mode      // test mode to bypass FFs
);

  logic  sl0nl1arc_isolate_n_sync_r;
  logic  sl0nl1arc_isolate_sync_r;
  logic  sl0nl1arc_pd_mem_sync_r;
  logic  sl0nl1arc_pd_logic_sync_r;
  logic  sl0nl1arc_rst;
  logic  sl1nl1arc_isolate_n_sync_r;
  logic  sl1nl1arc_isolate_sync_r;
  logic  sl1nl1arc_pd_mem_sync_r;
  logic  sl1nl1arc_pd_logic_sync_r;
  logic  sl1nl1arc_rst;
  logic  sl2nl1arc_isolate_n_sync_r;
  logic  sl2nl1arc_isolate_sync_r;
  logic  sl2nl1arc_pd_mem_sync_r;
  logic  sl2nl1arc_pd_logic_sync_r;
  logic  sl2nl1arc_rst;
  logic  sl3nl1arc_isolate_n_sync_r;
  logic  sl3nl1arc_isolate_sync_r;
  logic  sl3nl1arc_pd_mem_sync_r;
  logic  sl3nl1arc_pd_logic_sync_r;
  logic  sl3nl1arc_rst;
  logic  sl4nl1arc_isolate_n_sync_r;
  logic  sl4nl1arc_isolate_sync_r;
  logic  sl4nl1arc_pd_mem_sync_r;
  logic  sl4nl1arc_pd_logic_sync_r;
  logic  sl4nl1arc_rst;
  logic  sl5nl1arc_isolate_n_sync_r;
  logic  sl5nl1arc_isolate_sync_r;
  logic  sl5nl1arc_pd_mem_sync_r;
  logic  sl5nl1arc_pd_logic_sync_r;
  logic  sl5nl1arc_rst;
  logic  sl6nl1arc_isolate_n_sync_r;
  logic  sl6nl1arc_isolate_sync_r;
  logic  sl6nl1arc_pd_mem_sync_r;
  logic  sl6nl1arc_pd_logic_sync_r;
  logic  sl6nl1arc_rst;
  logic  sl7nl1arc_isolate_n_sync_r;
  logic  sl7nl1arc_isolate_sync_r;
  logic  sl7nl1arc_pd_mem_sync_r;
  logic  sl7nl1arc_pd_logic_sync_r;
  logic  sl7nl1arc_rst;
  logic  sl8nl1arc_isolate_n_sync_r;
  logic  sl8nl1arc_isolate_sync_r;
  logic  sl8nl1arc_pd_mem_sync_r;
  logic  sl8nl1arc_pd_logic_sync_r;
  logic  sl8nl1arc_rst;
  logic  sl9nl1arc_isolate_n_sync_r;
  logic  sl9nl1arc_isolate_sync_r;
  logic  sl9nl1arc_pd_mem_sync_r;
  logic  sl9nl1arc_pd_logic_sync_r;
  logic  sl9nl1arc_rst;
  logic  sl10nl1arc_isolate_n_sync_r;
  logic  sl10nl1arc_isolate_sync_r;
  logic  sl10nl1arc_pd_mem_sync_r;
  logic  sl10nl1arc_pd_logic_sync_r;
  logic  sl10nl1arc_rst;
  logic  sl11nl1arc_isolate_n_sync_r;
  logic  sl11nl1arc_isolate_sync_r;
  logic  sl11nl1arc_pd_mem_sync_r;
  logic  sl11nl1arc_pd_logic_sync_r;
  logic  sl11nl1arc_rst;
  logic  sl12nl1arc_isolate_n_sync_r;
  logic  sl12nl1arc_isolate_sync_r;
  logic  sl12nl1arc_pd_mem_sync_r;
  logic  sl12nl1arc_pd_logic_sync_r;
  logic  sl12nl1arc_rst;
  logic  sl13nl1arc_isolate_n_sync_r;
  logic  sl13nl1arc_isolate_sync_r;
  logic  sl13nl1arc_pd_mem_sync_r;
  logic  sl13nl1arc_pd_logic_sync_r;
  logic  sl13nl1arc_rst;
  logic  sl14nl1arc_isolate_n_sync_r;
  logic  sl14nl1arc_isolate_sync_r;
  logic  sl14nl1arc_pd_mem_sync_r;
  logic  sl14nl1arc_pd_logic_sync_r;
  logic  sl14nl1arc_rst;
  logic  sl15nl1arc_isolate_n_sync_r;
  logic  sl15nl1arc_isolate_sync_r;
  logic  sl15nl1arc_pd_mem_sync_r;
  logic  sl15nl1arc_pd_logic_sync_r;
  logic  sl15nl1arc_rst;


  npu_reset_ctrl 
  u_reset_ctrl_main0
  (
   .clk        ( sl0nl1arc_clk    ),
   .rst_a      ( sl0nl1arc_rst_a  ),
   .test_mode  ( test_mode             ),
   .rst        ( sl0nl1arc_rst    )
  );


  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_n_cdc_sync0 
  (
    .clk        ( sl0nl1arc_clk              ),
    .rst_a      ( sl0nl1arc_rst_a            ),
    .din        ( {1{sl0nl1arc_isolate_n}}        ),
    .dout       ( sl0nl1arc_isolate_n_sync_r )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_cdc_sync0 
  (
    .clk        ( sl0nl1arc_clk              ),
    .rst_a      ( sl0nl1arc_rst_a            ),
    .din        ( {1{sl0nl1arc_isolate}}          ),
    .dout       ( sl0nl1arc_isolate_sync_r   )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_mem_cdc_sync0 
  (
    .clk        ( sl0nl1arc_clk              ),
    .rst_a      ( sl0nl1arc_rst_a            ),
    .din        ( {1{sl0nl1arc_pd_mem}}           ),
    .dout       ( sl0nl1arc_pd_mem_sync_r    )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_logic_cdc_sync0 
  (
    .clk        ( sl0nl1arc_clk              ),
    .rst_a      ( sl0nl1arc_rst_a            ),
    .din        ( {1{sl0nl1arc_pd_logic}}         ),
    .dout       ( sl0nl1arc_pd_logic_sync_r  )
  );

  npu_reset_ctrl 
  u_reset_ctrl_main1
  (
   .clk        ( sl1nl1arc_clk    ),
   .rst_a      ( sl1nl1arc_rst_a  ),
   .test_mode  ( test_mode             ),
   .rst        ( sl1nl1arc_rst    )
  );


  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_n_cdc_sync1 
  (
    .clk        ( sl1nl1arc_clk              ),
    .rst_a      ( sl1nl1arc_rst_a            ),
    .din        ( {1{sl1nl1arc_isolate_n}}        ),
    .dout       ( sl1nl1arc_isolate_n_sync_r )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_cdc_sync1 
  (
    .clk        ( sl1nl1arc_clk              ),
    .rst_a      ( sl1nl1arc_rst_a            ),
    .din        ( {1{sl1nl1arc_isolate}}          ),
    .dout       ( sl1nl1arc_isolate_sync_r   )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_mem_cdc_sync1 
  (
    .clk        ( sl1nl1arc_clk              ),
    .rst_a      ( sl1nl1arc_rst_a            ),
    .din        ( {1{sl1nl1arc_pd_mem}}           ),
    .dout       ( sl1nl1arc_pd_mem_sync_r    )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_logic_cdc_sync1 
  (
    .clk        ( sl1nl1arc_clk              ),
    .rst_a      ( sl1nl1arc_rst_a            ),
    .din        ( {1{sl1nl1arc_pd_logic}}         ),
    .dout       ( sl1nl1arc_pd_logic_sync_r  )
  );

  npu_reset_ctrl 
  u_reset_ctrl_main2
  (
   .clk        ( sl2nl1arc_clk    ),
   .rst_a      ( sl2nl1arc_rst_a  ),
   .test_mode  ( test_mode             ),
   .rst        ( sl2nl1arc_rst    )
  );


  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_n_cdc_sync2 
  (
    .clk        ( sl2nl1arc_clk              ),
    .rst_a      ( sl2nl1arc_rst_a            ),
    .din        ( {1{sl2nl1arc_isolate_n}}        ),
    .dout       ( sl2nl1arc_isolate_n_sync_r )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_cdc_sync2 
  (
    .clk        ( sl2nl1arc_clk              ),
    .rst_a      ( sl2nl1arc_rst_a            ),
    .din        ( {1{sl2nl1arc_isolate}}          ),
    .dout       ( sl2nl1arc_isolate_sync_r   )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_mem_cdc_sync2 
  (
    .clk        ( sl2nl1arc_clk              ),
    .rst_a      ( sl2nl1arc_rst_a            ),
    .din        ( {1{sl2nl1arc_pd_mem}}           ),
    .dout       ( sl2nl1arc_pd_mem_sync_r    )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_logic_cdc_sync2 
  (
    .clk        ( sl2nl1arc_clk              ),
    .rst_a      ( sl2nl1arc_rst_a            ),
    .din        ( {1{sl2nl1arc_pd_logic}}         ),
    .dout       ( sl2nl1arc_pd_logic_sync_r  )
  );

  npu_reset_ctrl 
  u_reset_ctrl_main3
  (
   .clk        ( sl3nl1arc_clk    ),
   .rst_a      ( sl3nl1arc_rst_a  ),
   .test_mode  ( test_mode             ),
   .rst        ( sl3nl1arc_rst    )
  );


  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_n_cdc_sync3 
  (
    .clk        ( sl3nl1arc_clk              ),
    .rst_a      ( sl3nl1arc_rst_a            ),
    .din        ( {1{sl3nl1arc_isolate_n}}        ),
    .dout       ( sl3nl1arc_isolate_n_sync_r )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_cdc_sync3 
  (
    .clk        ( sl3nl1arc_clk              ),
    .rst_a      ( sl3nl1arc_rst_a            ),
    .din        ( {1{sl3nl1arc_isolate}}          ),
    .dout       ( sl3nl1arc_isolate_sync_r   )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_mem_cdc_sync3 
  (
    .clk        ( sl3nl1arc_clk              ),
    .rst_a      ( sl3nl1arc_rst_a            ),
    .din        ( {1{sl3nl1arc_pd_mem}}           ),
    .dout       ( sl3nl1arc_pd_mem_sync_r    )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_logic_cdc_sync3 
  (
    .clk        ( sl3nl1arc_clk              ),
    .rst_a      ( sl3nl1arc_rst_a            ),
    .din        ( {1{sl3nl1arc_pd_logic}}         ),
    .dout       ( sl3nl1arc_pd_logic_sync_r  )
  );

  npu_reset_ctrl 
  u_reset_ctrl_main4
  (
   .clk        ( sl4nl1arc_clk    ),
   .rst_a      ( sl4nl1arc_rst_a  ),
   .test_mode  ( test_mode             ),
   .rst        ( sl4nl1arc_rst    )
  );


  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_n_cdc_sync4 
  (
    .clk        ( sl4nl1arc_clk              ),
    .rst_a      ( sl4nl1arc_rst_a            ),
    .din        ( {1{sl4nl1arc_isolate_n}}        ),
    .dout       ( sl4nl1arc_isolate_n_sync_r )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_cdc_sync4 
  (
    .clk        ( sl4nl1arc_clk              ),
    .rst_a      ( sl4nl1arc_rst_a            ),
    .din        ( {1{sl4nl1arc_isolate}}          ),
    .dout       ( sl4nl1arc_isolate_sync_r   )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_mem_cdc_sync4 
  (
    .clk        ( sl4nl1arc_clk              ),
    .rst_a      ( sl4nl1arc_rst_a            ),
    .din        ( {1{sl4nl1arc_pd_mem}}           ),
    .dout       ( sl4nl1arc_pd_mem_sync_r    )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_logic_cdc_sync4 
  (
    .clk        ( sl4nl1arc_clk              ),
    .rst_a      ( sl4nl1arc_rst_a            ),
    .din        ( {1{sl4nl1arc_pd_logic}}         ),
    .dout       ( sl4nl1arc_pd_logic_sync_r  )
  );

  npu_reset_ctrl 
  u_reset_ctrl_main5
  (
   .clk        ( sl5nl1arc_clk    ),
   .rst_a      ( sl5nl1arc_rst_a  ),
   .test_mode  ( test_mode             ),
   .rst        ( sl5nl1arc_rst    )
  );


  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_n_cdc_sync5 
  (
    .clk        ( sl5nl1arc_clk              ),
    .rst_a      ( sl5nl1arc_rst_a            ),
    .din        ( {1{sl5nl1arc_isolate_n}}        ),
    .dout       ( sl5nl1arc_isolate_n_sync_r )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_cdc_sync5 
  (
    .clk        ( sl5nl1arc_clk              ),
    .rst_a      ( sl5nl1arc_rst_a            ),
    .din        ( {1{sl5nl1arc_isolate}}          ),
    .dout       ( sl5nl1arc_isolate_sync_r   )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_mem_cdc_sync5 
  (
    .clk        ( sl5nl1arc_clk              ),
    .rst_a      ( sl5nl1arc_rst_a            ),
    .din        ( {1{sl5nl1arc_pd_mem}}           ),
    .dout       ( sl5nl1arc_pd_mem_sync_r    )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_logic_cdc_sync5 
  (
    .clk        ( sl5nl1arc_clk              ),
    .rst_a      ( sl5nl1arc_rst_a            ),
    .din        ( {1{sl5nl1arc_pd_logic}}         ),
    .dout       ( sl5nl1arc_pd_logic_sync_r  )
  );

  npu_reset_ctrl 
  u_reset_ctrl_main6
  (
   .clk        ( sl6nl1arc_clk    ),
   .rst_a      ( sl6nl1arc_rst_a  ),
   .test_mode  ( test_mode             ),
   .rst        ( sl6nl1arc_rst    )
  );


  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_n_cdc_sync6 
  (
    .clk        ( sl6nl1arc_clk              ),
    .rst_a      ( sl6nl1arc_rst_a            ),
    .din        ( {1{sl6nl1arc_isolate_n}}        ),
    .dout       ( sl6nl1arc_isolate_n_sync_r )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_cdc_sync6 
  (
    .clk        ( sl6nl1arc_clk              ),
    .rst_a      ( sl6nl1arc_rst_a            ),
    .din        ( {1{sl6nl1arc_isolate}}          ),
    .dout       ( sl6nl1arc_isolate_sync_r   )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_mem_cdc_sync6 
  (
    .clk        ( sl6nl1arc_clk              ),
    .rst_a      ( sl6nl1arc_rst_a            ),
    .din        ( {1{sl6nl1arc_pd_mem}}           ),
    .dout       ( sl6nl1arc_pd_mem_sync_r    )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_logic_cdc_sync6 
  (
    .clk        ( sl6nl1arc_clk              ),
    .rst_a      ( sl6nl1arc_rst_a            ),
    .din        ( {1{sl6nl1arc_pd_logic}}         ),
    .dout       ( sl6nl1arc_pd_logic_sync_r  )
  );

  npu_reset_ctrl 
  u_reset_ctrl_main7
  (
   .clk        ( sl7nl1arc_clk    ),
   .rst_a      ( sl7nl1arc_rst_a  ),
   .test_mode  ( test_mode             ),
   .rst        ( sl7nl1arc_rst    )
  );


  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_n_cdc_sync7 
  (
    .clk        ( sl7nl1arc_clk              ),
    .rst_a      ( sl7nl1arc_rst_a            ),
    .din        ( {1{sl7nl1arc_isolate_n}}        ),
    .dout       ( sl7nl1arc_isolate_n_sync_r )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_cdc_sync7 
  (
    .clk        ( sl7nl1arc_clk              ),
    .rst_a      ( sl7nl1arc_rst_a            ),
    .din        ( {1{sl7nl1arc_isolate}}          ),
    .dout       ( sl7nl1arc_isolate_sync_r   )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_mem_cdc_sync7 
  (
    .clk        ( sl7nl1arc_clk              ),
    .rst_a      ( sl7nl1arc_rst_a            ),
    .din        ( {1{sl7nl1arc_pd_mem}}           ),
    .dout       ( sl7nl1arc_pd_mem_sync_r    )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_logic_cdc_sync7 
  (
    .clk        ( sl7nl1arc_clk              ),
    .rst_a      ( sl7nl1arc_rst_a            ),
    .din        ( {1{sl7nl1arc_pd_logic}}         ),
    .dout       ( sl7nl1arc_pd_logic_sync_r  )
  );

  npu_reset_ctrl 
  u_reset_ctrl_main8
  (
   .clk        ( sl8nl1arc_clk    ),
   .rst_a      ( sl8nl1arc_rst_a  ),
   .test_mode  ( test_mode             ),
   .rst        ( sl8nl1arc_rst    )
  );


  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_n_cdc_sync8 
  (
    .clk        ( sl8nl1arc_clk              ),
    .rst_a      ( sl8nl1arc_rst_a            ),
    .din        ( {1{sl8nl1arc_isolate_n}}        ),
    .dout       ( sl8nl1arc_isolate_n_sync_r )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_cdc_sync8 
  (
    .clk        ( sl8nl1arc_clk              ),
    .rst_a      ( sl8nl1arc_rst_a            ),
    .din        ( {1{sl8nl1arc_isolate}}          ),
    .dout       ( sl8nl1arc_isolate_sync_r   )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_mem_cdc_sync8 
  (
    .clk        ( sl8nl1arc_clk              ),
    .rst_a      ( sl8nl1arc_rst_a            ),
    .din        ( {1{sl8nl1arc_pd_mem}}           ),
    .dout       ( sl8nl1arc_pd_mem_sync_r    )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_logic_cdc_sync8 
  (
    .clk        ( sl8nl1arc_clk              ),
    .rst_a      ( sl8nl1arc_rst_a            ),
    .din        ( {1{sl8nl1arc_pd_logic}}         ),
    .dout       ( sl8nl1arc_pd_logic_sync_r  )
  );

  npu_reset_ctrl 
  u_reset_ctrl_main9
  (
   .clk        ( sl9nl1arc_clk    ),
   .rst_a      ( sl9nl1arc_rst_a  ),
   .test_mode  ( test_mode             ),
   .rst        ( sl9nl1arc_rst    )
  );


  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_n_cdc_sync9 
  (
    .clk        ( sl9nl1arc_clk              ),
    .rst_a      ( sl9nl1arc_rst_a            ),
    .din        ( {1{sl9nl1arc_isolate_n}}        ),
    .dout       ( sl9nl1arc_isolate_n_sync_r )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_cdc_sync9 
  (
    .clk        ( sl9nl1arc_clk              ),
    .rst_a      ( sl9nl1arc_rst_a            ),
    .din        ( {1{sl9nl1arc_isolate}}          ),
    .dout       ( sl9nl1arc_isolate_sync_r   )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_mem_cdc_sync9 
  (
    .clk        ( sl9nl1arc_clk              ),
    .rst_a      ( sl9nl1arc_rst_a            ),
    .din        ( {1{sl9nl1arc_pd_mem}}           ),
    .dout       ( sl9nl1arc_pd_mem_sync_r    )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_logic_cdc_sync9 
  (
    .clk        ( sl9nl1arc_clk              ),
    .rst_a      ( sl9nl1arc_rst_a            ),
    .din        ( {1{sl9nl1arc_pd_logic}}         ),
    .dout       ( sl9nl1arc_pd_logic_sync_r  )
  );

  npu_reset_ctrl 
  u_reset_ctrl_main10
  (
   .clk        ( sl10nl1arc_clk    ),
   .rst_a      ( sl10nl1arc_rst_a  ),
   .test_mode  ( test_mode             ),
   .rst        ( sl10nl1arc_rst    )
  );


  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_n_cdc_sync10 
  (
    .clk        ( sl10nl1arc_clk              ),
    .rst_a      ( sl10nl1arc_rst_a            ),
    .din        ( {1{sl10nl1arc_isolate_n}}        ),
    .dout       ( sl10nl1arc_isolate_n_sync_r )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_cdc_sync10 
  (
    .clk        ( sl10nl1arc_clk              ),
    .rst_a      ( sl10nl1arc_rst_a            ),
    .din        ( {1{sl10nl1arc_isolate}}          ),
    .dout       ( sl10nl1arc_isolate_sync_r   )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_mem_cdc_sync10 
  (
    .clk        ( sl10nl1arc_clk              ),
    .rst_a      ( sl10nl1arc_rst_a            ),
    .din        ( {1{sl10nl1arc_pd_mem}}           ),
    .dout       ( sl10nl1arc_pd_mem_sync_r    )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_logic_cdc_sync10 
  (
    .clk        ( sl10nl1arc_clk              ),
    .rst_a      ( sl10nl1arc_rst_a            ),
    .din        ( {1{sl10nl1arc_pd_logic}}         ),
    .dout       ( sl10nl1arc_pd_logic_sync_r  )
  );

  npu_reset_ctrl 
  u_reset_ctrl_main11
  (
   .clk        ( sl11nl1arc_clk    ),
   .rst_a      ( sl11nl1arc_rst_a  ),
   .test_mode  ( test_mode             ),
   .rst        ( sl11nl1arc_rst    )
  );


  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_n_cdc_sync11 
  (
    .clk        ( sl11nl1arc_clk              ),
    .rst_a      ( sl11nl1arc_rst_a            ),
    .din        ( {1{sl11nl1arc_isolate_n}}        ),
    .dout       ( sl11nl1arc_isolate_n_sync_r )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_cdc_sync11 
  (
    .clk        ( sl11nl1arc_clk              ),
    .rst_a      ( sl11nl1arc_rst_a            ),
    .din        ( {1{sl11nl1arc_isolate}}          ),
    .dout       ( sl11nl1arc_isolate_sync_r   )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_mem_cdc_sync11 
  (
    .clk        ( sl11nl1arc_clk              ),
    .rst_a      ( sl11nl1arc_rst_a            ),
    .din        ( {1{sl11nl1arc_pd_mem}}           ),
    .dout       ( sl11nl1arc_pd_mem_sync_r    )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_logic_cdc_sync11 
  (
    .clk        ( sl11nl1arc_clk              ),
    .rst_a      ( sl11nl1arc_rst_a            ),
    .din        ( {1{sl11nl1arc_pd_logic}}         ),
    .dout       ( sl11nl1arc_pd_logic_sync_r  )
  );

  npu_reset_ctrl 
  u_reset_ctrl_main12
  (
   .clk        ( sl12nl1arc_clk    ),
   .rst_a      ( sl12nl1arc_rst_a  ),
   .test_mode  ( test_mode             ),
   .rst        ( sl12nl1arc_rst    )
  );


  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_n_cdc_sync12 
  (
    .clk        ( sl12nl1arc_clk              ),
    .rst_a      ( sl12nl1arc_rst_a            ),
    .din        ( {1{sl12nl1arc_isolate_n}}        ),
    .dout       ( sl12nl1arc_isolate_n_sync_r )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_cdc_sync12 
  (
    .clk        ( sl12nl1arc_clk              ),
    .rst_a      ( sl12nl1arc_rst_a            ),
    .din        ( {1{sl12nl1arc_isolate}}          ),
    .dout       ( sl12nl1arc_isolate_sync_r   )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_mem_cdc_sync12 
  (
    .clk        ( sl12nl1arc_clk              ),
    .rst_a      ( sl12nl1arc_rst_a            ),
    .din        ( {1{sl12nl1arc_pd_mem}}           ),
    .dout       ( sl12nl1arc_pd_mem_sync_r    )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_logic_cdc_sync12 
  (
    .clk        ( sl12nl1arc_clk              ),
    .rst_a      ( sl12nl1arc_rst_a            ),
    .din        ( {1{sl12nl1arc_pd_logic}}         ),
    .dout       ( sl12nl1arc_pd_logic_sync_r  )
  );

  npu_reset_ctrl 
  u_reset_ctrl_main13
  (
   .clk        ( sl13nl1arc_clk    ),
   .rst_a      ( sl13nl1arc_rst_a  ),
   .test_mode  ( test_mode             ),
   .rst        ( sl13nl1arc_rst    )
  );


  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_n_cdc_sync13 
  (
    .clk        ( sl13nl1arc_clk              ),
    .rst_a      ( sl13nl1arc_rst_a            ),
    .din        ( {1{sl13nl1arc_isolate_n}}        ),
    .dout       ( sl13nl1arc_isolate_n_sync_r )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_cdc_sync13 
  (
    .clk        ( sl13nl1arc_clk              ),
    .rst_a      ( sl13nl1arc_rst_a            ),
    .din        ( {1{sl13nl1arc_isolate}}          ),
    .dout       ( sl13nl1arc_isolate_sync_r   )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_mem_cdc_sync13 
  (
    .clk        ( sl13nl1arc_clk              ),
    .rst_a      ( sl13nl1arc_rst_a            ),
    .din        ( {1{sl13nl1arc_pd_mem}}           ),
    .dout       ( sl13nl1arc_pd_mem_sync_r    )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_logic_cdc_sync13 
  (
    .clk        ( sl13nl1arc_clk              ),
    .rst_a      ( sl13nl1arc_rst_a            ),
    .din        ( {1{sl13nl1arc_pd_logic}}         ),
    .dout       ( sl13nl1arc_pd_logic_sync_r  )
  );

  npu_reset_ctrl 
  u_reset_ctrl_main14
  (
   .clk        ( sl14nl1arc_clk    ),
   .rst_a      ( sl14nl1arc_rst_a  ),
   .test_mode  ( test_mode             ),
   .rst        ( sl14nl1arc_rst    )
  );


  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_n_cdc_sync14 
  (
    .clk        ( sl14nl1arc_clk              ),
    .rst_a      ( sl14nl1arc_rst_a            ),
    .din        ( {1{sl14nl1arc_isolate_n}}        ),
    .dout       ( sl14nl1arc_isolate_n_sync_r )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_cdc_sync14 
  (
    .clk        ( sl14nl1arc_clk              ),
    .rst_a      ( sl14nl1arc_rst_a            ),
    .din        ( {1{sl14nl1arc_isolate}}          ),
    .dout       ( sl14nl1arc_isolate_sync_r   )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_mem_cdc_sync14 
  (
    .clk        ( sl14nl1arc_clk              ),
    .rst_a      ( sl14nl1arc_rst_a            ),
    .din        ( {1{sl14nl1arc_pd_mem}}           ),
    .dout       ( sl14nl1arc_pd_mem_sync_r    )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_logic_cdc_sync14 
  (
    .clk        ( sl14nl1arc_clk              ),
    .rst_a      ( sl14nl1arc_rst_a            ),
    .din        ( {1{sl14nl1arc_pd_logic}}         ),
    .dout       ( sl14nl1arc_pd_logic_sync_r  )
  );

  npu_reset_ctrl 
  u_reset_ctrl_main15
  (
   .clk        ( sl15nl1arc_clk    ),
   .rst_a      ( sl15nl1arc_rst_a  ),
   .test_mode  ( test_mode             ),
   .rst        ( sl15nl1arc_rst    )
  );


  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_n_cdc_sync15 
  (
    .clk        ( sl15nl1arc_clk              ),
    .rst_a      ( sl15nl1arc_rst_a            ),
    .din        ( {1{sl15nl1arc_isolate_n}}        ),
    .dout       ( sl15nl1arc_isolate_n_sync_r )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_isolate_cdc_sync15 
  (
    .clk        ( sl15nl1arc_clk              ),
    .rst_a      ( sl15nl1arc_rst_a            ),
    .din        ( {1{sl15nl1arc_isolate}}          ),
    .dout       ( sl15nl1arc_isolate_sync_r   )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_mem_cdc_sync15 
  (
    .clk        ( sl15nl1arc_clk              ),
    .rst_a      ( sl15nl1arc_rst_a            ),
    .din        ( {1{sl15nl1arc_pd_mem}}           ),
    .dout       ( sl15nl1arc_pd_mem_sync_r    )
  );

  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_pd_logic_cdc_sync15 
  (
    .clk        ( sl15nl1arc_clk              ),
    .rst_a      ( sl15nl1arc_rst_a            ),
    .din        ( {1{sl15nl1arc_pd_logic}}         ),
    .dout       ( sl15nl1arc_pd_logic_sync_r  )
  );

  assign sl0nl1arc_isolate_n_sync = sl0nl1arc_isolate_n_sync_r;
  assign sl0nl1arc_isolate_sync   = sl0nl1arc_isolate_sync_r;
  assign sl0nl1arc_pd_mem_sync    = sl0nl1arc_pd_mem_sync_r;
  assign sl0nl1arc_pd_logic_sync  = sl0nl1arc_pd_logic_sync_r;
  assign sl1nl1arc_isolate_n_sync = sl1nl1arc_isolate_n_sync_r;
  assign sl1nl1arc_isolate_sync   = sl1nl1arc_isolate_sync_r;
  assign sl1nl1arc_pd_mem_sync    = sl1nl1arc_pd_mem_sync_r;
  assign sl1nl1arc_pd_logic_sync  = sl1nl1arc_pd_logic_sync_r;
  assign sl2nl1arc_isolate_n_sync = sl2nl1arc_isolate_n_sync_r;
  assign sl2nl1arc_isolate_sync   = sl2nl1arc_isolate_sync_r;
  assign sl2nl1arc_pd_mem_sync    = sl2nl1arc_pd_mem_sync_r;
  assign sl2nl1arc_pd_logic_sync  = sl2nl1arc_pd_logic_sync_r;
  assign sl3nl1arc_isolate_n_sync = sl3nl1arc_isolate_n_sync_r;
  assign sl3nl1arc_isolate_sync   = sl3nl1arc_isolate_sync_r;
  assign sl3nl1arc_pd_mem_sync    = sl3nl1arc_pd_mem_sync_r;
  assign sl3nl1arc_pd_logic_sync  = sl3nl1arc_pd_logic_sync_r;
  assign sl4nl1arc_isolate_n_sync = sl4nl1arc_isolate_n_sync_r;
  assign sl4nl1arc_isolate_sync   = sl4nl1arc_isolate_sync_r;
  assign sl4nl1arc_pd_mem_sync    = sl4nl1arc_pd_mem_sync_r;
  assign sl4nl1arc_pd_logic_sync  = sl4nl1arc_pd_logic_sync_r;
  assign sl5nl1arc_isolate_n_sync = sl5nl1arc_isolate_n_sync_r;
  assign sl5nl1arc_isolate_sync   = sl5nl1arc_isolate_sync_r;
  assign sl5nl1arc_pd_mem_sync    = sl5nl1arc_pd_mem_sync_r;
  assign sl5nl1arc_pd_logic_sync  = sl5nl1arc_pd_logic_sync_r;
  assign sl6nl1arc_isolate_n_sync = sl6nl1arc_isolate_n_sync_r;
  assign sl6nl1arc_isolate_sync   = sl6nl1arc_isolate_sync_r;
  assign sl6nl1arc_pd_mem_sync    = sl6nl1arc_pd_mem_sync_r;
  assign sl6nl1arc_pd_logic_sync  = sl6nl1arc_pd_logic_sync_r;
  assign sl7nl1arc_isolate_n_sync = sl7nl1arc_isolate_n_sync_r;
  assign sl7nl1arc_isolate_sync   = sl7nl1arc_isolate_sync_r;
  assign sl7nl1arc_pd_mem_sync    = sl7nl1arc_pd_mem_sync_r;
  assign sl7nl1arc_pd_logic_sync  = sl7nl1arc_pd_logic_sync_r;
  assign sl8nl1arc_isolate_n_sync = sl8nl1arc_isolate_n_sync_r;
  assign sl8nl1arc_isolate_sync   = sl8nl1arc_isolate_sync_r;
  assign sl8nl1arc_pd_mem_sync    = sl8nl1arc_pd_mem_sync_r;
  assign sl8nl1arc_pd_logic_sync  = sl8nl1arc_pd_logic_sync_r;
  assign sl9nl1arc_isolate_n_sync = sl9nl1arc_isolate_n_sync_r;
  assign sl9nl1arc_isolate_sync   = sl9nl1arc_isolate_sync_r;
  assign sl9nl1arc_pd_mem_sync    = sl9nl1arc_pd_mem_sync_r;
  assign sl9nl1arc_pd_logic_sync  = sl9nl1arc_pd_logic_sync_r;
  assign sl10nl1arc_isolate_n_sync = sl10nl1arc_isolate_n_sync_r;
  assign sl10nl1arc_isolate_sync   = sl10nl1arc_isolate_sync_r;
  assign sl10nl1arc_pd_mem_sync    = sl10nl1arc_pd_mem_sync_r;
  assign sl10nl1arc_pd_logic_sync  = sl10nl1arc_pd_logic_sync_r;
  assign sl11nl1arc_isolate_n_sync = sl11nl1arc_isolate_n_sync_r;
  assign sl11nl1arc_isolate_sync   = sl11nl1arc_isolate_sync_r;
  assign sl11nl1arc_pd_mem_sync    = sl11nl1arc_pd_mem_sync_r;
  assign sl11nl1arc_pd_logic_sync  = sl11nl1arc_pd_logic_sync_r;
  assign sl12nl1arc_isolate_n_sync = sl12nl1arc_isolate_n_sync_r;
  assign sl12nl1arc_isolate_sync   = sl12nl1arc_isolate_sync_r;
  assign sl12nl1arc_pd_mem_sync    = sl12nl1arc_pd_mem_sync_r;
  assign sl12nl1arc_pd_logic_sync  = sl12nl1arc_pd_logic_sync_r;
  assign sl13nl1arc_isolate_n_sync = sl13nl1arc_isolate_n_sync_r;
  assign sl13nl1arc_isolate_sync   = sl13nl1arc_isolate_sync_r;
  assign sl13nl1arc_pd_mem_sync    = sl13nl1arc_pd_mem_sync_r;
  assign sl13nl1arc_pd_logic_sync  = sl13nl1arc_pd_logic_sync_r;
  assign sl14nl1arc_isolate_n_sync = sl14nl1arc_isolate_n_sync_r;
  assign sl14nl1arc_isolate_sync   = sl14nl1arc_isolate_sync_r;
  assign sl14nl1arc_pd_mem_sync    = sl14nl1arc_pd_mem_sync_r;
  assign sl14nl1arc_pd_logic_sync  = sl14nl1arc_pd_logic_sync_r;
  assign sl15nl1arc_isolate_n_sync = sl15nl1arc_isolate_n_sync_r;
  assign sl15nl1arc_isolate_sync   = sl15nl1arc_isolate_sync_r;
  assign sl15nl1arc_pd_mem_sync    = sl15nl1arc_pd_mem_sync_r;
  assign sl15nl1arc_pd_logic_sync  = sl15nl1arc_pd_logic_sync_r;


endmodule : npu_pdm_cdc_resync


