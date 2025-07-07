
# Structure level
core_chip: core_sys core_sys_stub
core_sys: core_archipelago arcsync_top_stub alb_mss_fab alb_mss_mem

core_archipelago: npu_top arcsync_top
end_hierarchy

# Port aliases
## core_sys


# NPX CL0
alias npu_rst_a       core_archipelago.npu_rst_a      npu_top.rst_a
# ARCsync <-> NPX CL0 L2 ARC

alias nl2arc0_clusternum    npu_top.clusternum                   arcsync_top.nl2arc_clusternum
alias nl2arc0_arc_halt_ack  npu_top.nl2arc0_arc_halt_ack    arcsync_top.nl2arc0_arc_halt_ack_a
alias nl2arc0_arc_halt_req  npu_top.nl2arc0_arc_halt_req_a  arcsync_top.nl2arc0_arc_halt_req
alias nl2arc0_arc_run_ack   npu_top.nl2arc0_arc_run_ack     arcsync_top.nl2arc0_arc_run_ack_a
alias nl2arc0_arc_run_req   npu_top.nl2arc0_arc_run_req_a   arcsync_top.nl2arc0_arc_run_req
alias nl2arc0_arc_event_a   npu_top.nl2arc0_arc_event_a     arcsync_top.nl2arc0_arc_event
alias nl2arc0_arc_irq_a     npu_top.nl2arc0_arc_irq_a       arcsync_top.nl2arc0_arc_irq
alias nl2arc0_intvbase_in   npu_top.nl2arc0_intvbase_in     arcsync_top.nl2arc0_intvbase
alias nl2arc0_rst_a         npu_top.nl2arc0_rst_a           arcsync_top.nl2arc0_rst_a
alias nl2arc0_clk_en_a      npu_top.nl2arc0_clk_en_a        arcsync_top.nl2arc0_clk_en
alias nl2arc0_pwr_dwn       npu_top.nl2arc0_pwr_dwn_a       arcsync_top.nl2arc0_pwr_dwn
alias nl2arc1_pwr_dwn       npu_top.nl2arc1_pwr_dwn_a       arcsync_top.nl2arc1_pwr_dwn
alias nl2arc_pwr_dwn           npu_top.nl2arc_pwr_dwn_a           arcsync_top.nl2arc_pwr_dwn
alias nl2arc_isolate           npu_top.nl2arc_isolate             arcsync_top.nl2arc0_isolate  
alias nl2arc_isolate_n         npu_top.nl2arc_isolate_n           arcsync_top.nl2arc0_isolate_n
alias nl2arc_pd_mem            npu_top.nl2arc_pd_mem              arcsync_top.nl2arc0_pd_mem   
alias nl2arc_pd_logic          npu_top.nl2arc_pd_logic            arcsync_top.nl2arc0_pd_logic 
alias nl2arc_pu_rst            npu_top.nl2arc_pu_rst              arcsync_top.nl2arc0_pu_rst   

alias nl2arc1_arc_halt_ack  npu_top.nl2arc1_arc_halt_ack    arcsync_top.nl2arc1_arc_halt_ack_a
alias nl2arc1_arc_halt_req  npu_top.nl2arc1_arc_halt_req_a  arcsync_top.nl2arc1_arc_halt_req
alias nl2arc1_arc_run_ack   npu_top.nl2arc1_arc_run_ack     arcsync_top.nl2arc1_arc_run_ack_a
alias nl2arc1_arc_run_req   npu_top.nl2arc1_arc_run_req_a   arcsync_top.nl2arc1_arc_run_req
alias nl2arc1_arc_event_a   npu_top.nl2arc1_arc_event_a     arcsync_top.nl2arc1_arc_event
alias nl2arc1_arc_irq_a     npu_top.nl2arc1_arc_irq_a       arcsync_top.nl2arc1_arc_irq
alias nl2arc1_intvbase_in   npu_top.nl2arc1_intvbase_in     arcsync_top.nl2arc1_intvbase
alias nl2arc1_rst_a         npu_top.nl2arc1_rst_a           arcsync_top.nl2arc1_rst_a
alias nl2arc1_clk_en_a      npu_top.nl2arc1_clk_en_a        arcsync_top.nl2arc1_clk_en
alias nl2_rst_a                  npu_top.nl2_rst_a                    arcsync_top.nl2_rst

# ARCsync <-> NPX CL0 L1 Slice 0
alias sl0nl1arc_arc_halt_ack  npu_top.sl0nl1arc_arc_halt_ack    arcsync_top.sl0nl1arc_arc_halt_ack_a
alias sl0nl1arc_arc_halt_req  npu_top.sl0nl1arc_arc_halt_req_a  arcsync_top.sl0nl1arc_arc_halt_req
alias sl0nl1arc_arc_run_ack   npu_top.sl0nl1arc_arc_run_ack     arcsync_top.sl0nl1arc_arc_run_ack_a
alias sl0nl1arc_arc_run_req   npu_top.sl0nl1arc_arc_run_req_a   arcsync_top.sl0nl1arc_arc_run_req
alias sl0nl1arc_arc_event_a   npu_top.sl0nl1arc_arc_event_a     arcsync_top.sl0nl1arc_arc_event
alias sl0nl1arc_arc_irq_a     npu_top.sl0nl1arc_arc_irq_a       arcsync_top.sl0nl1arc_arc_irq
alias sl0nl1arc_intvbase_in   npu_top.sl0nl1arc_intvbase_in     arcsync_top.sl0nl1arc_intvbase
alias sl0nl1arc_pwr_dwn       npu_top.sl0nl1arc_pwr_dwn_a       arcsync_top.sl0nl1arc_pwr_dwn
alias sl0_rst_a                 npu_top.sl0_rst_a                   arcsync_top.sl0_rst_a
alias sl0_clk_en_a              npu_top.sl0_clk_en_a                arcsync_top.sl0_clk_en

# ARCsync <-> NPX CL0 L1 Slice 1
alias sl1nl1arc_arc_halt_ack  npu_top.sl1nl1arc_arc_halt_ack    arcsync_top.sl1nl1arc_arc_halt_ack_a
alias sl1nl1arc_arc_halt_req  npu_top.sl1nl1arc_arc_halt_req_a  arcsync_top.sl1nl1arc_arc_halt_req
alias sl1nl1arc_arc_run_ack   npu_top.sl1nl1arc_arc_run_ack     arcsync_top.sl1nl1arc_arc_run_ack_a
alias sl1nl1arc_arc_run_req   npu_top.sl1nl1arc_arc_run_req_a   arcsync_top.sl1nl1arc_arc_run_req
alias sl1nl1arc_arc_event_a   npu_top.sl1nl1arc_arc_event_a     arcsync_top.sl1nl1arc_arc_event
alias sl1nl1arc_arc_irq_a     npu_top.sl1nl1arc_arc_irq_a       arcsync_top.sl1nl1arc_arc_irq
alias sl1nl1arc_intvbase_in   npu_top.sl1nl1arc_intvbase_in     arcsync_top.sl1nl1arc_intvbase
alias sl1nl1arc_pwr_dwn       npu_top.sl1nl1arc_pwr_dwn_a       arcsync_top.sl1nl1arc_pwr_dwn
alias sl1_rst_a                 npu_top.sl1_rst_a                   arcsync_top.sl1_rst_a
alias sl1_clk_en_a              npu_top.sl1_clk_en_a                arcsync_top.sl1_clk_en

# ARCsync <-> NPX CL0 L1 Slice 2
alias sl2nl1arc_arc_halt_ack  npu_top.sl2nl1arc_arc_halt_ack    arcsync_top.sl2nl1arc_arc_halt_ack_a
alias sl2nl1arc_arc_halt_req  npu_top.sl2nl1arc_arc_halt_req_a  arcsync_top.sl2nl1arc_arc_halt_req
alias sl2nl1arc_arc_run_ack   npu_top.sl2nl1arc_arc_run_ack     arcsync_top.sl2nl1arc_arc_run_ack_a
alias sl2nl1arc_arc_run_req   npu_top.sl2nl1arc_arc_run_req_a   arcsync_top.sl2nl1arc_arc_run_req
alias sl2nl1arc_arc_event_a   npu_top.sl2nl1arc_arc_event_a     arcsync_top.sl2nl1arc_arc_event
alias sl2nl1arc_arc_irq_a     npu_top.sl2nl1arc_arc_irq_a       arcsync_top.sl2nl1arc_arc_irq
alias sl2nl1arc_intvbase_in   npu_top.sl2nl1arc_intvbase_in     arcsync_top.sl2nl1arc_intvbase
alias sl2nl1arc_pwr_dwn       npu_top.sl2nl1arc_pwr_dwn_a       arcsync_top.sl2nl1arc_pwr_dwn
alias sl2_rst_a                 npu_top.sl2_rst_a                   arcsync_top.sl2_rst_a
alias sl2_clk_en_a              npu_top.sl2_clk_en_a                arcsync_top.sl2_clk_en

# ARCsync <-> NPX CL0 L1 Slice 3
alias sl3nl1arc_arc_halt_ack  npu_top.sl3nl1arc_arc_halt_ack    arcsync_top.sl3nl1arc_arc_halt_ack_a
alias sl3nl1arc_arc_halt_req  npu_top.sl3nl1arc_arc_halt_req_a  arcsync_top.sl3nl1arc_arc_halt_req
alias sl3nl1arc_arc_run_ack   npu_top.sl3nl1arc_arc_run_ack     arcsync_top.sl3nl1arc_arc_run_ack_a
alias sl3nl1arc_arc_run_req   npu_top.sl3nl1arc_arc_run_req_a   arcsync_top.sl3nl1arc_arc_run_req
alias sl3nl1arc_arc_event_a   npu_top.sl3nl1arc_arc_event_a     arcsync_top.sl3nl1arc_arc_event
alias sl3nl1arc_arc_irq_a     npu_top.sl3nl1arc_arc_irq_a       arcsync_top.sl3nl1arc_arc_irq
alias sl3nl1arc_intvbase_in   npu_top.sl3nl1arc_intvbase_in     arcsync_top.sl3nl1arc_intvbase
alias sl3nl1arc_pwr_dwn       npu_top.sl3nl1arc_pwr_dwn_a       arcsync_top.sl3nl1arc_pwr_dwn
alias sl3_rst_a                 npu_top.sl3_rst_a                   arcsync_top.sl3_rst_a
alias sl3_clk_en_a              npu_top.sl3_clk_en_a                arcsync_top.sl3_clk_en

# ARCsync <-> NPX CL0 L1 Slice 4
alias sl4nl1arc_arc_halt_ack  npu_top.sl4nl1arc_arc_halt_ack    arcsync_top.sl4nl1arc_arc_halt_ack_a
alias sl4nl1arc_arc_halt_req  npu_top.sl4nl1arc_arc_halt_req_a  arcsync_top.sl4nl1arc_arc_halt_req
alias sl4nl1arc_arc_run_ack   npu_top.sl4nl1arc_arc_run_ack     arcsync_top.sl4nl1arc_arc_run_ack_a
alias sl4nl1arc_arc_run_req   npu_top.sl4nl1arc_arc_run_req_a   arcsync_top.sl4nl1arc_arc_run_req
alias sl4nl1arc_arc_event_a   npu_top.sl4nl1arc_arc_event_a     arcsync_top.sl4nl1arc_arc_event
alias sl4nl1arc_arc_irq_a     npu_top.sl4nl1arc_arc_irq_a       arcsync_top.sl4nl1arc_arc_irq
alias sl4nl1arc_intvbase_in   npu_top.sl4nl1arc_intvbase_in     arcsync_top.sl4nl1arc_intvbase
alias sl4nl1arc_pwr_dwn       npu_top.sl4nl1arc_pwr_dwn_a       arcsync_top.sl4nl1arc_pwr_dwn
alias sl4_rst_a                 npu_top.sl4_rst_a                   arcsync_top.sl4_rst_a
alias sl4_clk_en_a              npu_top.sl4_clk_en_a                arcsync_top.sl4_clk_en

# ARCsync <-> NPX CL0 L1 Slice 5
alias sl5nl1arc_arc_halt_ack  npu_top.sl5nl1arc_arc_halt_ack    arcsync_top.sl5nl1arc_arc_halt_ack_a
alias sl5nl1arc_arc_halt_req  npu_top.sl5nl1arc_arc_halt_req_a  arcsync_top.sl5nl1arc_arc_halt_req
alias sl5nl1arc_arc_run_ack   npu_top.sl5nl1arc_arc_run_ack     arcsync_top.sl5nl1arc_arc_run_ack_a
alias sl5nl1arc_arc_run_req   npu_top.sl5nl1arc_arc_run_req_a   arcsync_top.sl5nl1arc_arc_run_req
alias sl5nl1arc_arc_event_a   npu_top.sl5nl1arc_arc_event_a     arcsync_top.sl5nl1arc_arc_event
alias sl5nl1arc_arc_irq_a     npu_top.sl5nl1arc_arc_irq_a       arcsync_top.sl5nl1arc_arc_irq
alias sl5nl1arc_intvbase_in   npu_top.sl5nl1arc_intvbase_in     arcsync_top.sl5nl1arc_intvbase
alias sl5nl1arc_pwr_dwn       npu_top.sl5nl1arc_pwr_dwn_a       arcsync_top.sl5nl1arc_pwr_dwn
alias sl5_rst_a                 npu_top.sl5_rst_a                   arcsync_top.sl5_rst_a
alias sl5_clk_en_a              npu_top.sl5_clk_en_a                arcsync_top.sl5_clk_en

# ARCsync <-> NPX CL0 L1 Slice 6
alias sl6nl1arc_arc_halt_ack  npu_top.sl6nl1arc_arc_halt_ack    arcsync_top.sl6nl1arc_arc_halt_ack_a
alias sl6nl1arc_arc_halt_req  npu_top.sl6nl1arc_arc_halt_req_a  arcsync_top.sl6nl1arc_arc_halt_req
alias sl6nl1arc_arc_run_ack   npu_top.sl6nl1arc_arc_run_ack     arcsync_top.sl6nl1arc_arc_run_ack_a
alias sl6nl1arc_arc_run_req   npu_top.sl6nl1arc_arc_run_req_a   arcsync_top.sl6nl1arc_arc_run_req
alias sl6nl1arc_arc_event_a   npu_top.sl6nl1arc_arc_event_a     arcsync_top.sl6nl1arc_arc_event
alias sl6nl1arc_arc_irq_a     npu_top.sl6nl1arc_arc_irq_a       arcsync_top.sl6nl1arc_arc_irq
alias sl6nl1arc_intvbase_in   npu_top.sl6nl1arc_intvbase_in     arcsync_top.sl6nl1arc_intvbase
alias sl6nl1arc_pwr_dwn       npu_top.sl6nl1arc_pwr_dwn_a       arcsync_top.sl6nl1arc_pwr_dwn
alias sl6_rst_a                 npu_top.sl6_rst_a                   arcsync_top.sl6_rst_a
alias sl6_clk_en_a              npu_top.sl6_clk_en_a                arcsync_top.sl6_clk_en

# ARCsync <-> NPX CL0 L1 Slice 7
alias sl7nl1arc_arc_halt_ack  npu_top.sl7nl1arc_arc_halt_ack    arcsync_top.sl7nl1arc_arc_halt_ack_a
alias sl7nl1arc_arc_halt_req  npu_top.sl7nl1arc_arc_halt_req_a  arcsync_top.sl7nl1arc_arc_halt_req
alias sl7nl1arc_arc_run_ack   npu_top.sl7nl1arc_arc_run_ack     arcsync_top.sl7nl1arc_arc_run_ack_a
alias sl7nl1arc_arc_run_req   npu_top.sl7nl1arc_arc_run_req_a   arcsync_top.sl7nl1arc_arc_run_req
alias sl7nl1arc_arc_event_a   npu_top.sl7nl1arc_arc_event_a     arcsync_top.sl7nl1arc_arc_event
alias sl7nl1arc_arc_irq_a     npu_top.sl7nl1arc_arc_irq_a       arcsync_top.sl7nl1arc_arc_irq
alias sl7nl1arc_intvbase_in   npu_top.sl7nl1arc_intvbase_in     arcsync_top.sl7nl1arc_intvbase
alias sl7nl1arc_pwr_dwn       npu_top.sl7nl1arc_pwr_dwn_a       arcsync_top.sl7nl1arc_pwr_dwn
alias sl7_rst_a                 npu_top.sl7_rst_a                   arcsync_top.sl7_rst_a
alias sl7_clk_en_a              npu_top.sl7_clk_en_a                arcsync_top.sl7_clk_en

# ARCsync <-> NPX CL0 L1 Slice 8
alias sl8nl1arc_arc_halt_ack  npu_top.sl8nl1arc_arc_halt_ack    arcsync_top.sl8nl1arc_arc_halt_ack_a
alias sl8nl1arc_arc_halt_req  npu_top.sl8nl1arc_arc_halt_req_a  arcsync_top.sl8nl1arc_arc_halt_req
alias sl8nl1arc_arc_run_ack   npu_top.sl8nl1arc_arc_run_ack     arcsync_top.sl8nl1arc_arc_run_ack_a
alias sl8nl1arc_arc_run_req   npu_top.sl8nl1arc_arc_run_req_a   arcsync_top.sl8nl1arc_arc_run_req
alias sl8nl1arc_arc_event_a   npu_top.sl8nl1arc_arc_event_a     arcsync_top.sl8nl1arc_arc_event
alias sl8nl1arc_arc_irq_a     npu_top.sl8nl1arc_arc_irq_a       arcsync_top.sl8nl1arc_arc_irq
alias sl8nl1arc_intvbase_in   npu_top.sl8nl1arc_intvbase_in     arcsync_top.sl8nl1arc_intvbase
alias sl8nl1arc_pwr_dwn       npu_top.sl8nl1arc_pwr_dwn_a       arcsync_top.sl8nl1arc_pwr_dwn
alias sl8_rst_a                 npu_top.sl8_rst_a                   arcsync_top.sl8_rst_a
alias sl8_clk_en_a              npu_top.sl8_clk_en_a                arcsync_top.sl8_clk_en

# ARCsync <-> NPX CL0 L1 Slice 9
alias sl9nl1arc_arc_halt_ack  npu_top.sl9nl1arc_arc_halt_ack    arcsync_top.sl9nl1arc_arc_halt_ack_a
alias sl9nl1arc_arc_halt_req  npu_top.sl9nl1arc_arc_halt_req_a  arcsync_top.sl9nl1arc_arc_halt_req
alias sl9nl1arc_arc_run_ack   npu_top.sl9nl1arc_arc_run_ack     arcsync_top.sl9nl1arc_arc_run_ack_a
alias sl9nl1arc_arc_run_req   npu_top.sl9nl1arc_arc_run_req_a   arcsync_top.sl9nl1arc_arc_run_req
alias sl9nl1arc_arc_event_a   npu_top.sl9nl1arc_arc_event_a     arcsync_top.sl9nl1arc_arc_event
alias sl9nl1arc_arc_irq_a     npu_top.sl9nl1arc_arc_irq_a       arcsync_top.sl9nl1arc_arc_irq
alias sl9nl1arc_intvbase_in   npu_top.sl9nl1arc_intvbase_in     arcsync_top.sl9nl1arc_intvbase
alias sl9nl1arc_pwr_dwn       npu_top.sl9nl1arc_pwr_dwn_a       arcsync_top.sl9nl1arc_pwr_dwn
alias sl9_rst_a                 npu_top.sl9_rst_a                   arcsync_top.sl9_rst_a
alias sl9_clk_en_a              npu_top.sl9_clk_en_a                arcsync_top.sl9_clk_en

# ARCsync <-> NPX CL0 L1 Slice 10
alias sl10nl1arc_arc_halt_ack  npu_top.sl10nl1arc_arc_halt_ack    arcsync_top.sl10nl1arc_arc_halt_ack_a
alias sl10nl1arc_arc_halt_req  npu_top.sl10nl1arc_arc_halt_req_a  arcsync_top.sl10nl1arc_arc_halt_req
alias sl10nl1arc_arc_run_ack   npu_top.sl10nl1arc_arc_run_ack     arcsync_top.sl10nl1arc_arc_run_ack_a
alias sl10nl1arc_arc_run_req   npu_top.sl10nl1arc_arc_run_req_a   arcsync_top.sl10nl1arc_arc_run_req
alias sl10nl1arc_arc_event_a   npu_top.sl10nl1arc_arc_event_a     arcsync_top.sl10nl1arc_arc_event
alias sl10nl1arc_arc_irq_a     npu_top.sl10nl1arc_arc_irq_a       arcsync_top.sl10nl1arc_arc_irq
alias sl10nl1arc_intvbase_in   npu_top.sl10nl1arc_intvbase_in     arcsync_top.sl10nl1arc_intvbase
alias sl10nl1arc_pwr_dwn       npu_top.sl10nl1arc_pwr_dwn_a       arcsync_top.sl10nl1arc_pwr_dwn
alias sl10_rst_a                 npu_top.sl10_rst_a                   arcsync_top.sl10_rst_a
alias sl10_clk_en_a              npu_top.sl10_clk_en_a                arcsync_top.sl10_clk_en

# ARCsync <-> NPX CL0 L1 Slice 11
alias sl11nl1arc_arc_halt_ack  npu_top.sl11nl1arc_arc_halt_ack    arcsync_top.sl11nl1arc_arc_halt_ack_a
alias sl11nl1arc_arc_halt_req  npu_top.sl11nl1arc_arc_halt_req_a  arcsync_top.sl11nl1arc_arc_halt_req
alias sl11nl1arc_arc_run_ack   npu_top.sl11nl1arc_arc_run_ack     arcsync_top.sl11nl1arc_arc_run_ack_a
alias sl11nl1arc_arc_run_req   npu_top.sl11nl1arc_arc_run_req_a   arcsync_top.sl11nl1arc_arc_run_req
alias sl11nl1arc_arc_event_a   npu_top.sl11nl1arc_arc_event_a     arcsync_top.sl11nl1arc_arc_event
alias sl11nl1arc_arc_irq_a     npu_top.sl11nl1arc_arc_irq_a       arcsync_top.sl11nl1arc_arc_irq
alias sl11nl1arc_intvbase_in   npu_top.sl11nl1arc_intvbase_in     arcsync_top.sl11nl1arc_intvbase
alias sl11nl1arc_pwr_dwn       npu_top.sl11nl1arc_pwr_dwn_a       arcsync_top.sl11nl1arc_pwr_dwn
alias sl11_rst_a                 npu_top.sl11_rst_a                   arcsync_top.sl11_rst_a
alias sl11_clk_en_a              npu_top.sl11_clk_en_a                arcsync_top.sl11_clk_en

# ARCsync <-> NPX CL0 L1 Slice 12
alias sl12nl1arc_arc_halt_ack  npu_top.sl12nl1arc_arc_halt_ack    arcsync_top.sl12nl1arc_arc_halt_ack_a
alias sl12nl1arc_arc_halt_req  npu_top.sl12nl1arc_arc_halt_req_a  arcsync_top.sl12nl1arc_arc_halt_req
alias sl12nl1arc_arc_run_ack   npu_top.sl12nl1arc_arc_run_ack     arcsync_top.sl12nl1arc_arc_run_ack_a
alias sl12nl1arc_arc_run_req   npu_top.sl12nl1arc_arc_run_req_a   arcsync_top.sl12nl1arc_arc_run_req
alias sl12nl1arc_arc_event_a   npu_top.sl12nl1arc_arc_event_a     arcsync_top.sl12nl1arc_arc_event
alias sl12nl1arc_arc_irq_a     npu_top.sl12nl1arc_arc_irq_a       arcsync_top.sl12nl1arc_arc_irq
alias sl12nl1arc_intvbase_in   npu_top.sl12nl1arc_intvbase_in     arcsync_top.sl12nl1arc_intvbase
alias sl12nl1arc_pwr_dwn       npu_top.sl12nl1arc_pwr_dwn_a       arcsync_top.sl12nl1arc_pwr_dwn
alias sl12_rst_a                 npu_top.sl12_rst_a                   arcsync_top.sl12_rst_a
alias sl12_clk_en_a              npu_top.sl12_clk_en_a                arcsync_top.sl12_clk_en

# ARCsync <-> NPX CL0 L1 Slice 13
alias sl13nl1arc_arc_halt_ack  npu_top.sl13nl1arc_arc_halt_ack    arcsync_top.sl13nl1arc_arc_halt_ack_a
alias sl13nl1arc_arc_halt_req  npu_top.sl13nl1arc_arc_halt_req_a  arcsync_top.sl13nl1arc_arc_halt_req
alias sl13nl1arc_arc_run_ack   npu_top.sl13nl1arc_arc_run_ack     arcsync_top.sl13nl1arc_arc_run_ack_a
alias sl13nl1arc_arc_run_req   npu_top.sl13nl1arc_arc_run_req_a   arcsync_top.sl13nl1arc_arc_run_req
alias sl13nl1arc_arc_event_a   npu_top.sl13nl1arc_arc_event_a     arcsync_top.sl13nl1arc_arc_event
alias sl13nl1arc_arc_irq_a     npu_top.sl13nl1arc_arc_irq_a       arcsync_top.sl13nl1arc_arc_irq
alias sl13nl1arc_intvbase_in   npu_top.sl13nl1arc_intvbase_in     arcsync_top.sl13nl1arc_intvbase
alias sl13nl1arc_pwr_dwn       npu_top.sl13nl1arc_pwr_dwn_a       arcsync_top.sl13nl1arc_pwr_dwn
alias sl13_rst_a                 npu_top.sl13_rst_a                   arcsync_top.sl13_rst_a
alias sl13_clk_en_a              npu_top.sl13_clk_en_a                arcsync_top.sl13_clk_en

# ARCsync <-> NPX CL0 L1 Slice 14
alias sl14nl1arc_arc_halt_ack  npu_top.sl14nl1arc_arc_halt_ack    arcsync_top.sl14nl1arc_arc_halt_ack_a
alias sl14nl1arc_arc_halt_req  npu_top.sl14nl1arc_arc_halt_req_a  arcsync_top.sl14nl1arc_arc_halt_req
alias sl14nl1arc_arc_run_ack   npu_top.sl14nl1arc_arc_run_ack     arcsync_top.sl14nl1arc_arc_run_ack_a
alias sl14nl1arc_arc_run_req   npu_top.sl14nl1arc_arc_run_req_a   arcsync_top.sl14nl1arc_arc_run_req
alias sl14nl1arc_arc_event_a   npu_top.sl14nl1arc_arc_event_a     arcsync_top.sl14nl1arc_arc_event
alias sl14nl1arc_arc_irq_a     npu_top.sl14nl1arc_arc_irq_a       arcsync_top.sl14nl1arc_arc_irq
alias sl14nl1arc_intvbase_in   npu_top.sl14nl1arc_intvbase_in     arcsync_top.sl14nl1arc_intvbase
alias sl14nl1arc_pwr_dwn       npu_top.sl14nl1arc_pwr_dwn_a       arcsync_top.sl14nl1arc_pwr_dwn
alias sl14_rst_a                 npu_top.sl14_rst_a                   arcsync_top.sl14_rst_a
alias sl14_clk_en_a              npu_top.sl14_clk_en_a                arcsync_top.sl14_clk_en

# ARCsync <-> NPX CL0 L1 Slice 15
alias sl15nl1arc_arc_halt_ack  npu_top.sl15nl1arc_arc_halt_ack    arcsync_top.sl15nl1arc_arc_halt_ack_a
alias sl15nl1arc_arc_halt_req  npu_top.sl15nl1arc_arc_halt_req_a  arcsync_top.sl15nl1arc_arc_halt_req
alias sl15nl1arc_arc_run_ack   npu_top.sl15nl1arc_arc_run_ack     arcsync_top.sl15nl1arc_arc_run_ack_a
alias sl15nl1arc_arc_run_req   npu_top.sl15nl1arc_arc_run_req_a   arcsync_top.sl15nl1arc_arc_run_req
alias sl15nl1arc_arc_event_a   npu_top.sl15nl1arc_arc_event_a     arcsync_top.sl15nl1arc_arc_event
alias sl15nl1arc_arc_irq_a     npu_top.sl15nl1arc_arc_irq_a       arcsync_top.sl15nl1arc_arc_irq
alias sl15nl1arc_intvbase_in   npu_top.sl15nl1arc_intvbase_in     arcsync_top.sl15nl1arc_intvbase
alias sl15nl1arc_pwr_dwn       npu_top.sl15nl1arc_pwr_dwn_a       arcsync_top.sl15nl1arc_pwr_dwn
alias sl15_rst_a                 npu_top.sl15_rst_a                   arcsync_top.sl15_rst_a
alias sl15_clk_en_a              npu_top.sl15_clk_en_a                arcsync_top.sl15_clk_en


alias grp0_rst_a                npu_top.grp0_rst_a          arcsync_top.grp0_rst_a
alias grp0_clk_en               npu_top.grp0_clk_en_a       arcsync_top.grp0_clk_en
alias grp0_pwr_dwn              npu_top.grp0_pwr_dwn_a      arcsync_top.grp0_pwr_dwn
alias grp1_rst_a                npu_top.grp1_rst_a          arcsync_top.grp1_rst_a
alias grp1_clk_en               npu_top.grp1_clk_en_a       arcsync_top.grp1_clk_en
alias grp1_pwr_dwn              npu_top.grp1_pwr_dwn_a      arcsync_top.grp1_pwr_dwn
alias grp2_rst_a                npu_top.grp2_rst_a          arcsync_top.grp2_rst_a
alias grp2_clk_en               npu_top.grp2_clk_en_a       arcsync_top.grp2_clk_en
alias grp2_pwr_dwn              npu_top.grp2_pwr_dwn_a      arcsync_top.grp2_pwr_dwn
alias grp3_rst_a                npu_top.grp3_rst_a          arcsync_top.grp3_rst_a
alias grp3_clk_en               npu_top.grp3_clk_en_a       arcsync_top.grp3_clk_en
alias grp3_pwr_dwn              npu_top.grp3_pwr_dwn_a      arcsync_top.grp3_pwr_dwn









# Resets
alias arcsync_rst_a   core_archipelago.arcsync_rst_a  arcsync_top.rst_a


