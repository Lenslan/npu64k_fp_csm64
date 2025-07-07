`ifndef CLN_TXC_STRUCTS__INCLUDED // {
`define CLN_TXC_STRUCTS__INCLUDED
package CLN_TXC_structs;
import CLN_structs::*;
`ifndef nl2_CLN_DEFINES_INCLUDED_
   `include "nl2_cln_defines.v"
`endif

typedef enum reg [6:0]
{
  S_IDLE,

  // Write START phase
  S_RD_SWITCH_TO_WRITE,
  S_WR_START_WAIT_DATA_CAPTURE,
  S_WR_START_WAIT_DATA_CAPTURE_RETRY,
  // Write DATA phase
  S_WR_DATA_CAPTURE,
  S_WR_DATA_QUEUE_SCM,
  // Write EARLY phase:
  S_WR_EARLY_RESPONSE,
  S_WR_EARLY_QUEUE_WRSP,
  S_WR_EARLY_QUEUE_SCM,
  // Write DISPATCH phase
  S_WR_DISPATCH,
  S_WR_DISPATCH_BNK_REQUEUE_SCM,
  S_WR_DISPATCH_BNK,
  S_WR_DISPATCH_MST,
  S_WR_DISPATCH_WAIT_ACCESS_MST,
  S_WR_DISPATCH_WATCH_LINE,
  S_WR_DISPATCH_REQUEUE_SCM,
  S_WR_DISPATCH_CMO,
  S_WR_DISPATCH_CMO_BNK_ISSUED,
  S_WR_DISPATCH_SCU_EVT,
  S_WR_DISPATCH_RUNOUT,
  // Write ACCESS phase
  S_WR_ACCESS_BNK,
  S_WR_ACCESS_MST,
  S_WR_ACCESS_WAIT_RESPONSE_MST,
  S_WR_ACCESS_SCU,
  S_WR_ACCESS_RUNOUT,
  // Write RESPONSE phase
  S_WR_RESPONSE_MST,
  S_WR_RESPONSE_BNK,
  S_WR_RESPONSE_SCU,
  S_WR_RESPONSE_MST_RUNOUT,
  S_WR_RESPONSE_BNK_RUNOUT,
  S_WR_RESPONSE_RUNOUT,
  // Not part of a phase:
  // These states should never test txc_release.

  // Read START phase
  S_RD_START_QUEUE_SCM = 7'b1000001,
  S_RD_START_QUEUE_SCM_RETRY,
  // Read DISPATCH phase
  S_RD_DISPATCH,
  S_RD_DISPATCH_BNK,
  S_RD_DISPATCH_MST,
  S_RD_DISPATCH_WATCH_LINE,
  S_RD_DISPATCH_REQUEUE_SCM,
  S_RD_DISPATCH_SCU,

  S_RD_DISPATCH_SCU_WRB_WAIT,
  S_RD_DISPATCH_SCU_WRB,
  S_RD_DISPATCH_SCU_WRB_QUEUE_SCM,
  S_RD_DISPATCH_SCU_WRB_REQUEUE_SCM,
  S_RD_DISPATCH_SCU_WRB_WATCH_LINE,
  S_RD_DISPATCH_SCU_WRB_QUEUED,
  S_RD_DISPATCH_SCU_WRB_TO_DST,
  S_RD_DISPATCH_SCU_RESPONSE_READY,

  S_RD_DISPATCH_SCU_WAIT,
  S_RD_DISPATCH_SCU_WAIT2,
  S_RD_DISPATCH_SCU_LPASS,
  S_RD_DISPATCH_SCU_RRESP_WAIT,
  S_RD_DISPATCH_SCU_RRESP,
  // Read ACCESS phase
  S_RD_ACCESS_BNK,
  S_RD_ACCESS_MST,
  S_RD_ACCESS_SCU_LPASS,
  S_RD_ACCESS_SCU_RRESP,
  // Read DELIVER phase
  S_RD_DELIVER_BNK,
  S_RD_DELIVER_MST,
  S_RD_DELIVER_SCU_RESP,

`ifdef CLN_WITH_MULTICAST // {
  S_RD_DISPATCH_WAIT_ACCESS_MCAST,
  S_RD_ACCESS_WAIT_DELIVER_MCAST,
  S_RD_DELIVER_MCAST,
`endif // } CLN_WITH_MULTICAST

  // Not part of a phase.
  // These states should never test txc_release:
  S_WR_WAIT_FINALIZE,
  S_FINALIZE_PENDING,
  S_FINALIZE
} txc_fsm_t;

typedef enum reg [2:0]
{
  R_IDLE,

  R_WRITEBACK_WAIT_FOR_DATA,
  R_REFILL_WAIT_FOR_DATA,
  R_REFILL_WAIT_FOR_RESPONSE,
  R_WRITEBACK_WAIT_FOR_RESPONSE
} txc_refill_fsm_t;

typedef enum reg [3:0]
{PH_RD_START    = 4'b1000,
 PH_RD_DISPATCH = 4'b1001,
 PH_RD_ACCESS   = 4'b1010,
 PH_RD_DELIVER  = 4'b1011,

 PH_WR_START    = 4'b0000,
 PH_WR_DATA     = 4'b0001,
 PH_WR_EARLY    = 4'b0010,
 PH_WR_DISPATCH = 4'b0011,
 PH_WR_ACCESS   = 4'b0100,
 PH_WR_RESPONSE = 4'b0101,

 PH_NONE        = 4'b1111
} txc_phase_t;

typedef struct packed {
  txc_fsm_t                  fsm;
  txc_phase_t                phase;

  cmda_cmd_s                 cmd;

  reg                        scc_enable;
  reg                        refill;
  reg                        writeback;
  reg                        outer_flsh;
  reg                        outer_ivld;
  reg                        scu_resend;
  reg                        resend;
  reg                        resend_immediate;
  reg                        resend_wait4txb;
  reg                        set_unstable;
  reg                        atomic;

  reg                        is_tail;    // mid-section or tail-section of a split sequence
  reg                        has_tail;   // head-section or mid-section of a split sequence
  reg                        tail_processed; // the tail TXC has started
  reg   [`nl2_CLN_CMD_BURST_RNG] tail_burst;     // burst size of the tail sequence
  reg                        nonblk;         // non-blocking transaction
  reg                        split_suppressed; // e.g. because cmd_cache[1] == 0 (unmodifiable)
  reg [$clog2(`nl2_ADEP_BLOCKS_PER_4k)-1:0] lo_blk; // used with split transaction address dependencies
  reg [$clog2(`nl2_ADEP_BLOCKS_PER_4k)-1:0] hi_blk; // used with split transaction address dependencies
  reg                        xboundary_4k;     // original transaction crosses a 4kB boundary

  reg                        slv_atomic_rsp;
  reg                        slv_atomic_err;
  reg                        slv2txb_arrived;
  reg    [`nl2_CFG_TXB_ADR_M1:0] slv2txb_id;
  reg                        slv2txb_started;
  reg                        slv2txb_completed;
  reg                        slv2txb_finalized;
  reg                        txb2slv_completed;

  reg                        dbk_dispatched;
  reg                        dbk_issued;
  reg                        dbk_issued_wr;
  reg [`nl2_CFG_BNK_ADDR_SIZE-`nl2_CFG_SCM_CACHE_BLOCK_ADDR-1:0] dbk_issued_addr;
  reg                        bnk_finished;
  reg                  [1:0] bnk_rsp;
  reg                        bnk2txb_arrived;
  reg    [`nl2_CFG_TXB_ADR_M1:0] bnk2txb_id;
  reg                        bnk2txb_completed;
  reg                        bnk2txb_finalized;
  reg                        bnk2txb_error;
  reg                        txb2bnk_completed;

  reg                        mst_dispatched;
  cln_port_type_s            mst_dispatched_src_type;
  reg     [`nl2_CFG_MST_ADR-1:0] mst_dispatched_id;
  reg                        mst_has_cmdid;
  reg                        mst_rd_issued;
  reg                        mst_wr_issued;
  reg                        mst_wr_issued_xboundary;
  reg                        mst_wr_done;
  reg        [`nl2_IBP_WRSP_RNG] mst_wr_done_wrsp;
  reg     [`nl2_CFG_MST_ADR-1:0] mst_wr_done_id;
  reg                        mst2txb_arrived;
  reg    [`nl2_CFG_TXB_ADR_M1:0] mst2txb_id;
  reg                        mst2txb_completed;
  reg                        mst2txb_finalized;
  reg                        mst2txb_error;
  reg                        txb2mst_completed;
  reg                        refill_error;
  
  reg                        patch_to_scu;
  reg                        scu_responded;
  reg                        scu_evt_dispatched;
  reg                        scu_linepass;
  reg                        scu_writeback;
  reg                        scu_wrb_completed;
  reg                        scu_snpwr_completed;
  reg                        scu2txb_arrived;
  reg    [`nl2_CFG_TXB_ADR_M1:0] scu2txb_id;
  reg                        scu2txb_started;
  reg                        scu2txb_completed;
  reg                        scu2txb_finalized;

  reg                        cache_op_dispatched;
  scm_cmo_dispatch_info_s    cache_op_dispatched_info;
  reg                        cache_op_processing;
} txc_state_s;

typedef struct packed {
  txc_refill_fsm_t           fsm;
  reg                        refill;
  reg [$clog2(`nl2_SCM_DBANK_CTRL_FIF_DEP)-1:0] refill_dependencies;
  reg                        writeback;
  reg [$clog2(`nl2_CLN_MST_QUEUE_FIF_DEP)-1:0] writeback_dependencies;
  reg                        wrb_wrsp_ack;
  reg  [`nl2_CFG_ADDR_SIZE_M1:0] victim_addr;
} txc_refill_state_s;


endpackage
`endif // } CLN_TXC_STRUCTS__INCLUDED
