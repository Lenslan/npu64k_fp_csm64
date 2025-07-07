package CLN_structs;
`ifndef nl2_CLN_DEFINES_INCLUDED_
   `include "nl2_cln_defines.v"
`endif

typedef struct packed {
  reg                                      op_valid;   
  reg                                      index_mode;
  reg                                      region_addr; 
  reg                                      invalidate; 
  reg                                      clean; 
  reg                                      region_last; 
  reg      [`nl2_MAX_SCM_CACHE_SETS_ADDR-1 :0] cache_index; 
  reg     [`nl2_MAX_SCM_CACHE_ASSOC_ADDR-1 :0] cache_way; 
  reg                               [ 3:0] cache_slv_arc; 
  reg                                      cache_coherent; 
  reg                                      update_index_way; 
  reg                                      update_moesip; 
  reg                                      update_cache_addr; 
  reg                                      cache_op_err; 
} scm_cache_op_cmd_s;

typedef struct packed {
  reg                   [`nl2_CFG_SLV_ADR-1:0] slv_id;
  reg           [`nl2_CFG_CMD_ID_SIZE_MAX-1:0] cmd_id;
  reg                 [`nl2_CFG_ADDR_SIZE-1:0] addr;
  reg                                      xcmd_error;
  reg                                      xcmd_wcombine;
  reg                                      xcmd_fast_wrsp;
`ifdef CLN_WITH_MULTICAST
  reg            [`nl2_CLN_MULTICAST_SIZE-1:0] xcmd_multicast;
`endif
  reg                                      read;
  reg                  [`nl2_IBP_CMD_DATA_RNG] data_size;
  reg                 [`nl2_CLN_CMD_BURST_RNG] burst_size;
  reg                 [`nl2_IBP_CMD_SPACE_RNG] space;
  reg                                      wrap;
  reg                                      fixed;
  reg                                [1:0] ar;
  reg                                [1:0] atomic;
  reg                                      excl;
  reg                                [1:0] prot;
  reg                                [3:0] cache;
  reg                                [3:0] snoop;
  reg                                [3:0] victim;
  reg                                [1:0] domain;
  reg                                [2:0] rdomid;
  scm_cache_op_cmd_s                       cache_op_cmd;
} cmda_cmd_s;

typedef struct packed {
  reg                                      clean; 
  reg                                      cache_op_err; 
  reg      [`nl2_CFG_SCM_CACHE_ASSOC_ADDR-1:0] victim_way_id;
} scm_cmo_dispatch_info_s;

typedef enum logic [1:0] {
  SPLIT_NONE,                   // transaction is not split
  SPLIT_HEAD_SECTION,           // first part of a split transaction
  SPLIT_MID_SECTION,            // in-between the head and the tail
  SPLIT_TAIL_SECTION            // last part of a split transaction
} split_t;

typedef struct packed {
  split_t                                  split;
  reg                                      split_suppressed; // size calls for a split
  reg                                      xboundary_4k;     // transaction crossing 4kB boundary
  reg                                      scc_enable;
  reg                                      refill;
  reg                                      resend;
  reg                                      writeback;
  reg                                      scu_writeback;
  reg                                      nonblk;
  reg                                      outer_flsh; //indicator to SC
  reg                                      outer_ivld; //indicator to SC
  reg                   [`nl2_CFG_TXC_ADR-1:0] txc_id;
  reg                   [`nl2_CFG_SLV_ADR-1:0] slv_id;
  reg           [`nl2_CFG_CMD_ID_SIZE_MAX-1:0] cmd_id;
  reg                 [`nl2_CFG_ADDR_SIZE-1:0] addr;
  reg    [$clog2(`nl2_ADEP_BLOCKS_PER_4k)-1:0] lo_blk; // Same for all sections of a split-chain, used for aperture matching.
  reg    [$clog2(`nl2_ADEP_BLOCKS_PER_4k)-1:0] hi_blk; // Same for all sections of a split-chain, used for aperture matching.
  reg                                      read;
  reg                  [`nl2_IBP_CMD_DATA_RNG] data_size;
  reg                 [`nl2_CLN_CMD_BURST_RNG] burst_size;
  reg                 [`nl2_CLN_CMD_BURST_RNG] orig_burst_size; // for split transactions
  reg                 [`nl2_IBP_CMD_SPACE_RNG] space;
  reg                                      wrap;
  reg                                      fixed;
  reg                                [1:0] ar;
  reg                                [1:0] atomic;
  reg                                      excl;
  reg                                [1:0] prot;
  reg                                [3:0] cache;
  reg                                [3:0] snoop;
  reg                                [3:0] victim;
  reg                                [1:0] domain;
  reg                                [2:0] rdomid;
  reg           [`nl2_CFG_MST_MAX_APT_ADR-1:0] aperture;
  reg                                      error;
  reg                                      shared;
  reg                                      wcombine;
`ifdef CLN_WITH_MULTICAST
  reg            [`nl2_CLN_MULTICAST_SIZE-1:0] participants;
`endif
  scm_cache_op_cmd_s                       cache_op_cmd;
} txc_cmd_s;

typedef struct packed {
  reg       [`nl2_CFG_SCM_CACHE_TAG_ADDR-1:0] tag;                              
  reg     [`nl2_CFG_SCM_CACHE_INDEX_ADDR-1:0] bank_addr;                              
  reg [`nl2_CFG_SCM_CACHE_TAG_BANKS_ADDR-1:0] bank;                              
  reg     [`nl2_CFG_SCM_CACHE_BLOCK_ADDR-1:0] byte_addr;                              
} scm_lookup_addr_s;

typedef struct packed {
  split_t                                  split;
  reg                                      refill;
  reg                                      outer_flsh;
  reg                                      outer_ivld;
  reg                                      scu_writeback;
  reg                                      nonblk;
  reg                   [`nl2_CFG_TXC_ADR-1:0] txc_id;
  reg                   [`nl2_CFG_SLV_ADR-1:0] slv_id;
  reg           [`nl2_CFG_CMD_ID_SIZE_MAX-1:0] cmd_id;
  scm_lookup_addr_s                        addr;
  reg                                      read;
  reg                  [`nl2_IBP_CMD_DATA_RNG] data_size;
  reg                 [`nl2_CLN_CMD_BURST_RNG] burst_size;
  reg                 [`nl2_IBP_CMD_SPACE_RNG] space;
  reg                                      wrap;
  reg                                      fixed;
  reg                                [1:0] ar;
  reg                                [1:0] atomic;
  reg                                      excl;
  reg                                [1:0] prot;
  reg                                [3:0] cache;
  reg                                [3:0] snoop;
  reg                                [1:0] domain;
  reg                                [2:0] rdomid;
  reg                                      error;
  reg                                      shared;
  reg                                      dirty;
  reg                                      scu; //add a SCU flag bit to indicate whether the cmd has also been sent to SCU simultaneously
  scm_cache_op_cmd_s                       cache_op_cmd;
} scm_cache_cmd_s;

typedef struct packed {
  reg                                      error;
  split_t                                  split;
  reg                                      writeback;
  reg                                      refill;
  reg                                      nonblk;
  reg                   [`nl2_CFG_TXC_ADR-1:0] txc_id;
  reg                   [`nl2_CFG_SLV_ADR-1:0] slv_id;
  reg             [`nl2_CFG_BNK_ADDR_SIZE-1:0] addr;
  reg                                      read;
  reg                  [`nl2_IBP_CMD_DATA_RNG] data_size;
  reg                 [`nl2_CLN_CMD_BURST_RNG] burst_size;
  reg                                [1:0] atomic;
  reg                                      wrap;
  reg                                      fixed;
  reg                                      excl;
  reg                                      shared;
  reg                                      dirty;
  reg                                      outer_op;
`ifdef CLN_WITH_MULTICAST
  reg            [`nl2_CLN_MULTICAST_SIZE-1:0] participants;
`endif
} scm_dbk_cmd_s;

typedef enum reg [2:0] {
  CLN_MODIFIED  = 3'b010,
  CLN_OWNED     = 3'b011,
  CLN_EXCLUSIVE = 3'b100,
  CLN_SHARED    = 3'b101,
  CLN_INVALID   = 3'b000,
  CLN_PENDING   = 3'b001
} moesip_t;

typedef struct packed {
`ifdef nl2_SCM_WITH_ECC
  reg               [`nl2_TBANK_ECC_WIDTH-1:0] ecc;
`endif
`ifdef CFG_QOS_ENABLED
  reg              [`nl2_TBANK_DATA_WIDTH-9:0] tag;
  reg                                [2:0] rdomid;
`else
  reg              [`nl2_TBANK_DATA_WIDTH-6:0] tag;
`endif
  reg                                      outer;
  reg                                      prot;
  moesip_t                                 moesip;
} scm_tbnk_way_s;

typedef struct packed {
  reg                                       hit;
  reg       [`nl2_CFG_SCM_CACHE_ASSOC_ADDR-1:0] hit_way_id;
  moesip_t                                  hit_moesip;
  scm_tbnk_way_s [`nl2_CFG_SCM_CACHE_ASSOC-1:0] all_ways;
`ifdef nl2_SCM_WITH_ECC
  reg                                       ecc_single_err;
  reg                                       ecc_double_err;
`endif
} scm_tag_res_s;

typedef struct packed {
  reg     [`nl2_CFG_SCM_CACHE_INDEX_ADDR-1:0] bank_addr;                              
  reg [`nl2_CFG_SCM_CACHE_TAG_BANKS_ADDR-1:0] bank;                              
} scm_update_addr_s;

typedef struct packed {
  reg                                      inval_set;
  scm_update_addr_s                        addr;
  reg      [`nl2_CFG_SCM_CACHE_ASSOC_ADDR-1:0] way_id;
  scm_tbnk_way_s                           new_tag;
} scm_new_tag_cmd_s;

typedef struct packed {
  reg                                      inval_set;
  reg      [`nl2_CFG_SCM_CACHE_INDEX_ADDR-1:0] addr;
  reg                                      rd_en;
  reg                                      wr_en;
  reg      [`nl2_CFG_SCM_CACHE_ASSOC_ADDR-1:0] wr_sel;
`ifdef nl2_SCM_WITH_ECC
  reg [`nl2_TBANK_ECC_WIDTH+`nl2_TBANK_DATA_WIDTH-1:0] wr_data; // {ecc, data}
`else
  reg              [`nl2_TBANK_DATA_WIDTH-1:0] wr_data;
`endif
} scm_tbnk_sram_intf_s;

typedef struct packed {
  split_t                                 split;
  reg                                     scc_enable;
  reg                                     refill;
  reg                                     resend;
  reg                                     writeback;
  reg                  [`nl2_CFG_TXC_ADR-1:0] txc_id;
  reg                  [`nl2_CFG_SLV_ADR-1:0] slv_id;
  reg          [`nl2_CFG_CMD_ID_SIZE_MAX-1:0] cmd_id;
  reg                [`nl2_CFG_ADDR_SIZE-1:0] addr;
  reg                                     read;
  reg                 [`nl2_IBP_CMD_DATA_RNG] data_size;
  reg                [`nl2_CLN_CMD_BURST_RNG] burst_size;
  reg                [`nl2_CLN_CMD_BURST_RNG] orig_burst_size; // for split transactions
  reg                [`nl2_IBP_CMD_SPACE_RNG] space;
  reg                                     wrap;
  reg                                     fixed;
  reg                               [1:0] ar;
  reg                                     excl;
  reg                               [1:0] prot;
  reg                               [3:0] cache;
  reg                               [3:0] snoop;
  reg                               [3:0] victim;
  reg                               [1:0] domain;
  reg                               [2:0] rdomid;
`ifdef CLN_WITH_MULTICAST
  reg            [`nl2_CLN_MULTICAST_SIZE-1:0] participants;
`endif
  reg                                     shm; //fall into shared memory space
  reg                                     scc; //fall into shared cache space
} scm_scu_cmd_s;

typedef struct packed {
  reg                                     resend;
  reg                                     read;
  reg                               [3:0] snoop;
} scu_ahint_s;

typedef struct packed {
  split_t                                 split;
  reg                                     scc_enable;
  reg                                     refill;
  reg                                     resend;
  reg                                     writeback;
  reg                  [`nl2_CFG_TXC_ADR-1:0] txc_id;
  reg                  [`nl2_CFG_SLV_ADR-1:0] slv_id;
  reg          [`nl2_CFG_CMD_ID_SIZE_MAX-1:0] cmd_id;
  reg                [`nl2_CFG_ADDR_SIZE-1:0] addr;
  reg                                     read;
  reg                 [`nl2_IBP_CMD_DATA_RNG] data_size;
  reg                [`nl2_CLN_CMD_BURST_RNG] burst_size;
  reg                [`nl2_CLN_CMD_BURST_RNG] orig_burst_size; // for split transactions
  reg                [`nl2_IBP_CMD_SPACE_RNG] space;
  reg                                     wrap;
  reg                                     fixed;
  reg                               [1:0] ar;
  reg                                     excl;
  reg                               [1:0] prot;
  reg                               [3:0] cache;
  reg                               [3:0] snoop;
  reg                               [3:0] orig_snoop;
  reg                               [3:0] victim;
  reg                               [1:0] domain;
  reg                               [2:0] rdomid;
`ifdef CLN_WITH_MULTICAST
  reg            [`nl2_CLN_MULTICAST_SIZE-1:0] participants;
`endif
  reg                                     shm; //fall into shared memory space
  reg                                     scc; //fall into shared cache space
} stb_scu_cmd_s;

//SCU internal
typedef struct packed {
  reg [`nl2_CFG_CMD_ID_SIZE_MAX-1:0] cmd_id;
  reg [`nl2_STB_IDX_BITS-1:0]        stb_id;
} scu_ack_fifo_s;

typedef struct packed {
  reg                            has_stb_adep;
  reg [`nl2_STB_IDX_BITS-1:0]        pred_stb_id; //tail of STB predecessor with addr dependency
  reg                            has_wtb_adep;
  reg  [`nl2_WTB_ENTRIES-1:0]        pred_wtb_vec;
} stb_adep_state_s;

typedef struct packed {
  reg                            has_cmdid_dep;
  reg [`nl2_STB_IDX_BITS-1:0]        pred_id; //tail of STB predecesssor
} stb_cmdid_state_s;

typedef struct packed {
  reg                            tlu_ongoing;
  reg                            is_resend;
} stb_tlu_state_s;

//for SCC tag lookup result
typedef struct packed {
  scm_lookup_addr_s              addr;
  scm_tag_res_s                  tag_res;
} scu_scc_tag_res_s;

//SCU <---> SCC_TAG_UPT
typedef struct packed {
reg [3:0]                   lup_res;
reg                         need_resp;
reg [`nl2_STB_IDX_BITS-1:0]     stb_id;
 } scu_lup_res_s;

//SCC_TAG_UPT <--> SCU
typedef struct packed {
//reg [2:0]                   snp_resp;
reg [`nl2_STB_IDX_BITS-1:0]     stb_id;
 } scc_snp_resp_s;

//SCU D$ shadow tag
typedef struct packed {
reg  [`nl2_CFG_ADDR_SIZE-1:0]   addr;
reg  [`nl2_STB_IDX_BITS-1:0]    stb_idx;
reg  [`nl2_ARC_DC_ASSOC-1:0]    way;
reg                         valid_we;
reg                         valid;
reg                         domain_we;
reg                         domain;
reg                         moe;
} stag_upt_s;

//SCU D$ shadow tag
typedef struct packed {
reg                         hit;
reg  [`nl2_ARC_DC_ASSOC-1:0]    hit_way;
reg                         moe;
reg                         shared;
reg                         domain;
reg                         from_stb;
reg  [`nl2_STB_IDX_BITS-1:0]    stb_idx;
} stag_lup_s;

//SCU PF shadow tag
typedef struct packed {
reg                         hit; 
reg                         hit_way;
reg                         domain;
reg [`nl2_STB_IDX_BITS-1:0]     stb_id;
 } scu_pf_lup_s;

typedef struct packed {
reg                         odd_even;
reg [`nl2_ARC_PF_INDX_BITS-1:0] set_index;
reg                         way;
reg                         valid;
reg                         domain;
reg [`nl2_ARC_PF_TAG_BITS-1:0]  tag;
 } scu_pf_upt_s;

 //SCU<-->TXC
 


`ifdef CLN_WITH_MULTICAST
typedef enum logic [2:0] {
  CLN_MCAST = 4,
`else
typedef enum logic [1:0] {
`endif
  CLN_SLV   = 0,
  CLN_MST   = 1,
  CLN_BNK   = 2,
  CLN_SCU   = 3
} cln_port_type_s;

typedef struct packed {
reg   [`nl2_CFG_TXC_ADR-1:0] txc_id;
reg   [`nl2_CFG_SLV_ADR-1:0] slv_id;
reg    [`nl2_TXB_PTR_SZ-1:0] addr;
reg  [`nl2_IBP_CMD_DATA_RNG] data_size;
reg [`nl2_CLN_CMD_BURST_RNG] burst_size;
reg                      wrap;
reg                      linepass;
reg                      writeback;
reg                      outer_op;
reg                      merge;
reg                      error;
reg                [2:0] rd_resp;
split_t                  split;
cln_port_type_s          dst_type;

} scu_snp_cmd_s;

typedef struct packed {
reg                      valid;
reg   [`nl2_CFG_SLV_ADR-1:0] slv_id;
reg [`nl2_CFG_ADDR_SIZE-1:0] addr;
} scu_dis_info_s;

typedef struct packed {
  logic   [`nl2_CFG_TXC_ADR-1:0] txc_id;
  logic    [`nl2_TXB_PTR_SZ-1:0] addr;
  logic  [`nl2_IBP_CMD_DATA_RNG] data_size;
  logic [`nl2_CLN_CMD_BURST_RNG] burst_size;
  logic                      amoswap;
  logic                      amoload;
  logic                      outer_op; //indicator to SC
  logic                      wrap;
  logic                      fixed;
  logic                      merge;
  logic                      refill;
  logic                      shared;
  logic                      dirty;
  cln_port_type_s            src_type;
} cln_wchan_cmd_s;

typedef struct packed {
  logic         [`nl2_TXB_PTR_SZ-1:0] addr;
  logic       [`nl2_IBP_CMD_DATA_RNG] data_size;
  logic      [`nl2_CLN_CMD_BURST_RNG] burst_size;
  logic                           wrap;
  logic                           fixed;
  logic                           amoswap;
  logic                           amoload;
  logic                           outer_op; //indicator to SC
  logic                           suppress_last;
  cln_port_type_s                 dst_type;
  logic        [`nl2_CFG_DST_ADR-1:0] dst_id;  
} cln_rchan_cmd_s;

typedef struct packed {
  cln_wchan_cmd_s            wchan;
  logic                      activate_rchan;
  cln_rchan_cmd_s            rchan;
} cln_txb_cmd_s;

`ifdef CLN_HAS_SILICON_DEBUG
typedef struct packed {
  reg                    enable;
  reg [`nl2_CFG_TXC_ADR-1:0] txc_id;
} sdg_txc_s;
`endif

typedef struct packed {
  logic                 valid;                              
  logic           [2:0] rdomid;
} qos_noc_chan_s;

typedef struct packed {
  qos_noc_chan_s    cmd;                              
  qos_noc_chan_s    wr;                              
  qos_noc_chan_s    rd;                              
} qos_noc_txn_s;

typedef struct packed {
  reg   [`nl2_CLN_SRCSYN_SUBCHAN_SIZE-1:0] fw_data;
  logic                                fw_strb;
} fw_subchan_s;

typedef struct packed {
  logic   [`nl2_CLN_SRCSYN_SUBCHAN_SIZE-1:0] payload;
  logic                                  clk_payload;
} fw_srcrcv_s;

endpackage
