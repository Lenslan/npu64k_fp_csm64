// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2014 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2014, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//----------------------------------------------------------------------------
//
// @f:alb_pct
//
// Description:
// @p
//     This module implements the logic used to manage the processing of
//   performance counters
// @e
//
//  This .vpp source file must be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command such as:
//
//   vpp +q +o alb_pct.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"
`include "npuarc_pct_defines.v"

// Set simulation timescale
//
`include "const.def"




//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 }, rst: "rst_a", edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_pct (

  // General input signals
  //
  input                       clk                 ,
  output                      pct_unit_enable     ,
  input                       rst_a               ,
  input                       irq_clk_en_r        ,
  // Fetch Events
  //

  input                       ifu_issue_stall_r   ,
  input                       icm                 ,
  input                       icll                ,
  input                       icoff               ,
  input                       ivic                ,
  input                       ivil                ,
  input                       icwpm               ,
  input                       ifu_brch_mispred_r  ,
  input                       ifu_cond_mispred_r  ,
  input                       ifu_bta_mispred_r   ,
  input                       ifu_missing_pred_r  ,
  input                       ifu_late_br_mispred ,
  input                       ifu_error_branch_r  ,
  input                       ifu_branch_cache_miss,
  input                       ifu_bit_error_r     ,
  input                       icm_stall           ,
 input  [`npuarc_DATA_RANGE]         ar_aux_ecr_r        ,
  //  DMP Events
  //
  input                       dccmbc              , // DCCM bank conlficts             
  input                       dcm                 , // Data Cache miss
  input                       dclm                , // Data Cache load miss
  input                       dcsm                , // Data Cache store miss
  input                       dcpm                , // Data Cache predictor miss
  input                       dcbc                , // Data Cache bank conflicts
  input                       ivdc                , // Invalidate data cache
  input                       ivdl                , // Invalidate data line
  input                       flsh                , // Flush entire d-cache
  input                       fldl                , // Flush data line
  input                       dc_bdcmstall        , // miss queue full
  input                       dep_bdcmstall    , // dependency on ld miss

  //  DA Events
  //
  input                       da_eslot_stall      ,
  input                       da_uop_stall        ,
  input                       db_active_r         ,
  input                       x1_dslot_stall      ,
  input                       dc1_stall           ,
  input                       dc2_stall           ,
  input                       dc4_stall_r         ,
  input                       wa_restart_r        ,
  input                       bzolcnt             ,

  input                       bauxflsh            ,


  //  DA Events
  //

  //  SA Events
  //
  input                       sa_flag_stall       ,
  input                       sa_stall_r15        ,
  
  input                       sa_stall_r1         ,
  input                       sa_acc_raw   ,    // 

  //  X1 Events
  //

  //  X2 Events
  //

  //  X3 Events
  //


  //  Commit Events
  //
  input                       ca_pass             ,

  input                       ca_normal_evt       ,
  input                       ca_sleep_evt        ,
  input                       ca_lp_lpcc_evt         ,
  input                       ca_br_taken         ,

  input                       ca_jump_r           ,
  input                       ca_bcc_r            ,
  input                       ca_zol_branch       , 
  input                       ca_brcc_bbit_r      ,
  input                       ca_dslot_r          ,

  input                       ca_load_r           ,
  input                       ca_store_r          ,
  input                       dc4_pref_r          ,
  input [`npuarc_DMP_TARGET_RANGE]   ca_target_r         ,
  input                       ca_locked_r         ,

  input                       ca_lr_op_r          ,
  input                       ca_sr_op_r          ,

  input                       ca_trap_op_r        ,
  input                       ca_byte_size_r      ,

  input                       ca_has_limm_r       ,
  input                       ca_is_16bit_r       ,
  input                       ca_br_jmp_op        ,  // Insn. is BL, BLcc, 
                                                     // BL_S, JL, JL_S, JLcc
  input     [4:0]             ca_q_field_r        ,
  input                       ca_hit_lp_end       ,
  input                       ca_acc_waw   ,    // 

// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ:  unused port range
  input  [`npuarc_INTEVT_RANGE]      excpn_evts          ,
// leda NTL_CON37 on  
  // Architectural Signals
  input      [`npuarc_DATA_RANGE]    ar_aux_debug_r      ,
  input      [`npuarc_DATA_RANGE]    ar_aux_status32_r   ,
  input      [`npuarc_DATA_RANGE]    ar_aux_irq_act_r    ,
// leda NTL_CON13C on
  // leda NTL_CON13C off
  // LMD: non driving port
  // LJ:  Not all bits used
  input [`npuarc_INTEVT_RANGE]       int_evts            ,
  // leda NTL_CON13C on


  input      [`npuarc_DATA_RANGE]    ar_aux_lp_start_r   ,
  input      [`npuarc_DATA_RANGE]    ar_aux_lp_end_r     ,
  input      [`npuarc_PC_RANGE]      ar_pc_r             ,

  output reg  [`npuarc_IRQM_RANGE]   pct_int_overflow_r  ,


  // Aux Write Interface
  input                       aux_pct_wen_r       ,
  input      [5:0]            aux_pct_waddr_r     ,
  input      [`npuarc_DATA_RANGE]    wa_sr_data_r        ,

  input                       aux_pct_active      ,
  input                       aux_pct_ren_r       ,
  input      [5:0]            aux_pct_raddr_r     ,
// spyglass disable_block W240
// SMD: Input 'aux_read' declared but not read
// SJ: Standard aux interface 
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  standard aux interface
  input                       aux_read            ,
// leda NTL_CON13C on
// spyglass enable_block W240
  input                       aux_write           ,
  output reg [`npuarc_DATA_RANGE]    pct_aux_rdata       ,
  output reg                  pct_aux_illegal     ,
  output reg                  pct_aux_k_rd        ,
  output reg                  pct_aux_k_wr        ,
  output reg                  pct_aux_unimpl      ,
  output reg                  pct_aux_serial_sr   ,
  output reg                  pct_aux_strict_sr   ,
  input                       sync_dsync_dmb_stall    // added for bsyncstall         
);

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Declare the payload signals.                                           //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg     [2:0] p_vbslot  ;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Declare the countable event signals.                                   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg     i_never   ; // always false
reg     i_always  ; // Cycles: always true, whether or not running
reg     i_iall    ; // Instrs: any instruction committed
reg     i_isleep  ; // Instrs: Sleep
reg     i_ijmp    ; // Instrs: Jump/Branch
reg     i_ijmpc   ; // Instrs: Jump conditional taken
reg     i_ijmpu   ; // Instrs: Jump unconditional taken
reg     i_ijmpd   ; // Instrs: Jump with delay slot
reg     i_ijmptak ; // Instrs: Jump taken
reg     i_icall   ; // Instrs: linked subroutine call
reg     i_ilr     ; // Instrs: Auxiliary Register Read (LR)
reg     i_isr     ; // Instrs: Auxiliary Register Write (SR)
reg     i_ilp     ; // Instrs: Loop
reg     i_ilpend  ; // Instrs: Loop End
reg     i_ilpin   ; // Instrs: inside a loop
reg     i_i2byte  ; // Instrs: 16-bit
reg     i_i4byte  ; // Instrs: 32-bit
reg     i_i2lbyte ; // Instrs: 16-bit with LIMM
reg     i_i4lbyte ; // Instrs: 32-bit with LIMM
reg     i_imemrd  ; // Instrs: Memory Read
reg     i_imemwr  ; // Instrs: Memory Write
reg     i_imemrdc ; // Instrs: Memory Read, cached
reg     i_imemwrc ; // Instrs: Memory Write, cached
reg     i_itrap   ; // Instrs: TRAP
reg     i_iswi    ; // Instrs: SWI
reg     i_illock  ; // Instrs: Load Locked
reg     i_iscond  ; // Instrs: Store Conditional
reg     i_ialljmp ; // Instrs: All Jump/Branch including ZOL branch
reg     i_ivec    ; // Instrs: All committed super instruction
reg     i_ivgather; // Instrs: count vvld with vector register as addr
reg     i_ivscatt ; // Instrs: count vvst with vector register as addr
reg     i_vgathbc ; // Instrs: bank conflict caused by ivec_gather
reg     i_vscatbc ; // Instrs: bank conflict caused by ivec_scatter
reg     i_vstall  ; // Bubbles: vector unit stall
reg     i_vbslot  ; // Instrs: All committed slots in a super instruction
reg     i_bwpcflt ; // Bubbles: Ca-stage stalls by RF write confilict
reg     i_bstall  ; // Bubbles: All stalls
reg     i_bflush  ; // Bubbles: All flushes
reg     i_bdebug  ; // Bubbles: Debug transaction
reg     i_bissue  ; // Bubbles: Instruction Issue stall
reg     i_beslot  ; // Bubbles: eSlot Instruction Fetch stall
reg     i_bdslot  ; // Bubbles: dSlot Instruction Fetch stall
reg     i_bflgstal; // Bubbles: Flag Dependency stall
reg     i_berrbrch; // Bubbles: Error Branch stall
reg     i_buopstal; // Bubbles: Micro-op stall
reg     i_brgbank ; // Bubbles: Bank Swap stall
reg     i_bagustl ; // Bubbles: Address Gen stall
reg     i_baccstal; // Bubbles: Accumulator stall
reg     i_bzolcnt ; // Bubbles: ZOL dependency stall
reg     i_bdata64 ; // Bubbles: 64-bit data stall
reg     i_bdcstall; // Bubbles: DMP stall
reg     i_bauxflsh; // Bubbles: Auxiliary Flush
reg     i_bfirqex ; // Bubbles: Interrupt or Exception taken
reg     i_etaken  ; // Event: Exception taken
reg     i_qtaken  ; // Event: Interrupt taken
reg     i_icm     ; // Event: Instruction cache miss
reg     i_icll    ; // Event: Instruction cache line load
reg     i_icoff   ; // Event: Instruction cache disabled
reg     i_ivic    ; // Event: Instruction cache invalidate
reg     i_ivil    ; // Event: Instruction cache invalidate line
reg     i_icwpm   ; // Event: Instruction cache Way Prediction Miss
reg     i_dcm     ; // Event: Data cache miss
reg     i_dclm    ; // Event: Data cache load miss
reg     i_dcsm    ; // Event: Data cache store miss
reg     i_dcpm    ; // Event: Data cache predictor miss
reg     i_dcbc    ; // Event: Data cache/dccm bank conflicts
reg     i_fldc    ; // Event: Data cache flush
reg     i_fldl    ; // Event: Data cache flush line
reg     i_ivdc    ; // Event: Data cache invalidate
reg     i_ivdl    ; // Event: Data cache invalidate line
reg     i_bpmp    ; // Event: mispredict
reg     i_bplate  ; // Event: late mispredict
reg     i_bpcmp   ; // Event: ifu_cond_mispredict
reg     i_bpbtamp ; // Event: ifu_bta_mispredict
reg     i_bpsubrt ; // Event: ifu_sub_return
reg     i_bperrbr ; // Event: ifu_error_branch
reg     i_bpbcm   ; // Event: ifu_bc_miss
reg     i_mecc1   ; // Event: ifu_bit_error
reg     i_eitlb   ; // Event: Instruction TLB miss taken
reg     i_edtlb   ; // Event: Data TLB miss taken
reg     i_evinst  ; // Event: Vector instruction committed
reg     i_ivgath  ; // Event: Vector gather instruction committed
reg     i_ivscat  ; // Event: Vector scatter instruction committed
reg     i_bvgath  ; // Event: Vector gather instruction committed
reg     i_bvscat  ; // Event: Vector scatter instruction committed
reg     i_ccdc2cm ; // Event: Coherency cache-to-cache transfer
reg     i_ccserial; // Event: Coherency serialize
reg     i_ccupgrad; // Event: Coherency cache upgrade
reg     i_ccresps ; // Event: Coherency non-null response
reg     i_dcstgrad; // Event: St instr commit when store data not ready
reg     i_dcldfwd ; // Event: ld in DC3 is stalled
reg     i_crun    ; // Cycles: CPU is running
reg     i_cruni   ; // Cycles: CPU is running with interrupts enabled
reg     i_cdualiss; // Event: IFU issues two instructions
reg     i_cdualco ; // Event: Two instructions committed
reg     i_uflag0  ; // Cycles: User flag 0 enabled
reg     i_uflag1  ; // Cycles: User flag 1 enabled
reg     i_uflag2  ; // Cycles: User flag 2 enabled
reg     i_uflag3  ; // Cycles: User flag 3 enabled
reg     i_uflag4  ; // Cycles: User flag 4 enabled
reg     i_uflag5  ; // Cycles: User flag 5 enabled
reg     i_uflag6  ; // Cycles: User flag 6 enabled
reg     i_uflag7  ; // Cycles: User flag 7 enabled
reg     i_uflag8  ; // Cycles: User flag 8 enabled
reg     i_uflag9  ; // Cycles: User flag 9 enabled
reg     i_uflag10 ; // Cycles: User flag 10 enabled
reg     i_uflag11 ; // Cycles: User flag 11 enabled
reg     i_uflag12 ; // Cycles: User flag 12 enabled
reg     i_uflag13 ; // Cycles: User flag 13 enabled
reg     i_uflag14 ; // Cycles: User flag 14 enabled
reg     i_uflag15 ; // Cycles: User flag 15 enabled
reg     i_uflag16 ; // Cycles: User flag 16 enabled
reg     i_uflag17 ; // Cycles: User flag 17 enabled
reg     i_uflag18 ; // Cycles: User flag 18 enabled
reg     i_uflag19 ; // Cycles: User flag 19 enabled
reg     i_uflag20 ; // Cycles: User flag 20 enabled
reg     i_uflag21 ; // Cycles: User flag 21 enabled
reg     i_uflag22 ; // Cycles: User flag 22 enabled
reg     i_uflag23 ; // Cycles: User flag 23 enabled
reg     i_uflag24 ; // Cycles: User flag 24 enabled
reg     i_uflag25 ; // Cycles: User flag 25 enabled
reg     i_uflag26 ; // Cycles: User flag 26 enabled
reg     i_uflag27 ; // Cycles: User flag 27 enabled
reg     i_uflag28 ; // Cycles: User flag 28 enabled
reg     i_uflag29 ; // Cycles: User flag 29 enabled
reg     i_uflag30 ; // Cycles: User flag 30 enabled
reg     i_uflag31 ; // Cycles: User flag 31 enabled

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Declare each bit of the input pipeline register.                       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg                           s_ca_normal_evt_r   ;
reg                           s_br_taken_r        ;

reg                           s_ilp_r             ;
reg                           s_ilpin_r           ;
reg                           s_ilpend_r          ;

//reg                           s_taken_r           ;
reg                           s_isleep_r          ;
reg                           s_ialljmp_r         ;
reg                           s_ijmp_r            ;
reg                           s_ca_jump_r         ;
reg                           s_ca_bcc_r          ;
reg                           s_ca_brcc_bbit_r    ;
reg                           s_cond_r            ;
reg                           s_icall_r           ;
reg                           s_imemrd_r          ;
reg                           s_imemwr_r          ;
reg                           s_imemrdc_r         ;
reg                           s_imemwrc_r         ;
reg                           s_locked_r          ;
reg                           s_dslot_r           ;

reg                           s_ilr_r             ;
reg                           s_isr_r             ;

reg                           s_iswi_r            ;
reg                           s_itrap_r           ;

reg                           s_i2byte_r          ;
reg                           s_i2lbyte_r         ;
reg                           s_i4byte_r          ;
reg                           s_i4lbyte_r         ;
reg                           s_etaken_r          ;
reg                           s_qtaken_r          ;

reg                           s_crun_r            ;
reg                           s_cruni_r           ;
//reg                           s_cuops_r           ;
    
reg                           s_bissue_r          ;

reg                           s_icm_r             ;
reg                           s_icll_r            ;
reg                           s_icoff_r           ;
reg                           s_ivic_r            ;
reg                           s_ivil_r            ;
reg                           s_icwpm_r           ;
reg                           s_dcm_r             ;
reg                           s_dclm_r            ;
reg                           s_dcsm_r            ;
reg                           s_dcpm_r            ;
reg                           s_fldc_r            ;
reg                           s_ivdl_r            ;
reg                           s_fldl_r            ;
reg                           s_ivdc_r            ;
reg                           s_bdcmstall_r       ;
reg                           s_dcbc_r            ;

reg                           s_bpmp_r            ;
reg                           s_bplate_r          ;
reg                           s_bpcmp_r           ;
reg                           s_bpbtamp_r         ;
reg                           s_bpsubrt_r         ;
reg                           s_bperrbr_r         ;
reg                           s_bpbcm_r           ;
reg                           s_bicmstall_r          ;
reg                           s_bsyncstall_r       ;
reg                           s_mecc1_r           ;
reg                           s_bflush_r          ;
reg                           s_eitlb_r           ;
reg                           s_edtlb_r           ;


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Declare the qualified signals for monitoring. These signals will be    //
// cleared by a downstream kill or stall signal if required.              //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg                           q_ca_normal_evt     ;

reg                           q_itrap             ;
reg                           q_ilp               ;
reg                           q_ilpin             ;

reg                           q_isleep            ;
reg                           q_ialljmp           ;
reg                           q_ijmp              ;
reg                           q_ijmpc             ;
reg                           q_ijmpu             ;
reg                           q_ijmpd             ;
reg                           q_ijmptak           ;
reg                           q_icall             ;
reg                           q_imemrd            ;
reg                           q_imemwr            ;
reg                           q_imemrdc           ;
reg                           q_imemwrc           ;
reg                           q_ilr               ;
reg                           q_isr               ;
reg                           q_iswi              ;
reg                           q_ilpend            ;
reg                           q_i2byte            ;
reg                           q_i2lbyte           ;
reg                           q_i4byte            ;
reg                           q_i4lbyte           ;
reg                           q_etaken            ;
reg                           q_qtaken            ;
reg                           q_illock            ;
reg                           q_iscond            ;

reg                           q_crun              ;
reg                           q_cruni             ;

reg                           q_bstall            ;
reg                           q_bflush            ;
reg                           q_bissue            ;
reg                           q_bdebug            ;
reg                           q_beslot            ;
reg                           q_bdslot            ;
reg                           q_bflgstal          ;
reg                           q_berrbrch          ;
reg                           q_buopstal          ;
reg                           q_brgbank           ;
reg                           q_bagustl           ;
reg                           q_baccstal          ;
reg                           q_bzolcnt           ;
reg                           q_bdata64           ;
reg                           q_bdcstall          ;
reg                           q_bauxflsh          ;
reg                           q_bfirqex           ;

reg                           q_icm               ;
reg                           q_icll              ;
reg                           q_icoff             ;
reg                           q_ivic              ;
reg                           q_ivil              ;
reg                           q_icwpm             ;

  ////////// PCT condtions for cache coherency unit   ////////////////////////
reg                           q_ccdc2cm           ;
reg                           q_ccserial          ;
reg                           q_ccupgrad          ;
reg                           q_ccresps           ;    

reg                           q_dcm               ;
reg                           q_dclm              ;
reg                           q_dcsm              ;
reg                           q_dcpm              ;
reg                           q_fldc              ;
reg                           q_fldl              ;
reg                           q_ivdc              ;
reg                           q_ivdl              ;
reg                           q_dcbc              ;
reg                           q_bdcmstall         ;

reg                           q_bpmp              ;
reg                           q_bplate            ;
reg                           q_bpcmp             ;
reg                           q_bpbtamp           ;
reg                           q_bpsubrt           ;
reg                           q_bperrbr           ;
reg                           q_bpbcm             ;
reg                           q_mecc1             ;
reg                           q_bicmstall         ;
reg                           q_bsyncstall        ;

reg                           q_eitlb             ;
reg                           q_edtlb             ;

reg                           q_ivec             ;
reg                           q_ivgather         ;
reg                           q_ivscatt          ;
reg                           q_vgathbc          ;  
reg                           q_vscatbc          ;
reg                           q_vstall           ;
reg                           q_vbslot           ;
reg                              q_cdualiss       ;
reg                              q_cdualco        ;
reg                              q_bwpcflt        ;
reg                              q_dcstgrad       ;
reg                              q_dcldfwd        ;  

reg                           debug_instr_commit;

// VPOST OFF
reg     [`npuarc_PCT_EVENTS_RANGE]   all_events_r /* verilator public_flat */; // registered count events 
// VPOST ON

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Declare the CC_<> aux register fields                                  //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg [`npuarc_DATA_RANGE]    cc_index_r                   ;
reg [`npuarc_DATA_RANGE]    cc_index_nxt                 ;
reg                  cc_index_sel                 ;
reg                  cc_index_wen                 ;

reg [63:0]           idx_name                     ; // selected condition name
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  Not used reg in rtl, temporary waived
reg [`npuarc_DATA_RANGE]    pct_countl_r                 ;
reg [`npuarc_DATA_RANGE]    pct_counth_r                 ;
reg [`npuarc_DATA_RANGE]    pct_snapl_r                  ;
reg [`npuarc_DATA_RANGE]    pct_snaph_r                  ;
reg [`npuarc_DATA_RANGE]    pct_config_r                 ;
// leda NTL_CON13A on
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some index bits unused
reg [`npuarc_DATA_RANGE]    pct_control_r                ;
// leda NTL_CON32 on
reg [`npuarc_PCT_IDX_RANGE]    pct_index_r                  ;
reg [`npuarc_DATA_RANGE]    pct_rangel_r                 ;
reg [`npuarc_DATA_RANGE]    pct_rangeh_r                 ;
reg [`npuarc_DATA_RANGE]    pct_uflags_r                 ;
reg [`npuarc_DATA_RANGE]    pct_int_ctrl_r               ;
reg [`npuarc_DATA_RANGE]    pct_int_act_r                ;

reg [`npuarc_DATA_RANGE]    pct_control_nxt              ;
reg [`npuarc_PCT_IDX_RANGE]    pct_index_nxt                ;
reg [`npuarc_DATA_RANGE]    pct_rangel_nxt               ;
reg [`npuarc_DATA_RANGE]    pct_rangeh_nxt               ;
reg [`npuarc_DATA_RANGE]    pct_uflags_nxt               ;
reg [`npuarc_DATA_RANGE]    pct_int_ctrl_nxt             ;
reg [`npuarc_DATA_RANGE]    pct_int_act_nxt              ;

reg             pct_countl_sel                    ;
reg             pct_counth_sel                    ;
reg             pct_config_sel                    ;
reg             pct_control_sel                   ;
reg             pct_index_sel                     ;
reg             pct_rangel_sel                    ;
reg             pct_rangeh_sel                    ;
reg             pct_uflags_sel                    ;
reg             pct_int_cntl_sel                  ;
reg             pct_int_cnth_sel                  ;
reg             pct_int_ctrl_sel                  ;
reg             pct_int_act_sel                   ;

reg             pct_countl_wen                    ;
reg             pct_counth_wen                    ;
reg             pct_config_wen                    ;
reg             pct_control_wen                   ;
reg             pct_index_wen                     ;
reg             pct_rangel_wen                    ;
reg             pct_rangeh_wen                    ;
reg             pct_uflags_wen                    ;
reg             pct_int_cntl_wen                  ;
reg             pct_int_cnth_wen                  ;
reg             pct_int_ctrl_wen                  ;
reg             pct_int_act_wen                   ;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Declare PCT_COUNTL, PCT_COUNTH, PCT_SNAPL, PCT_SNAPH and PCT_CONFIG    //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg                           count_cfg0_en    ;


reg     [47:0]                count0_r         ;
reg     [47:0]                count0_nxt       ;
reg     [2:0]                 count0_payload   ;
reg                           count0_wen       ;
reg                           inc_count0         ;
reg                           countl0_wen      ;
reg                           counth0_wen      ;

reg     [47:0]                snap0_r          ;
reg                           snap0_wen        ;

reg     [`npuarc_DATA_RANGE]         config0_r        ;
reg                           config0_wen      ;

reg     [47:0]                int_cnt0_r       ;
reg     [47:0]                int_cnt0_nxt     ;

reg                           int_cntl0_wen    ;
reg                           int_cnth0_wen    ;
reg                           count_cfg1_en    ;


reg     [47:0]                count1_r         ;
reg     [47:0]                count1_nxt       ;
reg     [2:0]                 count1_payload   ;
reg                           count1_wen       ;
reg                           inc_count1         ;
reg                           countl1_wen      ;
reg                           counth1_wen      ;

reg     [47:0]                snap1_r          ;
reg                           snap1_wen        ;

reg     [`npuarc_DATA_RANGE]         config1_r        ;
reg                           config1_wen      ;

reg     [47:0]                int_cnt1_r       ;
reg     [47:0]                int_cnt1_nxt     ;

reg                           int_cntl1_wen    ;
reg                           int_cnth1_wen    ;
reg                           count_cfg2_en    ;


reg     [47:0]                count2_r         ;
reg     [47:0]                count2_nxt       ;
reg     [2:0]                 count2_payload   ;
reg                           count2_wen       ;
reg                           inc_count2         ;
reg                           countl2_wen      ;
reg                           counth2_wen      ;

reg     [47:0]                snap2_r          ;
reg                           snap2_wen        ;

reg     [`npuarc_DATA_RANGE]         config2_r        ;
reg                           config2_wen      ;

reg     [47:0]                int_cnt2_r       ;
reg     [47:0]                int_cnt2_nxt     ;

reg                           int_cntl2_wen    ;
reg                           int_cnth2_wen    ;
reg                           count_cfg3_en    ;


reg     [47:0]                count3_r         ;
reg     [47:0]                count3_nxt       ;
reg     [2:0]                 count3_payload   ;
reg                           count3_wen       ;
reg                           inc_count3         ;
reg                           countl3_wen      ;
reg                           counth3_wen      ;

reg     [47:0]                snap3_r          ;
reg                           snap3_wen        ;

reg     [`npuarc_DATA_RANGE]         config3_r        ;
reg                           config3_wen      ;

reg     [47:0]                int_cnt3_r       ;
reg     [47:0]                int_cnt3_nxt     ;

reg                           int_cntl3_wen    ;
reg                           int_cnth3_wen    ;
reg                           count_cfg4_en    ;


reg     [47:0]                count4_r         ;
reg     [47:0]                count4_nxt       ;
reg     [2:0]                 count4_payload   ;
reg                           count4_wen       ;
reg                           inc_count4         ;
reg                           countl4_wen      ;
reg                           counth4_wen      ;

reg     [47:0]                snap4_r          ;
reg                           snap4_wen        ;

reg     [`npuarc_DATA_RANGE]         config4_r        ;
reg                           config4_wen      ;

reg     [47:0]                int_cnt4_r       ;
reg     [47:0]                int_cnt4_nxt     ;

reg                           int_cntl4_wen    ;
reg                           int_cnth4_wen    ;
reg                           count_cfg5_en    ;


reg     [47:0]                count5_r         ;
reg     [47:0]                count5_nxt       ;
reg     [2:0]                 count5_payload   ;
reg                           count5_wen       ;
reg                           inc_count5         ;
reg                           countl5_wen      ;
reg                           counth5_wen      ;

reg     [47:0]                snap5_r          ;
reg                           snap5_wen        ;

reg     [`npuarc_DATA_RANGE]         config5_r        ;
reg                           config5_wen      ;

reg     [47:0]                int_cnt5_r       ;
reg     [47:0]                int_cnt5_nxt     ;

reg                           int_cntl5_wen    ;
reg                           int_cnth5_wen    ;
reg                           count_cfg6_en    ;


reg     [47:0]                count6_r         ;
reg     [47:0]                count6_nxt       ;
reg     [2:0]                 count6_payload   ;
reg                           count6_wen       ;
reg                           inc_count6         ;
reg                           countl6_wen      ;
reg                           counth6_wen      ;

reg     [47:0]                snap6_r          ;
reg                           snap6_wen        ;

reg     [`npuarc_DATA_RANGE]         config6_r        ;
reg                           config6_wen      ;

reg     [47:0]                int_cnt6_r       ;
reg     [47:0]                int_cnt6_nxt     ;

reg                           int_cntl6_wen    ;
reg                           int_cnth6_wen    ;
reg                           count_cfg7_en    ;


reg     [47:0]                count7_r         ;
reg     [47:0]                count7_nxt       ;
reg     [2:0]                 count7_payload   ;
reg                           count7_wen       ;
reg                           inc_count7         ;
reg                           countl7_wen      ;
reg                           counth7_wen      ;

reg     [47:0]                snap7_r          ;
reg                           snap7_wen        ;

reg     [`npuarc_DATA_RANGE]         config7_r        ;
reg                           config7_wen      ;

reg     [47:0]                int_cnt7_r       ;
reg     [47:0]                int_cnt7_nxt     ;

reg                           int_cntl7_wen    ;
reg                           int_cnth7_wen    ;

reg     [`npuarc_DATA_RANGE]         set_index           ;
reg     [`npuarc_DATA_RANGE]         clr_index           ;
reg     [4:0]                 si_bits             ;
reg     [4:0]                 ci_bits             ;
reg                           si_cmd              ;
reg                           ci_cmd              ;
reg                           clr_cmd             ;

parameter PCT_SEL_BITS = 5;
parameter PCT_INDEX_0  = 5'd0;
parameter PCT_INDEX_1  = 5'd1;
parameter PCT_INDEX_2  = 5'd2;
parameter PCT_INDEX_3  = 5'd3;
parameter PCT_INDEX_4  = 5'd4;
parameter PCT_INDEX_5  = 5'd5;
parameter PCT_INDEX_6  = 5'd6;
parameter PCT_INDEX_7  = 5'd7;
parameter PCT_INDEX_8  = 5'd8;
parameter PCT_INDEX_9  = 5'd9;
parameter PCT_INDEX_10  = 5'd10;
parameter PCT_INDEX_11  = 5'd11;
parameter PCT_INDEX_12  = 5'd12;
parameter PCT_INDEX_13  = 5'd13;
parameter PCT_INDEX_14  = 5'd14;
parameter PCT_INDEX_15  = 5'd15;
parameter PCT_INDEX_16  = 5'd16;
parameter PCT_INDEX_17  = 5'd17;
parameter PCT_INDEX_18  = 5'd18;
parameter PCT_INDEX_19  = 5'd19;
parameter PCT_INDEX_20  = 5'd20;
parameter PCT_INDEX_21  = 5'd21;
parameter PCT_INDEX_22  = 5'd22;
parameter PCT_INDEX_23  = 5'd23;
parameter PCT_INDEX_24  = 5'd24;
parameter PCT_INDEX_25  = 5'd25;
parameter PCT_INDEX_26  = 5'd26;
parameter PCT_INDEX_27  = 5'd27;
parameter PCT_INDEX_28  = 5'd28;
parameter PCT_INDEX_29  = 5'd29;
parameter PCT_INDEX_30  = 5'd30;
parameter PCT_INDEX_31  = 5'd31;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Declare the selected count and snapshot register signals               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg     [47:0]                idx_count           ; // index-selected COUNT
reg     [47:0]                idx_snap            ; // index-selected SNAP

reg     [`npuarc_DATA_RANGE]         idx_config          ; // index-selected CONFIG
reg     [47:0]                idx_int_cnt         ; // index-selected INT COUNT
reg                           i_range_en          ; // PC - Range Count Enable
reg                           i_global_en         ; // Global Count Enable
reg                           s_global_en         ; // 1 cycle clk delay
reg                           i_uf_en             ; // User Flag Condition enable

// leda NTL_CON12A off
// leda NTL_CON12 off
// LMD: undriven internal net Range
// LJ:  all bits are driven
reg [`npuarc_DATA_RANGE]             int_active_nxt      ;
// leda NTL_CON12A on
// leda NTL_CON12 on

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous logic for selecting aux register values for LR and SR     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : pct_select_PROC

    pct_countl_r   = 32'd0                        ;
    pct_counth_r   = 32'd0                        ;
    pct_snapl_r    = 32'd0                        ;
    pct_snaph_r    = 32'd0                        ;
    pct_config_r   = 32'd0                        ;

  case (pct_index_r[`npuarc_PCT_IDX_RANGE])
  `npuarc_PCT_IDX_BITS'd0:
    begin
    pct_countl_r   = count0_r [`npuarc_DATA_RANGE]    ;
    pct_counth_r   = {{16{1'b0}}, count0_r [47:`npuarc_DATA_SIZE]};
    pct_snapl_r    = snap0_r [`npuarc_DATA_RANGE]     ;
    pct_snaph_r    = {{16{1'b0}}, snap0_r [47:`npuarc_DATA_SIZE]};
    pct_config_r   = config0_r                 ;
    end
    
  `npuarc_PCT_IDX_BITS'd1:
    begin
    pct_countl_r   = count1_r [`npuarc_DATA_RANGE]    ;
    pct_counth_r   = {{16{1'b0}}, count1_r [47:`npuarc_DATA_SIZE]};
    pct_snapl_r    = snap1_r [`npuarc_DATA_RANGE]     ;
    pct_snaph_r    = {{16{1'b0}}, snap1_r [47:`npuarc_DATA_SIZE]};
    pct_config_r   = config1_r                 ;
    end
    
  `npuarc_PCT_IDX_BITS'd2:
    begin
    pct_countl_r   = count2_r [`npuarc_DATA_RANGE]    ;
    pct_counth_r   = {{16{1'b0}}, count2_r [47:`npuarc_DATA_SIZE]};
    pct_snapl_r    = snap2_r [`npuarc_DATA_RANGE]     ;
    pct_snaph_r    = {{16{1'b0}}, snap2_r [47:`npuarc_DATA_SIZE]};
    pct_config_r   = config2_r                 ;
    end
    
  `npuarc_PCT_IDX_BITS'd3:
    begin
    pct_countl_r   = count3_r [`npuarc_DATA_RANGE]    ;
    pct_counth_r   = {{16{1'b0}}, count3_r [47:`npuarc_DATA_SIZE]};
    pct_snapl_r    = snap3_r [`npuarc_DATA_RANGE]     ;
    pct_snaph_r    = {{16{1'b0}}, snap3_r [47:`npuarc_DATA_SIZE]};
    pct_config_r   = config3_r                 ;
    end
    
  `npuarc_PCT_IDX_BITS'd4:
    begin
    pct_countl_r   = count4_r [`npuarc_DATA_RANGE]    ;
    pct_counth_r   = {{16{1'b0}}, count4_r [47:`npuarc_DATA_SIZE]};
    pct_snapl_r    = snap4_r [`npuarc_DATA_RANGE]     ;
    pct_snaph_r    = {{16{1'b0}}, snap4_r [47:`npuarc_DATA_SIZE]};
    pct_config_r   = config4_r                 ;
    end
    
  `npuarc_PCT_IDX_BITS'd5:
    begin
    pct_countl_r   = count5_r [`npuarc_DATA_RANGE]    ;
    pct_counth_r   = {{16{1'b0}}, count5_r [47:`npuarc_DATA_SIZE]};
    pct_snapl_r    = snap5_r [`npuarc_DATA_RANGE]     ;
    pct_snaph_r    = {{16{1'b0}}, snap5_r [47:`npuarc_DATA_SIZE]};
    pct_config_r   = config5_r                 ;
    end
    
  `npuarc_PCT_IDX_BITS'd6:
    begin
    pct_countl_r   = count6_r [`npuarc_DATA_RANGE]    ;
    pct_counth_r   = {{16{1'b0}}, count6_r [47:`npuarc_DATA_SIZE]};
    pct_snapl_r    = snap6_r [`npuarc_DATA_RANGE]     ;
    pct_snaph_r    = {{16{1'b0}}, snap6_r [47:`npuarc_DATA_SIZE]};
    pct_config_r   = config6_r                 ;
    end
    
  `npuarc_PCT_IDX_BITS'd7:
    begin
    pct_countl_r   = count7_r [`npuarc_DATA_RANGE]    ;
    pct_counth_r   = {{16{1'b0}}, count7_r [47:`npuarc_DATA_SIZE]};
    pct_snapl_r    = snap7_r [`npuarc_DATA_RANGE]     ;
    pct_snaph_r    = {{16{1'b0}}, snap7_r [47:`npuarc_DATA_SIZE]};
    pct_config_r   = config7_r                 ;
    end
    
  default:
    begin
    pct_countl_r   = 32'd0                        ;
    pct_counth_r   = 32'd0                        ;
    pct_snapl_r    = 32'd0                        ;
    pct_snaph_r    = 32'd0                        ;
    pct_config_r   = 32'd0                        ;
    end
  endcase

end // block : pct_select_PROC

always @*
begin : pct_aux_ren_PROC

  
  //////////////////////////////////////////////////////////////////////////
  // Gate the wa_sr_data_r signals with the SR operation control signal
  // to minimize spurious transitions when not performing SR operations.
  //

  pct_aux_rdata     = `npuarc_DATA_SIZE'd0               ;
  pct_aux_k_rd      = 1'b0                        ;
  pct_aux_k_wr      = 1'b0                        ;
  pct_aux_unimpl    = 1'b1                        ;
  pct_aux_illegal   = 1'b0                        ;
  pct_aux_strict_sr = 1'b0                        ;
  pct_aux_serial_sr = 1'b0                        ;

  case (pct_index_r[`npuarc_PCT_IDX_RANGE])
  `npuarc_PCT_IDX_BITS'd0:
    begin
    idx_count   = count0_r;
    idx_snap    = snap0_r;
    idx_config  = config0_r;
    idx_int_cnt = int_cnt0_r;
    end
    
  `npuarc_PCT_IDX_BITS'd1:
    begin
    idx_count   = count1_r;
    idx_snap    = snap1_r;
    idx_config  = config1_r;
    idx_int_cnt = int_cnt1_r;
    end
    
  `npuarc_PCT_IDX_BITS'd2:
    begin
    idx_count   = count2_r;
    idx_snap    = snap2_r;
    idx_config  = config2_r;
    idx_int_cnt = int_cnt2_r;
    end
    
  `npuarc_PCT_IDX_BITS'd3:
    begin
    idx_count   = count3_r;
    idx_snap    = snap3_r;
    idx_config  = config3_r;
    idx_int_cnt = int_cnt3_r;
    end
    
  `npuarc_PCT_IDX_BITS'd4:
    begin
    idx_count   = count4_r;
    idx_snap    = snap4_r;
    idx_config  = config4_r;
    idx_int_cnt = int_cnt4_r;
    end
    
  `npuarc_PCT_IDX_BITS'd5:
    begin
    idx_count   = count5_r;
    idx_snap    = snap5_r;
    idx_config  = config5_r;
    idx_int_cnt = int_cnt5_r;
    end
    
  `npuarc_PCT_IDX_BITS'd6:
    begin
    idx_count   = count6_r;
    idx_snap    = snap6_r;
    idx_config  = config6_r;
    idx_int_cnt = int_cnt6_r;
    end
    
  `npuarc_PCT_IDX_BITS'd7:
    begin
    idx_count   = count7_r;
    idx_snap    = snap7_r;
    idx_config  = config7_r;
    idx_int_cnt = int_cnt7_r;
    end
    
  default:
    begin
    idx_count   = 48'd0;
    idx_snap    = 48'd0;
    idx_config  = `npuarc_DATA_SIZE'd0;
    idx_int_cnt = 48'd0;
    end
  endcase

  if (aux_pct_ren_r == 1'b1)
  begin
    
    case ({4'h2, 2'b01, aux_pct_raddr_r})

      `npuarc_CC_INDEX_AUX:     // K_RW
      begin

        pct_aux_rdata       = cc_index_r          ;
        pct_aux_unimpl      = 1'b0                ;
        pct_aux_k_rd        = 1'b1                ;
        pct_aux_k_wr        = 1'b1                ;

      end

      `npuarc_CC_NAME0_AUX:     // K_RW
      begin

        pct_aux_rdata       = idx_name[31:0]      ;
        pct_aux_unimpl      = 1'b0                ;
        pct_aux_k_rd        = 1'b1                ;
        pct_aux_illegal     = aux_write           ;

      end

      `npuarc_CC_NAME1_AUX:     // K_RW
      begin

        pct_aux_rdata       = idx_name[63:32]     ;
        pct_aux_unimpl      = 1'b0                ;
        pct_aux_k_rd        = 1'b1                ;
        pct_aux_illegal     = aux_write           ;

      end

      `npuarc_PCT_COUNTL_AUX:     // K_RW
      begin

        pct_aux_rdata       = idx_count [`npuarc_DATA_RANGE];
        pct_aux_unimpl      = 1'b0                ;
        pct_aux_k_rd        = 1'b1                ;

      end

      `npuarc_PCT_COUNTH_AUX:     // K_RW
      begin

        pct_aux_rdata       = {{(`npuarc_DATA_MSB-15){1'b0}}
                            , idx_count [`npuarc_DATA_MSB+16:`npuarc_DATA_MSB+1]}
                            ;
        pct_aux_unimpl      = 1'b0                ;
        pct_aux_k_rd        = 1'b1                ;

      end

      `npuarc_PCT_SNAPL_AUX:     // K_RW
      begin

        pct_aux_rdata       = idx_snap [`npuarc_DATA_RANGE];
        pct_aux_unimpl      = 1'b0                ;
        pct_aux_k_rd        = 1'b1                ;

      end

      `npuarc_PCT_SNAPH_AUX:     // K_RW
      begin

        pct_aux_rdata       =  {{(`npuarc_DATA_MSB-15){1'b0}}
                            , idx_snap [`npuarc_DATA_MSB+16:`npuarc_DATA_MSB+1]}
                            ;
        pct_aux_unimpl      = 1'b0                ;
        pct_aux_k_rd        = 1'b1                ;

      end

      `npuarc_PCT_CONFIG_AUX:     // K_RW
      begin

        pct_aux_rdata       = idx_config;
        pct_aux_unimpl      = 1'b0;
        pct_aux_k_rd        = 1'b1;
        pct_aux_k_wr        = 1'b1;

      end

      `npuarc_PCT_CONTROL_AUX:     // K_RW
      begin

        pct_aux_rdata       = pct_control_r;
        pct_aux_unimpl      = 1'b0;
        pct_aux_k_rd        = 1'b1;
        pct_aux_k_wr        = 1'b1;

      end

      `npuarc_PCT_INDEX_AUX:     // K_RW
      begin

        pct_aux_rdata       = `npuarc_DATA_SIZE'd0               ;
        pct_aux_rdata       = {{(`npuarc_DATA_SIZE-`npuarc_PCT_IDX_BITS){1'b0}}, pct_index_r [`npuarc_PCT_IDX_RANGE]};
        pct_aux_unimpl      = 1'b0;
        pct_aux_k_rd        = 1'b1;
        pct_aux_k_wr        = 1'b1;
      end

      `npuarc_PCT_RANGEL_AUX:     // K_RW
      begin

        pct_aux_rdata       = pct_rangel_r;
        pct_aux_unimpl      = 1'b0;
        pct_aux_k_rd        = 1'b1;
        pct_aux_k_wr        = 1'b1;

      end

      `npuarc_PCT_RANGEH_AUX:     // K_RW
      begin

        pct_aux_rdata       = pct_rangeh_r;
        pct_aux_unimpl      = 1'b0;
        pct_aux_k_rd        = 1'b1;
        pct_aux_k_wr        = 1'b1;

      end

      `npuarc_PCT_UFLAGS_AUX:     // K_RW
      begin

        pct_aux_rdata       = pct_uflags_r;
        pct_aux_unimpl      = 1'b0;
        pct_aux_k_rd        = 1'b1;
        pct_aux_k_wr        = 1'b1;

      end

      `npuarc_PCT_INT_CNTL_AUX:     // K_RW
      begin

        pct_aux_rdata       = idx_int_cnt [`npuarc_DATA_RANGE];
        pct_aux_unimpl      = 1'b0;
        pct_aux_k_rd        = 1'b1;

      end

      `npuarc_PCT_INT_CNTH_AUX:     // K_RW
      begin

        pct_aux_rdata       = {{(`npuarc_DATA_MSB-15){1'b0}}
                            , idx_int_cnt [`npuarc_DATA_MSB+16:`npuarc_DATA_MSB+1]}
                            ;
        pct_aux_unimpl      = 1'b0;
        pct_aux_k_rd        = 1'b1;

      end

      `npuarc_PCT_INT_CTRL_AUX:     // K_RW
      begin

        pct_aux_rdata       = pct_int_ctrl_r               ;
        pct_aux_unimpl      = 1'b0                         ;
        pct_aux_k_rd        = 1'b1                         ;

      end

      `npuarc_PCT_INT_ACT_AUX:     // K_RW
      begin

        pct_aux_rdata       = pct_int_act_r                ;
        pct_aux_unimpl      = 1'b0                         ;
        pct_aux_k_rd        = 1'b1                         ;

      end

      default:
        // aux_pct_raddr_r is not implemented in this module
        //
        pct_aux_unimpl  = 1'b1;
        
    endcase
  end
end // block : pct_aux_ren_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous logic for selecting countable condition names             //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : cc_name_PROC

  idx_name = 64'd0;
  
  case (cc_index_r[`npuarc_PCT_CONFIG_RANGE])
  `npuarc_PCT_CONFIG_BITS'd0: idx_name = 64'h00000072_6576656e; // never   
  `npuarc_PCT_CONFIG_BITS'd1: idx_name = 64'h00007379_61776c61; // always  
  `npuarc_PCT_CONFIG_BITS'd2: idx_name = 64'h00000000_6c6c6169; // iall    
  `npuarc_PCT_CONFIG_BITS'd3: idx_name = 64'h00007065_656c7369; // isleep  
  `npuarc_PCT_CONFIG_BITS'd4: idx_name = 64'h00000000_706d6a69; // ijmp    
  `npuarc_PCT_CONFIG_BITS'd5: idx_name = 64'h00000063_706d6a69; // ijmpc   
  `npuarc_PCT_CONFIG_BITS'd6: idx_name = 64'h00000075_706d6a69; // ijmpu   
  `npuarc_PCT_CONFIG_BITS'd7: idx_name = 64'h00000064_706d6a69; // ijmpd   
  `npuarc_PCT_CONFIG_BITS'd8: idx_name = 64'h006b6174_706d6a69; // ijmptak 
  `npuarc_PCT_CONFIG_BITS'd9: idx_name = 64'h0000006c_6c616369; // icall   
  `npuarc_PCT_CONFIG_BITS'd10: idx_name = 64'h00000000_00726c69; // ilr     
  `npuarc_PCT_CONFIG_BITS'd11: idx_name = 64'h00000000_00727369; // isr     
  `npuarc_PCT_CONFIG_BITS'd12: idx_name = 64'h00000000_00706c69; // ilp     
  `npuarc_PCT_CONFIG_BITS'd13: idx_name = 64'h0000646e_65706c69; // ilpend  
  `npuarc_PCT_CONFIG_BITS'd14: idx_name = 64'h0000006e_69706c69; // ilpin   
  `npuarc_PCT_CONFIG_BITS'd15: idx_name = 64'h00006574_79623269; // i2byte  
  `npuarc_PCT_CONFIG_BITS'd16: idx_name = 64'h00006574_79623469; // i4byte  
  `npuarc_PCT_CONFIG_BITS'd17: idx_name = 64'h00657479_626c3269; // i2lbyte 
  `npuarc_PCT_CONFIG_BITS'd18: idx_name = 64'h00657479_626c3469; // i4lbyte 
  `npuarc_PCT_CONFIG_BITS'd19: idx_name = 64'h00006472_6d656d69; // imemrd  
  `npuarc_PCT_CONFIG_BITS'd20: idx_name = 64'h00007277_6d656d69; // imemwr  
  `npuarc_PCT_CONFIG_BITS'd21: idx_name = 64'h00636472_6d656d69; // imemrdc 
  `npuarc_PCT_CONFIG_BITS'd22: idx_name = 64'h00637277_6d656d69; // imemwrc 
  `npuarc_PCT_CONFIG_BITS'd23: idx_name = 64'h00000070_61727469; // itrap   
  `npuarc_PCT_CONFIG_BITS'd24: idx_name = 64'h00000000_69777369; // iswi    
  `npuarc_PCT_CONFIG_BITS'd25: idx_name = 64'h00006b63_6f6c6c69; // illock  
  `npuarc_PCT_CONFIG_BITS'd26: idx_name = 64'h0000646e_6f637369; // iscond  
  `npuarc_PCT_CONFIG_BITS'd27: idx_name = 64'h00706d6a_6c6c6169; // ialljmp 
  `npuarc_PCT_CONFIG_BITS'd28: idx_name = 64'h00000000_63657669; // ivec    
  `npuarc_PCT_CONFIG_BITS'd29: idx_name = 64'h72656874_61677669; // ivgather
  `npuarc_PCT_CONFIG_BITS'd30: idx_name = 64'h00747461_63737669; // ivscatt 
  `npuarc_PCT_CONFIG_BITS'd31: idx_name = 64'h00636268_74616776; // vgathbc 
  `npuarc_PCT_CONFIG_BITS'd32: idx_name = 64'h00636274_61637376; // vscatbc 
  `npuarc_PCT_CONFIG_BITS'd33: idx_name = 64'h00006c6c_61747376; // vstall  
  `npuarc_PCT_CONFIG_BITS'd34: idx_name = 64'h0000746f_6c736276; // vbslot  
  `npuarc_PCT_CONFIG_BITS'd35: idx_name = 64'h00746c66_63707762; // bwpcflt 
  `npuarc_PCT_CONFIG_BITS'd36: idx_name = 64'h00006c6c_61747362; // bstall  
  `npuarc_PCT_CONFIG_BITS'd37: idx_name = 64'h00006873_756c6662; // bflush  
  `npuarc_PCT_CONFIG_BITS'd38: idx_name = 64'h00006775_62656462; // bdebug  
  `npuarc_PCT_CONFIG_BITS'd39: idx_name = 64'h00006575_73736962; // bissue  
  `npuarc_PCT_CONFIG_BITS'd40: idx_name = 64'h0000746f_6c736562; // beslot  
  `npuarc_PCT_CONFIG_BITS'd41: idx_name = 64'h0000746f_6c736462; // bdslot  
  `npuarc_PCT_CONFIG_BITS'd42: idx_name = 64'h6c617473_676c6662; // bflgstal
  `npuarc_PCT_CONFIG_BITS'd43: idx_name = 64'h68637262_72726562; // berrbrch
  `npuarc_PCT_CONFIG_BITS'd44: idx_name = 64'h6c617473_706f7562; // buopstal
  `npuarc_PCT_CONFIG_BITS'd45: idx_name = 64'h006b6e61_62677262; // brgbank 
  `npuarc_PCT_CONFIG_BITS'd46: idx_name = 64'h006c7473_75676162; // bagustl 
  `npuarc_PCT_CONFIG_BITS'd47: idx_name = 64'h6c617473_63636162; // baccstal
  `npuarc_PCT_CONFIG_BITS'd48: idx_name = 64'h00746e63_6c6f7a62; // bzolcnt 
  `npuarc_PCT_CONFIG_BITS'd49: idx_name = 64'h00343661_74616462; // bdata64 
  `npuarc_PCT_CONFIG_BITS'd50: idx_name = 64'h6c6c6174_73636462; // bdcstall
  `npuarc_PCT_CONFIG_BITS'd51: idx_name = 64'h68736c66_78756162; // bauxflsh
  `npuarc_PCT_CONFIG_BITS'd52: idx_name = 64'h00786571_72696662; // bfirqex 
  `npuarc_PCT_CONFIG_BITS'd53: idx_name = 64'h00006e65_6b617465; // etaken  
  `npuarc_PCT_CONFIG_BITS'd54: idx_name = 64'h00006e65_6b617471; // qtaken  
  `npuarc_PCT_CONFIG_BITS'd55: idx_name = 64'h00000000_006d6369; // icm     
  `npuarc_PCT_CONFIG_BITS'd56: idx_name = 64'h00000000_6c6c6369; // icll    
  `npuarc_PCT_CONFIG_BITS'd57: idx_name = 64'h00000066_666f6369; // icoff   
  `npuarc_PCT_CONFIG_BITS'd58: idx_name = 64'h00000000_63697669; // ivic    
  `npuarc_PCT_CONFIG_BITS'd59: idx_name = 64'h00000000_6c697669; // ivil    
  `npuarc_PCT_CONFIG_BITS'd60: idx_name = 64'h0000006d_70776369; // icwpm   
  `npuarc_PCT_CONFIG_BITS'd61: idx_name = 64'h00000000_006d6364; // dcm     
  `npuarc_PCT_CONFIG_BITS'd62: idx_name = 64'h00000000_6d6c6364; // dclm    
  `npuarc_PCT_CONFIG_BITS'd63: idx_name = 64'h00000000_6d736364; // dcsm    
  `npuarc_PCT_CONFIG_BITS'd64: idx_name = 64'h00000000_6d706364; // dcpm    
  `npuarc_PCT_CONFIG_BITS'd65: idx_name = 64'h00000000_63626364; // dcbc    
  `npuarc_PCT_CONFIG_BITS'd66: idx_name = 64'h00000000_63646c66; // fldc    
  `npuarc_PCT_CONFIG_BITS'd67: idx_name = 64'h00000000_6c646c66; // fldl    
  `npuarc_PCT_CONFIG_BITS'd68: idx_name = 64'h00000000_63647669; // ivdc    
  `npuarc_PCT_CONFIG_BITS'd69: idx_name = 64'h00000000_6c647669; // ivdl    
  `npuarc_PCT_CONFIG_BITS'd70: idx_name = 64'h00000000_706d7062; // bpmp    
  `npuarc_PCT_CONFIG_BITS'd71: idx_name = 64'h00006574_616c7062; // bplate  
  `npuarc_PCT_CONFIG_BITS'd72: idx_name = 64'h00000070_6d637062; // bpcmp   
  `npuarc_PCT_CONFIG_BITS'd73: idx_name = 64'h00706d61_74627062; // bpbtamp 
  `npuarc_PCT_CONFIG_BITS'd74: idx_name = 64'h00747262_75737062; // bpsubrt 
  `npuarc_PCT_CONFIG_BITS'd75: idx_name = 64'h00726272_72657062; // bperrbr 
  `npuarc_PCT_CONFIG_BITS'd76: idx_name = 64'h0000006d_63627062; // bpbcm   
  `npuarc_PCT_CONFIG_BITS'd77: idx_name = 64'h00000031_6363656d; // mecc1   
  `npuarc_PCT_CONFIG_BITS'd78: idx_name = 64'h00000062_6c746965; // eitlb   
  `npuarc_PCT_CONFIG_BITS'd79: idx_name = 64'h00000062_6c746465; // edtlb   
  `npuarc_PCT_CONFIG_BITS'd80: idx_name = 64'h00007473_6e697665; // evinst  
  `npuarc_PCT_CONFIG_BITS'd81: idx_name = 64'h00006874_61677669; // ivgath  
  `npuarc_PCT_CONFIG_BITS'd82: idx_name = 64'h00007461_63737669; // ivscat  
  `npuarc_PCT_CONFIG_BITS'd83: idx_name = 64'h00006874_61677662; // bvgath  
  `npuarc_PCT_CONFIG_BITS'd84: idx_name = 64'h00007461_63737662; // bvscat  
  `npuarc_PCT_CONFIG_BITS'd85: idx_name = 64'h006d6332_63646363; // ccdc2cm 
  `npuarc_PCT_CONFIG_BITS'd86: idx_name = 64'h6c616972_65736363; // ccserial
  `npuarc_PCT_CONFIG_BITS'd87: idx_name = 64'h64617267_70756363; // ccupgrad
  `npuarc_PCT_CONFIG_BITS'd88: idx_name = 64'h00737073_65726363; // ccresps 
  `npuarc_PCT_CONFIG_BITS'd89: idx_name = 64'h64617267_74736364; // dcstgrad
  `npuarc_PCT_CONFIG_BITS'd90: idx_name = 64'h00647766_646c6364; // dcldfwd 
  `npuarc_PCT_CONFIG_BITS'd91: idx_name = 64'h00000000_6e757263; // crun    
  `npuarc_PCT_CONFIG_BITS'd92: idx_name = 64'h00000069_6e757263; // cruni   
  `npuarc_PCT_CONFIG_BITS'd93: idx_name = 64'h7373696c_61756463; // cdualiss
  `npuarc_PCT_CONFIG_BITS'd94: idx_name = 64'h006f636c_61756463; // cdualco 
  `npuarc_PCT_CONFIG_BITS'd95: idx_name = 64'h00003067_616c6675; // uflag0  
  `npuarc_PCT_CONFIG_BITS'd96: idx_name = 64'h00003167_616c6675; // uflag1  
  `npuarc_PCT_CONFIG_BITS'd97: idx_name = 64'h00003267_616c6675; // uflag2  
  `npuarc_PCT_CONFIG_BITS'd98: idx_name = 64'h00003367_616c6675; // uflag3  
  `npuarc_PCT_CONFIG_BITS'd99: idx_name = 64'h00003467_616c6675; // uflag4  
  `npuarc_PCT_CONFIG_BITS'd100: idx_name = 64'h00003567_616c6675; // uflag5  
  `npuarc_PCT_CONFIG_BITS'd101: idx_name = 64'h00003667_616c6675; // uflag6  
  `npuarc_PCT_CONFIG_BITS'd102: idx_name = 64'h00003767_616c6675; // uflag7  
  `npuarc_PCT_CONFIG_BITS'd103: idx_name = 64'h00003867_616c6675; // uflag8  
  `npuarc_PCT_CONFIG_BITS'd104: idx_name = 64'h00003967_616c6675; // uflag9  
  `npuarc_PCT_CONFIG_BITS'd105: idx_name = 64'h00303167_616c6675; // uflag10 
  `npuarc_PCT_CONFIG_BITS'd106: idx_name = 64'h00313167_616c6675; // uflag11 
  `npuarc_PCT_CONFIG_BITS'd107: idx_name = 64'h00323167_616c6675; // uflag12 
  `npuarc_PCT_CONFIG_BITS'd108: idx_name = 64'h00333167_616c6675; // uflag13 
  `npuarc_PCT_CONFIG_BITS'd109: idx_name = 64'h00343167_616c6675; // uflag14 
  `npuarc_PCT_CONFIG_BITS'd110: idx_name = 64'h00353167_616c6675; // uflag15 
  `npuarc_PCT_CONFIG_BITS'd111: idx_name = 64'h00363167_616c6675; // uflag16 
  `npuarc_PCT_CONFIG_BITS'd112: idx_name = 64'h00373167_616c6675; // uflag17 
  `npuarc_PCT_CONFIG_BITS'd113: idx_name = 64'h00383167_616c6675; // uflag18 
  `npuarc_PCT_CONFIG_BITS'd114: idx_name = 64'h00393167_616c6675; // uflag19 
  `npuarc_PCT_CONFIG_BITS'd115: idx_name = 64'h00303267_616c6675; // uflag20 
  `npuarc_PCT_CONFIG_BITS'd116: idx_name = 64'h00313267_616c6675; // uflag21 
  `npuarc_PCT_CONFIG_BITS'd117: idx_name = 64'h00323267_616c6675; // uflag22 
  `npuarc_PCT_CONFIG_BITS'd118: idx_name = 64'h00333267_616c6675; // uflag23 
  `npuarc_PCT_CONFIG_BITS'd119: idx_name = 64'h00343267_616c6675; // uflag24 
  `npuarc_PCT_CONFIG_BITS'd120: idx_name = 64'h00353267_616c6675; // uflag25 
  `npuarc_PCT_CONFIG_BITS'd121: idx_name = 64'h00363267_616c6675; // uflag26 
  `npuarc_PCT_CONFIG_BITS'd122: idx_name = 64'h00373267_616c6675; // uflag27 
  `npuarc_PCT_CONFIG_BITS'd123: idx_name = 64'h00383267_616c6675; // uflag28 
  `npuarc_PCT_CONFIG_BITS'd124: idx_name = 64'h00393267_616c6675; // uflag29 
  `npuarc_PCT_CONFIG_BITS'd125: idx_name = 64'h00303367_616c6675; // uflag30 
  `npuarc_PCT_CONFIG_BITS'd126: idx_name = 64'h00313367_616c6675; // uflag31 
// spyglass disable_block W193 
// SMD: empty statements
// SJ:  empty default statements kept
  default: ;
// spyglass enable_block W193
  endcase
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational logic for selecting an SR                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @*
begin : pct_sr_sel_PROC

  cc_index_sel    = 1'b0;
  pct_countl_sel  = 1'b0;
  pct_counth_sel  = 1'b0;
  pct_config_sel  = 1'b0;
  pct_control_sel = 1'b0;
  pct_index_sel   = 1'b0;
  pct_rangel_sel  = 1'b0;
  pct_rangeh_sel  = 1'b0;
  pct_uflags_sel  = 1'b0;
  pct_int_cntl_sel  = 1'b0;
  pct_int_cnth_sel  = 1'b0;
  pct_int_ctrl_sel  = 1'b0;
  pct_int_act_sel   = 1'b0;

  if (aux_pct_wen_r == 1'b1)
  begin
    case ({4'h2, 2'b01, aux_pct_waddr_r})
      `npuarc_CC_INDEX_AUX:   cc_index_sel   = 1'b1;
      `npuarc_PCT_COUNTL_AUX:   pct_countl_sel  = 1'b1;
      `npuarc_PCT_COUNTH_AUX:   pct_counth_sel  = 1'b1;
      `npuarc_PCT_CONFIG_AUX:   pct_config_sel  = 1'b1;
      `npuarc_PCT_CONTROL_AUX:  pct_control_sel = 1'b1;
      `npuarc_PCT_INDEX_AUX:    pct_index_sel   = 1'b1;
      `npuarc_PCT_RANGEL_AUX:   pct_rangel_sel  = 1'b1;
      `npuarc_PCT_RANGEH_AUX:   pct_rangeh_sel  = 1'b1;
      `npuarc_PCT_UFLAGS_AUX:   pct_uflags_sel  = 1'b1;
      `npuarc_PCT_INT_CNTL_AUX:   pct_int_cntl_sel  = 1'b1;
      `npuarc_PCT_INT_CNTH_AUX:   pct_int_cnth_sel  = 1'b1;
      `npuarc_PCT_INT_CTRL_AUX:   pct_int_ctrl_sel  = 1'b1;
      `npuarc_PCT_INT_ACT_AUX :   pct_int_act_sel   = 1'b1;
// spyglass disable_block W193 
// SMD: empty statements
// SJ:  empty default statements kept
    default: ;
// spyglass enable_block W193
    endcase // case (aux_pct_waddr_r)
  end

end // pct_sr_sel_PROC

always @*
begin : pct_aux_wen_PROC

  config0_wen    = 1'b0;
  countl0_wen    = 1'b0;
  counth0_wen    = 1'b0;
  int_cntl0_wen  = 1'b0;
  int_cnth0_wen  = 1'b0;
  config1_wen    = 1'b0;
  countl1_wen    = 1'b0;
  counth1_wen    = 1'b0;
  int_cntl1_wen  = 1'b0;
  int_cnth1_wen  = 1'b0;
  config2_wen    = 1'b0;
  countl2_wen    = 1'b0;
  counth2_wen    = 1'b0;
  int_cntl2_wen  = 1'b0;
  int_cnth2_wen  = 1'b0;
  config3_wen    = 1'b0;
  countl3_wen    = 1'b0;
  counth3_wen    = 1'b0;
  int_cntl3_wen  = 1'b0;
  int_cnth3_wen  = 1'b0;
  config4_wen    = 1'b0;
  countl4_wen    = 1'b0;
  counth4_wen    = 1'b0;
  int_cntl4_wen  = 1'b0;
  int_cnth4_wen  = 1'b0;
  config5_wen    = 1'b0;
  countl5_wen    = 1'b0;
  counth5_wen    = 1'b0;
  int_cntl5_wen  = 1'b0;
  int_cnth5_wen  = 1'b0;
  config6_wen    = 1'b0;
  countl6_wen    = 1'b0;
  counth6_wen    = 1'b0;
  int_cntl6_wen  = 1'b0;
  int_cnth6_wen  = 1'b0;
  config7_wen    = 1'b0;
  countl7_wen    = 1'b0;
  counth7_wen    = 1'b0;
  int_cntl7_wen  = 1'b0;
  int_cnth7_wen  = 1'b0;

      cc_index_wen    = cc_index_sel;
      pct_countl_wen  = pct_countl_sel;
      pct_counth_wen  = pct_counth_sel;
      pct_config_wen  = pct_config_sel;
      pct_control_wen = pct_control_sel;
      pct_index_wen   = pct_index_sel;
      pct_rangel_wen  = pct_rangel_sel;
      pct_rangeh_wen  = pct_rangeh_sel;
      pct_uflags_wen  = pct_uflags_sel;
      pct_int_cntl_wen  = pct_int_cntl_sel;
      pct_int_cnth_wen  = pct_int_cnth_sel;
      pct_int_ctrl_wen  = pct_int_ctrl_sel
                        | pct_int_act_sel 
                        ;
      pct_int_act_wen   = pct_int_act_sel 
                        | (|int_active_nxt[`npuarc_PCT_COUNTERS-1:0])
                        ;

  case (pct_index_r[`npuarc_PCT_IDX_RANGE])
  `npuarc_PCT_IDX_BITS'd0: config0_wen = pct_config_wen;    
  `npuarc_PCT_IDX_BITS'd1: config1_wen = pct_config_wen;    
  `npuarc_PCT_IDX_BITS'd2: config2_wen = pct_config_wen;    
  `npuarc_PCT_IDX_BITS'd3: config3_wen = pct_config_wen;    
  `npuarc_PCT_IDX_BITS'd4: config4_wen = pct_config_wen;    
  `npuarc_PCT_IDX_BITS'd5: config5_wen = pct_config_wen;    
  `npuarc_PCT_IDX_BITS'd6: config6_wen = pct_config_wen;    
  `npuarc_PCT_IDX_BITS'd7: config7_wen = pct_config_wen;    
  endcase

  case (pct_index_r[`npuarc_PCT_IDX_RANGE])
  `npuarc_PCT_IDX_BITS'd0: countl0_wen = pct_countl_wen;
  `npuarc_PCT_IDX_BITS'd1: countl1_wen = pct_countl_wen;
  `npuarc_PCT_IDX_BITS'd2: countl2_wen = pct_countl_wen;
  `npuarc_PCT_IDX_BITS'd3: countl3_wen = pct_countl_wen;
  `npuarc_PCT_IDX_BITS'd4: countl4_wen = pct_countl_wen;
  `npuarc_PCT_IDX_BITS'd5: countl5_wen = pct_countl_wen;
  `npuarc_PCT_IDX_BITS'd6: countl6_wen = pct_countl_wen;
  `npuarc_PCT_IDX_BITS'd7: countl7_wen = pct_countl_wen;
  endcase

  case (pct_index_r[`npuarc_PCT_IDX_RANGE])
  `npuarc_PCT_IDX_BITS'd0: counth0_wen = pct_counth_wen;
  `npuarc_PCT_IDX_BITS'd1: counth1_wen = pct_counth_wen;
  `npuarc_PCT_IDX_BITS'd2: counth2_wen = pct_counth_wen;
  `npuarc_PCT_IDX_BITS'd3: counth3_wen = pct_counth_wen;
  `npuarc_PCT_IDX_BITS'd4: counth4_wen = pct_counth_wen;
  `npuarc_PCT_IDX_BITS'd5: counth5_wen = pct_counth_wen;
  `npuarc_PCT_IDX_BITS'd6: counth6_wen = pct_counth_wen;
  `npuarc_PCT_IDX_BITS'd7: counth7_wen = pct_counth_wen;
  endcase
  case (pct_index_r[`npuarc_PCT_IDX_RANGE])
  `npuarc_PCT_IDX_BITS'd0: int_cntl0_wen = pct_int_cntl_wen;
  `npuarc_PCT_IDX_BITS'd1: int_cntl1_wen = pct_int_cntl_wen;
  `npuarc_PCT_IDX_BITS'd2: int_cntl2_wen = pct_int_cntl_wen;
  `npuarc_PCT_IDX_BITS'd3: int_cntl3_wen = pct_int_cntl_wen;
  `npuarc_PCT_IDX_BITS'd4: int_cntl4_wen = pct_int_cntl_wen;
  `npuarc_PCT_IDX_BITS'd5: int_cntl5_wen = pct_int_cntl_wen;
  `npuarc_PCT_IDX_BITS'd6: int_cntl6_wen = pct_int_cntl_wen;
  `npuarc_PCT_IDX_BITS'd7: int_cntl7_wen = pct_int_cntl_wen;
  endcase

  case (pct_index_r[`npuarc_PCT_IDX_RANGE])
  `npuarc_PCT_IDX_BITS'd0: int_cnth0_wen = pct_int_cnth_wen;
  `npuarc_PCT_IDX_BITS'd1: int_cnth1_wen = pct_int_cnth_wen;
  `npuarc_PCT_IDX_BITS'd2: int_cnth2_wen = pct_int_cnth_wen;
  `npuarc_PCT_IDX_BITS'd3: int_cnth3_wen = pct_int_cnth_wen;
  `npuarc_PCT_IDX_BITS'd4: int_cnth4_wen = pct_int_cnth_wen;
  `npuarc_PCT_IDX_BITS'd5: int_cnth5_wen = pct_int_cnth_wen;
  `npuarc_PCT_IDX_BITS'd6: int_cnth6_wen = pct_int_cnth_wen;
  `npuarc_PCT_IDX_BITS'd7: int_cnth7_wen = pct_int_cnth_wen;
  endcase

end // pct_aux_wen_PROC

always @*
begin : pct_aux_nxt_PROC

    cc_index_nxt = (cc_index_sel == 1'b1)
                   ?  wa_sr_data_r
                   :  cc_index_r
                   ;

    pct_control_nxt = (pct_control_sel == 1'b1)
                   ?  {
                      {17{1'b0}}, 
                       wa_sr_data_r [14:0]     // EN

                      }
                   :  pct_control_r
                   ;

    pct_index_nxt = `npuarc_PCT_IDX_BITS'd0               ;
    pct_index_nxt  =  (pct_index_sel == 1'b1)
                   ?  wa_sr_data_r [`npuarc_PCT_IDX_RANGE]
                   :  pct_index_r [`npuarc_PCT_IDX_RANGE]
                   ;

    pct_rangel_nxt = (pct_rangel_sel == 1'b1)
                   ?  wa_sr_data_r
                   :  pct_rangel_r
                   ;

    pct_rangeh_nxt = (pct_rangeh_sel == 1'b1)
                   ?  wa_sr_data_r
                   :  pct_rangeh_r
                   ;



    pct_int_ctrl_nxt = (pct_int_ctrl_sel == 1'b1)
                   ?  wa_sr_data_r
                   :  (pct_int_act_sel ? ((~wa_sr_data_r) & pct_int_ctrl_r) : pct_int_ctrl_r)
                   ;


    pct_int_act_nxt = (pct_int_act_sel == 1'b1)
                   ?  ((~wa_sr_data_r) & pct_int_act_r)
                   :  (pct_int_act_r | int_active_nxt)
                   ;

end  //   pct_aux_nxt_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous logic to determine the next pct_uflags_r value            //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : uflags_PROC

  set_index = `npuarc_DATA_SIZE'd0;
  clr_index = `npuarc_DATA_SIZE'd0;
  
  si_bits   = wa_sr_data_r[4:0]  & {PCT_SEL_BITS{pct_uflags_sel}};
  ci_bits   = wa_sr_data_r[12:8] & {PCT_SEL_BITS{pct_uflags_sel}};
  
  si_cmd    = wa_sr_data_r[18] & pct_uflags_sel;
  ci_cmd    = wa_sr_data_r[17] & pct_uflags_sel;
  clr_cmd   = wa_sr_data_r[16] & pct_uflags_sel;
 
  case (si_bits)
  PCT_INDEX_0: set_index = {{31{1'b0}}, 1'b1};
  PCT_INDEX_1: set_index = {{30{1'b0}}, 1'b1, {1{1'b0}}};
  PCT_INDEX_2: set_index = {{29{1'b0}}, 1'b1, {2{1'b0}}};
  PCT_INDEX_3: set_index = {{28{1'b0}}, 1'b1, {3{1'b0}}};
  PCT_INDEX_4: set_index = {{27{1'b0}}, 1'b1, {4{1'b0}}};
  PCT_INDEX_5: set_index = {{26{1'b0}}, 1'b1, {5{1'b0}}};
  PCT_INDEX_6: set_index = {{25{1'b0}}, 1'b1, {6{1'b0}}};
  PCT_INDEX_7: set_index = {{24{1'b0}}, 1'b1, {7{1'b0}}};
  PCT_INDEX_8: set_index = {{23{1'b0}}, 1'b1, {8{1'b0}}};
  PCT_INDEX_9: set_index = {{22{1'b0}}, 1'b1, {9{1'b0}}};
  PCT_INDEX_10: set_index = {{21{1'b0}}, 1'b1, {10{1'b0}}};
  PCT_INDEX_11: set_index = {{20{1'b0}}, 1'b1, {11{1'b0}}};
  PCT_INDEX_12: set_index = {{19{1'b0}}, 1'b1, {12{1'b0}}};
  PCT_INDEX_13: set_index = {{18{1'b0}}, 1'b1, {13{1'b0}}};
  PCT_INDEX_14: set_index = {{17{1'b0}}, 1'b1, {14{1'b0}}};
  PCT_INDEX_15: set_index = {{16{1'b0}}, 1'b1, {15{1'b0}}};
  PCT_INDEX_16: set_index = {{15{1'b0}}, 1'b1, {16{1'b0}}};
  PCT_INDEX_17: set_index = {{14{1'b0}}, 1'b1, {17{1'b0}}};
  PCT_INDEX_18: set_index = {{13{1'b0}}, 1'b1, {18{1'b0}}};
  PCT_INDEX_19: set_index = {{12{1'b0}}, 1'b1, {19{1'b0}}};
  PCT_INDEX_20: set_index = {{11{1'b0}}, 1'b1, {20{1'b0}}};
  PCT_INDEX_21: set_index = {{10{1'b0}}, 1'b1, {21{1'b0}}};
  PCT_INDEX_22: set_index = {{9{1'b0}}, 1'b1, {22{1'b0}}};
  PCT_INDEX_23: set_index = {{8{1'b0}}, 1'b1, {23{1'b0}}};
  PCT_INDEX_24: set_index = {{7{1'b0}}, 1'b1, {24{1'b0}}};
  PCT_INDEX_25: set_index = {{6{1'b0}}, 1'b1, {25{1'b0}}};
  PCT_INDEX_26: set_index = {{5{1'b0}}, 1'b1, {26{1'b0}}};
  PCT_INDEX_27: set_index = {{4{1'b0}}, 1'b1, {27{1'b0}}};
  PCT_INDEX_28: set_index = {{3{1'b0}}, 1'b1, {28{1'b0}}};
  PCT_INDEX_29: set_index = {{2{1'b0}}, 1'b1, {29{1'b0}}};
  PCT_INDEX_30: set_index = {{1{1'b0}}, 1'b1, {30{1'b0}}};
  PCT_INDEX_31: set_index = {1'b1, {31{1'b0}}};
  endcase
  
  case (ci_bits)
  PCT_INDEX_0: clr_index = {{31{1'b0}}, 1'b1};
  PCT_INDEX_1: clr_index = {{30{1'b0}}, 1'b1, {1{1'b0}}};
  PCT_INDEX_2: clr_index = {{29{1'b0}}, 1'b1, {2{1'b0}}};
  PCT_INDEX_3: clr_index = {{28{1'b0}}, 1'b1, {3{1'b0}}};
  PCT_INDEX_4: clr_index = {{27{1'b0}}, 1'b1, {4{1'b0}}};
  PCT_INDEX_5: clr_index = {{26{1'b0}}, 1'b1, {5{1'b0}}};
  PCT_INDEX_6: clr_index = {{25{1'b0}}, 1'b1, {6{1'b0}}};
  PCT_INDEX_7: clr_index = {{24{1'b0}}, 1'b1, {7{1'b0}}};
  PCT_INDEX_8: clr_index = {{23{1'b0}}, 1'b1, {8{1'b0}}};
  PCT_INDEX_9: clr_index = {{22{1'b0}}, 1'b1, {9{1'b0}}};
  PCT_INDEX_10: clr_index = {{21{1'b0}}, 1'b1, {10{1'b0}}};
  PCT_INDEX_11: clr_index = {{20{1'b0}}, 1'b1, {11{1'b0}}};
  PCT_INDEX_12: clr_index = {{19{1'b0}}, 1'b1, {12{1'b0}}};
  PCT_INDEX_13: clr_index = {{18{1'b0}}, 1'b1, {13{1'b0}}};
  PCT_INDEX_14: clr_index = {{17{1'b0}}, 1'b1, {14{1'b0}}};
  PCT_INDEX_15: clr_index = {{16{1'b0}}, 1'b1, {15{1'b0}}};
  PCT_INDEX_16: clr_index = {{15{1'b0}}, 1'b1, {16{1'b0}}};
  PCT_INDEX_17: clr_index = {{14{1'b0}}, 1'b1, {17{1'b0}}};
  PCT_INDEX_18: clr_index = {{13{1'b0}}, 1'b1, {18{1'b0}}};
  PCT_INDEX_19: clr_index = {{12{1'b0}}, 1'b1, {19{1'b0}}};
  PCT_INDEX_20: clr_index = {{11{1'b0}}, 1'b1, {20{1'b0}}};
  PCT_INDEX_21: clr_index = {{10{1'b0}}, 1'b1, {21{1'b0}}};
  PCT_INDEX_22: clr_index = {{9{1'b0}}, 1'b1, {22{1'b0}}};
  PCT_INDEX_23: clr_index = {{8{1'b0}}, 1'b1, {23{1'b0}}};
  PCT_INDEX_24: clr_index = {{7{1'b0}}, 1'b1, {24{1'b0}}};
  PCT_INDEX_25: clr_index = {{6{1'b0}}, 1'b1, {25{1'b0}}};
  PCT_INDEX_26: clr_index = {{5{1'b0}}, 1'b1, {26{1'b0}}};
  PCT_INDEX_27: clr_index = {{4{1'b0}}, 1'b1, {27{1'b0}}};
  PCT_INDEX_28: clr_index = {{3{1'b0}}, 1'b1, {28{1'b0}}};
  PCT_INDEX_29: clr_index = {{2{1'b0}}, 1'b1, {29{1'b0}}};
  PCT_INDEX_30: clr_index = {{1{1'b0}}, 1'b1, {30{1'b0}}};
  PCT_INDEX_31: clr_index = {1'b1, {31{1'b0}}};
  endcase
  
  pct_uflags_nxt  = ( set_index 
                    & ({32{(si_cmd & (!clr_cmd))}})
                    )
                  | ( pct_uflags_r 
                    & (~(clr_index & {32{ci_cmd}})) 
                    & {32{~clr_cmd}}
                    )
                  ;

end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous blocks for architectural state updates                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : pct_cc_index_reg_PROC
  if (rst_a == 1'b1)
    cc_index_r    <= `npuarc_DATA_SIZE'd0;
  else if (cc_index_wen)
    cc_index_r    <= cc_index_nxt;
end

always @(posedge clk or posedge rst_a)
begin : pct_control_reg_PROC
  if (rst_a == 1'b1)
    pct_control_r <= `npuarc_DATA_SIZE'd0;
  else if (pct_control_wen)
    pct_control_r <= pct_control_nxt;
end

always @(posedge clk or posedge rst_a)
begin : pct_index_reg_PROC
  if (rst_a == 1'b1)
    pct_index_r   <= `npuarc_PCT_IDX_BITS'd0;
  else if (pct_index_wen)
    pct_index_r   <= pct_index_nxt;
end

always @(posedge clk or posedge rst_a)
begin : pct_rangel_reg_PROC
  if (rst_a == 1'b1)
    pct_rangel_r  <= `npuarc_DATA_SIZE'd0;
  else if (pct_rangel_wen)
    pct_rangel_r  <= pct_rangel_nxt;
end

always @(posedge clk or posedge rst_a)
begin : pct_rangeh_reg_PROC
  if (rst_a == 1'b1)
    pct_rangeh_r  <= `npuarc_DATA_SIZE'd0;
  else if (pct_rangeh_wen)
    pct_rangeh_r  <= pct_rangeh_nxt;
end

always @(posedge clk or posedge rst_a)
begin : pct_uflags_reg_PROC
  if (rst_a == 1'b1)
    pct_uflags_r  <= `npuarc_DATA_SIZE'd0;
  else if (pct_uflags_wen)
    pct_uflags_r  <= pct_uflags_nxt;
end

always @(posedge clk or posedge rst_a)
begin : pct_int_ctrl_reg_PROC
  if (rst_a == 1'b1)
    pct_int_ctrl_r <= `npuarc_DATA_SIZE'd0;
  else if (pct_int_ctrl_wen)
    pct_int_ctrl_r <= pct_int_ctrl_nxt;
end

always @(posedge clk or posedge rst_a)
begin : pct_int_act_reg_PROC
  if (rst_a == 1'b1)
    pct_int_act_r   <= `npuarc_DATA_SIZE'd0;
  else if (pct_int_act_wen)
    pct_int_act_r  <= pct_int_act_nxt ;
end

////////////////////////////////////////////////////////////////////////////
// one more register added for irq of irq_clk_en_r
//
reg pct_int_act_2cycle_r;

always @(posedge clk or posedge rst_a)
begin : pct_int_2cycle_PROC
  if (rst_a == 1'b1)
    pct_int_act_2cycle_r <= 1'b0;
  else if (irq_clk_en_r == 1'b1)
    pct_int_act_2cycle_r <= |pct_int_act_r[`npuarc_PCT_COUNTERS-1:0];
end


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous logic to select each configured signal for counting,      //
// to select the global enable condition according to PCT_CONTROL.EN,     //
// and to enable or disable counting based on the PC address range check. //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : pct_switch_PROC

  i_range_en  =  ({ar_pc_r,1'b0} >= pct_rangel_r)
              && (    ({ar_pc_r, 1'b0} <  pct_rangeh_r)
                  || (pct_rangeh_r == 32'd0)
                 )
              ;

  case (pct_control_r [1:0])
  2'b00: i_uf_en = 1'b0;
  2'b01: i_uf_en = 1'b1;
  2'b10:
    begin 
    case (pct_control_r [5:4]) // {
      2'b00:
        begin
          i_uf_en = ( i_uflag0 ^ pct_control_r [2])
                  & ( i_uflag1 ^ pct_control_r [3])
                  ;
        end
      2'b01:
        begin
          i_uf_en = ( i_uflag0 ^ pct_control_r [2])
                  | ( i_uflag1 ^ pct_control_r [3])
                  ;
        end
      2'b10:
        begin
          i_uf_en = ( i_uflag0 ^ pct_control_r [2])
                  ;
        end
      2'b11:
        begin
          i_uf_en = ( i_uflag1 ^ pct_control_r [3])
                  ;
        end
    endcase // }
    end
  2'b11: 
    begin 
          i_uf_en = 1'b1
                & (~((~ar_aux_status32_r[`npuarc_U_FLAG])            & pct_control_r[6]))
                & (~(  ar_aux_status32_r[`npuarc_U_FLAG]             & pct_control_r[6+1]))
                & (~((~ar_aux_status32_r[`npuarc_AE_FLAG])           & pct_control_r[6+3]))
                & (~(  ar_aux_status32_r[`npuarc_AE_FLAG]            & pct_control_r[6+4]))
                & (~((~|ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & pct_control_r[6+6]))
                & (~(( |ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & pct_control_r[6+7]))
                ;
    end
  default: i_uf_en = 1'b0;
  endcase

  i_global_en = s_global_en; 

    case (config0_r[`npuarc_PCT_CONFIG_RANGE])
    `npuarc_PCT_CONFIG_BITS'd0: inc_count0 = all_events_r[0];
    `npuarc_PCT_CONFIG_BITS'd1: inc_count0 = all_events_r[1];
    `npuarc_PCT_CONFIG_BITS'd2: inc_count0 = all_events_r[2];
    `npuarc_PCT_CONFIG_BITS'd3: inc_count0 = all_events_r[3];
    `npuarc_PCT_CONFIG_BITS'd4: inc_count0 = all_events_r[4];
    `npuarc_PCT_CONFIG_BITS'd5: inc_count0 = all_events_r[5];
    `npuarc_PCT_CONFIG_BITS'd6: inc_count0 = all_events_r[6];
    `npuarc_PCT_CONFIG_BITS'd7: inc_count0 = all_events_r[7];
    `npuarc_PCT_CONFIG_BITS'd8: inc_count0 = all_events_r[8];
    `npuarc_PCT_CONFIG_BITS'd9: inc_count0 = all_events_r[9];
    `npuarc_PCT_CONFIG_BITS'd10: inc_count0 = all_events_r[10];
    `npuarc_PCT_CONFIG_BITS'd11: inc_count0 = all_events_r[11];
    `npuarc_PCT_CONFIG_BITS'd12: inc_count0 = all_events_r[12];
    `npuarc_PCT_CONFIG_BITS'd13: inc_count0 = all_events_r[13];
    `npuarc_PCT_CONFIG_BITS'd14: inc_count0 = all_events_r[14];
    `npuarc_PCT_CONFIG_BITS'd15: inc_count0 = all_events_r[15];
    `npuarc_PCT_CONFIG_BITS'd16: inc_count0 = all_events_r[16];
    `npuarc_PCT_CONFIG_BITS'd17: inc_count0 = all_events_r[17];
    `npuarc_PCT_CONFIG_BITS'd18: inc_count0 = all_events_r[18];
    `npuarc_PCT_CONFIG_BITS'd19: inc_count0 = all_events_r[19];
    `npuarc_PCT_CONFIG_BITS'd20: inc_count0 = all_events_r[20];
    `npuarc_PCT_CONFIG_BITS'd21: inc_count0 = all_events_r[21];
    `npuarc_PCT_CONFIG_BITS'd22: inc_count0 = all_events_r[22];
    `npuarc_PCT_CONFIG_BITS'd23: inc_count0 = all_events_r[23];
    `npuarc_PCT_CONFIG_BITS'd24: inc_count0 = all_events_r[24];
    `npuarc_PCT_CONFIG_BITS'd25: inc_count0 = all_events_r[25];
    `npuarc_PCT_CONFIG_BITS'd26: inc_count0 = all_events_r[26];
    `npuarc_PCT_CONFIG_BITS'd27: inc_count0 = all_events_r[27];
    `npuarc_PCT_CONFIG_BITS'd28: inc_count0 = all_events_r[28];
    `npuarc_PCT_CONFIG_BITS'd29: inc_count0 = all_events_r[29];
    `npuarc_PCT_CONFIG_BITS'd30: inc_count0 = all_events_r[30];
    `npuarc_PCT_CONFIG_BITS'd31: inc_count0 = all_events_r[31];
    `npuarc_PCT_CONFIG_BITS'd32: inc_count0 = all_events_r[32];
    `npuarc_PCT_CONFIG_BITS'd33: inc_count0 = all_events_r[33];
    `npuarc_PCT_CONFIG_BITS'd34: inc_count0 = all_events_r[34];
    `npuarc_PCT_CONFIG_BITS'd35: inc_count0 = all_events_r[35];
    `npuarc_PCT_CONFIG_BITS'd36: inc_count0 = all_events_r[36];
    `npuarc_PCT_CONFIG_BITS'd37: inc_count0 = all_events_r[37];
    `npuarc_PCT_CONFIG_BITS'd38: inc_count0 = all_events_r[38];
    `npuarc_PCT_CONFIG_BITS'd39: inc_count0 = all_events_r[39];
    `npuarc_PCT_CONFIG_BITS'd40: inc_count0 = all_events_r[40];
    `npuarc_PCT_CONFIG_BITS'd41: inc_count0 = all_events_r[41];
    `npuarc_PCT_CONFIG_BITS'd42: inc_count0 = all_events_r[42];
    `npuarc_PCT_CONFIG_BITS'd43: inc_count0 = all_events_r[43];
    `npuarc_PCT_CONFIG_BITS'd44: inc_count0 = all_events_r[44];
    `npuarc_PCT_CONFIG_BITS'd45: inc_count0 = all_events_r[45];
    `npuarc_PCT_CONFIG_BITS'd46: inc_count0 = all_events_r[46];
    `npuarc_PCT_CONFIG_BITS'd47: inc_count0 = all_events_r[47];
    `npuarc_PCT_CONFIG_BITS'd48: inc_count0 = all_events_r[48];
    `npuarc_PCT_CONFIG_BITS'd49: inc_count0 = all_events_r[49];
    `npuarc_PCT_CONFIG_BITS'd50: inc_count0 = all_events_r[50];
    `npuarc_PCT_CONFIG_BITS'd51: inc_count0 = all_events_r[51];
    `npuarc_PCT_CONFIG_BITS'd52: inc_count0 = all_events_r[52];
    `npuarc_PCT_CONFIG_BITS'd53: inc_count0 = all_events_r[53];
    `npuarc_PCT_CONFIG_BITS'd54: inc_count0 = all_events_r[54];
    `npuarc_PCT_CONFIG_BITS'd55: inc_count0 = all_events_r[55];
    `npuarc_PCT_CONFIG_BITS'd56: inc_count0 = all_events_r[56];
    `npuarc_PCT_CONFIG_BITS'd57: inc_count0 = all_events_r[57];
    `npuarc_PCT_CONFIG_BITS'd58: inc_count0 = all_events_r[58];
    `npuarc_PCT_CONFIG_BITS'd59: inc_count0 = all_events_r[59];
    `npuarc_PCT_CONFIG_BITS'd60: inc_count0 = all_events_r[60];
    `npuarc_PCT_CONFIG_BITS'd61: inc_count0 = all_events_r[61];
    `npuarc_PCT_CONFIG_BITS'd62: inc_count0 = all_events_r[62];
    `npuarc_PCT_CONFIG_BITS'd63: inc_count0 = all_events_r[63];
    `npuarc_PCT_CONFIG_BITS'd64: inc_count0 = all_events_r[64];
    `npuarc_PCT_CONFIG_BITS'd65: inc_count0 = all_events_r[65];
    `npuarc_PCT_CONFIG_BITS'd66: inc_count0 = all_events_r[66];
    `npuarc_PCT_CONFIG_BITS'd67: inc_count0 = all_events_r[67];
    `npuarc_PCT_CONFIG_BITS'd68: inc_count0 = all_events_r[68];
    `npuarc_PCT_CONFIG_BITS'd69: inc_count0 = all_events_r[69];
    `npuarc_PCT_CONFIG_BITS'd70: inc_count0 = all_events_r[70];
    `npuarc_PCT_CONFIG_BITS'd71: inc_count0 = all_events_r[71];
    `npuarc_PCT_CONFIG_BITS'd72: inc_count0 = all_events_r[72];
    `npuarc_PCT_CONFIG_BITS'd73: inc_count0 = all_events_r[73];
    `npuarc_PCT_CONFIG_BITS'd74: inc_count0 = all_events_r[74];
    `npuarc_PCT_CONFIG_BITS'd75: inc_count0 = all_events_r[75];
    `npuarc_PCT_CONFIG_BITS'd76: inc_count0 = all_events_r[76];
    `npuarc_PCT_CONFIG_BITS'd77: inc_count0 = all_events_r[77];
    `npuarc_PCT_CONFIG_BITS'd78: inc_count0 = all_events_r[78];
    `npuarc_PCT_CONFIG_BITS'd79: inc_count0 = all_events_r[79];
    `npuarc_PCT_CONFIG_BITS'd80: inc_count0 = all_events_r[80];
    `npuarc_PCT_CONFIG_BITS'd81: inc_count0 = all_events_r[81];
    `npuarc_PCT_CONFIG_BITS'd82: inc_count0 = all_events_r[82];
    `npuarc_PCT_CONFIG_BITS'd83: inc_count0 = all_events_r[83];
    `npuarc_PCT_CONFIG_BITS'd84: inc_count0 = all_events_r[84];
    `npuarc_PCT_CONFIG_BITS'd85: inc_count0 = all_events_r[85];
    `npuarc_PCT_CONFIG_BITS'd86: inc_count0 = all_events_r[86];
    `npuarc_PCT_CONFIG_BITS'd87: inc_count0 = all_events_r[87];
    `npuarc_PCT_CONFIG_BITS'd88: inc_count0 = all_events_r[88];
    `npuarc_PCT_CONFIG_BITS'd89: inc_count0 = all_events_r[89];
    `npuarc_PCT_CONFIG_BITS'd90: inc_count0 = all_events_r[90];
    `npuarc_PCT_CONFIG_BITS'd91: inc_count0 = all_events_r[91];
    `npuarc_PCT_CONFIG_BITS'd92: inc_count0 = all_events_r[92];
    `npuarc_PCT_CONFIG_BITS'd93: inc_count0 = all_events_r[93];
    `npuarc_PCT_CONFIG_BITS'd94: inc_count0 = all_events_r[94];
    `npuarc_PCT_CONFIG_BITS'd95: inc_count0 = all_events_r[95];
    `npuarc_PCT_CONFIG_BITS'd96: inc_count0 = all_events_r[96];
    `npuarc_PCT_CONFIG_BITS'd97: inc_count0 = all_events_r[97];
    `npuarc_PCT_CONFIG_BITS'd98: inc_count0 = all_events_r[98];
    `npuarc_PCT_CONFIG_BITS'd99: inc_count0 = all_events_r[99];
    `npuarc_PCT_CONFIG_BITS'd100: inc_count0 = all_events_r[100];
    `npuarc_PCT_CONFIG_BITS'd101: inc_count0 = all_events_r[101];
    `npuarc_PCT_CONFIG_BITS'd102: inc_count0 = all_events_r[102];
    `npuarc_PCT_CONFIG_BITS'd103: inc_count0 = all_events_r[103];
    `npuarc_PCT_CONFIG_BITS'd104: inc_count0 = all_events_r[104];
    `npuarc_PCT_CONFIG_BITS'd105: inc_count0 = all_events_r[105];
    `npuarc_PCT_CONFIG_BITS'd106: inc_count0 = all_events_r[106];
    `npuarc_PCT_CONFIG_BITS'd107: inc_count0 = all_events_r[107];
    `npuarc_PCT_CONFIG_BITS'd108: inc_count0 = all_events_r[108];
    `npuarc_PCT_CONFIG_BITS'd109: inc_count0 = all_events_r[109];
    `npuarc_PCT_CONFIG_BITS'd110: inc_count0 = all_events_r[110];
    `npuarc_PCT_CONFIG_BITS'd111: inc_count0 = all_events_r[111];
    `npuarc_PCT_CONFIG_BITS'd112: inc_count0 = all_events_r[112];
    `npuarc_PCT_CONFIG_BITS'd113: inc_count0 = all_events_r[113];
    `npuarc_PCT_CONFIG_BITS'd114: inc_count0 = all_events_r[114];
    `npuarc_PCT_CONFIG_BITS'd115: inc_count0 = all_events_r[115];
    `npuarc_PCT_CONFIG_BITS'd116: inc_count0 = all_events_r[116];
    `npuarc_PCT_CONFIG_BITS'd117: inc_count0 = all_events_r[117];
    `npuarc_PCT_CONFIG_BITS'd118: inc_count0 = all_events_r[118];
    `npuarc_PCT_CONFIG_BITS'd119: inc_count0 = all_events_r[119];
    `npuarc_PCT_CONFIG_BITS'd120: inc_count0 = all_events_r[120];
    `npuarc_PCT_CONFIG_BITS'd121: inc_count0 = all_events_r[121];
    `npuarc_PCT_CONFIG_BITS'd122: inc_count0 = all_events_r[122];
    `npuarc_PCT_CONFIG_BITS'd123: inc_count0 = all_events_r[123];
    `npuarc_PCT_CONFIG_BITS'd124: inc_count0 = all_events_r[124];
    `npuarc_PCT_CONFIG_BITS'd125: inc_count0 = all_events_r[125];
    `npuarc_PCT_CONFIG_BITS'd126: inc_count0 = all_events_r[126];
    default: inc_count0 = 1'b0;
    endcase
    
    case (config1_r[`npuarc_PCT_CONFIG_RANGE])
    `npuarc_PCT_CONFIG_BITS'd0: inc_count1 = all_events_r[0];
    `npuarc_PCT_CONFIG_BITS'd1: inc_count1 = all_events_r[1];
    `npuarc_PCT_CONFIG_BITS'd2: inc_count1 = all_events_r[2];
    `npuarc_PCT_CONFIG_BITS'd3: inc_count1 = all_events_r[3];
    `npuarc_PCT_CONFIG_BITS'd4: inc_count1 = all_events_r[4];
    `npuarc_PCT_CONFIG_BITS'd5: inc_count1 = all_events_r[5];
    `npuarc_PCT_CONFIG_BITS'd6: inc_count1 = all_events_r[6];
    `npuarc_PCT_CONFIG_BITS'd7: inc_count1 = all_events_r[7];
    `npuarc_PCT_CONFIG_BITS'd8: inc_count1 = all_events_r[8];
    `npuarc_PCT_CONFIG_BITS'd9: inc_count1 = all_events_r[9];
    `npuarc_PCT_CONFIG_BITS'd10: inc_count1 = all_events_r[10];
    `npuarc_PCT_CONFIG_BITS'd11: inc_count1 = all_events_r[11];
    `npuarc_PCT_CONFIG_BITS'd12: inc_count1 = all_events_r[12];
    `npuarc_PCT_CONFIG_BITS'd13: inc_count1 = all_events_r[13];
    `npuarc_PCT_CONFIG_BITS'd14: inc_count1 = all_events_r[14];
    `npuarc_PCT_CONFIG_BITS'd15: inc_count1 = all_events_r[15];
    `npuarc_PCT_CONFIG_BITS'd16: inc_count1 = all_events_r[16];
    `npuarc_PCT_CONFIG_BITS'd17: inc_count1 = all_events_r[17];
    `npuarc_PCT_CONFIG_BITS'd18: inc_count1 = all_events_r[18];
    `npuarc_PCT_CONFIG_BITS'd19: inc_count1 = all_events_r[19];
    `npuarc_PCT_CONFIG_BITS'd20: inc_count1 = all_events_r[20];
    `npuarc_PCT_CONFIG_BITS'd21: inc_count1 = all_events_r[21];
    `npuarc_PCT_CONFIG_BITS'd22: inc_count1 = all_events_r[22];
    `npuarc_PCT_CONFIG_BITS'd23: inc_count1 = all_events_r[23];
    `npuarc_PCT_CONFIG_BITS'd24: inc_count1 = all_events_r[24];
    `npuarc_PCT_CONFIG_BITS'd25: inc_count1 = all_events_r[25];
    `npuarc_PCT_CONFIG_BITS'd26: inc_count1 = all_events_r[26];
    `npuarc_PCT_CONFIG_BITS'd27: inc_count1 = all_events_r[27];
    `npuarc_PCT_CONFIG_BITS'd28: inc_count1 = all_events_r[28];
    `npuarc_PCT_CONFIG_BITS'd29: inc_count1 = all_events_r[29];
    `npuarc_PCT_CONFIG_BITS'd30: inc_count1 = all_events_r[30];
    `npuarc_PCT_CONFIG_BITS'd31: inc_count1 = all_events_r[31];
    `npuarc_PCT_CONFIG_BITS'd32: inc_count1 = all_events_r[32];
    `npuarc_PCT_CONFIG_BITS'd33: inc_count1 = all_events_r[33];
    `npuarc_PCT_CONFIG_BITS'd34: inc_count1 = all_events_r[34];
    `npuarc_PCT_CONFIG_BITS'd35: inc_count1 = all_events_r[35];
    `npuarc_PCT_CONFIG_BITS'd36: inc_count1 = all_events_r[36];
    `npuarc_PCT_CONFIG_BITS'd37: inc_count1 = all_events_r[37];
    `npuarc_PCT_CONFIG_BITS'd38: inc_count1 = all_events_r[38];
    `npuarc_PCT_CONFIG_BITS'd39: inc_count1 = all_events_r[39];
    `npuarc_PCT_CONFIG_BITS'd40: inc_count1 = all_events_r[40];
    `npuarc_PCT_CONFIG_BITS'd41: inc_count1 = all_events_r[41];
    `npuarc_PCT_CONFIG_BITS'd42: inc_count1 = all_events_r[42];
    `npuarc_PCT_CONFIG_BITS'd43: inc_count1 = all_events_r[43];
    `npuarc_PCT_CONFIG_BITS'd44: inc_count1 = all_events_r[44];
    `npuarc_PCT_CONFIG_BITS'd45: inc_count1 = all_events_r[45];
    `npuarc_PCT_CONFIG_BITS'd46: inc_count1 = all_events_r[46];
    `npuarc_PCT_CONFIG_BITS'd47: inc_count1 = all_events_r[47];
    `npuarc_PCT_CONFIG_BITS'd48: inc_count1 = all_events_r[48];
    `npuarc_PCT_CONFIG_BITS'd49: inc_count1 = all_events_r[49];
    `npuarc_PCT_CONFIG_BITS'd50: inc_count1 = all_events_r[50];
    `npuarc_PCT_CONFIG_BITS'd51: inc_count1 = all_events_r[51];
    `npuarc_PCT_CONFIG_BITS'd52: inc_count1 = all_events_r[52];
    `npuarc_PCT_CONFIG_BITS'd53: inc_count1 = all_events_r[53];
    `npuarc_PCT_CONFIG_BITS'd54: inc_count1 = all_events_r[54];
    `npuarc_PCT_CONFIG_BITS'd55: inc_count1 = all_events_r[55];
    `npuarc_PCT_CONFIG_BITS'd56: inc_count1 = all_events_r[56];
    `npuarc_PCT_CONFIG_BITS'd57: inc_count1 = all_events_r[57];
    `npuarc_PCT_CONFIG_BITS'd58: inc_count1 = all_events_r[58];
    `npuarc_PCT_CONFIG_BITS'd59: inc_count1 = all_events_r[59];
    `npuarc_PCT_CONFIG_BITS'd60: inc_count1 = all_events_r[60];
    `npuarc_PCT_CONFIG_BITS'd61: inc_count1 = all_events_r[61];
    `npuarc_PCT_CONFIG_BITS'd62: inc_count1 = all_events_r[62];
    `npuarc_PCT_CONFIG_BITS'd63: inc_count1 = all_events_r[63];
    `npuarc_PCT_CONFIG_BITS'd64: inc_count1 = all_events_r[64];
    `npuarc_PCT_CONFIG_BITS'd65: inc_count1 = all_events_r[65];
    `npuarc_PCT_CONFIG_BITS'd66: inc_count1 = all_events_r[66];
    `npuarc_PCT_CONFIG_BITS'd67: inc_count1 = all_events_r[67];
    `npuarc_PCT_CONFIG_BITS'd68: inc_count1 = all_events_r[68];
    `npuarc_PCT_CONFIG_BITS'd69: inc_count1 = all_events_r[69];
    `npuarc_PCT_CONFIG_BITS'd70: inc_count1 = all_events_r[70];
    `npuarc_PCT_CONFIG_BITS'd71: inc_count1 = all_events_r[71];
    `npuarc_PCT_CONFIG_BITS'd72: inc_count1 = all_events_r[72];
    `npuarc_PCT_CONFIG_BITS'd73: inc_count1 = all_events_r[73];
    `npuarc_PCT_CONFIG_BITS'd74: inc_count1 = all_events_r[74];
    `npuarc_PCT_CONFIG_BITS'd75: inc_count1 = all_events_r[75];
    `npuarc_PCT_CONFIG_BITS'd76: inc_count1 = all_events_r[76];
    `npuarc_PCT_CONFIG_BITS'd77: inc_count1 = all_events_r[77];
    `npuarc_PCT_CONFIG_BITS'd78: inc_count1 = all_events_r[78];
    `npuarc_PCT_CONFIG_BITS'd79: inc_count1 = all_events_r[79];
    `npuarc_PCT_CONFIG_BITS'd80: inc_count1 = all_events_r[80];
    `npuarc_PCT_CONFIG_BITS'd81: inc_count1 = all_events_r[81];
    `npuarc_PCT_CONFIG_BITS'd82: inc_count1 = all_events_r[82];
    `npuarc_PCT_CONFIG_BITS'd83: inc_count1 = all_events_r[83];
    `npuarc_PCT_CONFIG_BITS'd84: inc_count1 = all_events_r[84];
    `npuarc_PCT_CONFIG_BITS'd85: inc_count1 = all_events_r[85];
    `npuarc_PCT_CONFIG_BITS'd86: inc_count1 = all_events_r[86];
    `npuarc_PCT_CONFIG_BITS'd87: inc_count1 = all_events_r[87];
    `npuarc_PCT_CONFIG_BITS'd88: inc_count1 = all_events_r[88];
    `npuarc_PCT_CONFIG_BITS'd89: inc_count1 = all_events_r[89];
    `npuarc_PCT_CONFIG_BITS'd90: inc_count1 = all_events_r[90];
    `npuarc_PCT_CONFIG_BITS'd91: inc_count1 = all_events_r[91];
    `npuarc_PCT_CONFIG_BITS'd92: inc_count1 = all_events_r[92];
    `npuarc_PCT_CONFIG_BITS'd93: inc_count1 = all_events_r[93];
    `npuarc_PCT_CONFIG_BITS'd94: inc_count1 = all_events_r[94];
    `npuarc_PCT_CONFIG_BITS'd95: inc_count1 = all_events_r[95];
    `npuarc_PCT_CONFIG_BITS'd96: inc_count1 = all_events_r[96];
    `npuarc_PCT_CONFIG_BITS'd97: inc_count1 = all_events_r[97];
    `npuarc_PCT_CONFIG_BITS'd98: inc_count1 = all_events_r[98];
    `npuarc_PCT_CONFIG_BITS'd99: inc_count1 = all_events_r[99];
    `npuarc_PCT_CONFIG_BITS'd100: inc_count1 = all_events_r[100];
    `npuarc_PCT_CONFIG_BITS'd101: inc_count1 = all_events_r[101];
    `npuarc_PCT_CONFIG_BITS'd102: inc_count1 = all_events_r[102];
    `npuarc_PCT_CONFIG_BITS'd103: inc_count1 = all_events_r[103];
    `npuarc_PCT_CONFIG_BITS'd104: inc_count1 = all_events_r[104];
    `npuarc_PCT_CONFIG_BITS'd105: inc_count1 = all_events_r[105];
    `npuarc_PCT_CONFIG_BITS'd106: inc_count1 = all_events_r[106];
    `npuarc_PCT_CONFIG_BITS'd107: inc_count1 = all_events_r[107];
    `npuarc_PCT_CONFIG_BITS'd108: inc_count1 = all_events_r[108];
    `npuarc_PCT_CONFIG_BITS'd109: inc_count1 = all_events_r[109];
    `npuarc_PCT_CONFIG_BITS'd110: inc_count1 = all_events_r[110];
    `npuarc_PCT_CONFIG_BITS'd111: inc_count1 = all_events_r[111];
    `npuarc_PCT_CONFIG_BITS'd112: inc_count1 = all_events_r[112];
    `npuarc_PCT_CONFIG_BITS'd113: inc_count1 = all_events_r[113];
    `npuarc_PCT_CONFIG_BITS'd114: inc_count1 = all_events_r[114];
    `npuarc_PCT_CONFIG_BITS'd115: inc_count1 = all_events_r[115];
    `npuarc_PCT_CONFIG_BITS'd116: inc_count1 = all_events_r[116];
    `npuarc_PCT_CONFIG_BITS'd117: inc_count1 = all_events_r[117];
    `npuarc_PCT_CONFIG_BITS'd118: inc_count1 = all_events_r[118];
    `npuarc_PCT_CONFIG_BITS'd119: inc_count1 = all_events_r[119];
    `npuarc_PCT_CONFIG_BITS'd120: inc_count1 = all_events_r[120];
    `npuarc_PCT_CONFIG_BITS'd121: inc_count1 = all_events_r[121];
    `npuarc_PCT_CONFIG_BITS'd122: inc_count1 = all_events_r[122];
    `npuarc_PCT_CONFIG_BITS'd123: inc_count1 = all_events_r[123];
    `npuarc_PCT_CONFIG_BITS'd124: inc_count1 = all_events_r[124];
    `npuarc_PCT_CONFIG_BITS'd125: inc_count1 = all_events_r[125];
    `npuarc_PCT_CONFIG_BITS'd126: inc_count1 = all_events_r[126];
    default: inc_count1 = 1'b0;
    endcase
    
    case (config2_r[`npuarc_PCT_CONFIG_RANGE])
    `npuarc_PCT_CONFIG_BITS'd0: inc_count2 = all_events_r[0];
    `npuarc_PCT_CONFIG_BITS'd1: inc_count2 = all_events_r[1];
    `npuarc_PCT_CONFIG_BITS'd2: inc_count2 = all_events_r[2];
    `npuarc_PCT_CONFIG_BITS'd3: inc_count2 = all_events_r[3];
    `npuarc_PCT_CONFIG_BITS'd4: inc_count2 = all_events_r[4];
    `npuarc_PCT_CONFIG_BITS'd5: inc_count2 = all_events_r[5];
    `npuarc_PCT_CONFIG_BITS'd6: inc_count2 = all_events_r[6];
    `npuarc_PCT_CONFIG_BITS'd7: inc_count2 = all_events_r[7];
    `npuarc_PCT_CONFIG_BITS'd8: inc_count2 = all_events_r[8];
    `npuarc_PCT_CONFIG_BITS'd9: inc_count2 = all_events_r[9];
    `npuarc_PCT_CONFIG_BITS'd10: inc_count2 = all_events_r[10];
    `npuarc_PCT_CONFIG_BITS'd11: inc_count2 = all_events_r[11];
    `npuarc_PCT_CONFIG_BITS'd12: inc_count2 = all_events_r[12];
    `npuarc_PCT_CONFIG_BITS'd13: inc_count2 = all_events_r[13];
    `npuarc_PCT_CONFIG_BITS'd14: inc_count2 = all_events_r[14];
    `npuarc_PCT_CONFIG_BITS'd15: inc_count2 = all_events_r[15];
    `npuarc_PCT_CONFIG_BITS'd16: inc_count2 = all_events_r[16];
    `npuarc_PCT_CONFIG_BITS'd17: inc_count2 = all_events_r[17];
    `npuarc_PCT_CONFIG_BITS'd18: inc_count2 = all_events_r[18];
    `npuarc_PCT_CONFIG_BITS'd19: inc_count2 = all_events_r[19];
    `npuarc_PCT_CONFIG_BITS'd20: inc_count2 = all_events_r[20];
    `npuarc_PCT_CONFIG_BITS'd21: inc_count2 = all_events_r[21];
    `npuarc_PCT_CONFIG_BITS'd22: inc_count2 = all_events_r[22];
    `npuarc_PCT_CONFIG_BITS'd23: inc_count2 = all_events_r[23];
    `npuarc_PCT_CONFIG_BITS'd24: inc_count2 = all_events_r[24];
    `npuarc_PCT_CONFIG_BITS'd25: inc_count2 = all_events_r[25];
    `npuarc_PCT_CONFIG_BITS'd26: inc_count2 = all_events_r[26];
    `npuarc_PCT_CONFIG_BITS'd27: inc_count2 = all_events_r[27];
    `npuarc_PCT_CONFIG_BITS'd28: inc_count2 = all_events_r[28];
    `npuarc_PCT_CONFIG_BITS'd29: inc_count2 = all_events_r[29];
    `npuarc_PCT_CONFIG_BITS'd30: inc_count2 = all_events_r[30];
    `npuarc_PCT_CONFIG_BITS'd31: inc_count2 = all_events_r[31];
    `npuarc_PCT_CONFIG_BITS'd32: inc_count2 = all_events_r[32];
    `npuarc_PCT_CONFIG_BITS'd33: inc_count2 = all_events_r[33];
    `npuarc_PCT_CONFIG_BITS'd34: inc_count2 = all_events_r[34];
    `npuarc_PCT_CONFIG_BITS'd35: inc_count2 = all_events_r[35];
    `npuarc_PCT_CONFIG_BITS'd36: inc_count2 = all_events_r[36];
    `npuarc_PCT_CONFIG_BITS'd37: inc_count2 = all_events_r[37];
    `npuarc_PCT_CONFIG_BITS'd38: inc_count2 = all_events_r[38];
    `npuarc_PCT_CONFIG_BITS'd39: inc_count2 = all_events_r[39];
    `npuarc_PCT_CONFIG_BITS'd40: inc_count2 = all_events_r[40];
    `npuarc_PCT_CONFIG_BITS'd41: inc_count2 = all_events_r[41];
    `npuarc_PCT_CONFIG_BITS'd42: inc_count2 = all_events_r[42];
    `npuarc_PCT_CONFIG_BITS'd43: inc_count2 = all_events_r[43];
    `npuarc_PCT_CONFIG_BITS'd44: inc_count2 = all_events_r[44];
    `npuarc_PCT_CONFIG_BITS'd45: inc_count2 = all_events_r[45];
    `npuarc_PCT_CONFIG_BITS'd46: inc_count2 = all_events_r[46];
    `npuarc_PCT_CONFIG_BITS'd47: inc_count2 = all_events_r[47];
    `npuarc_PCT_CONFIG_BITS'd48: inc_count2 = all_events_r[48];
    `npuarc_PCT_CONFIG_BITS'd49: inc_count2 = all_events_r[49];
    `npuarc_PCT_CONFIG_BITS'd50: inc_count2 = all_events_r[50];
    `npuarc_PCT_CONFIG_BITS'd51: inc_count2 = all_events_r[51];
    `npuarc_PCT_CONFIG_BITS'd52: inc_count2 = all_events_r[52];
    `npuarc_PCT_CONFIG_BITS'd53: inc_count2 = all_events_r[53];
    `npuarc_PCT_CONFIG_BITS'd54: inc_count2 = all_events_r[54];
    `npuarc_PCT_CONFIG_BITS'd55: inc_count2 = all_events_r[55];
    `npuarc_PCT_CONFIG_BITS'd56: inc_count2 = all_events_r[56];
    `npuarc_PCT_CONFIG_BITS'd57: inc_count2 = all_events_r[57];
    `npuarc_PCT_CONFIG_BITS'd58: inc_count2 = all_events_r[58];
    `npuarc_PCT_CONFIG_BITS'd59: inc_count2 = all_events_r[59];
    `npuarc_PCT_CONFIG_BITS'd60: inc_count2 = all_events_r[60];
    `npuarc_PCT_CONFIG_BITS'd61: inc_count2 = all_events_r[61];
    `npuarc_PCT_CONFIG_BITS'd62: inc_count2 = all_events_r[62];
    `npuarc_PCT_CONFIG_BITS'd63: inc_count2 = all_events_r[63];
    `npuarc_PCT_CONFIG_BITS'd64: inc_count2 = all_events_r[64];
    `npuarc_PCT_CONFIG_BITS'd65: inc_count2 = all_events_r[65];
    `npuarc_PCT_CONFIG_BITS'd66: inc_count2 = all_events_r[66];
    `npuarc_PCT_CONFIG_BITS'd67: inc_count2 = all_events_r[67];
    `npuarc_PCT_CONFIG_BITS'd68: inc_count2 = all_events_r[68];
    `npuarc_PCT_CONFIG_BITS'd69: inc_count2 = all_events_r[69];
    `npuarc_PCT_CONFIG_BITS'd70: inc_count2 = all_events_r[70];
    `npuarc_PCT_CONFIG_BITS'd71: inc_count2 = all_events_r[71];
    `npuarc_PCT_CONFIG_BITS'd72: inc_count2 = all_events_r[72];
    `npuarc_PCT_CONFIG_BITS'd73: inc_count2 = all_events_r[73];
    `npuarc_PCT_CONFIG_BITS'd74: inc_count2 = all_events_r[74];
    `npuarc_PCT_CONFIG_BITS'd75: inc_count2 = all_events_r[75];
    `npuarc_PCT_CONFIG_BITS'd76: inc_count2 = all_events_r[76];
    `npuarc_PCT_CONFIG_BITS'd77: inc_count2 = all_events_r[77];
    `npuarc_PCT_CONFIG_BITS'd78: inc_count2 = all_events_r[78];
    `npuarc_PCT_CONFIG_BITS'd79: inc_count2 = all_events_r[79];
    `npuarc_PCT_CONFIG_BITS'd80: inc_count2 = all_events_r[80];
    `npuarc_PCT_CONFIG_BITS'd81: inc_count2 = all_events_r[81];
    `npuarc_PCT_CONFIG_BITS'd82: inc_count2 = all_events_r[82];
    `npuarc_PCT_CONFIG_BITS'd83: inc_count2 = all_events_r[83];
    `npuarc_PCT_CONFIG_BITS'd84: inc_count2 = all_events_r[84];
    `npuarc_PCT_CONFIG_BITS'd85: inc_count2 = all_events_r[85];
    `npuarc_PCT_CONFIG_BITS'd86: inc_count2 = all_events_r[86];
    `npuarc_PCT_CONFIG_BITS'd87: inc_count2 = all_events_r[87];
    `npuarc_PCT_CONFIG_BITS'd88: inc_count2 = all_events_r[88];
    `npuarc_PCT_CONFIG_BITS'd89: inc_count2 = all_events_r[89];
    `npuarc_PCT_CONFIG_BITS'd90: inc_count2 = all_events_r[90];
    `npuarc_PCT_CONFIG_BITS'd91: inc_count2 = all_events_r[91];
    `npuarc_PCT_CONFIG_BITS'd92: inc_count2 = all_events_r[92];
    `npuarc_PCT_CONFIG_BITS'd93: inc_count2 = all_events_r[93];
    `npuarc_PCT_CONFIG_BITS'd94: inc_count2 = all_events_r[94];
    `npuarc_PCT_CONFIG_BITS'd95: inc_count2 = all_events_r[95];
    `npuarc_PCT_CONFIG_BITS'd96: inc_count2 = all_events_r[96];
    `npuarc_PCT_CONFIG_BITS'd97: inc_count2 = all_events_r[97];
    `npuarc_PCT_CONFIG_BITS'd98: inc_count2 = all_events_r[98];
    `npuarc_PCT_CONFIG_BITS'd99: inc_count2 = all_events_r[99];
    `npuarc_PCT_CONFIG_BITS'd100: inc_count2 = all_events_r[100];
    `npuarc_PCT_CONFIG_BITS'd101: inc_count2 = all_events_r[101];
    `npuarc_PCT_CONFIG_BITS'd102: inc_count2 = all_events_r[102];
    `npuarc_PCT_CONFIG_BITS'd103: inc_count2 = all_events_r[103];
    `npuarc_PCT_CONFIG_BITS'd104: inc_count2 = all_events_r[104];
    `npuarc_PCT_CONFIG_BITS'd105: inc_count2 = all_events_r[105];
    `npuarc_PCT_CONFIG_BITS'd106: inc_count2 = all_events_r[106];
    `npuarc_PCT_CONFIG_BITS'd107: inc_count2 = all_events_r[107];
    `npuarc_PCT_CONFIG_BITS'd108: inc_count2 = all_events_r[108];
    `npuarc_PCT_CONFIG_BITS'd109: inc_count2 = all_events_r[109];
    `npuarc_PCT_CONFIG_BITS'd110: inc_count2 = all_events_r[110];
    `npuarc_PCT_CONFIG_BITS'd111: inc_count2 = all_events_r[111];
    `npuarc_PCT_CONFIG_BITS'd112: inc_count2 = all_events_r[112];
    `npuarc_PCT_CONFIG_BITS'd113: inc_count2 = all_events_r[113];
    `npuarc_PCT_CONFIG_BITS'd114: inc_count2 = all_events_r[114];
    `npuarc_PCT_CONFIG_BITS'd115: inc_count2 = all_events_r[115];
    `npuarc_PCT_CONFIG_BITS'd116: inc_count2 = all_events_r[116];
    `npuarc_PCT_CONFIG_BITS'd117: inc_count2 = all_events_r[117];
    `npuarc_PCT_CONFIG_BITS'd118: inc_count2 = all_events_r[118];
    `npuarc_PCT_CONFIG_BITS'd119: inc_count2 = all_events_r[119];
    `npuarc_PCT_CONFIG_BITS'd120: inc_count2 = all_events_r[120];
    `npuarc_PCT_CONFIG_BITS'd121: inc_count2 = all_events_r[121];
    `npuarc_PCT_CONFIG_BITS'd122: inc_count2 = all_events_r[122];
    `npuarc_PCT_CONFIG_BITS'd123: inc_count2 = all_events_r[123];
    `npuarc_PCT_CONFIG_BITS'd124: inc_count2 = all_events_r[124];
    `npuarc_PCT_CONFIG_BITS'd125: inc_count2 = all_events_r[125];
    `npuarc_PCT_CONFIG_BITS'd126: inc_count2 = all_events_r[126];
    default: inc_count2 = 1'b0;
    endcase
    
    case (config3_r[`npuarc_PCT_CONFIG_RANGE])
    `npuarc_PCT_CONFIG_BITS'd0: inc_count3 = all_events_r[0];
    `npuarc_PCT_CONFIG_BITS'd1: inc_count3 = all_events_r[1];
    `npuarc_PCT_CONFIG_BITS'd2: inc_count3 = all_events_r[2];
    `npuarc_PCT_CONFIG_BITS'd3: inc_count3 = all_events_r[3];
    `npuarc_PCT_CONFIG_BITS'd4: inc_count3 = all_events_r[4];
    `npuarc_PCT_CONFIG_BITS'd5: inc_count3 = all_events_r[5];
    `npuarc_PCT_CONFIG_BITS'd6: inc_count3 = all_events_r[6];
    `npuarc_PCT_CONFIG_BITS'd7: inc_count3 = all_events_r[7];
    `npuarc_PCT_CONFIG_BITS'd8: inc_count3 = all_events_r[8];
    `npuarc_PCT_CONFIG_BITS'd9: inc_count3 = all_events_r[9];
    `npuarc_PCT_CONFIG_BITS'd10: inc_count3 = all_events_r[10];
    `npuarc_PCT_CONFIG_BITS'd11: inc_count3 = all_events_r[11];
    `npuarc_PCT_CONFIG_BITS'd12: inc_count3 = all_events_r[12];
    `npuarc_PCT_CONFIG_BITS'd13: inc_count3 = all_events_r[13];
    `npuarc_PCT_CONFIG_BITS'd14: inc_count3 = all_events_r[14];
    `npuarc_PCT_CONFIG_BITS'd15: inc_count3 = all_events_r[15];
    `npuarc_PCT_CONFIG_BITS'd16: inc_count3 = all_events_r[16];
    `npuarc_PCT_CONFIG_BITS'd17: inc_count3 = all_events_r[17];
    `npuarc_PCT_CONFIG_BITS'd18: inc_count3 = all_events_r[18];
    `npuarc_PCT_CONFIG_BITS'd19: inc_count3 = all_events_r[19];
    `npuarc_PCT_CONFIG_BITS'd20: inc_count3 = all_events_r[20];
    `npuarc_PCT_CONFIG_BITS'd21: inc_count3 = all_events_r[21];
    `npuarc_PCT_CONFIG_BITS'd22: inc_count3 = all_events_r[22];
    `npuarc_PCT_CONFIG_BITS'd23: inc_count3 = all_events_r[23];
    `npuarc_PCT_CONFIG_BITS'd24: inc_count3 = all_events_r[24];
    `npuarc_PCT_CONFIG_BITS'd25: inc_count3 = all_events_r[25];
    `npuarc_PCT_CONFIG_BITS'd26: inc_count3 = all_events_r[26];
    `npuarc_PCT_CONFIG_BITS'd27: inc_count3 = all_events_r[27];
    `npuarc_PCT_CONFIG_BITS'd28: inc_count3 = all_events_r[28];
    `npuarc_PCT_CONFIG_BITS'd29: inc_count3 = all_events_r[29];
    `npuarc_PCT_CONFIG_BITS'd30: inc_count3 = all_events_r[30];
    `npuarc_PCT_CONFIG_BITS'd31: inc_count3 = all_events_r[31];
    `npuarc_PCT_CONFIG_BITS'd32: inc_count3 = all_events_r[32];
    `npuarc_PCT_CONFIG_BITS'd33: inc_count3 = all_events_r[33];
    `npuarc_PCT_CONFIG_BITS'd34: inc_count3 = all_events_r[34];
    `npuarc_PCT_CONFIG_BITS'd35: inc_count3 = all_events_r[35];
    `npuarc_PCT_CONFIG_BITS'd36: inc_count3 = all_events_r[36];
    `npuarc_PCT_CONFIG_BITS'd37: inc_count3 = all_events_r[37];
    `npuarc_PCT_CONFIG_BITS'd38: inc_count3 = all_events_r[38];
    `npuarc_PCT_CONFIG_BITS'd39: inc_count3 = all_events_r[39];
    `npuarc_PCT_CONFIG_BITS'd40: inc_count3 = all_events_r[40];
    `npuarc_PCT_CONFIG_BITS'd41: inc_count3 = all_events_r[41];
    `npuarc_PCT_CONFIG_BITS'd42: inc_count3 = all_events_r[42];
    `npuarc_PCT_CONFIG_BITS'd43: inc_count3 = all_events_r[43];
    `npuarc_PCT_CONFIG_BITS'd44: inc_count3 = all_events_r[44];
    `npuarc_PCT_CONFIG_BITS'd45: inc_count3 = all_events_r[45];
    `npuarc_PCT_CONFIG_BITS'd46: inc_count3 = all_events_r[46];
    `npuarc_PCT_CONFIG_BITS'd47: inc_count3 = all_events_r[47];
    `npuarc_PCT_CONFIG_BITS'd48: inc_count3 = all_events_r[48];
    `npuarc_PCT_CONFIG_BITS'd49: inc_count3 = all_events_r[49];
    `npuarc_PCT_CONFIG_BITS'd50: inc_count3 = all_events_r[50];
    `npuarc_PCT_CONFIG_BITS'd51: inc_count3 = all_events_r[51];
    `npuarc_PCT_CONFIG_BITS'd52: inc_count3 = all_events_r[52];
    `npuarc_PCT_CONFIG_BITS'd53: inc_count3 = all_events_r[53];
    `npuarc_PCT_CONFIG_BITS'd54: inc_count3 = all_events_r[54];
    `npuarc_PCT_CONFIG_BITS'd55: inc_count3 = all_events_r[55];
    `npuarc_PCT_CONFIG_BITS'd56: inc_count3 = all_events_r[56];
    `npuarc_PCT_CONFIG_BITS'd57: inc_count3 = all_events_r[57];
    `npuarc_PCT_CONFIG_BITS'd58: inc_count3 = all_events_r[58];
    `npuarc_PCT_CONFIG_BITS'd59: inc_count3 = all_events_r[59];
    `npuarc_PCT_CONFIG_BITS'd60: inc_count3 = all_events_r[60];
    `npuarc_PCT_CONFIG_BITS'd61: inc_count3 = all_events_r[61];
    `npuarc_PCT_CONFIG_BITS'd62: inc_count3 = all_events_r[62];
    `npuarc_PCT_CONFIG_BITS'd63: inc_count3 = all_events_r[63];
    `npuarc_PCT_CONFIG_BITS'd64: inc_count3 = all_events_r[64];
    `npuarc_PCT_CONFIG_BITS'd65: inc_count3 = all_events_r[65];
    `npuarc_PCT_CONFIG_BITS'd66: inc_count3 = all_events_r[66];
    `npuarc_PCT_CONFIG_BITS'd67: inc_count3 = all_events_r[67];
    `npuarc_PCT_CONFIG_BITS'd68: inc_count3 = all_events_r[68];
    `npuarc_PCT_CONFIG_BITS'd69: inc_count3 = all_events_r[69];
    `npuarc_PCT_CONFIG_BITS'd70: inc_count3 = all_events_r[70];
    `npuarc_PCT_CONFIG_BITS'd71: inc_count3 = all_events_r[71];
    `npuarc_PCT_CONFIG_BITS'd72: inc_count3 = all_events_r[72];
    `npuarc_PCT_CONFIG_BITS'd73: inc_count3 = all_events_r[73];
    `npuarc_PCT_CONFIG_BITS'd74: inc_count3 = all_events_r[74];
    `npuarc_PCT_CONFIG_BITS'd75: inc_count3 = all_events_r[75];
    `npuarc_PCT_CONFIG_BITS'd76: inc_count3 = all_events_r[76];
    `npuarc_PCT_CONFIG_BITS'd77: inc_count3 = all_events_r[77];
    `npuarc_PCT_CONFIG_BITS'd78: inc_count3 = all_events_r[78];
    `npuarc_PCT_CONFIG_BITS'd79: inc_count3 = all_events_r[79];
    `npuarc_PCT_CONFIG_BITS'd80: inc_count3 = all_events_r[80];
    `npuarc_PCT_CONFIG_BITS'd81: inc_count3 = all_events_r[81];
    `npuarc_PCT_CONFIG_BITS'd82: inc_count3 = all_events_r[82];
    `npuarc_PCT_CONFIG_BITS'd83: inc_count3 = all_events_r[83];
    `npuarc_PCT_CONFIG_BITS'd84: inc_count3 = all_events_r[84];
    `npuarc_PCT_CONFIG_BITS'd85: inc_count3 = all_events_r[85];
    `npuarc_PCT_CONFIG_BITS'd86: inc_count3 = all_events_r[86];
    `npuarc_PCT_CONFIG_BITS'd87: inc_count3 = all_events_r[87];
    `npuarc_PCT_CONFIG_BITS'd88: inc_count3 = all_events_r[88];
    `npuarc_PCT_CONFIG_BITS'd89: inc_count3 = all_events_r[89];
    `npuarc_PCT_CONFIG_BITS'd90: inc_count3 = all_events_r[90];
    `npuarc_PCT_CONFIG_BITS'd91: inc_count3 = all_events_r[91];
    `npuarc_PCT_CONFIG_BITS'd92: inc_count3 = all_events_r[92];
    `npuarc_PCT_CONFIG_BITS'd93: inc_count3 = all_events_r[93];
    `npuarc_PCT_CONFIG_BITS'd94: inc_count3 = all_events_r[94];
    `npuarc_PCT_CONFIG_BITS'd95: inc_count3 = all_events_r[95];
    `npuarc_PCT_CONFIG_BITS'd96: inc_count3 = all_events_r[96];
    `npuarc_PCT_CONFIG_BITS'd97: inc_count3 = all_events_r[97];
    `npuarc_PCT_CONFIG_BITS'd98: inc_count3 = all_events_r[98];
    `npuarc_PCT_CONFIG_BITS'd99: inc_count3 = all_events_r[99];
    `npuarc_PCT_CONFIG_BITS'd100: inc_count3 = all_events_r[100];
    `npuarc_PCT_CONFIG_BITS'd101: inc_count3 = all_events_r[101];
    `npuarc_PCT_CONFIG_BITS'd102: inc_count3 = all_events_r[102];
    `npuarc_PCT_CONFIG_BITS'd103: inc_count3 = all_events_r[103];
    `npuarc_PCT_CONFIG_BITS'd104: inc_count3 = all_events_r[104];
    `npuarc_PCT_CONFIG_BITS'd105: inc_count3 = all_events_r[105];
    `npuarc_PCT_CONFIG_BITS'd106: inc_count3 = all_events_r[106];
    `npuarc_PCT_CONFIG_BITS'd107: inc_count3 = all_events_r[107];
    `npuarc_PCT_CONFIG_BITS'd108: inc_count3 = all_events_r[108];
    `npuarc_PCT_CONFIG_BITS'd109: inc_count3 = all_events_r[109];
    `npuarc_PCT_CONFIG_BITS'd110: inc_count3 = all_events_r[110];
    `npuarc_PCT_CONFIG_BITS'd111: inc_count3 = all_events_r[111];
    `npuarc_PCT_CONFIG_BITS'd112: inc_count3 = all_events_r[112];
    `npuarc_PCT_CONFIG_BITS'd113: inc_count3 = all_events_r[113];
    `npuarc_PCT_CONFIG_BITS'd114: inc_count3 = all_events_r[114];
    `npuarc_PCT_CONFIG_BITS'd115: inc_count3 = all_events_r[115];
    `npuarc_PCT_CONFIG_BITS'd116: inc_count3 = all_events_r[116];
    `npuarc_PCT_CONFIG_BITS'd117: inc_count3 = all_events_r[117];
    `npuarc_PCT_CONFIG_BITS'd118: inc_count3 = all_events_r[118];
    `npuarc_PCT_CONFIG_BITS'd119: inc_count3 = all_events_r[119];
    `npuarc_PCT_CONFIG_BITS'd120: inc_count3 = all_events_r[120];
    `npuarc_PCT_CONFIG_BITS'd121: inc_count3 = all_events_r[121];
    `npuarc_PCT_CONFIG_BITS'd122: inc_count3 = all_events_r[122];
    `npuarc_PCT_CONFIG_BITS'd123: inc_count3 = all_events_r[123];
    `npuarc_PCT_CONFIG_BITS'd124: inc_count3 = all_events_r[124];
    `npuarc_PCT_CONFIG_BITS'd125: inc_count3 = all_events_r[125];
    `npuarc_PCT_CONFIG_BITS'd126: inc_count3 = all_events_r[126];
    default: inc_count3 = 1'b0;
    endcase
    
    case (config4_r[`npuarc_PCT_CONFIG_RANGE])
    `npuarc_PCT_CONFIG_BITS'd0: inc_count4 = all_events_r[0];
    `npuarc_PCT_CONFIG_BITS'd1: inc_count4 = all_events_r[1];
    `npuarc_PCT_CONFIG_BITS'd2: inc_count4 = all_events_r[2];
    `npuarc_PCT_CONFIG_BITS'd3: inc_count4 = all_events_r[3];
    `npuarc_PCT_CONFIG_BITS'd4: inc_count4 = all_events_r[4];
    `npuarc_PCT_CONFIG_BITS'd5: inc_count4 = all_events_r[5];
    `npuarc_PCT_CONFIG_BITS'd6: inc_count4 = all_events_r[6];
    `npuarc_PCT_CONFIG_BITS'd7: inc_count4 = all_events_r[7];
    `npuarc_PCT_CONFIG_BITS'd8: inc_count4 = all_events_r[8];
    `npuarc_PCT_CONFIG_BITS'd9: inc_count4 = all_events_r[9];
    `npuarc_PCT_CONFIG_BITS'd10: inc_count4 = all_events_r[10];
    `npuarc_PCT_CONFIG_BITS'd11: inc_count4 = all_events_r[11];
    `npuarc_PCT_CONFIG_BITS'd12: inc_count4 = all_events_r[12];
    `npuarc_PCT_CONFIG_BITS'd13: inc_count4 = all_events_r[13];
    `npuarc_PCT_CONFIG_BITS'd14: inc_count4 = all_events_r[14];
    `npuarc_PCT_CONFIG_BITS'd15: inc_count4 = all_events_r[15];
    `npuarc_PCT_CONFIG_BITS'd16: inc_count4 = all_events_r[16];
    `npuarc_PCT_CONFIG_BITS'd17: inc_count4 = all_events_r[17];
    `npuarc_PCT_CONFIG_BITS'd18: inc_count4 = all_events_r[18];
    `npuarc_PCT_CONFIG_BITS'd19: inc_count4 = all_events_r[19];
    `npuarc_PCT_CONFIG_BITS'd20: inc_count4 = all_events_r[20];
    `npuarc_PCT_CONFIG_BITS'd21: inc_count4 = all_events_r[21];
    `npuarc_PCT_CONFIG_BITS'd22: inc_count4 = all_events_r[22];
    `npuarc_PCT_CONFIG_BITS'd23: inc_count4 = all_events_r[23];
    `npuarc_PCT_CONFIG_BITS'd24: inc_count4 = all_events_r[24];
    `npuarc_PCT_CONFIG_BITS'd25: inc_count4 = all_events_r[25];
    `npuarc_PCT_CONFIG_BITS'd26: inc_count4 = all_events_r[26];
    `npuarc_PCT_CONFIG_BITS'd27: inc_count4 = all_events_r[27];
    `npuarc_PCT_CONFIG_BITS'd28: inc_count4 = all_events_r[28];
    `npuarc_PCT_CONFIG_BITS'd29: inc_count4 = all_events_r[29];
    `npuarc_PCT_CONFIG_BITS'd30: inc_count4 = all_events_r[30];
    `npuarc_PCT_CONFIG_BITS'd31: inc_count4 = all_events_r[31];
    `npuarc_PCT_CONFIG_BITS'd32: inc_count4 = all_events_r[32];
    `npuarc_PCT_CONFIG_BITS'd33: inc_count4 = all_events_r[33];
    `npuarc_PCT_CONFIG_BITS'd34: inc_count4 = all_events_r[34];
    `npuarc_PCT_CONFIG_BITS'd35: inc_count4 = all_events_r[35];
    `npuarc_PCT_CONFIG_BITS'd36: inc_count4 = all_events_r[36];
    `npuarc_PCT_CONFIG_BITS'd37: inc_count4 = all_events_r[37];
    `npuarc_PCT_CONFIG_BITS'd38: inc_count4 = all_events_r[38];
    `npuarc_PCT_CONFIG_BITS'd39: inc_count4 = all_events_r[39];
    `npuarc_PCT_CONFIG_BITS'd40: inc_count4 = all_events_r[40];
    `npuarc_PCT_CONFIG_BITS'd41: inc_count4 = all_events_r[41];
    `npuarc_PCT_CONFIG_BITS'd42: inc_count4 = all_events_r[42];
    `npuarc_PCT_CONFIG_BITS'd43: inc_count4 = all_events_r[43];
    `npuarc_PCT_CONFIG_BITS'd44: inc_count4 = all_events_r[44];
    `npuarc_PCT_CONFIG_BITS'd45: inc_count4 = all_events_r[45];
    `npuarc_PCT_CONFIG_BITS'd46: inc_count4 = all_events_r[46];
    `npuarc_PCT_CONFIG_BITS'd47: inc_count4 = all_events_r[47];
    `npuarc_PCT_CONFIG_BITS'd48: inc_count4 = all_events_r[48];
    `npuarc_PCT_CONFIG_BITS'd49: inc_count4 = all_events_r[49];
    `npuarc_PCT_CONFIG_BITS'd50: inc_count4 = all_events_r[50];
    `npuarc_PCT_CONFIG_BITS'd51: inc_count4 = all_events_r[51];
    `npuarc_PCT_CONFIG_BITS'd52: inc_count4 = all_events_r[52];
    `npuarc_PCT_CONFIG_BITS'd53: inc_count4 = all_events_r[53];
    `npuarc_PCT_CONFIG_BITS'd54: inc_count4 = all_events_r[54];
    `npuarc_PCT_CONFIG_BITS'd55: inc_count4 = all_events_r[55];
    `npuarc_PCT_CONFIG_BITS'd56: inc_count4 = all_events_r[56];
    `npuarc_PCT_CONFIG_BITS'd57: inc_count4 = all_events_r[57];
    `npuarc_PCT_CONFIG_BITS'd58: inc_count4 = all_events_r[58];
    `npuarc_PCT_CONFIG_BITS'd59: inc_count4 = all_events_r[59];
    `npuarc_PCT_CONFIG_BITS'd60: inc_count4 = all_events_r[60];
    `npuarc_PCT_CONFIG_BITS'd61: inc_count4 = all_events_r[61];
    `npuarc_PCT_CONFIG_BITS'd62: inc_count4 = all_events_r[62];
    `npuarc_PCT_CONFIG_BITS'd63: inc_count4 = all_events_r[63];
    `npuarc_PCT_CONFIG_BITS'd64: inc_count4 = all_events_r[64];
    `npuarc_PCT_CONFIG_BITS'd65: inc_count4 = all_events_r[65];
    `npuarc_PCT_CONFIG_BITS'd66: inc_count4 = all_events_r[66];
    `npuarc_PCT_CONFIG_BITS'd67: inc_count4 = all_events_r[67];
    `npuarc_PCT_CONFIG_BITS'd68: inc_count4 = all_events_r[68];
    `npuarc_PCT_CONFIG_BITS'd69: inc_count4 = all_events_r[69];
    `npuarc_PCT_CONFIG_BITS'd70: inc_count4 = all_events_r[70];
    `npuarc_PCT_CONFIG_BITS'd71: inc_count4 = all_events_r[71];
    `npuarc_PCT_CONFIG_BITS'd72: inc_count4 = all_events_r[72];
    `npuarc_PCT_CONFIG_BITS'd73: inc_count4 = all_events_r[73];
    `npuarc_PCT_CONFIG_BITS'd74: inc_count4 = all_events_r[74];
    `npuarc_PCT_CONFIG_BITS'd75: inc_count4 = all_events_r[75];
    `npuarc_PCT_CONFIG_BITS'd76: inc_count4 = all_events_r[76];
    `npuarc_PCT_CONFIG_BITS'd77: inc_count4 = all_events_r[77];
    `npuarc_PCT_CONFIG_BITS'd78: inc_count4 = all_events_r[78];
    `npuarc_PCT_CONFIG_BITS'd79: inc_count4 = all_events_r[79];
    `npuarc_PCT_CONFIG_BITS'd80: inc_count4 = all_events_r[80];
    `npuarc_PCT_CONFIG_BITS'd81: inc_count4 = all_events_r[81];
    `npuarc_PCT_CONFIG_BITS'd82: inc_count4 = all_events_r[82];
    `npuarc_PCT_CONFIG_BITS'd83: inc_count4 = all_events_r[83];
    `npuarc_PCT_CONFIG_BITS'd84: inc_count4 = all_events_r[84];
    `npuarc_PCT_CONFIG_BITS'd85: inc_count4 = all_events_r[85];
    `npuarc_PCT_CONFIG_BITS'd86: inc_count4 = all_events_r[86];
    `npuarc_PCT_CONFIG_BITS'd87: inc_count4 = all_events_r[87];
    `npuarc_PCT_CONFIG_BITS'd88: inc_count4 = all_events_r[88];
    `npuarc_PCT_CONFIG_BITS'd89: inc_count4 = all_events_r[89];
    `npuarc_PCT_CONFIG_BITS'd90: inc_count4 = all_events_r[90];
    `npuarc_PCT_CONFIG_BITS'd91: inc_count4 = all_events_r[91];
    `npuarc_PCT_CONFIG_BITS'd92: inc_count4 = all_events_r[92];
    `npuarc_PCT_CONFIG_BITS'd93: inc_count4 = all_events_r[93];
    `npuarc_PCT_CONFIG_BITS'd94: inc_count4 = all_events_r[94];
    `npuarc_PCT_CONFIG_BITS'd95: inc_count4 = all_events_r[95];
    `npuarc_PCT_CONFIG_BITS'd96: inc_count4 = all_events_r[96];
    `npuarc_PCT_CONFIG_BITS'd97: inc_count4 = all_events_r[97];
    `npuarc_PCT_CONFIG_BITS'd98: inc_count4 = all_events_r[98];
    `npuarc_PCT_CONFIG_BITS'd99: inc_count4 = all_events_r[99];
    `npuarc_PCT_CONFIG_BITS'd100: inc_count4 = all_events_r[100];
    `npuarc_PCT_CONFIG_BITS'd101: inc_count4 = all_events_r[101];
    `npuarc_PCT_CONFIG_BITS'd102: inc_count4 = all_events_r[102];
    `npuarc_PCT_CONFIG_BITS'd103: inc_count4 = all_events_r[103];
    `npuarc_PCT_CONFIG_BITS'd104: inc_count4 = all_events_r[104];
    `npuarc_PCT_CONFIG_BITS'd105: inc_count4 = all_events_r[105];
    `npuarc_PCT_CONFIG_BITS'd106: inc_count4 = all_events_r[106];
    `npuarc_PCT_CONFIG_BITS'd107: inc_count4 = all_events_r[107];
    `npuarc_PCT_CONFIG_BITS'd108: inc_count4 = all_events_r[108];
    `npuarc_PCT_CONFIG_BITS'd109: inc_count4 = all_events_r[109];
    `npuarc_PCT_CONFIG_BITS'd110: inc_count4 = all_events_r[110];
    `npuarc_PCT_CONFIG_BITS'd111: inc_count4 = all_events_r[111];
    `npuarc_PCT_CONFIG_BITS'd112: inc_count4 = all_events_r[112];
    `npuarc_PCT_CONFIG_BITS'd113: inc_count4 = all_events_r[113];
    `npuarc_PCT_CONFIG_BITS'd114: inc_count4 = all_events_r[114];
    `npuarc_PCT_CONFIG_BITS'd115: inc_count4 = all_events_r[115];
    `npuarc_PCT_CONFIG_BITS'd116: inc_count4 = all_events_r[116];
    `npuarc_PCT_CONFIG_BITS'd117: inc_count4 = all_events_r[117];
    `npuarc_PCT_CONFIG_BITS'd118: inc_count4 = all_events_r[118];
    `npuarc_PCT_CONFIG_BITS'd119: inc_count4 = all_events_r[119];
    `npuarc_PCT_CONFIG_BITS'd120: inc_count4 = all_events_r[120];
    `npuarc_PCT_CONFIG_BITS'd121: inc_count4 = all_events_r[121];
    `npuarc_PCT_CONFIG_BITS'd122: inc_count4 = all_events_r[122];
    `npuarc_PCT_CONFIG_BITS'd123: inc_count4 = all_events_r[123];
    `npuarc_PCT_CONFIG_BITS'd124: inc_count4 = all_events_r[124];
    `npuarc_PCT_CONFIG_BITS'd125: inc_count4 = all_events_r[125];
    `npuarc_PCT_CONFIG_BITS'd126: inc_count4 = all_events_r[126];
    default: inc_count4 = 1'b0;
    endcase
    
    case (config5_r[`npuarc_PCT_CONFIG_RANGE])
    `npuarc_PCT_CONFIG_BITS'd0: inc_count5 = all_events_r[0];
    `npuarc_PCT_CONFIG_BITS'd1: inc_count5 = all_events_r[1];
    `npuarc_PCT_CONFIG_BITS'd2: inc_count5 = all_events_r[2];
    `npuarc_PCT_CONFIG_BITS'd3: inc_count5 = all_events_r[3];
    `npuarc_PCT_CONFIG_BITS'd4: inc_count5 = all_events_r[4];
    `npuarc_PCT_CONFIG_BITS'd5: inc_count5 = all_events_r[5];
    `npuarc_PCT_CONFIG_BITS'd6: inc_count5 = all_events_r[6];
    `npuarc_PCT_CONFIG_BITS'd7: inc_count5 = all_events_r[7];
    `npuarc_PCT_CONFIG_BITS'd8: inc_count5 = all_events_r[8];
    `npuarc_PCT_CONFIG_BITS'd9: inc_count5 = all_events_r[9];
    `npuarc_PCT_CONFIG_BITS'd10: inc_count5 = all_events_r[10];
    `npuarc_PCT_CONFIG_BITS'd11: inc_count5 = all_events_r[11];
    `npuarc_PCT_CONFIG_BITS'd12: inc_count5 = all_events_r[12];
    `npuarc_PCT_CONFIG_BITS'd13: inc_count5 = all_events_r[13];
    `npuarc_PCT_CONFIG_BITS'd14: inc_count5 = all_events_r[14];
    `npuarc_PCT_CONFIG_BITS'd15: inc_count5 = all_events_r[15];
    `npuarc_PCT_CONFIG_BITS'd16: inc_count5 = all_events_r[16];
    `npuarc_PCT_CONFIG_BITS'd17: inc_count5 = all_events_r[17];
    `npuarc_PCT_CONFIG_BITS'd18: inc_count5 = all_events_r[18];
    `npuarc_PCT_CONFIG_BITS'd19: inc_count5 = all_events_r[19];
    `npuarc_PCT_CONFIG_BITS'd20: inc_count5 = all_events_r[20];
    `npuarc_PCT_CONFIG_BITS'd21: inc_count5 = all_events_r[21];
    `npuarc_PCT_CONFIG_BITS'd22: inc_count5 = all_events_r[22];
    `npuarc_PCT_CONFIG_BITS'd23: inc_count5 = all_events_r[23];
    `npuarc_PCT_CONFIG_BITS'd24: inc_count5 = all_events_r[24];
    `npuarc_PCT_CONFIG_BITS'd25: inc_count5 = all_events_r[25];
    `npuarc_PCT_CONFIG_BITS'd26: inc_count5 = all_events_r[26];
    `npuarc_PCT_CONFIG_BITS'd27: inc_count5 = all_events_r[27];
    `npuarc_PCT_CONFIG_BITS'd28: inc_count5 = all_events_r[28];
    `npuarc_PCT_CONFIG_BITS'd29: inc_count5 = all_events_r[29];
    `npuarc_PCT_CONFIG_BITS'd30: inc_count5 = all_events_r[30];
    `npuarc_PCT_CONFIG_BITS'd31: inc_count5 = all_events_r[31];
    `npuarc_PCT_CONFIG_BITS'd32: inc_count5 = all_events_r[32];
    `npuarc_PCT_CONFIG_BITS'd33: inc_count5 = all_events_r[33];
    `npuarc_PCT_CONFIG_BITS'd34: inc_count5 = all_events_r[34];
    `npuarc_PCT_CONFIG_BITS'd35: inc_count5 = all_events_r[35];
    `npuarc_PCT_CONFIG_BITS'd36: inc_count5 = all_events_r[36];
    `npuarc_PCT_CONFIG_BITS'd37: inc_count5 = all_events_r[37];
    `npuarc_PCT_CONFIG_BITS'd38: inc_count5 = all_events_r[38];
    `npuarc_PCT_CONFIG_BITS'd39: inc_count5 = all_events_r[39];
    `npuarc_PCT_CONFIG_BITS'd40: inc_count5 = all_events_r[40];
    `npuarc_PCT_CONFIG_BITS'd41: inc_count5 = all_events_r[41];
    `npuarc_PCT_CONFIG_BITS'd42: inc_count5 = all_events_r[42];
    `npuarc_PCT_CONFIG_BITS'd43: inc_count5 = all_events_r[43];
    `npuarc_PCT_CONFIG_BITS'd44: inc_count5 = all_events_r[44];
    `npuarc_PCT_CONFIG_BITS'd45: inc_count5 = all_events_r[45];
    `npuarc_PCT_CONFIG_BITS'd46: inc_count5 = all_events_r[46];
    `npuarc_PCT_CONFIG_BITS'd47: inc_count5 = all_events_r[47];
    `npuarc_PCT_CONFIG_BITS'd48: inc_count5 = all_events_r[48];
    `npuarc_PCT_CONFIG_BITS'd49: inc_count5 = all_events_r[49];
    `npuarc_PCT_CONFIG_BITS'd50: inc_count5 = all_events_r[50];
    `npuarc_PCT_CONFIG_BITS'd51: inc_count5 = all_events_r[51];
    `npuarc_PCT_CONFIG_BITS'd52: inc_count5 = all_events_r[52];
    `npuarc_PCT_CONFIG_BITS'd53: inc_count5 = all_events_r[53];
    `npuarc_PCT_CONFIG_BITS'd54: inc_count5 = all_events_r[54];
    `npuarc_PCT_CONFIG_BITS'd55: inc_count5 = all_events_r[55];
    `npuarc_PCT_CONFIG_BITS'd56: inc_count5 = all_events_r[56];
    `npuarc_PCT_CONFIG_BITS'd57: inc_count5 = all_events_r[57];
    `npuarc_PCT_CONFIG_BITS'd58: inc_count5 = all_events_r[58];
    `npuarc_PCT_CONFIG_BITS'd59: inc_count5 = all_events_r[59];
    `npuarc_PCT_CONFIG_BITS'd60: inc_count5 = all_events_r[60];
    `npuarc_PCT_CONFIG_BITS'd61: inc_count5 = all_events_r[61];
    `npuarc_PCT_CONFIG_BITS'd62: inc_count5 = all_events_r[62];
    `npuarc_PCT_CONFIG_BITS'd63: inc_count5 = all_events_r[63];
    `npuarc_PCT_CONFIG_BITS'd64: inc_count5 = all_events_r[64];
    `npuarc_PCT_CONFIG_BITS'd65: inc_count5 = all_events_r[65];
    `npuarc_PCT_CONFIG_BITS'd66: inc_count5 = all_events_r[66];
    `npuarc_PCT_CONFIG_BITS'd67: inc_count5 = all_events_r[67];
    `npuarc_PCT_CONFIG_BITS'd68: inc_count5 = all_events_r[68];
    `npuarc_PCT_CONFIG_BITS'd69: inc_count5 = all_events_r[69];
    `npuarc_PCT_CONFIG_BITS'd70: inc_count5 = all_events_r[70];
    `npuarc_PCT_CONFIG_BITS'd71: inc_count5 = all_events_r[71];
    `npuarc_PCT_CONFIG_BITS'd72: inc_count5 = all_events_r[72];
    `npuarc_PCT_CONFIG_BITS'd73: inc_count5 = all_events_r[73];
    `npuarc_PCT_CONFIG_BITS'd74: inc_count5 = all_events_r[74];
    `npuarc_PCT_CONFIG_BITS'd75: inc_count5 = all_events_r[75];
    `npuarc_PCT_CONFIG_BITS'd76: inc_count5 = all_events_r[76];
    `npuarc_PCT_CONFIG_BITS'd77: inc_count5 = all_events_r[77];
    `npuarc_PCT_CONFIG_BITS'd78: inc_count5 = all_events_r[78];
    `npuarc_PCT_CONFIG_BITS'd79: inc_count5 = all_events_r[79];
    `npuarc_PCT_CONFIG_BITS'd80: inc_count5 = all_events_r[80];
    `npuarc_PCT_CONFIG_BITS'd81: inc_count5 = all_events_r[81];
    `npuarc_PCT_CONFIG_BITS'd82: inc_count5 = all_events_r[82];
    `npuarc_PCT_CONFIG_BITS'd83: inc_count5 = all_events_r[83];
    `npuarc_PCT_CONFIG_BITS'd84: inc_count5 = all_events_r[84];
    `npuarc_PCT_CONFIG_BITS'd85: inc_count5 = all_events_r[85];
    `npuarc_PCT_CONFIG_BITS'd86: inc_count5 = all_events_r[86];
    `npuarc_PCT_CONFIG_BITS'd87: inc_count5 = all_events_r[87];
    `npuarc_PCT_CONFIG_BITS'd88: inc_count5 = all_events_r[88];
    `npuarc_PCT_CONFIG_BITS'd89: inc_count5 = all_events_r[89];
    `npuarc_PCT_CONFIG_BITS'd90: inc_count5 = all_events_r[90];
    `npuarc_PCT_CONFIG_BITS'd91: inc_count5 = all_events_r[91];
    `npuarc_PCT_CONFIG_BITS'd92: inc_count5 = all_events_r[92];
    `npuarc_PCT_CONFIG_BITS'd93: inc_count5 = all_events_r[93];
    `npuarc_PCT_CONFIG_BITS'd94: inc_count5 = all_events_r[94];
    `npuarc_PCT_CONFIG_BITS'd95: inc_count5 = all_events_r[95];
    `npuarc_PCT_CONFIG_BITS'd96: inc_count5 = all_events_r[96];
    `npuarc_PCT_CONFIG_BITS'd97: inc_count5 = all_events_r[97];
    `npuarc_PCT_CONFIG_BITS'd98: inc_count5 = all_events_r[98];
    `npuarc_PCT_CONFIG_BITS'd99: inc_count5 = all_events_r[99];
    `npuarc_PCT_CONFIG_BITS'd100: inc_count5 = all_events_r[100];
    `npuarc_PCT_CONFIG_BITS'd101: inc_count5 = all_events_r[101];
    `npuarc_PCT_CONFIG_BITS'd102: inc_count5 = all_events_r[102];
    `npuarc_PCT_CONFIG_BITS'd103: inc_count5 = all_events_r[103];
    `npuarc_PCT_CONFIG_BITS'd104: inc_count5 = all_events_r[104];
    `npuarc_PCT_CONFIG_BITS'd105: inc_count5 = all_events_r[105];
    `npuarc_PCT_CONFIG_BITS'd106: inc_count5 = all_events_r[106];
    `npuarc_PCT_CONFIG_BITS'd107: inc_count5 = all_events_r[107];
    `npuarc_PCT_CONFIG_BITS'd108: inc_count5 = all_events_r[108];
    `npuarc_PCT_CONFIG_BITS'd109: inc_count5 = all_events_r[109];
    `npuarc_PCT_CONFIG_BITS'd110: inc_count5 = all_events_r[110];
    `npuarc_PCT_CONFIG_BITS'd111: inc_count5 = all_events_r[111];
    `npuarc_PCT_CONFIG_BITS'd112: inc_count5 = all_events_r[112];
    `npuarc_PCT_CONFIG_BITS'd113: inc_count5 = all_events_r[113];
    `npuarc_PCT_CONFIG_BITS'd114: inc_count5 = all_events_r[114];
    `npuarc_PCT_CONFIG_BITS'd115: inc_count5 = all_events_r[115];
    `npuarc_PCT_CONFIG_BITS'd116: inc_count5 = all_events_r[116];
    `npuarc_PCT_CONFIG_BITS'd117: inc_count5 = all_events_r[117];
    `npuarc_PCT_CONFIG_BITS'd118: inc_count5 = all_events_r[118];
    `npuarc_PCT_CONFIG_BITS'd119: inc_count5 = all_events_r[119];
    `npuarc_PCT_CONFIG_BITS'd120: inc_count5 = all_events_r[120];
    `npuarc_PCT_CONFIG_BITS'd121: inc_count5 = all_events_r[121];
    `npuarc_PCT_CONFIG_BITS'd122: inc_count5 = all_events_r[122];
    `npuarc_PCT_CONFIG_BITS'd123: inc_count5 = all_events_r[123];
    `npuarc_PCT_CONFIG_BITS'd124: inc_count5 = all_events_r[124];
    `npuarc_PCT_CONFIG_BITS'd125: inc_count5 = all_events_r[125];
    `npuarc_PCT_CONFIG_BITS'd126: inc_count5 = all_events_r[126];
    default: inc_count5 = 1'b0;
    endcase
    
    case (config6_r[`npuarc_PCT_CONFIG_RANGE])
    `npuarc_PCT_CONFIG_BITS'd0: inc_count6 = all_events_r[0];
    `npuarc_PCT_CONFIG_BITS'd1: inc_count6 = all_events_r[1];
    `npuarc_PCT_CONFIG_BITS'd2: inc_count6 = all_events_r[2];
    `npuarc_PCT_CONFIG_BITS'd3: inc_count6 = all_events_r[3];
    `npuarc_PCT_CONFIG_BITS'd4: inc_count6 = all_events_r[4];
    `npuarc_PCT_CONFIG_BITS'd5: inc_count6 = all_events_r[5];
    `npuarc_PCT_CONFIG_BITS'd6: inc_count6 = all_events_r[6];
    `npuarc_PCT_CONFIG_BITS'd7: inc_count6 = all_events_r[7];
    `npuarc_PCT_CONFIG_BITS'd8: inc_count6 = all_events_r[8];
    `npuarc_PCT_CONFIG_BITS'd9: inc_count6 = all_events_r[9];
    `npuarc_PCT_CONFIG_BITS'd10: inc_count6 = all_events_r[10];
    `npuarc_PCT_CONFIG_BITS'd11: inc_count6 = all_events_r[11];
    `npuarc_PCT_CONFIG_BITS'd12: inc_count6 = all_events_r[12];
    `npuarc_PCT_CONFIG_BITS'd13: inc_count6 = all_events_r[13];
    `npuarc_PCT_CONFIG_BITS'd14: inc_count6 = all_events_r[14];
    `npuarc_PCT_CONFIG_BITS'd15: inc_count6 = all_events_r[15];
    `npuarc_PCT_CONFIG_BITS'd16: inc_count6 = all_events_r[16];
    `npuarc_PCT_CONFIG_BITS'd17: inc_count6 = all_events_r[17];
    `npuarc_PCT_CONFIG_BITS'd18: inc_count6 = all_events_r[18];
    `npuarc_PCT_CONFIG_BITS'd19: inc_count6 = all_events_r[19];
    `npuarc_PCT_CONFIG_BITS'd20: inc_count6 = all_events_r[20];
    `npuarc_PCT_CONFIG_BITS'd21: inc_count6 = all_events_r[21];
    `npuarc_PCT_CONFIG_BITS'd22: inc_count6 = all_events_r[22];
    `npuarc_PCT_CONFIG_BITS'd23: inc_count6 = all_events_r[23];
    `npuarc_PCT_CONFIG_BITS'd24: inc_count6 = all_events_r[24];
    `npuarc_PCT_CONFIG_BITS'd25: inc_count6 = all_events_r[25];
    `npuarc_PCT_CONFIG_BITS'd26: inc_count6 = all_events_r[26];
    `npuarc_PCT_CONFIG_BITS'd27: inc_count6 = all_events_r[27];
    `npuarc_PCT_CONFIG_BITS'd28: inc_count6 = all_events_r[28];
    `npuarc_PCT_CONFIG_BITS'd29: inc_count6 = all_events_r[29];
    `npuarc_PCT_CONFIG_BITS'd30: inc_count6 = all_events_r[30];
    `npuarc_PCT_CONFIG_BITS'd31: inc_count6 = all_events_r[31];
    `npuarc_PCT_CONFIG_BITS'd32: inc_count6 = all_events_r[32];
    `npuarc_PCT_CONFIG_BITS'd33: inc_count6 = all_events_r[33];
    `npuarc_PCT_CONFIG_BITS'd34: inc_count6 = all_events_r[34];
    `npuarc_PCT_CONFIG_BITS'd35: inc_count6 = all_events_r[35];
    `npuarc_PCT_CONFIG_BITS'd36: inc_count6 = all_events_r[36];
    `npuarc_PCT_CONFIG_BITS'd37: inc_count6 = all_events_r[37];
    `npuarc_PCT_CONFIG_BITS'd38: inc_count6 = all_events_r[38];
    `npuarc_PCT_CONFIG_BITS'd39: inc_count6 = all_events_r[39];
    `npuarc_PCT_CONFIG_BITS'd40: inc_count6 = all_events_r[40];
    `npuarc_PCT_CONFIG_BITS'd41: inc_count6 = all_events_r[41];
    `npuarc_PCT_CONFIG_BITS'd42: inc_count6 = all_events_r[42];
    `npuarc_PCT_CONFIG_BITS'd43: inc_count6 = all_events_r[43];
    `npuarc_PCT_CONFIG_BITS'd44: inc_count6 = all_events_r[44];
    `npuarc_PCT_CONFIG_BITS'd45: inc_count6 = all_events_r[45];
    `npuarc_PCT_CONFIG_BITS'd46: inc_count6 = all_events_r[46];
    `npuarc_PCT_CONFIG_BITS'd47: inc_count6 = all_events_r[47];
    `npuarc_PCT_CONFIG_BITS'd48: inc_count6 = all_events_r[48];
    `npuarc_PCT_CONFIG_BITS'd49: inc_count6 = all_events_r[49];
    `npuarc_PCT_CONFIG_BITS'd50: inc_count6 = all_events_r[50];
    `npuarc_PCT_CONFIG_BITS'd51: inc_count6 = all_events_r[51];
    `npuarc_PCT_CONFIG_BITS'd52: inc_count6 = all_events_r[52];
    `npuarc_PCT_CONFIG_BITS'd53: inc_count6 = all_events_r[53];
    `npuarc_PCT_CONFIG_BITS'd54: inc_count6 = all_events_r[54];
    `npuarc_PCT_CONFIG_BITS'd55: inc_count6 = all_events_r[55];
    `npuarc_PCT_CONFIG_BITS'd56: inc_count6 = all_events_r[56];
    `npuarc_PCT_CONFIG_BITS'd57: inc_count6 = all_events_r[57];
    `npuarc_PCT_CONFIG_BITS'd58: inc_count6 = all_events_r[58];
    `npuarc_PCT_CONFIG_BITS'd59: inc_count6 = all_events_r[59];
    `npuarc_PCT_CONFIG_BITS'd60: inc_count6 = all_events_r[60];
    `npuarc_PCT_CONFIG_BITS'd61: inc_count6 = all_events_r[61];
    `npuarc_PCT_CONFIG_BITS'd62: inc_count6 = all_events_r[62];
    `npuarc_PCT_CONFIG_BITS'd63: inc_count6 = all_events_r[63];
    `npuarc_PCT_CONFIG_BITS'd64: inc_count6 = all_events_r[64];
    `npuarc_PCT_CONFIG_BITS'd65: inc_count6 = all_events_r[65];
    `npuarc_PCT_CONFIG_BITS'd66: inc_count6 = all_events_r[66];
    `npuarc_PCT_CONFIG_BITS'd67: inc_count6 = all_events_r[67];
    `npuarc_PCT_CONFIG_BITS'd68: inc_count6 = all_events_r[68];
    `npuarc_PCT_CONFIG_BITS'd69: inc_count6 = all_events_r[69];
    `npuarc_PCT_CONFIG_BITS'd70: inc_count6 = all_events_r[70];
    `npuarc_PCT_CONFIG_BITS'd71: inc_count6 = all_events_r[71];
    `npuarc_PCT_CONFIG_BITS'd72: inc_count6 = all_events_r[72];
    `npuarc_PCT_CONFIG_BITS'd73: inc_count6 = all_events_r[73];
    `npuarc_PCT_CONFIG_BITS'd74: inc_count6 = all_events_r[74];
    `npuarc_PCT_CONFIG_BITS'd75: inc_count6 = all_events_r[75];
    `npuarc_PCT_CONFIG_BITS'd76: inc_count6 = all_events_r[76];
    `npuarc_PCT_CONFIG_BITS'd77: inc_count6 = all_events_r[77];
    `npuarc_PCT_CONFIG_BITS'd78: inc_count6 = all_events_r[78];
    `npuarc_PCT_CONFIG_BITS'd79: inc_count6 = all_events_r[79];
    `npuarc_PCT_CONFIG_BITS'd80: inc_count6 = all_events_r[80];
    `npuarc_PCT_CONFIG_BITS'd81: inc_count6 = all_events_r[81];
    `npuarc_PCT_CONFIG_BITS'd82: inc_count6 = all_events_r[82];
    `npuarc_PCT_CONFIG_BITS'd83: inc_count6 = all_events_r[83];
    `npuarc_PCT_CONFIG_BITS'd84: inc_count6 = all_events_r[84];
    `npuarc_PCT_CONFIG_BITS'd85: inc_count6 = all_events_r[85];
    `npuarc_PCT_CONFIG_BITS'd86: inc_count6 = all_events_r[86];
    `npuarc_PCT_CONFIG_BITS'd87: inc_count6 = all_events_r[87];
    `npuarc_PCT_CONFIG_BITS'd88: inc_count6 = all_events_r[88];
    `npuarc_PCT_CONFIG_BITS'd89: inc_count6 = all_events_r[89];
    `npuarc_PCT_CONFIG_BITS'd90: inc_count6 = all_events_r[90];
    `npuarc_PCT_CONFIG_BITS'd91: inc_count6 = all_events_r[91];
    `npuarc_PCT_CONFIG_BITS'd92: inc_count6 = all_events_r[92];
    `npuarc_PCT_CONFIG_BITS'd93: inc_count6 = all_events_r[93];
    `npuarc_PCT_CONFIG_BITS'd94: inc_count6 = all_events_r[94];
    `npuarc_PCT_CONFIG_BITS'd95: inc_count6 = all_events_r[95];
    `npuarc_PCT_CONFIG_BITS'd96: inc_count6 = all_events_r[96];
    `npuarc_PCT_CONFIG_BITS'd97: inc_count6 = all_events_r[97];
    `npuarc_PCT_CONFIG_BITS'd98: inc_count6 = all_events_r[98];
    `npuarc_PCT_CONFIG_BITS'd99: inc_count6 = all_events_r[99];
    `npuarc_PCT_CONFIG_BITS'd100: inc_count6 = all_events_r[100];
    `npuarc_PCT_CONFIG_BITS'd101: inc_count6 = all_events_r[101];
    `npuarc_PCT_CONFIG_BITS'd102: inc_count6 = all_events_r[102];
    `npuarc_PCT_CONFIG_BITS'd103: inc_count6 = all_events_r[103];
    `npuarc_PCT_CONFIG_BITS'd104: inc_count6 = all_events_r[104];
    `npuarc_PCT_CONFIG_BITS'd105: inc_count6 = all_events_r[105];
    `npuarc_PCT_CONFIG_BITS'd106: inc_count6 = all_events_r[106];
    `npuarc_PCT_CONFIG_BITS'd107: inc_count6 = all_events_r[107];
    `npuarc_PCT_CONFIG_BITS'd108: inc_count6 = all_events_r[108];
    `npuarc_PCT_CONFIG_BITS'd109: inc_count6 = all_events_r[109];
    `npuarc_PCT_CONFIG_BITS'd110: inc_count6 = all_events_r[110];
    `npuarc_PCT_CONFIG_BITS'd111: inc_count6 = all_events_r[111];
    `npuarc_PCT_CONFIG_BITS'd112: inc_count6 = all_events_r[112];
    `npuarc_PCT_CONFIG_BITS'd113: inc_count6 = all_events_r[113];
    `npuarc_PCT_CONFIG_BITS'd114: inc_count6 = all_events_r[114];
    `npuarc_PCT_CONFIG_BITS'd115: inc_count6 = all_events_r[115];
    `npuarc_PCT_CONFIG_BITS'd116: inc_count6 = all_events_r[116];
    `npuarc_PCT_CONFIG_BITS'd117: inc_count6 = all_events_r[117];
    `npuarc_PCT_CONFIG_BITS'd118: inc_count6 = all_events_r[118];
    `npuarc_PCT_CONFIG_BITS'd119: inc_count6 = all_events_r[119];
    `npuarc_PCT_CONFIG_BITS'd120: inc_count6 = all_events_r[120];
    `npuarc_PCT_CONFIG_BITS'd121: inc_count6 = all_events_r[121];
    `npuarc_PCT_CONFIG_BITS'd122: inc_count6 = all_events_r[122];
    `npuarc_PCT_CONFIG_BITS'd123: inc_count6 = all_events_r[123];
    `npuarc_PCT_CONFIG_BITS'd124: inc_count6 = all_events_r[124];
    `npuarc_PCT_CONFIG_BITS'd125: inc_count6 = all_events_r[125];
    `npuarc_PCT_CONFIG_BITS'd126: inc_count6 = all_events_r[126];
    default: inc_count6 = 1'b0;
    endcase
    
    case (config7_r[`npuarc_PCT_CONFIG_RANGE])
    `npuarc_PCT_CONFIG_BITS'd0: inc_count7 = all_events_r[0];
    `npuarc_PCT_CONFIG_BITS'd1: inc_count7 = all_events_r[1];
    `npuarc_PCT_CONFIG_BITS'd2: inc_count7 = all_events_r[2];
    `npuarc_PCT_CONFIG_BITS'd3: inc_count7 = all_events_r[3];
    `npuarc_PCT_CONFIG_BITS'd4: inc_count7 = all_events_r[4];
    `npuarc_PCT_CONFIG_BITS'd5: inc_count7 = all_events_r[5];
    `npuarc_PCT_CONFIG_BITS'd6: inc_count7 = all_events_r[6];
    `npuarc_PCT_CONFIG_BITS'd7: inc_count7 = all_events_r[7];
    `npuarc_PCT_CONFIG_BITS'd8: inc_count7 = all_events_r[8];
    `npuarc_PCT_CONFIG_BITS'd9: inc_count7 = all_events_r[9];
    `npuarc_PCT_CONFIG_BITS'd10: inc_count7 = all_events_r[10];
    `npuarc_PCT_CONFIG_BITS'd11: inc_count7 = all_events_r[11];
    `npuarc_PCT_CONFIG_BITS'd12: inc_count7 = all_events_r[12];
    `npuarc_PCT_CONFIG_BITS'd13: inc_count7 = all_events_r[13];
    `npuarc_PCT_CONFIG_BITS'd14: inc_count7 = all_events_r[14];
    `npuarc_PCT_CONFIG_BITS'd15: inc_count7 = all_events_r[15];
    `npuarc_PCT_CONFIG_BITS'd16: inc_count7 = all_events_r[16];
    `npuarc_PCT_CONFIG_BITS'd17: inc_count7 = all_events_r[17];
    `npuarc_PCT_CONFIG_BITS'd18: inc_count7 = all_events_r[18];
    `npuarc_PCT_CONFIG_BITS'd19: inc_count7 = all_events_r[19];
    `npuarc_PCT_CONFIG_BITS'd20: inc_count7 = all_events_r[20];
    `npuarc_PCT_CONFIG_BITS'd21: inc_count7 = all_events_r[21];
    `npuarc_PCT_CONFIG_BITS'd22: inc_count7 = all_events_r[22];
    `npuarc_PCT_CONFIG_BITS'd23: inc_count7 = all_events_r[23];
    `npuarc_PCT_CONFIG_BITS'd24: inc_count7 = all_events_r[24];
    `npuarc_PCT_CONFIG_BITS'd25: inc_count7 = all_events_r[25];
    `npuarc_PCT_CONFIG_BITS'd26: inc_count7 = all_events_r[26];
    `npuarc_PCT_CONFIG_BITS'd27: inc_count7 = all_events_r[27];
    `npuarc_PCT_CONFIG_BITS'd28: inc_count7 = all_events_r[28];
    `npuarc_PCT_CONFIG_BITS'd29: inc_count7 = all_events_r[29];
    `npuarc_PCT_CONFIG_BITS'd30: inc_count7 = all_events_r[30];
    `npuarc_PCT_CONFIG_BITS'd31: inc_count7 = all_events_r[31];
    `npuarc_PCT_CONFIG_BITS'd32: inc_count7 = all_events_r[32];
    `npuarc_PCT_CONFIG_BITS'd33: inc_count7 = all_events_r[33];
    `npuarc_PCT_CONFIG_BITS'd34: inc_count7 = all_events_r[34];
    `npuarc_PCT_CONFIG_BITS'd35: inc_count7 = all_events_r[35];
    `npuarc_PCT_CONFIG_BITS'd36: inc_count7 = all_events_r[36];
    `npuarc_PCT_CONFIG_BITS'd37: inc_count7 = all_events_r[37];
    `npuarc_PCT_CONFIG_BITS'd38: inc_count7 = all_events_r[38];
    `npuarc_PCT_CONFIG_BITS'd39: inc_count7 = all_events_r[39];
    `npuarc_PCT_CONFIG_BITS'd40: inc_count7 = all_events_r[40];
    `npuarc_PCT_CONFIG_BITS'd41: inc_count7 = all_events_r[41];
    `npuarc_PCT_CONFIG_BITS'd42: inc_count7 = all_events_r[42];
    `npuarc_PCT_CONFIG_BITS'd43: inc_count7 = all_events_r[43];
    `npuarc_PCT_CONFIG_BITS'd44: inc_count7 = all_events_r[44];
    `npuarc_PCT_CONFIG_BITS'd45: inc_count7 = all_events_r[45];
    `npuarc_PCT_CONFIG_BITS'd46: inc_count7 = all_events_r[46];
    `npuarc_PCT_CONFIG_BITS'd47: inc_count7 = all_events_r[47];
    `npuarc_PCT_CONFIG_BITS'd48: inc_count7 = all_events_r[48];
    `npuarc_PCT_CONFIG_BITS'd49: inc_count7 = all_events_r[49];
    `npuarc_PCT_CONFIG_BITS'd50: inc_count7 = all_events_r[50];
    `npuarc_PCT_CONFIG_BITS'd51: inc_count7 = all_events_r[51];
    `npuarc_PCT_CONFIG_BITS'd52: inc_count7 = all_events_r[52];
    `npuarc_PCT_CONFIG_BITS'd53: inc_count7 = all_events_r[53];
    `npuarc_PCT_CONFIG_BITS'd54: inc_count7 = all_events_r[54];
    `npuarc_PCT_CONFIG_BITS'd55: inc_count7 = all_events_r[55];
    `npuarc_PCT_CONFIG_BITS'd56: inc_count7 = all_events_r[56];
    `npuarc_PCT_CONFIG_BITS'd57: inc_count7 = all_events_r[57];
    `npuarc_PCT_CONFIG_BITS'd58: inc_count7 = all_events_r[58];
    `npuarc_PCT_CONFIG_BITS'd59: inc_count7 = all_events_r[59];
    `npuarc_PCT_CONFIG_BITS'd60: inc_count7 = all_events_r[60];
    `npuarc_PCT_CONFIG_BITS'd61: inc_count7 = all_events_r[61];
    `npuarc_PCT_CONFIG_BITS'd62: inc_count7 = all_events_r[62];
    `npuarc_PCT_CONFIG_BITS'd63: inc_count7 = all_events_r[63];
    `npuarc_PCT_CONFIG_BITS'd64: inc_count7 = all_events_r[64];
    `npuarc_PCT_CONFIG_BITS'd65: inc_count7 = all_events_r[65];
    `npuarc_PCT_CONFIG_BITS'd66: inc_count7 = all_events_r[66];
    `npuarc_PCT_CONFIG_BITS'd67: inc_count7 = all_events_r[67];
    `npuarc_PCT_CONFIG_BITS'd68: inc_count7 = all_events_r[68];
    `npuarc_PCT_CONFIG_BITS'd69: inc_count7 = all_events_r[69];
    `npuarc_PCT_CONFIG_BITS'd70: inc_count7 = all_events_r[70];
    `npuarc_PCT_CONFIG_BITS'd71: inc_count7 = all_events_r[71];
    `npuarc_PCT_CONFIG_BITS'd72: inc_count7 = all_events_r[72];
    `npuarc_PCT_CONFIG_BITS'd73: inc_count7 = all_events_r[73];
    `npuarc_PCT_CONFIG_BITS'd74: inc_count7 = all_events_r[74];
    `npuarc_PCT_CONFIG_BITS'd75: inc_count7 = all_events_r[75];
    `npuarc_PCT_CONFIG_BITS'd76: inc_count7 = all_events_r[76];
    `npuarc_PCT_CONFIG_BITS'd77: inc_count7 = all_events_r[77];
    `npuarc_PCT_CONFIG_BITS'd78: inc_count7 = all_events_r[78];
    `npuarc_PCT_CONFIG_BITS'd79: inc_count7 = all_events_r[79];
    `npuarc_PCT_CONFIG_BITS'd80: inc_count7 = all_events_r[80];
    `npuarc_PCT_CONFIG_BITS'd81: inc_count7 = all_events_r[81];
    `npuarc_PCT_CONFIG_BITS'd82: inc_count7 = all_events_r[82];
    `npuarc_PCT_CONFIG_BITS'd83: inc_count7 = all_events_r[83];
    `npuarc_PCT_CONFIG_BITS'd84: inc_count7 = all_events_r[84];
    `npuarc_PCT_CONFIG_BITS'd85: inc_count7 = all_events_r[85];
    `npuarc_PCT_CONFIG_BITS'd86: inc_count7 = all_events_r[86];
    `npuarc_PCT_CONFIG_BITS'd87: inc_count7 = all_events_r[87];
    `npuarc_PCT_CONFIG_BITS'd88: inc_count7 = all_events_r[88];
    `npuarc_PCT_CONFIG_BITS'd89: inc_count7 = all_events_r[89];
    `npuarc_PCT_CONFIG_BITS'd90: inc_count7 = all_events_r[90];
    `npuarc_PCT_CONFIG_BITS'd91: inc_count7 = all_events_r[91];
    `npuarc_PCT_CONFIG_BITS'd92: inc_count7 = all_events_r[92];
    `npuarc_PCT_CONFIG_BITS'd93: inc_count7 = all_events_r[93];
    `npuarc_PCT_CONFIG_BITS'd94: inc_count7 = all_events_r[94];
    `npuarc_PCT_CONFIG_BITS'd95: inc_count7 = all_events_r[95];
    `npuarc_PCT_CONFIG_BITS'd96: inc_count7 = all_events_r[96];
    `npuarc_PCT_CONFIG_BITS'd97: inc_count7 = all_events_r[97];
    `npuarc_PCT_CONFIG_BITS'd98: inc_count7 = all_events_r[98];
    `npuarc_PCT_CONFIG_BITS'd99: inc_count7 = all_events_r[99];
    `npuarc_PCT_CONFIG_BITS'd100: inc_count7 = all_events_r[100];
    `npuarc_PCT_CONFIG_BITS'd101: inc_count7 = all_events_r[101];
    `npuarc_PCT_CONFIG_BITS'd102: inc_count7 = all_events_r[102];
    `npuarc_PCT_CONFIG_BITS'd103: inc_count7 = all_events_r[103];
    `npuarc_PCT_CONFIG_BITS'd104: inc_count7 = all_events_r[104];
    `npuarc_PCT_CONFIG_BITS'd105: inc_count7 = all_events_r[105];
    `npuarc_PCT_CONFIG_BITS'd106: inc_count7 = all_events_r[106];
    `npuarc_PCT_CONFIG_BITS'd107: inc_count7 = all_events_r[107];
    `npuarc_PCT_CONFIG_BITS'd108: inc_count7 = all_events_r[108];
    `npuarc_PCT_CONFIG_BITS'd109: inc_count7 = all_events_r[109];
    `npuarc_PCT_CONFIG_BITS'd110: inc_count7 = all_events_r[110];
    `npuarc_PCT_CONFIG_BITS'd111: inc_count7 = all_events_r[111];
    `npuarc_PCT_CONFIG_BITS'd112: inc_count7 = all_events_r[112];
    `npuarc_PCT_CONFIG_BITS'd113: inc_count7 = all_events_r[113];
    `npuarc_PCT_CONFIG_BITS'd114: inc_count7 = all_events_r[114];
    `npuarc_PCT_CONFIG_BITS'd115: inc_count7 = all_events_r[115];
    `npuarc_PCT_CONFIG_BITS'd116: inc_count7 = all_events_r[116];
    `npuarc_PCT_CONFIG_BITS'd117: inc_count7 = all_events_r[117];
    `npuarc_PCT_CONFIG_BITS'd118: inc_count7 = all_events_r[118];
    `npuarc_PCT_CONFIG_BITS'd119: inc_count7 = all_events_r[119];
    `npuarc_PCT_CONFIG_BITS'd120: inc_count7 = all_events_r[120];
    `npuarc_PCT_CONFIG_BITS'd121: inc_count7 = all_events_r[121];
    `npuarc_PCT_CONFIG_BITS'd122: inc_count7 = all_events_r[122];
    `npuarc_PCT_CONFIG_BITS'd123: inc_count7 = all_events_r[123];
    `npuarc_PCT_CONFIG_BITS'd124: inc_count7 = all_events_r[124];
    `npuarc_PCT_CONFIG_BITS'd125: inc_count7 = all_events_r[125];
    `npuarc_PCT_CONFIG_BITS'd126: inc_count7 = all_events_r[126];
    default: inc_count7 = 1'b0;
    endcase
    



       p_vbslot   = 3'd0;


    case (config0_r[`npuarc_PCT_CONFIG_RANGE])
    `npuarc_PCT_CONFIG_BITS'd34: count0_payload = p_vbslot  ;
    default: count0_payload = 3'b1;
    endcase
    
    case (config1_r[`npuarc_PCT_CONFIG_RANGE])
    `npuarc_PCT_CONFIG_BITS'd34: count1_payload = p_vbslot  ;
    default: count1_payload = 3'b1;
    endcase
    
    case (config2_r[`npuarc_PCT_CONFIG_RANGE])
    `npuarc_PCT_CONFIG_BITS'd34: count2_payload = p_vbslot  ;
    default: count2_payload = 3'b1;
    endcase
    
    case (config3_r[`npuarc_PCT_CONFIG_RANGE])
    `npuarc_PCT_CONFIG_BITS'd34: count3_payload = p_vbslot  ;
    default: count3_payload = 3'b1;
    endcase
    
    case (config4_r[`npuarc_PCT_CONFIG_RANGE])
    `npuarc_PCT_CONFIG_BITS'd34: count4_payload = p_vbslot  ;
    default: count4_payload = 3'b1;
    endcase
    
    case (config5_r[`npuarc_PCT_CONFIG_RANGE])
    `npuarc_PCT_CONFIG_BITS'd34: count5_payload = p_vbslot  ;
    default: count5_payload = 3'b1;
    endcase
    
    case (config6_r[`npuarc_PCT_CONFIG_RANGE])
    `npuarc_PCT_CONFIG_BITS'd34: count6_payload = p_vbslot  ;
    default: count6_payload = 3'b1;
    endcase
    
    case (config7_r[`npuarc_PCT_CONFIG_RANGE])
    `npuarc_PCT_CONFIG_BITS'd34: count7_payload = p_vbslot  ;
    default: count7_payload = 3'b1;
    endcase
    


    int_active_nxt      = `npuarc_DATA_SIZE'd0;
    int_active_nxt [0] = 1'b1
                        & i_global_en
                        & count_cfg0_en
                        & pct_int_ctrl_r [0]
                        & (count0_r >= int_cnt0_r)
                        ;

    
    int_active_nxt [1] = 1'b1
                        & i_global_en
                        & count_cfg1_en
                        & pct_int_ctrl_r [1]
                        & (count1_r >= int_cnt1_r)
                        ;

    
    int_active_nxt [2] = 1'b1
                        & i_global_en
                        & count_cfg2_en
                        & pct_int_ctrl_r [2]
                        & (count2_r >= int_cnt2_r)
                        ;

    
    int_active_nxt [3] = 1'b1
                        & i_global_en
                        & count_cfg3_en
                        & pct_int_ctrl_r [3]
                        & (count3_r >= int_cnt3_r)
                        ;

    
    int_active_nxt [4] = 1'b1
                        & i_global_en
                        & count_cfg4_en
                        & pct_int_ctrl_r [4]
                        & (count4_r >= int_cnt4_r)
                        ;

    
    int_active_nxt [5] = 1'b1
                        & i_global_en
                        & count_cfg5_en
                        & pct_int_ctrl_r [5]
                        & (count5_r >= int_cnt5_r)
                        ;

    
    int_active_nxt [6] = 1'b1
                        & i_global_en
                        & count_cfg6_en
                        & pct_int_ctrl_r [6]
                        & (count6_r >= int_cnt6_r)
                        ;

    
    int_active_nxt [7] = 1'b1
                        & i_global_en
                        & count_cfg7_en
                        & pct_int_ctrl_r [7]
                        & (count7_r >= int_cnt7_r)
                        ;

    
  pct_int_overflow_r        = `npuarc_IRQ_M'b0;
  pct_int_overflow_r[`npuarc_PCT_IRQ] = pct_int_act_2cycle_r;
end



////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous logic to determine the next counter values                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : count_nxt_PROC

  if  (pct_control_sel & wa_sr_data_r [16])
    begin
    count0_nxt = 48'd0;
    count1_nxt = 48'd0;
    count2_nxt = 48'd0;
    count3_nxt = 48'd0;
    count4_nxt = 48'd0;
    count5_nxt = 48'd0;
    count6_nxt = 48'd0;
    count7_nxt = 48'd0;
    end
  else if (pct_countl_wen || pct_counth_wen)
    begin
    count0_nxt = (countl0_wen == 1'b1)
                  ? {count0_r [47:32], wa_sr_data_r [`npuarc_DATA_RANGE]}
                  : {wa_sr_data_r [15:0],  count0_r [`npuarc_DATA_RANGE]}
                  ;
    count1_nxt = (countl1_wen == 1'b1)
                  ? {count1_r [47:32], wa_sr_data_r [`npuarc_DATA_RANGE]}
                  : {wa_sr_data_r [15:0],  count1_r [`npuarc_DATA_RANGE]}
                  ;
    count2_nxt = (countl2_wen == 1'b1)
                  ? {count2_r [47:32], wa_sr_data_r [`npuarc_DATA_RANGE]}
                  : {wa_sr_data_r [15:0],  count2_r [`npuarc_DATA_RANGE]}
                  ;
    count3_nxt = (countl3_wen == 1'b1)
                  ? {count3_r [47:32], wa_sr_data_r [`npuarc_DATA_RANGE]}
                  : {wa_sr_data_r [15:0],  count3_r [`npuarc_DATA_RANGE]}
                  ;
    count4_nxt = (countl4_wen == 1'b1)
                  ? {count4_r [47:32], wa_sr_data_r [`npuarc_DATA_RANGE]}
                  : {wa_sr_data_r [15:0],  count4_r [`npuarc_DATA_RANGE]}
                  ;
    count5_nxt = (countl5_wen == 1'b1)
                  ? {count5_r [47:32], wa_sr_data_r [`npuarc_DATA_RANGE]}
                  : {wa_sr_data_r [15:0],  count5_r [`npuarc_DATA_RANGE]}
                  ;
    count6_nxt = (countl6_wen == 1'b1)
                  ? {count6_r [47:32], wa_sr_data_r [`npuarc_DATA_RANGE]}
                  : {wa_sr_data_r [15:0],  count6_r [`npuarc_DATA_RANGE]}
                  ;
    count7_nxt = (countl7_wen == 1'b1)
                  ? {count7_r [47:32], wa_sr_data_r [`npuarc_DATA_RANGE]}
                  : {wa_sr_data_r [15:0],  count7_r [`npuarc_DATA_RANGE]}
                  ;
    end
  else
    begin
// spyglass disable_block W164a
// SMD: LHS width is less than the RHS width
// SJ:  Count values wrap to zero is safe, behavior documented; Explcit action not needed
// spyglass disable_block W484
// SMD: Possible assignment overflow: lhs width 48 (Expr: 'count0_nxt') should be greater than rhs width 48
// SJ:  Count values wrap to zero is safe, behavior documented; Explcit action not needed
// leda W484 off   
// LMD: Possible loss of carry/borrow in addition/subtraction LHS : 48, RHS : 49
// leda BTTF_D002 off
// LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y  
// LJ:  address addition is modulo 2^32, so carry-out should be ignored
    count0_nxt = count0_r + count0_payload;
    count1_nxt = count1_r + count1_payload;
    count2_nxt = count2_r + count2_payload;
    count3_nxt = count3_r + count3_payload;
    count4_nxt = count4_r + count4_payload;
    count5_nxt = count5_r + count5_payload;
    count6_nxt = count6_r + count6_payload;
    count7_nxt = count7_r + count7_payload;
// leda BTTF_D002 on
// leda W484 on   
// spyglass enable_block W484   
// spyglass enable_block W164a   
    end
end


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous blocks defining PCT registers                              //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
// spyglass disable_block W484 W164a
// SMD: Possible assignment overflow: lhs width 48 (Expr: 'count0_r') should be great
// SJ:  Count values wrap to zero is safe, behavior documented; Explcit action not needed

////////////////////////////////////////////////////////////////////////////
// Synchronous block defining count0_r
//
always @(posedge clk or posedge rst_a)
begin : pct_count0_PROC
  if (rst_a == 1'b1) begin
    count0_r   <= 48'd0;
  end
  else if (count0_wen == 1'b1) begin
    count0_r <= count0_nxt;
  end
end
////////////////////////////////////////////////////////////////////////////
// Synchronous block defining count1_r
//
always @(posedge clk or posedge rst_a)
begin : pct_count1_PROC
  if (rst_a == 1'b1) begin
    count1_r   <= 48'd0;
  end
  else if (count1_wen == 1'b1) begin
    count1_r <= count1_nxt;
  end
end
////////////////////////////////////////////////////////////////////////////
// Synchronous block defining count2_r
//
always @(posedge clk or posedge rst_a)
begin : pct_count2_PROC
  if (rst_a == 1'b1) begin
    count2_r   <= 48'd0;
  end
  else if (count2_wen == 1'b1) begin
    count2_r <= count2_nxt;
  end
end
////////////////////////////////////////////////////////////////////////////
// Synchronous block defining count3_r
//
always @(posedge clk or posedge rst_a)
begin : pct_count3_PROC
  if (rst_a == 1'b1) begin
    count3_r   <= 48'd0;
  end
  else if (count3_wen == 1'b1) begin
    count3_r <= count3_nxt;
  end
end
////////////////////////////////////////////////////////////////////////////
// Synchronous block defining count4_r
//
always @(posedge clk or posedge rst_a)
begin : pct_count4_PROC
  if (rst_a == 1'b1) begin
    count4_r   <= 48'd0;
  end
  else if (count4_wen == 1'b1) begin
    count4_r <= count4_nxt;
  end
end
////////////////////////////////////////////////////////////////////////////
// Synchronous block defining count5_r
//
always @(posedge clk or posedge rst_a)
begin : pct_count5_PROC
  if (rst_a == 1'b1) begin
    count5_r   <= 48'd0;
  end
  else if (count5_wen == 1'b1) begin
    count5_r <= count5_nxt;
  end
end
////////////////////////////////////////////////////////////////////////////
// Synchronous block defining count6_r
//
always @(posedge clk or posedge rst_a)
begin : pct_count6_PROC
  if (rst_a == 1'b1) begin
    count6_r   <= 48'd0;
  end
  else if (count6_wen == 1'b1) begin
    count6_r <= count6_nxt;
  end
end
////////////////////////////////////////////////////////////////////////////
// Synchronous block defining count7_r
//
always @(posedge clk or posedge rst_a)
begin : pct_count7_PROC
  if (rst_a == 1'b1) begin
    count7_r   <= 48'd0;
  end
  else if (count7_wen == 1'b1) begin
    count7_r <= count7_nxt;
  end
end
// spyglass enable_block W484 W164a

////////////////////////////////////////////////////////////////////////////
// Synchronous block defining snap0_r
//
always @(posedge clk or posedge rst_a)
begin : pct_snap0_PROC
  if (rst_a == 1'b1)
    snap0_r <= 48'd0;
  else if (snap0_wen == 1'b1)
    snap0_r <= count0_r;
end

////////////////////////////////////////////////////////////////////////////
// Synchronous block defining snap1_r
//
always @(posedge clk or posedge rst_a)
begin : pct_snap1_PROC
  if (rst_a == 1'b1)
    snap1_r <= 48'd0;
  else if (snap1_wen == 1'b1)
    snap1_r <= count1_r;
end

////////////////////////////////////////////////////////////////////////////
// Synchronous block defining snap2_r
//
always @(posedge clk or posedge rst_a)
begin : pct_snap2_PROC
  if (rst_a == 1'b1)
    snap2_r <= 48'd0;
  else if (snap2_wen == 1'b1)
    snap2_r <= count2_r;
end

////////////////////////////////////////////////////////////////////////////
// Synchronous block defining snap3_r
//
always @(posedge clk or posedge rst_a)
begin : pct_snap3_PROC
  if (rst_a == 1'b1)
    snap3_r <= 48'd0;
  else if (snap3_wen == 1'b1)
    snap3_r <= count3_r;
end

////////////////////////////////////////////////////////////////////////////
// Synchronous block defining snap4_r
//
always @(posedge clk or posedge rst_a)
begin : pct_snap4_PROC
  if (rst_a == 1'b1)
    snap4_r <= 48'd0;
  else if (snap4_wen == 1'b1)
    snap4_r <= count4_r;
end

////////////////////////////////////////////////////////////////////////////
// Synchronous block defining snap5_r
//
always @(posedge clk or posedge rst_a)
begin : pct_snap5_PROC
  if (rst_a == 1'b1)
    snap5_r <= 48'd0;
  else if (snap5_wen == 1'b1)
    snap5_r <= count5_r;
end

////////////////////////////////////////////////////////////////////////////
// Synchronous block defining snap6_r
//
always @(posedge clk or posedge rst_a)
begin : pct_snap6_PROC
  if (rst_a == 1'b1)
    snap6_r <= 48'd0;
  else if (snap6_wen == 1'b1)
    snap6_r <= count6_r;
end

////////////////////////////////////////////////////////////////////////////
// Synchronous block defining snap7_r
//
always @(posedge clk or posedge rst_a)
begin : pct_snap7_PROC
  if (rst_a == 1'b1)
    snap7_r <= 48'd0;
  else if (snap7_wen == 1'b1)
    snap7_r <= count7_r;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining config0_r                                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : pct_config0_PROC
  if (rst_a == 1'b1)
    config0_r <= `npuarc_DATA_SIZE'd0;
  else if (config0_wen == 1'b1)
    config0_r <= { 5'd0
                    , wa_sr_data_r [26:18]
                    , 2'b00
                    , wa_sr_data_r [15:0]
                    }
                  ;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining config1_r                                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : pct_config1_PROC
  if (rst_a == 1'b1)
    config1_r <= `npuarc_DATA_SIZE'd0;
  else if (config1_wen == 1'b1)
    config1_r <= { 5'd0
                    , wa_sr_data_r [26:18]
                    , 2'b00
                    , wa_sr_data_r [15:0]
                    }
                  ;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining config2_r                                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : pct_config2_PROC
  if (rst_a == 1'b1)
    config2_r <= `npuarc_DATA_SIZE'd0;
  else if (config2_wen == 1'b1)
    config2_r <= { 5'd0
                    , wa_sr_data_r [26:18]
                    , 2'b00
                    , wa_sr_data_r [15:0]
                    }
                  ;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining config3_r                                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : pct_config3_PROC
  if (rst_a == 1'b1)
    config3_r <= `npuarc_DATA_SIZE'd0;
  else if (config3_wen == 1'b1)
    config3_r <= { 5'd0
                    , wa_sr_data_r [26:18]
                    , 2'b00
                    , wa_sr_data_r [15:0]
                    }
                  ;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining config4_r                                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : pct_config4_PROC
  if (rst_a == 1'b1)
    config4_r <= `npuarc_DATA_SIZE'd0;
  else if (config4_wen == 1'b1)
    config4_r <= { 5'd0
                    , wa_sr_data_r [26:18]
                    , 2'b00
                    , wa_sr_data_r [15:0]
                    }
                  ;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining config5_r                                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : pct_config5_PROC
  if (rst_a == 1'b1)
    config5_r <= `npuarc_DATA_SIZE'd0;
  else if (config5_wen == 1'b1)
    config5_r <= { 5'd0
                    , wa_sr_data_r [26:18]
                    , 2'b00
                    , wa_sr_data_r [15:0]
                    }
                  ;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining config6_r                                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : pct_config6_PROC
  if (rst_a == 1'b1)
    config6_r <= `npuarc_DATA_SIZE'd0;
  else if (config6_wen == 1'b1)
    config6_r <= { 5'd0
                    , wa_sr_data_r [26:18]
                    , 2'b00
                    , wa_sr_data_r [15:0]
                    }
                  ;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining config7_r                                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : pct_config7_PROC
  if (rst_a == 1'b1)
    config7_r <= `npuarc_DATA_SIZE'd0;
  else if (config7_wen == 1'b1)
    config7_r <= { 5'd0
                    , wa_sr_data_r [26:18]
                    , 2'b00
                    , wa_sr_data_r [15:0]
                    }
                  ;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous logic to determine the next int_cnter values              //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : int_cnt_nxt_PROC

  if  (pct_control_sel & wa_sr_data_r [16])
    begin
    int_cnt0_nxt = 48'd0;
    int_cnt1_nxt = 48'd0;
    int_cnt2_nxt = 48'd0;
    int_cnt3_nxt = 48'd0;
    int_cnt4_nxt = 48'd0;
    int_cnt5_nxt = 48'd0;
    int_cnt6_nxt = 48'd0;
    int_cnt7_nxt = 48'd0;
    end
  else if (pct_int_cntl_wen || pct_int_cnth_wen)
    begin
    int_cnt0_nxt = (int_cntl0_wen == 1'b1)
                  ? {int_cnt0_r [47:32], wa_sr_data_r [`npuarc_DATA_RANGE]}
                  : {wa_sr_data_r [15:0],  int_cnt0_r [`npuarc_DATA_RANGE]}
                  ;
    int_cnt1_nxt = (int_cntl1_wen == 1'b1)
                  ? {int_cnt1_r [47:32], wa_sr_data_r [`npuarc_DATA_RANGE]}
                  : {wa_sr_data_r [15:0],  int_cnt1_r [`npuarc_DATA_RANGE]}
                  ;
    int_cnt2_nxt = (int_cntl2_wen == 1'b1)
                  ? {int_cnt2_r [47:32], wa_sr_data_r [`npuarc_DATA_RANGE]}
                  : {wa_sr_data_r [15:0],  int_cnt2_r [`npuarc_DATA_RANGE]}
                  ;
    int_cnt3_nxt = (int_cntl3_wen == 1'b1)
                  ? {int_cnt3_r [47:32], wa_sr_data_r [`npuarc_DATA_RANGE]}
                  : {wa_sr_data_r [15:0],  int_cnt3_r [`npuarc_DATA_RANGE]}
                  ;
    int_cnt4_nxt = (int_cntl4_wen == 1'b1)
                  ? {int_cnt4_r [47:32], wa_sr_data_r [`npuarc_DATA_RANGE]}
                  : {wa_sr_data_r [15:0],  int_cnt4_r [`npuarc_DATA_RANGE]}
                  ;
    int_cnt5_nxt = (int_cntl5_wen == 1'b1)
                  ? {int_cnt5_r [47:32], wa_sr_data_r [`npuarc_DATA_RANGE]}
                  : {wa_sr_data_r [15:0],  int_cnt5_r [`npuarc_DATA_RANGE]}
                  ;
    int_cnt6_nxt = (int_cntl6_wen == 1'b1)
                  ? {int_cnt6_r [47:32], wa_sr_data_r [`npuarc_DATA_RANGE]}
                  : {wa_sr_data_r [15:0],  int_cnt6_r [`npuarc_DATA_RANGE]}
                  ;
    int_cnt7_nxt = (int_cntl7_wen == 1'b1)
                  ? {int_cnt7_r [47:32], wa_sr_data_r [`npuarc_DATA_RANGE]}
                  : {wa_sr_data_r [15:0],  int_cnt7_r [`npuarc_DATA_RANGE]}
                  ;
    end
  else
    begin
// leda W484 off
// leda BTTF_D002 off
// LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y  
// LJ:  address addition is modulo 2^32, so carry-out should be ignored
    int_cnt0_nxt = int_cnt0_r + 1;
    int_cnt1_nxt = int_cnt1_r + 1;
    int_cnt2_nxt = int_cnt2_r + 1;
    int_cnt3_nxt = int_cnt3_r + 1;
    int_cnt4_nxt = int_cnt4_r + 1;
    int_cnt5_nxt = int_cnt5_r + 1;
    int_cnt6_nxt = int_cnt6_r + 1;
    int_cnt7_nxt = int_cnt7_r + 1;
// leda BTTF_D002 on
// leda W484 on
    end
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining int_cnt0_r                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : pct_int_cnt0_PROC
  if (rst_a == 1'b1)
    int_cnt0_r <= 48'd0;
  else if ((int_cntl0_wen == 1'b1) || (int_cnth0_wen == 1'b1))
    int_cnt0_r <= int_cnt0_nxt;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining int_cnt1_r                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : pct_int_cnt1_PROC
  if (rst_a == 1'b1)
    int_cnt1_r <= 48'd0;
  else if ((int_cntl1_wen == 1'b1) || (int_cnth1_wen == 1'b1))
    int_cnt1_r <= int_cnt1_nxt;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining int_cnt2_r                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : pct_int_cnt2_PROC
  if (rst_a == 1'b1)
    int_cnt2_r <= 48'd0;
  else if ((int_cntl2_wen == 1'b1) || (int_cnth2_wen == 1'b1))
    int_cnt2_r <= int_cnt2_nxt;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining int_cnt3_r                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : pct_int_cnt3_PROC
  if (rst_a == 1'b1)
    int_cnt3_r <= 48'd0;
  else if ((int_cntl3_wen == 1'b1) || (int_cnth3_wen == 1'b1))
    int_cnt3_r <= int_cnt3_nxt;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining int_cnt4_r                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : pct_int_cnt4_PROC
  if (rst_a == 1'b1)
    int_cnt4_r <= 48'd0;
  else if ((int_cntl4_wen == 1'b1) || (int_cnth4_wen == 1'b1))
    int_cnt4_r <= int_cnt4_nxt;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining int_cnt5_r                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : pct_int_cnt5_PROC
  if (rst_a == 1'b1)
    int_cnt5_r <= 48'd0;
  else if ((int_cntl5_wen == 1'b1) || (int_cnth5_wen == 1'b1))
    int_cnt5_r <= int_cnt5_nxt;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining int_cnt6_r                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : pct_int_cnt6_PROC
  if (rst_a == 1'b1)
    int_cnt6_r <= 48'd0;
  else if ((int_cntl6_wen == 1'b1) || (int_cnth6_wen == 1'b1))
    int_cnt6_r <= int_cnt6_nxt;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining int_cnt7_r                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : pct_int_cnt7_PROC
  if (rst_a == 1'b1)
    int_cnt7_r <= 48'd0;
  else if ((int_cntl7_wen == 1'b1) || (int_cnth7_wen == 1'b1))
    int_cnt7_r <= int_cnt7_nxt;
end


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous logic to determine the counter and snapshot enables       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : pct_enables_PROC

  count_cfg0_en = 1'b1
                & (~((~ar_aux_status32_r[`npuarc_U_FLAG])            & config0_r[18]))
                & (~(  ar_aux_status32_r[`npuarc_U_FLAG]             & config0_r[18+1]))
                & (~((~ar_aux_status32_r[`npuarc_AE_FLAG])           & config0_r[18+3]))
                & (~(  ar_aux_status32_r[`npuarc_AE_FLAG]            & config0_r[18+4]))
                & (~((~|ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & config0_r[18+6]))
                & (~(( |ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & config0_r[18+7]))
                ;
  count_cfg1_en = 1'b1
                & (~((~ar_aux_status32_r[`npuarc_U_FLAG])            & config1_r[18]))
                & (~(  ar_aux_status32_r[`npuarc_U_FLAG]             & config1_r[18+1]))
                & (~((~ar_aux_status32_r[`npuarc_AE_FLAG])           & config1_r[18+3]))
                & (~(  ar_aux_status32_r[`npuarc_AE_FLAG]            & config1_r[18+4]))
                & (~((~|ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & config1_r[18+6]))
                & (~(( |ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & config1_r[18+7]))
                ;
  count_cfg2_en = 1'b1
                & (~((~ar_aux_status32_r[`npuarc_U_FLAG])            & config2_r[18]))
                & (~(  ar_aux_status32_r[`npuarc_U_FLAG]             & config2_r[18+1]))
                & (~((~ar_aux_status32_r[`npuarc_AE_FLAG])           & config2_r[18+3]))
                & (~(  ar_aux_status32_r[`npuarc_AE_FLAG]            & config2_r[18+4]))
                & (~((~|ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & config2_r[18+6]))
                & (~(( |ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & config2_r[18+7]))
                ;
  count_cfg3_en = 1'b1
                & (~((~ar_aux_status32_r[`npuarc_U_FLAG])            & config3_r[18]))
                & (~(  ar_aux_status32_r[`npuarc_U_FLAG]             & config3_r[18+1]))
                & (~((~ar_aux_status32_r[`npuarc_AE_FLAG])           & config3_r[18+3]))
                & (~(  ar_aux_status32_r[`npuarc_AE_FLAG]            & config3_r[18+4]))
                & (~((~|ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & config3_r[18+6]))
                & (~(( |ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & config3_r[18+7]))
                ;
  count_cfg4_en = 1'b1
                & (~((~ar_aux_status32_r[`npuarc_U_FLAG])            & config4_r[18]))
                & (~(  ar_aux_status32_r[`npuarc_U_FLAG]             & config4_r[18+1]))
                & (~((~ar_aux_status32_r[`npuarc_AE_FLAG])           & config4_r[18+3]))
                & (~(  ar_aux_status32_r[`npuarc_AE_FLAG]            & config4_r[18+4]))
                & (~((~|ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & config4_r[18+6]))
                & (~(( |ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & config4_r[18+7]))
                ;
  count_cfg5_en = 1'b1
                & (~((~ar_aux_status32_r[`npuarc_U_FLAG])            & config5_r[18]))
                & (~(  ar_aux_status32_r[`npuarc_U_FLAG]             & config5_r[18+1]))
                & (~((~ar_aux_status32_r[`npuarc_AE_FLAG])           & config5_r[18+3]))
                & (~(  ar_aux_status32_r[`npuarc_AE_FLAG]            & config5_r[18+4]))
                & (~((~|ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & config5_r[18+6]))
                & (~(( |ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & config5_r[18+7]))
                ;
  count_cfg6_en = 1'b1
                & (~((~ar_aux_status32_r[`npuarc_U_FLAG])            & config6_r[18]))
                & (~(  ar_aux_status32_r[`npuarc_U_FLAG]             & config6_r[18+1]))
                & (~((~ar_aux_status32_r[`npuarc_AE_FLAG])           & config6_r[18+3]))
                & (~(  ar_aux_status32_r[`npuarc_AE_FLAG]            & config6_r[18+4]))
                & (~((~|ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & config6_r[18+6]))
                & (~(( |ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & config6_r[18+7]))
                ;
  count_cfg7_en = 1'b1
                & (~((~ar_aux_status32_r[`npuarc_U_FLAG])            & config7_r[18]))
                & (~(  ar_aux_status32_r[`npuarc_U_FLAG]             & config7_r[18+1]))
                & (~((~ar_aux_status32_r[`npuarc_AE_FLAG])           & config7_r[18+3]))
                & (~(  ar_aux_status32_r[`npuarc_AE_FLAG]            & config7_r[18+4]))
                & (~((~|ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & config7_r[18+6]))
                & (~(( |ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & config7_r[18+7]))
                ;

  count0_wen    = 
                (  i_global_en
                 & count_cfg0_en
                 & (inc_count0 ^ config0_r[15])
                )
                | (pct_control_sel & wa_sr_data_r [16])
                | countl0_wen
                | counth0_wen
                ;
  count1_wen    = 
                (  i_global_en
                 & count_cfg1_en
                 & (inc_count1 ^ config1_r[15])
                )
                | (pct_control_sel & wa_sr_data_r [16])
                | countl1_wen
                | counth1_wen
                ;
  count2_wen    = 
                (  i_global_en
                 & count_cfg2_en
                 & (inc_count2 ^ config2_r[15])
                )
                | (pct_control_sel & wa_sr_data_r [16])
                | countl2_wen
                | counth2_wen
                ;
  count3_wen    = 
                (  i_global_en
                 & count_cfg3_en
                 & (inc_count3 ^ config3_r[15])
                )
                | (pct_control_sel & wa_sr_data_r [16])
                | countl3_wen
                | counth3_wen
                ;
  count4_wen    = 
                (  i_global_en
                 & count_cfg4_en
                 & (inc_count4 ^ config4_r[15])
                )
                | (pct_control_sel & wa_sr_data_r [16])
                | countl4_wen
                | counth4_wen
                ;
  count5_wen    = 
                (  i_global_en
                 & count_cfg5_en
                 & (inc_count5 ^ config5_r[15])
                )
                | (pct_control_sel & wa_sr_data_r [16])
                | countl5_wen
                | counth5_wen
                ;
  count6_wen    = 
                (  i_global_en
                 & count_cfg6_en
                 & (inc_count6 ^ config6_r[15])
                )
                | (pct_control_sel & wa_sr_data_r [16])
                | countl6_wen
                | counth6_wen
                ;
  count7_wen    = 
                (  i_global_en
                 & count_cfg7_en
                 & (inc_count7 ^ config7_r[15])
                )
                | (pct_control_sel & wa_sr_data_r [16])
                | countl7_wen
                | counth7_wen
                ;

  snap0_wen     = (pct_control_sel & wa_sr_data_r [17])
                ;
  snap1_wen     = (pct_control_sel & wa_sr_data_r [17])
                ;
  snap2_wen     = (pct_control_sel & wa_sr_data_r [17])
                ;
  snap3_wen     = (pct_control_sel & wa_sr_data_r [17])
                ;
  snap4_wen     = (pct_control_sel & wa_sr_data_r [17])
                ;
  snap5_wen     = (pct_control_sel & wa_sr_data_r [17])
                ;
  snap6_wen     = (pct_control_sel & wa_sr_data_r [17])
                ;
  snap7_wen     = (pct_control_sel & wa_sr_data_r [17])
                ;

end


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous blocks defining the input pipeline register, which serves  //
// to isolate the PCT block from the rest of the pipeline for timing.     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

// VPOST OFF
always @(posedge clk or posedge rst_a)
begin : pct_events_PROC
  if (rst_a == 1'b1) begin
    all_events_r[0]      <= 1'b0;
    all_events_r[1]      <= 1'b0;
    all_events_r[2]      <= 1'b0;
    all_events_r[3]      <= 1'b0;
    all_events_r[4]      <= 1'b0;
    all_events_r[5]      <= 1'b0;
    all_events_r[6]      <= 1'b0;
    all_events_r[7]      <= 1'b0;
    all_events_r[8]      <= 1'b0;
    all_events_r[9]      <= 1'b0;
    all_events_r[10]      <= 1'b0;
    all_events_r[11]      <= 1'b0;
    all_events_r[12]      <= 1'b0;
    all_events_r[13]      <= 1'b0;
    all_events_r[14]      <= 1'b0;
    all_events_r[15]      <= 1'b0;
    all_events_r[16]      <= 1'b0;
    all_events_r[17]      <= 1'b0;
    all_events_r[18]      <= 1'b0;
    all_events_r[19]      <= 1'b0;
    all_events_r[20]      <= 1'b0;
    all_events_r[21]      <= 1'b0;
    all_events_r[22]      <= 1'b0;
    all_events_r[23]      <= 1'b0;
    all_events_r[24]      <= 1'b0;
    all_events_r[25]      <= 1'b0;
    all_events_r[26]      <= 1'b0;
    all_events_r[27]      <= 1'b0;
    all_events_r[28]      <= 1'b0;
    all_events_r[29]      <= 1'b0;
    all_events_r[30]      <= 1'b0;
    all_events_r[31]      <= 1'b0;
    all_events_r[32]      <= 1'b0;
    all_events_r[33]      <= 1'b0;
    all_events_r[34]      <= 1'b0;
    all_events_r[35]      <= 1'b0;
    all_events_r[36]      <= 1'b0;
    all_events_r[37]      <= 1'b0;
    all_events_r[38]      <= 1'b0;
    all_events_r[39]      <= 1'b0;
    all_events_r[40]      <= 1'b0;
    all_events_r[41]      <= 1'b0;
    all_events_r[42]      <= 1'b0;
    all_events_r[43]      <= 1'b0;
    all_events_r[44]      <= 1'b0;
    all_events_r[45]      <= 1'b0;
    all_events_r[46]      <= 1'b0;
    all_events_r[47]      <= 1'b0;
    all_events_r[48]      <= 1'b0;
    all_events_r[49]      <= 1'b0;
    all_events_r[50]      <= 1'b0;
    all_events_r[51]      <= 1'b0;
    all_events_r[52]      <= 1'b0;
    all_events_r[53]      <= 1'b0;
    all_events_r[54]      <= 1'b0;
    all_events_r[55]      <= 1'b0;
    all_events_r[56]      <= 1'b0;
    all_events_r[57]      <= 1'b0;
    all_events_r[58]      <= 1'b0;
    all_events_r[59]      <= 1'b0;
    all_events_r[60]      <= 1'b0;
    all_events_r[61]      <= 1'b0;
    all_events_r[62]      <= 1'b0;
    all_events_r[63]      <= 1'b0;
    all_events_r[64]      <= 1'b0;
    all_events_r[65]      <= 1'b0;
    all_events_r[66]      <= 1'b0;
    all_events_r[67]      <= 1'b0;
    all_events_r[68]      <= 1'b0;
    all_events_r[69]      <= 1'b0;
    all_events_r[70]      <= 1'b0;
    all_events_r[71]      <= 1'b0;
    all_events_r[72]      <= 1'b0;
    all_events_r[73]      <= 1'b0;
    all_events_r[74]      <= 1'b0;
    all_events_r[75]      <= 1'b0;
    all_events_r[76]      <= 1'b0;
    all_events_r[77]      <= 1'b0;
    all_events_r[78]      <= 1'b0;
    all_events_r[79]      <= 1'b0;
    all_events_r[80]      <= 1'b0;
    all_events_r[81]      <= 1'b0;
    all_events_r[82]      <= 1'b0;
    all_events_r[83]      <= 1'b0;
    all_events_r[84]      <= 1'b0;
    all_events_r[85]      <= 1'b0;
    all_events_r[86]      <= 1'b0;
    all_events_r[87]      <= 1'b0;
    all_events_r[88]      <= 1'b0;
    all_events_r[89]      <= 1'b0;
    all_events_r[90]      <= 1'b0;
    all_events_r[91]      <= 1'b0;
    all_events_r[92]      <= 1'b0;
    all_events_r[93]      <= 1'b0;
    all_events_r[94]      <= 1'b0;
    all_events_r[95]      <= 1'b0;
    all_events_r[96]      <= 1'b0;
    all_events_r[97]      <= 1'b0;
    all_events_r[98]      <= 1'b0;
    all_events_r[99]      <= 1'b0;
    all_events_r[100]      <= 1'b0;
    all_events_r[101]      <= 1'b0;
    all_events_r[102]      <= 1'b0;
    all_events_r[103]      <= 1'b0;
    all_events_r[104]      <= 1'b0;
    all_events_r[105]      <= 1'b0;
    all_events_r[106]      <= 1'b0;
    all_events_r[107]      <= 1'b0;
    all_events_r[108]      <= 1'b0;
    all_events_r[109]      <= 1'b0;
    all_events_r[110]      <= 1'b0;
    all_events_r[111]      <= 1'b0;
    all_events_r[112]      <= 1'b0;
    all_events_r[113]      <= 1'b0;
    all_events_r[114]      <= 1'b0;
    all_events_r[115]      <= 1'b0;
    all_events_r[116]      <= 1'b0;
    all_events_r[117]      <= 1'b0;
    all_events_r[118]      <= 1'b0;
    all_events_r[119]      <= 1'b0;
    all_events_r[120]      <= 1'b0;
    all_events_r[121]      <= 1'b0;
    all_events_r[122]      <= 1'b0;
    all_events_r[123]      <= 1'b0;
    all_events_r[124]      <= 1'b0;
    all_events_r[125]      <= 1'b0;
    all_events_r[126]      <= 1'b0;
    end
  else begin
    all_events_r[0] <= i_never   ;
    all_events_r[1] <= i_always  ;
    all_events_r[2] <= i_iall    ;
    all_events_r[3] <= i_isleep  ;
    all_events_r[4] <= i_ijmp    ;
    all_events_r[5] <= i_ijmpc   ;
    all_events_r[6] <= i_ijmpu   ;
    all_events_r[7] <= i_ijmpd   ;
    all_events_r[8] <= i_ijmptak ;
    all_events_r[9] <= i_icall   ;
    all_events_r[10] <= i_ilr     ;
    all_events_r[11] <= i_isr     ;
    all_events_r[12] <= i_ilp     ;
    all_events_r[13] <= i_ilpend  ;
    all_events_r[14] <= i_ilpin   ;
    all_events_r[15] <= i_i2byte  ;
    all_events_r[16] <= i_i4byte  ;
    all_events_r[17] <= i_i2lbyte ;
    all_events_r[18] <= i_i4lbyte ;
    all_events_r[19] <= i_imemrd  ;
    all_events_r[20] <= i_imemwr  ;
    all_events_r[21] <= i_imemrdc ;
    all_events_r[22] <= i_imemwrc ;
    all_events_r[23] <= i_itrap   ;
    all_events_r[24] <= i_iswi    ;
    all_events_r[25] <= i_illock  ;
    all_events_r[26] <= i_iscond  ;
    all_events_r[27] <= i_ialljmp ;
    all_events_r[28] <= i_ivec    ;
    all_events_r[29] <= i_ivgather;
    all_events_r[30] <= i_ivscatt ;
    all_events_r[31] <= i_vgathbc ;
    all_events_r[32] <= i_vscatbc ;
    all_events_r[33] <= i_vstall  ;
    all_events_r[34] <= i_vbslot  ;
    all_events_r[35] <= i_bwpcflt ;
    all_events_r[36] <= i_bstall  ;
    all_events_r[37] <= i_bflush  ;
    all_events_r[38] <= i_bdebug  ;
    all_events_r[39] <= i_bissue  ;
    all_events_r[40] <= i_beslot  ;
    all_events_r[41] <= i_bdslot  ;
    all_events_r[42] <= i_bflgstal;
    all_events_r[43] <= i_berrbrch;
    all_events_r[44] <= i_buopstal;
    all_events_r[45] <= i_brgbank ;
    all_events_r[46] <= i_bagustl ;
    all_events_r[47] <= i_baccstal;
    all_events_r[48] <= i_bzolcnt ;
    all_events_r[49] <= i_bdata64 ;
    all_events_r[50] <= i_bdcstall;
    all_events_r[51] <= i_bauxflsh;
    all_events_r[52] <= i_bfirqex ;
    all_events_r[53] <= i_etaken  ;
    all_events_r[54] <= i_qtaken  ;
    all_events_r[55] <= i_icm     ;
    all_events_r[56] <= i_icll    ;
    all_events_r[57] <= i_icoff   ;
    all_events_r[58] <= i_ivic    ;
    all_events_r[59] <= i_ivil    ;
    all_events_r[60] <= i_icwpm   ;
    all_events_r[61] <= i_dcm     ;
    all_events_r[62] <= i_dclm    ;
    all_events_r[63] <= i_dcsm    ;
    all_events_r[64] <= i_dcpm    ;
    all_events_r[65] <= i_dcbc    ;
    all_events_r[66] <= i_fldc    ;
    all_events_r[67] <= i_fldl    ;
    all_events_r[68] <= i_ivdc    ;
    all_events_r[69] <= i_ivdl    ;
    all_events_r[70] <= i_bpmp    ;
    all_events_r[71] <= i_bplate  ;
    all_events_r[72] <= i_bpcmp   ;
    all_events_r[73] <= i_bpbtamp ;
    all_events_r[74] <= i_bpsubrt ;
    all_events_r[75] <= i_bperrbr ;
    all_events_r[76] <= i_bpbcm   ;
    all_events_r[77] <= i_mecc1   ;
    all_events_r[78] <= i_eitlb   ;
    all_events_r[79] <= i_edtlb   ;
    all_events_r[80] <= i_evinst  ;
    all_events_r[81] <= i_ivgath  ;
    all_events_r[82] <= i_ivscat  ;
    all_events_r[83] <= i_bvgath  ;
    all_events_r[84] <= i_bvscat  ;
    all_events_r[85] <= i_ccdc2cm ;
    all_events_r[86] <= i_ccserial;
    all_events_r[87] <= i_ccupgrad;
    all_events_r[88] <= i_ccresps ;
    all_events_r[89] <= i_dcstgrad;
    all_events_r[90] <= i_dcldfwd ;
    all_events_r[91] <= i_crun    ;
    all_events_r[92] <= i_cruni   ;
    all_events_r[93] <= i_cdualiss;
    all_events_r[94] <= i_cdualco ;
    all_events_r[95] <= i_uflag0  ;
    all_events_r[96] <= i_uflag1  ;
    all_events_r[97] <= i_uflag2  ;
    all_events_r[98] <= i_uflag3  ;
    all_events_r[99] <= i_uflag4  ;
    all_events_r[100] <= i_uflag5  ;
    all_events_r[101] <= i_uflag6  ;
    all_events_r[102] <= i_uflag7  ;
    all_events_r[103] <= i_uflag8  ;
    all_events_r[104] <= i_uflag9  ;
    all_events_r[105] <= i_uflag10 ;
    all_events_r[106] <= i_uflag11 ;
    all_events_r[107] <= i_uflag12 ;
    all_events_r[108] <= i_uflag13 ;
    all_events_r[109] <= i_uflag14 ;
    all_events_r[110] <= i_uflag15 ;
    all_events_r[111] <= i_uflag16 ;
    all_events_r[112] <= i_uflag17 ;
    all_events_r[113] <= i_uflag18 ;
    all_events_r[114] <= i_uflag19 ;
    all_events_r[115] <= i_uflag20 ;
    all_events_r[116] <= i_uflag21 ;
    all_events_r[117] <= i_uflag22 ;
    all_events_r[118] <= i_uflag23 ;
    all_events_r[119] <= i_uflag24 ;
    all_events_r[120] <= i_uflag25 ;
    all_events_r[121] <= i_uflag26 ;
    all_events_r[122] <= i_uflag27 ;
    all_events_r[123] <= i_uflag28 ;
    all_events_r[124] <= i_uflag29 ;
    all_events_r[125] <= i_uflag30 ;
    all_events_r[126] <= i_uflag31 ;
    end
end // pct_events_PROC
// VPOST ON

// spyglass disable_block Reset_sync04
// SMD: Async reset signal is synchronized at least twice
// SJ:  Causes no issues
always @(posedge clk or posedge rst_a)
begin : pct_sync_PROC
  if (rst_a == 1'b1) begin
    s_global_en         <= 1'b0;
    s_ca_normal_evt_r   <= 1'b0;
    s_isleep_r          <= 1'b0;
    s_ialljmp_r         <= 1'b0;
    s_ijmp_r            <= 1'b0;
    s_ca_jump_r         <= 1'b0;
    s_ca_bcc_r          <= 1'b0;
    s_ca_brcc_bbit_r    <= 1'b0;
    s_cond_r            <= 1'b0;
    s_icall_r           <= 1'b0;

    s_imemrd_r          <= 1'b0;
    s_imemwr_r          <= 1'b0;
    
    s_imemrdc_r         <= 1'b0;
    s_imemwrc_r         <= 1'b0;

    s_locked_r          <= 1'b0;
    s_dslot_r           <= 1'b0;
    s_br_taken_r        <= 1'b0;

    s_ilr_r             <= 1'b0;
    s_isr_r             <= 1'b0;

    s_iswi_r            <= 1'b0;
    s_itrap_r           <= 1'b0;

    s_ilp_r             <= 1'b0;
    s_ilpin_r           <= 1'b0;
    s_ilpend_r          <= 1'b0;

    s_i2byte_r          <= 1'b0;
    s_i2lbyte_r         <= 1'b0;
    s_i4byte_r          <= 1'b0;
    s_i4lbyte_r         <= 1'b0;
    s_etaken_r          <= 1'b0;
    s_qtaken_r          <= 1'b0;

    s_crun_r            <= 1'b0;
    s_cruni_r           <= 1'b0;
    s_bissue_r          <= 1'b0;
    s_icm_r             <= 1'b0;
    s_icll_r            <= 1'b0;
    s_icoff_r           <= 1'b0;
    s_ivic_r            <= 1'b0;
    s_ivil_r            <= 1'b0;
    s_icwpm_r           <= 1'b0;
    s_dcm_r             <= 1'b0;
    s_dclm_r            <= 1'b0;
    s_dcsm_r            <= 1'b0;
    s_dcpm_r            <= 1'b0;
    s_fldc_r            <= 1'b0;
    s_fldl_r            <= 1'b0;
    s_ivdl_r            <= 1'b0;
    s_ivdc_r            <= 1'b0;
    s_bdcmstall_r       <= 1'b0;
    s_dcbc_r            <= 1'b0;

    s_bpmp_r            <= 1'b0;
    s_bplate_r          <= 1'b0;
    s_bpcmp_r           <= 1'b0;
    s_bpbtamp_r         <= 1'b0;
    s_bpsubrt_r         <= 1'b0;
    s_bperrbr_r         <= 1'b0;
    s_bpbcm_r           <= 1'b0;
    s_mecc1_r           <= 1'b0;
    s_bicmstall_r       <= 1'b0;
    s_bsyncstall_r      <= 1'b0;
    s_eitlb_r           <= 1'b0;
    s_edtlb_r           <= 1'b0;

  end
  else begin
    s_global_en         <=  i_range_en & i_uf_en;
    s_ca_normal_evt_r   <= ca_normal_evt;
    s_isleep_r          <= ca_sleep_evt;

    s_br_taken_r        <= ca_br_taken;
    s_ialljmp_r         <= (ca_jump_r | ca_bcc_r | ca_brcc_bbit_r | ca_zol_branch) 
                           & (~excpn_evts[`npuarc_INTEVT_ENTER] & ~excpn_evts[0])
                           & (~int_evts[`npuarc_INTEVT_ENTER] & ~int_evts[0])
                           ;
    s_ijmp_r            <= (ca_jump_r | ca_bcc_r | ca_brcc_bbit_r)
                           & (~excpn_evts[`npuarc_INTEVT_ENTER] & ~excpn_evts[0])
                           & ~int_evts[`npuarc_INTEVT_ENTER] & ~int_evts[0]
                           ;
    s_ca_jump_r         <= ca_jump_r & ~excpn_evts[`npuarc_INTEVT_ENTER] & ~excpn_evts[0]
                           & ~int_evts[`npuarc_INTEVT_ENTER] & ~int_evts[0]
                           ;
    s_ca_bcc_r          <= ca_bcc_r;
    s_ca_brcc_bbit_r    <= ca_brcc_bbit_r;
    s_cond_r            <= (|ca_q_field_r);
    s_icall_r           <= ca_br_jmp_op;

    s_imemrd_r          <= ca_load_r;

    s_imemwr_r          <= ca_store_r 
                         & (~ca_load_r) 
                         ;
    s_imemrdc_r         <= ca_load_r   
                         & (ca_target_r == `npuarc_DMP_TARGET_DC) 
                         & (~dc4_pref_r)
                         ;

    s_imemwrc_r  <= ca_store_r
                         & (~ca_load_r) & (~dc4_pref_r)
                         & (ca_target_r == `npuarc_DMP_TARGET_DC);

    s_locked_r          <= ca_locked_r;
    s_dslot_r           <= ca_dslot_r;

    s_ilr_r             <= ca_lr_op_r;
    s_isr_r             <= ca_sr_op_r & (~ca_lr_op_r);

    s_iswi_r            <= ca_trap_op_r & (~ca_byte_size_r) & excpn_evts[`npuarc_INTEVT_PROLOGUE];
    s_ilp_r             <= ca_lp_lpcc_evt;

    s_itrap_r           <= ca_trap_op_r & ( ca_byte_size_r);

    s_ilpin_r           <=  ({ar_pc_r, 1'b0} >= ar_aux_lp_start_r) 
                         && ({ar_pc_r, 1'b0} <  ar_aux_lp_end_r);
    s_ilpend_r          <= ca_hit_lp_end;

    s_i2byte_r          <=   ca_is_16bit_r;
    s_i4byte_r          <= (~ca_is_16bit_r);
    s_i2lbyte_r         <=   ca_is_16bit_r  & ca_has_limm_r;
    s_i4lbyte_r         <= (~ca_is_16bit_r) & ca_has_limm_r;


    s_etaken_r          <= excpn_evts[`npuarc_INTEVT_ENTER];
    s_qtaken_r          <= int_evts[`npuarc_INTEVT_ENTER];

    s_crun_r            <= !ar_aux_status32_r[`npuarc_H_FLAG];
    s_cruni_r           <= ar_aux_status32_r[`npuarc_IE_FLAG];    
    s_bissue_r          <= ifu_issue_stall_r & !ar_aux_status32_r[`npuarc_H_FLAG] & !ar_aux_debug_r[`npuarc_DEBUG_ZZ] & !db_active_r;
                                           
    s_icm_r             <= icm;
    s_icll_r            <= icll;
    s_icoff_r           <= icoff;
    s_ivic_r            <= ivic;
    s_ivil_r            <= ivil; 
    s_icwpm_r           <= icwpm;
    s_dcm_r             <= dcm;
    s_dclm_r            <= dclm;
    s_dcsm_r            <= dcsm;
    s_dcpm_r            <= dcpm;
    s_fldc_r            <= flsh;
    s_ivdl_r            <= ivdl;
    s_fldl_r            <= fldl;
    s_ivdc_r            <= ivdc;
    s_bdcmstall_r       <= dc_bdcmstall | dep_bdcmstall;
    s_dcbc_r            <=   1'b0
                           | dcbc
                           | dccmbc
                           ;
    
    s_bpmp_r            <= ifu_brch_mispred_r; 
    s_bplate_r          <= ifu_late_br_mispred;                     
    s_bpcmp_r           <= ifu_cond_mispred_r; 
    s_bpbtamp_r         <= ifu_bta_mispred_r;  
    s_bpsubrt_r         <= ifu_missing_pred_r; 
    s_bperrbr_r         <= ifu_error_branch_r; 
    s_bpbcm_r           <= ifu_branch_cache_miss;
    s_bicmstall_r       <= icm_stall;
    s_bsyncstall_r      <= sync_dsync_dmb_stall;
    s_mecc1_r           <= ifu_bit_error_r;                

    s_eitlb_r           <= (ar_aux_ecr_r[`npuarc_ECR_VEC_RANGE] == `npuarc_EV_ITLB_MISS) & excpn_evts[`npuarc_INTEVT_ENTER];                   
    s_edtlb_r           <= (ar_aux_ecr_r[`npuarc_ECR_VEC_RANGE] == `npuarc_EV_DTLB_MISS) & excpn_evts[`npuarc_INTEVT_ENTER];                

    end
end // pct_sync_PROC
// spyglass enable_block Reset_sync04

reg s_bflush_nxt;
reg debug_instr_commit_nxt;

always @*
begin : pct_bflush_debug_nxt_PROC
    s_bflush_nxt           = s_bflush_r;
    debug_instr_commit_nxt = debug_instr_commit;
    if (wa_restart_r == 1'b1 && ~debug_instr_commit && ~ar_aux_status32_r[`npuarc_H_FLAG])
      s_bflush_nxt           = 1'b1;
    else if (ca_pass)
    begin 
      s_bflush_nxt           = 1'b0;
      debug_instr_commit_nxt = db_active_r;
    end
end

always @(posedge clk or posedge rst_a)
begin : pct_bflush_debug_reg_PROC
  if (rst_a == 1'b1) begin
    s_bflush_r          <= 1'b0;
    debug_instr_commit  <= 1'b0;
  end
  else begin
    s_bflush_r          <= s_bflush_nxt;
    debug_instr_commit  <= debug_instr_commit_nxt;
  end
end

reg  sa_bissue_r          ;
reg  x1_bissue_r          ;
reg  x2_bissue_r          ;
reg  x3_bissue_r          ;
reg  ca_bissue_r          ;
reg  sa_bdebug_r          ;
reg  x1_bdebug_r          ;
reg  x2_bdebug_r          ;
reg  x3_bdebug_r          ;
reg  ca_bdebug_r          ;
reg  sa_beslot_r          ;
reg  x1_beslot_r          ;
reg  x2_beslot_r          ;
reg  x3_beslot_r          ;
reg  ca_beslot_r          ;
reg  x2_bdslot_r          ;
reg  x3_bdslot_r          ;
reg  ca_bdslot_r          ;
reg  sa_bflgstal_r        ;
reg  x1_bflgstal_r        ;
reg  x2_bflgstal_r        ;
reg  x3_bflgstal_r        ;
reg  ca_bflgstal_r        ;
reg  sa_berrbrch_r        ;
reg  x1_berrbrch_r        ;
reg  x2_berrbrch_r        ;
reg  x3_berrbrch_r        ;
reg  ca_berrbrch_r        ;
reg  sa_buopstal_r        ;
reg  x1_buopstal_r        ;
reg  x2_buopstal_r        ;
reg  x3_buopstal_r        ;
reg  ca_buopstal_r        ;
//reg  sa_bagustl_r         ;
reg  x1_bagustl_r         ;
reg  x2_bagustl_r         ;
reg  x3_bagustl_r         ;
reg  ca_bagustl_r         ;
// VPOST OFF
reg  x1_baccstal_r        ;
// VPOST ON
reg  x2_baccstal_r        ;
reg  x3_baccstal_r        ;
reg  ca_baccstal_r        ;
reg  sa_bzolcnt_r         ;
reg  x1_bzolcnt_r         ;
reg  x2_bzolcnt_r         ;
reg  x3_bzolcnt_r         ;
reg  ca_bzolcnt_r         ;
reg  sa_bdata64_r         ;
reg  x1_bdata64_r         ;
reg  x2_bdata64_r         ;
reg  x3_bdata64_r         ;
reg  ca_bdata64_r         ;
reg  x2_bdcstall_r        ;
reg  x3_bdcstall_r        ;
reg  ca_bdcstall_r        ;
reg  sa_bauxflsh_r        ;
reg  x1_bauxflsh_r        ;
reg  x2_bauxflsh_r        ;
reg  x3_bauxflsh_r        ;
reg  ca_bauxflsh_r        ;
reg  sa_bfirqex_r         ;
reg  x1_bfirqex_r         ;
reg  x2_bfirqex_r         ;
reg  x3_bfirqex_r         ;
reg  ca_bfirqex_r         ;

always @(posedge clk or posedge rst_a)
begin : pct_sa_PROC
  if (rst_a == 1'b1)
    begin
      sa_bissue_r           <= 1'b0               ;
      sa_bdebug_r           <= 1'b0               ;
      sa_beslot_r           <= 1'b0               ;
      sa_bflgstal_r         <= 1'b0               ;
      sa_berrbrch_r         <= 1'b0               ;
      sa_buopstal_r         <= 1'b0               ;
      sa_bzolcnt_r          <= 1'b0               ;
      sa_bdata64_r          <= 1'b0               ;
      sa_bauxflsh_r         <= 1'b0               ;
      sa_bfirqex_r          <= 1'b0               ;
    end
  else
    begin
      sa_bissue_r           <= s_bissue_r         ;
      sa_bdebug_r           <= db_active_r;
      sa_beslot_r           <= da_eslot_stall;
      sa_bflgstal_r         <= sa_flag_stall;
      sa_berrbrch_r         <= s_bperrbr_r        ;
      sa_buopstal_r         <= da_uop_stall;
      sa_bzolcnt_r          <= bzolcnt   ;
      sa_bdata64_r          <= sa_stall_r15 ;
      sa_bauxflsh_r         <= bauxflsh      ;
      sa_bfirqex_r          <= q_etaken | q_qtaken;
    end
end // pct_sa_PROC

always @(posedge clk or posedge rst_a)
begin : pct_x1_PROC
  if (rst_a == 1'b1)
    begin
      x1_bissue_r           <= 1'b0               ;
      x1_bdebug_r           <= 1'b0               ;
      x1_beslot_r           <= 1'b0               ;
      x1_bflgstal_r         <= 1'b0               ;
      x1_berrbrch_r         <= 1'b0               ;
      x1_buopstal_r         <= 1'b0               ;
      x1_bagustl_r          <= 1'b0               ;
// VPOST OFF
      x1_baccstal_r         <= 1'b0               ;
// VPOST ON
      x1_bzolcnt_r          <= 1'b0               ;
      x1_bdata64_r          <= 1'b0               ;
      x1_bauxflsh_r         <= 1'b0               ;
      x1_bfirqex_r          <= 1'b0               ;
    end
  else
    begin
      x1_bissue_r           <= sa_bissue_r        ;
      x1_bdebug_r           <= sa_bdebug_r        ;
      x1_beslot_r           <= sa_beslot_r        ;
      x1_bflgstal_r         <= sa_bflgstal_r      ;
      x1_berrbrch_r         <= sa_berrbrch_r      ;
      x1_buopstal_r         <= sa_buopstal_r      ;
      x1_bagustl_r          <= sa_stall_r1;
// VPOST OFF
      x1_baccstal_r         <= sa_acc_raw;
// VPOST ON
      x1_bzolcnt_r          <= sa_bzolcnt_r       ;
      x1_bdata64_r          <= sa_bdata64_r       ;
      x1_bauxflsh_r         <= sa_bauxflsh_r      ;
      x1_bfirqex_r          <= sa_bfirqex_r       ;
    end
end // pct_x1_PROC

always @(posedge clk or posedge rst_a)
begin : pct_x2_PROC
  if (rst_a == 1'b1)
    begin
      x2_bissue_r           <= 1'b0               ;
      x2_bdebug_r           <= 1'b0               ;
      x2_beslot_r           <= 1'b0               ;
      x2_bdslot_r           <= 1'b0               ;
      x2_bflgstal_r         <= 1'b0               ;
      x2_berrbrch_r         <= 1'b0               ;
      x2_buopstal_r         <= 1'b0               ;
      x2_bagustl_r          <= 1'b0               ;
      x2_baccstal_r         <= 1'b0               ;
      x2_bzolcnt_r          <= 1'b0               ;
      x2_bdata64_r          <= 1'b0               ;
      x2_bdcstall_r         <= 1'b0               ;
      x2_bauxflsh_r         <= 1'b0               ;
      x2_bfirqex_r          <= 1'b0               ;
    end
  else
    begin
      x2_bissue_r           <= x1_bissue_r        ;
      x2_bdebug_r           <= x1_bdebug_r        ;
      x2_beslot_r           <= x1_beslot_r        ;
      x2_bdslot_r           <= x1_dslot_stall ;
      x2_bflgstal_r         <= x1_bflgstal_r      ;
      x2_berrbrch_r         <= x1_berrbrch_r      ;
      x2_buopstal_r         <= x1_buopstal_r      ;
      x2_bagustl_r          <= x1_bagustl_r       ;
      x2_baccstal_r         <= x1_baccstal_r
                             ;

      x2_bzolcnt_r          <= x1_bzolcnt_r       ;
      x2_bdata64_r          <= x1_bdata64_r       ;
      x2_bdcstall_r         <= dc1_stall          ;
      x2_bauxflsh_r         <= x1_bauxflsh_r      ;
      x2_bfirqex_r          <= x1_bfirqex_r       ;
    end
end // pct_x2_PROC

always @(posedge clk or posedge rst_a)
begin : pct_x3_PROC
  if (rst_a == 1'b1)
    begin
      x3_bissue_r           <= 1'b0               ;
      x3_bdebug_r           <= 1'b0               ;
      x3_beslot_r           <= 1'b0               ;
      x3_bdslot_r           <= 1'b0               ;
      x3_bflgstal_r         <= 1'b0               ;
      x3_berrbrch_r         <= 1'b0               ;
      x3_buopstal_r         <= 1'b0               ;
      x3_bagustl_r          <= 1'b0               ;
      x3_baccstal_r         <= 1'b0               ;
      x3_bzolcnt_r          <= 1'b0               ;
      x3_bdata64_r          <= 1'b0               ;
      x3_bdcstall_r         <= 1'b0               ;
      x3_bauxflsh_r         <= 1'b0               ;
      x3_bfirqex_r          <= 1'b0               ;
    end
  else
    begin
      x3_bissue_r           <= x2_bissue_r        ;
      x3_bdebug_r           <= x2_bdebug_r        ;
      x3_beslot_r           <= x2_beslot_r        ;
      x3_bdslot_r           <= x2_bdslot_r        ;
      x3_bflgstal_r         <= x2_bflgstal_r      ;
      x3_berrbrch_r         <= x2_berrbrch_r      ;
      x3_buopstal_r         <= x2_buopstal_r      ;
      x3_bagustl_r          <= x2_bagustl_r       ;
      x3_baccstal_r         <= x2_baccstal_r      ;
      x3_bzolcnt_r          <= x2_bzolcnt_r       ;
      x3_bdata64_r          <= x2_bdata64_r       ;
      x3_bdcstall_r         <= x2_bdcstall_r | dc2_stall ;
      x3_bauxflsh_r         <= x2_bauxflsh_r      ;
      x3_bfirqex_r          <= x2_bfirqex_r       ;
    end
end // pct_x3_PROC

always @(posedge clk or posedge rst_a)
begin : pct_ca_PROC
  if (rst_a == 1'b1)
    begin
      ca_bissue_r           <= 1'b0               ;
      ca_bdebug_r           <= 1'b0               ;
      ca_beslot_r           <= 1'b0               ;
      ca_bdslot_r           <= 1'b0               ;
      ca_bflgstal_r         <= 1'b0               ;
      ca_berrbrch_r         <= 1'b0               ;
      ca_buopstal_r         <= 1'b0               ;
      ca_bagustl_r          <= 1'b0               ;
      ca_baccstal_r         <= 1'b0               ;
      ca_bzolcnt_r          <= 1'b0               ;
      ca_bdata64_r          <= 1'b0               ;
      ca_bdcstall_r         <= 1'b0               ;
      ca_bauxflsh_r         <= 1'b0               ;
      ca_bfirqex_r          <= 1'b0               ;
    end
  else
    begin
      ca_bissue_r           <= x3_bissue_r        ;
      ca_bdebug_r           <= x3_bdebug_r        ;
      ca_beslot_r           <= x3_beslot_r        ;
      ca_bdslot_r           <= x3_bdslot_r        ;
      ca_bflgstal_r         <= x3_bflgstal_r      ;
      ca_berrbrch_r         <= x3_berrbrch_r      ;
      ca_buopstal_r         <= x3_buopstal_r      ;
      ca_bagustl_r          <= x3_bagustl_r       ;
      ca_baccstal_r         <= x3_baccstal_r
                             | ca_acc_waw 
                             ;
      ca_bzolcnt_r          <= x3_bzolcnt_r       ;
      ca_bdata64_r          <= x3_bdata64_r       ;
      ca_bdcstall_r         <= x3_bdcstall_r;
      ca_bauxflsh_r         <= x3_bauxflsh_r      ;
      ca_bfirqex_r          <= x3_bfirqex_r       ;
    end
end // pct_ca_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous logic for qualifying the input pipeline signals and       //
// generating the logic for each countable condition.                     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : cond_qual_PROC

  q_ca_normal_evt    = s_ca_normal_evt_r;

  q_isleep           = s_isleep_r 
                     & s_ca_normal_evt_r;
  q_ialljmp          = s_ialljmp_r & s_ca_normal_evt_r;
  q_ijmp             = s_ijmp_r   & s_ca_normal_evt_r;
  q_ijmpc            = (((s_ca_jump_r | s_ca_bcc_r)  & s_cond_r) | s_ca_brcc_bbit_r)   
                     & s_ca_normal_evt_r
                     & s_br_taken_r;
  q_ijmpu            = (s_ca_jump_r | s_ca_bcc_r)  
                     & s_ca_normal_evt_r
                     & (~s_cond_r)
                     & s_br_taken_r;
  q_ijmpd            = s_ijmp_r
                     & s_ca_normal_evt_r 
                     & s_dslot_r;
  q_ijmptak          = s_ijmp_r
                     & s_ca_normal_evt_r 
                     & s_br_taken_r ;
  q_icall            = s_icall_r  & s_ca_normal_evt_r;

  q_imemrd           = s_imemrd_r  & ~s_locked_r & s_ca_normal_evt_r;
  q_imemwr           = s_imemwr_r  & ~s_locked_r & s_ca_normal_evt_r;
  q_imemrdc          = s_imemrdc_r & ~s_locked_r & s_ca_normal_evt_r;
  q_imemwrc          = s_imemwrc_r & ~s_locked_r & s_ca_normal_evt_r;
  q_illock           = s_imemrd_r  &  s_locked_r & s_ca_normal_evt_r;
  q_iscond           = s_imemwr_r  &  s_locked_r & s_ca_normal_evt_r;

  q_ilr              = s_ilr_r & s_ca_normal_evt_r;
  q_isr              = s_isr_r & s_ca_normal_evt_r;

  q_iswi             = s_iswi_r;
  q_itrap            = s_itrap_r & s_ca_normal_evt_r;

  q_ilp              = s_ilp_r                    ;
  q_ilpin            = s_ilpin_r  & s_ca_normal_evt_r;
  q_ilpend           = s_ilpend_r
                     & s_ca_normal_evt_r
                     ;
  q_i2byte           = s_i2byte_r
                     & s_ca_normal_evt_r
                     ;
  q_i2lbyte          = s_i2lbyte_r
                     & s_ca_normal_evt_r
                     ;
  q_i4byte           = s_i4byte_r
                     & s_ca_normal_evt_r
                     ;
  q_i4lbyte          = s_i4lbyte_r
                     & s_ca_normal_evt_r
                     ;
  q_etaken           = s_etaken_r                 ;
  q_qtaken           = s_qtaken_r                 ;

  q_crun             = s_crun_r                   ;
  q_cruni            = s_cruni_r                  ;
  q_bstall           = (~s_isleep_r) & (~s_ca_normal_evt_r) & (~ar_aux_status32_r[`npuarc_H_FLAG]);
  q_bflush           = s_bflush_r                ;
  q_bissue           = ca_bissue_r                ;
  q_bdebug           = ca_bdebug_r                ;
  q_beslot           = ca_beslot_r                ;
  q_bdslot           = ca_bdslot_r                ;
  q_bflgstal         = ca_bflgstal_r              ;
  q_berrbrch         = ca_berrbrch_r              ;
  q_buopstal         = ca_buopstal_r              ;
  q_brgbank          = 1'b0                       ;
  q_bagustl          = ca_bagustl_r               ;
  q_baccstal         = ca_baccstal_r              ;
  q_bzolcnt          = ca_bzolcnt_r               ;
  q_bdata64          = ca_bdata64_r               ;
  q_bdcstall         = ca_bdcstall_r | dc4_stall_r;
  q_bauxflsh         = ca_bauxflsh_r              ;
  q_bfirqex          = ca_bfirqex_r               ;

  q_icm               = s_icm_r                   ;
  q_icll              = s_icll_r                  ;
  q_icoff             = s_icoff_r                 ;
  q_ivic              = s_ivic_r                  ;
  q_ivil              = s_ivil_r                  ;
  q_icwpm             = s_icwpm_r                 ;
  q_ccdc2cm           = 1'b0                      ; 
  q_ccserial          = 1'b0                      ; 
  q_ccupgrad          = 1'b0                      ; 
  q_ccresps           = 1'b0                      ; 
  q_dcm               = s_dcm_r                   ;
  q_dclm              = s_dclm_r                  ;
  q_dcsm              = s_dcsm_r                  ;
  q_dcpm              = s_dcpm_r                  ;
  q_fldc              = s_fldc_r                  ;
  q_ivdl              = s_ivdl_r                  ;
  q_fldl              = s_fldl_r                  ;
  q_ivdc              = s_ivdc_r                  ;
  q_bdcmstall         = s_bdcmstall_r             ;
  q_dcbc              = s_dcbc_r                  ;

  q_bpmp              = s_bpmp_r                  ;
  q_bplate            = s_bplate_r                ;
  q_bpcmp             = s_bpcmp_r                 ;
  q_bpbtamp           = s_bpbtamp_r               ;
  q_bpsubrt           = s_bpsubrt_r               ;
  q_bperrbr           = s_bperrbr_r               ;
  q_bpbcm             = s_bpbcm_r                 ;
  q_bicmstall         = s_bicmstall_r && ~(ar_aux_status32_r[`npuarc_H_FLAG] || ar_aux_debug_r[`npuarc_DEBUG_ZZ] || db_active_r);
  q_bsyncstall        = s_bsyncstall_r            ; 
  q_mecc1             = s_mecc1_r                 ;

  q_eitlb             = s_eitlb_r                 ;
  q_edtlb             = s_edtlb_r                 ;


  q_ivec                    = 1'b0                      ; 
  q_ivgather                = 1'b0                      ; 
  q_ivscatt                 = 1'b0                      ; 
  q_vgathbc                 = 1'b0                      ; 
  q_vscatbc                 = 1'b0                      ; 
  q_vstall                  = 1'b0                      ; 
  q_vbslot                  = 1'b0                      ;

    q_cdualiss         = 1'b0                      ; 
    q_cdualco          = 1'b0                      ; 
    q_bwpcflt          = 1'b0                      ; 
    q_dcstgrad         = 1'b0                      ; 
    q_dcldfwd          = 1'b0                      ; 
end

always @*
begin : wca_PROC

  i_never              = 1'b0;
  i_always             = 1'b0;
  i_iall               = 1'b0;
  i_isleep             = 1'b0;
  i_ijmp               = 1'b0;
  i_ijmpc              = 1'b0;
  i_ijmpu              = 1'b0;
  i_ijmpd              = 1'b0;
  i_ijmptak            = 1'b0;
  i_icall              = 1'b0;
  i_ilr                = 1'b0;
  i_isr                = 1'b0;
  i_ilp                = 1'b0;
  i_ilpend             = 1'b0;
  i_ilpin              = 1'b0;
  i_i2byte             = 1'b0;
  i_i4byte             = 1'b0;
  i_i2lbyte            = 1'b0;
  i_i4lbyte            = 1'b0;
  i_imemrd             = 1'b0;
  i_imemwr             = 1'b0;
  i_imemrdc            = 1'b0;
  i_imemwrc            = 1'b0;
  i_itrap              = 1'b0;
  i_iswi               = 1'b0;
  i_illock             = 1'b0;
  i_iscond             = 1'b0;
  i_ialljmp            = 1'b0;
  i_ivec               = 1'b0;
  i_ivgather           = 1'b0;
  i_ivscatt            = 1'b0;
  i_vgathbc            = 1'b0;
  i_vscatbc            = 1'b0;
  i_vstall             = 1'b0;
  i_vbslot             = 1'b0;
  i_bwpcflt            = 1'b0;
  i_bstall             = 1'b0;
  i_bflush             = 1'b0;
  i_bdebug             = 1'b0;
  i_bissue             = 1'b0;
  i_beslot             = 1'b0;
  i_bdslot             = 1'b0;
  i_bflgstal           = 1'b0;
  i_berrbrch           = 1'b0;
  i_buopstal           = 1'b0;
  i_brgbank            = 1'b0;
  i_bagustl            = 1'b0;
  i_baccstal           = 1'b0;
  i_bzolcnt            = 1'b0;
  i_bdata64            = 1'b0;
  i_bdcstall           = 1'b0;
  i_bauxflsh           = 1'b0;
  i_bfirqex            = 1'b0;
  i_etaken             = 1'b0;
  i_qtaken             = 1'b0;
  i_icm                = 1'b0;
  i_icll               = 1'b0;
  i_icoff              = 1'b0;
  i_ivic               = 1'b0;
  i_ivil               = 1'b0;
  i_icwpm              = 1'b0;
  i_dcm                = 1'b0;
  i_dclm               = 1'b0;
  i_dcsm               = 1'b0;
  i_dcpm               = 1'b0;
  i_dcbc               = 1'b0;
  i_fldc               = 1'b0;
  i_fldl               = 1'b0;
  i_ivdc               = 1'b0;
  i_ivdl               = 1'b0;
  i_bpmp               = 1'b0;
  i_bplate             = 1'b0;
  i_bpcmp              = 1'b0;
  i_bpbtamp            = 1'b0;
  i_bpsubrt            = 1'b0;
  i_bperrbr            = 1'b0;
  i_bpbcm              = 1'b0;
  i_mecc1              = 1'b0;
  i_eitlb              = 1'b0;
  i_edtlb              = 1'b0;
  i_evinst             = 1'b0;
  i_ivgath             = 1'b0;
  i_ivscat             = 1'b0;
  i_bvgath             = 1'b0;
  i_bvscat             = 1'b0;
  i_ccdc2cm            = 1'b0;
  i_ccserial           = 1'b0;
  i_ccupgrad           = 1'b0;
  i_ccresps            = 1'b0;
  i_dcstgrad           = 1'b0;
  i_dcldfwd            = 1'b0;
  i_crun               = 1'b0;
  i_cruni              = 1'b0;
  i_cdualiss           = 1'b0;
  i_cdualco            = 1'b0;
  i_uflag0             = 1'b0;
  i_uflag1             = 1'b0;
  i_uflag2             = 1'b0;
  i_uflag3             = 1'b0;
  i_uflag4             = 1'b0;
  i_uflag5             = 1'b0;
  i_uflag6             = 1'b0;
  i_uflag7             = 1'b0;
  i_uflag8             = 1'b0;
  i_uflag9             = 1'b0;
  i_uflag10            = 1'b0;
  i_uflag11            = 1'b0;
  i_uflag12            = 1'b0;
  i_uflag13            = 1'b0;
  i_uflag14            = 1'b0;
  i_uflag15            = 1'b0;
  i_uflag16            = 1'b0;
  i_uflag17            = 1'b0;
  i_uflag18            = 1'b0;
  i_uflag19            = 1'b0;
  i_uflag20            = 1'b0;
  i_uflag21            = 1'b0;
  i_uflag22            = 1'b0;
  i_uflag23            = 1'b0;
  i_uflag24            = 1'b0;
  i_uflag25            = 1'b0;
  i_uflag26            = 1'b0;
  i_uflag27            = 1'b0;
  i_uflag28            = 1'b0;
  i_uflag29            = 1'b0;
  i_uflag30            = 1'b0;
  i_uflag31            = 1'b0;

  i_never      = 1'b0                             ;
  i_always     = 1'b1                             ;

  // committed events
  //
  i_iall        = q_ca_normal_evt                 ; 
  i_isleep      = q_isleep                        ;
  i_ialljmp     = q_ialljmp                       ;
  i_ijmp        = q_ijmp                          ;
  i_ijmpc       = q_ijmpc                         ;
  i_ijmpu       = q_ijmpu                         ;
  i_ijmpd       = q_ijmpd                         ;
  i_ijmptak     = q_ijmptak                       ;
  i_icall       = q_icall                         ;

  i_imemrd      = q_imemrd                        ;
  i_imemwr      = q_imemwr                        ;
  i_imemrdc     = q_imemrdc                       ;
  i_imemwrc     = q_imemwrc                       ;
  i_ilr         = q_ilr                           ;
  i_isr         = q_isr                           ;

  i_iswi        = q_iswi                          ;
  i_itrap       = q_itrap                         ;

  i_ilp         = q_ilp                           ;
  i_ilpin       = q_ilpin                         ;
  i_ilpend      = q_ilpend                        ;

  i_i2byte      = q_i2byte                        ;
  i_i4byte      = q_i4byte                        ;
  i_i2lbyte     = q_i2lbyte                       ;
  i_i4lbyte     = q_i4lbyte                       ;

  i_etaken      = q_etaken                        ;
  i_qtaken      = q_qtaken                        ;

  i_illock      = q_illock                        ;
  i_iscond      = q_iscond                        ;

  i_crun        = q_crun                          ;
  i_cruni       = q_cruni                         ;  

  // User flags register, a programmable 32-bit vector of conditions
  //
  { i_uflag31,
    i_uflag30,
    i_uflag29,
    i_uflag28,
    i_uflag27,
    i_uflag26,
    i_uflag25,
    i_uflag24,
    i_uflag23,
    i_uflag22,
    i_uflag21,
    i_uflag20,
    i_uflag19,
    i_uflag18,
    i_uflag17,
    i_uflag16,
    i_uflag15,
    i_uflag14,
    i_uflag13,
    i_uflag12,
    i_uflag11,
    i_uflag10,
    i_uflag9,
    i_uflag8,
    i_uflag7,
    i_uflag6,
    i_uflag5,
    i_uflag4,
    i_uflag3,
    i_uflag2,
    i_uflag1,
    i_uflag0 } = pct_uflags_r                    ;

  i_bstall  = q_bstall ;

  i_bflush   = q_bflush                           ;
  i_bissue   = q_bissue                           ;
  i_bdebug   = q_bdebug                           ;
  i_beslot   = q_beslot                           ;
  i_bdslot   = q_bdslot                           ;
  i_bflgstal = q_bflgstal                         ;
  i_berrbrch = q_berrbrch                         ;
  i_buopstal = q_buopstal                         ;
  i_brgbank  = q_brgbank                          ;
  i_bagustl  = q_bagustl                          ;
  i_baccstal = q_baccstal                         ;
  i_bzolcnt  = q_bzolcnt                          ;
  i_bdata64  = q_bdata64                          ;
  i_bdcstall = q_bdcstall                         ;
  i_bauxflsh = q_bauxflsh                         ;
  i_bfirqex  = q_bfirqex                          ;

  i_icm      = q_icm                              ;
  i_icll     = q_icll                             ;
  i_icoff    = q_icoff                            ;
  i_ivic     = q_ivic                             ;
  i_ivil     = q_ivil                             ;
  i_icwpm    = q_icwpm                            ;

  i_dcm      = q_dcm                              ;
  i_dclm     = q_dclm                             ;
  i_dcsm     = q_dcsm                             ;
  i_dcpm     = q_dcpm                             ;
  i_dcbc     = q_dcbc                             ;
  i_fldc     = q_fldc                             ;
  i_fldl     = q_fldl                             ;
  i_ivdc     = q_ivdc                             ;
  i_ivdl     = q_ivdl                             ;
  i_ccdc2cm           = q_ccdc2cm                 ; 
  i_ccserial          = q_ccserial                ; 
  i_ccupgrad          = q_ccupgrad                ; 
  i_ccresps           = q_ccresps                 ;

  i_bpmp    = q_bpmp                              ;
  i_bplate  = q_bplate                            ;
  i_bpcmp   = q_bpcmp                             ;
  i_bpbtamp = q_bpbtamp                           ;
  i_bpsubrt = q_bpsubrt                           ;
  i_bperrbr = q_bperrbr                           ;
  i_bpbcm   = q_bpbcm                             ;
  i_mecc1   = q_mecc1                             ;

  i_eitlb   = q_eitlb                             ;
  i_edtlb   = q_edtlb                             ;
  i_ivec          = q_ivec                     ;
  i_ivgather      = q_ivgather                 ;
  i_ivscatt       = q_ivscatt               ;
  i_vgathbc       = q_vgathbc               ;    
  i_vscatbc       = q_vscatbc               ; 
  i_vstall        = q_vstall                ;
  i_vbslot       = q_vbslot        ;
  i_cdualiss       = q_cdualiss                  ;
  i_cdualco        = q_cdualco                   ;
  i_bwpcflt        = q_bwpcflt                ;
  i_dcstgrad       = q_dcstgrad               ;    
  i_dcldfwd        = q_dcldfwd                ; 
end


assign pct_unit_enable = aux_pct_active
                       | pct_control_r[0] 
                       | i_uf_en
                       ;


// VPOST OFF
`ifdef RTL_ASSERT_PCT_ON
// synopsys translate_off
 reg ca_pass_r;
 wire ca_any_pass;

 assign ca_any_pass = ca_pass; 

 always @(posedge clk or posedge rst_a)
 begin
   if (rst_a)
     ca_pass_r <= 1'b0;
   else
     ca_pass_r <= ca_any_pass;
 end

   property bdcmstall_ca_pass (bit cache_miss_stall, bit ca_pass);
     @(posedge clk) 
      disable iff (rst_a === 1'bx || rst_a == 1'b1)
      cache_miss_stall |-> ~ca_pass; 
   endproperty
   
   dc_bdcmstall_assert : assert property (bdcmstall_ca_pass (dc_bdcmstall, ca_any_pass))
   else $fatal("PCT RTL ASSERTION FAILED : stall caused by DMP miss queue is counted even when instruction is moved forward in CA stage");
   dep_bdcmstall_assert : assert property (bdcmstall_ca_pass (dep_bdcmstall, ca_pass_r))
   else $fatal("PCT RTL ASSERTION FAILED : stall from dependency pipe is counted even when instruction is moved forward in CA stage");
   icmstall_assert : assert property (bdcmstall_ca_pass (icm_stall, ca_pass_r))
   else $fatal("PCT RTL ASSERTION FAILED : stall because of I-Cache miss is counted even when instruction is moved forward in CA stage");

// synopsys translate_on
// VPOST ON
`endif


endmodule // module : alb_pct
 
