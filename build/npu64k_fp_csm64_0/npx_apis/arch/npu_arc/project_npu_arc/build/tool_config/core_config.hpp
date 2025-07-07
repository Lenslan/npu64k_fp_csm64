#ifndef core_config_hpp
#define core_config_hpp

#include <cstdint>

    /* coverity[cert_dcl51_cpp_violation] */
    /* coverity[autosar_cpp14_a16_0_1_violation] */
    /* coverity[autosar_cpp14_a17_0_1_violation] */
#define _TOOL_CONFIG_VER 10099

namespace snps_arc {
    namespace core_config {

	/********  NOTE: Start of BCR/CIR Variables ******************
	 * The initial variables with "kBcr" or "kCir" in the macro name
	 * may appear and disappear as different hardware releases change the
	 * layout of configuration registers. Additionally, the semantics of
	 * a "kBcr" or "KCir" variable value is subject to change.
	 * For these reasons it is recommended to avoid dependency on symbols
	 * which have "kBcr" or "kCir" in the name (and request alternative
	 * variables as needed).
	 **********************************************************/
	    /* value for identity */
	static constexpr std::uint32_t kCirIdentity{0x00000054UL};
	    /* value for identity.chipid */
	static constexpr std::uint32_t kCirIdentityChipid{0UL};
	    /* value for identity.arcnum */
	static constexpr std::uint32_t kCirIdentityArcnum{0UL};
	    /* value for identity.arcver */
	static constexpr std::uint32_t kCirIdentityArcver{84UL};
	    /* value for identity.family */
	static constexpr std::uint32_t kCirIdentityFamily{5UL};
	    /* value for identity.corever */
	static constexpr std::uint32_t kCirIdentityCorever{4UL};
	    /* value for aux_dccm */
	static constexpr std::uint32_t kCirAuxDccm{0x70000000UL};
	    /* value for aux_volatile */
	static constexpr std::uint32_t kCirAuxVolatile{0xF0000002UL};
	    /* value for aux_volatile.base_region */
	static constexpr std::uint32_t kCirAuxVolatileBaseRegion{15UL};
	    /* value for aux_volatile.limit_region */
	static constexpr std::uint32_t kCirAuxVolatileLimitRegion{0UL};
	    /* value for aux_volatile.s */
	static constexpr std::uint32_t kCirAuxVolatileS{1UL};
	    /* value for aux_volatile.d */
	static constexpr std::uint32_t kCirAuxVolatileD{0UL};
	    /* value for bcr_ver */
	static constexpr std::uint32_t kBcrBcrVer{0x00000002UL};
	    /* value for bcr_ver.version */
	static constexpr std::uint32_t kBcrBcrVerVersion{2UL};
	    /* value for vecbase_ac_build */
	static constexpr std::uint32_t kBcrVecbaseAcBuild{0x00000011UL};
	    /* value for vecbase_ac_build.version */
	static constexpr std::uint32_t kBcrVecbaseAcBuildVersion{4UL};
	    /* value for vecbase_ac_build.vector_config */
	static constexpr std::uint32_t kBcrVecbaseAcBuildVectorConfig{1UL};
	    /* value for vecbase_ac_build.addr */
	static constexpr std::uint32_t kBcrVecbaseAcBuildAddr{0UL};
	    /* value for mpu_build */
	static constexpr std::uint32_t kBcrMpuBuild{0x00000803UL};
	    /* value for mpu_build.ecc */
	static constexpr std::uint32_t kBcrMpuBuildEcc{0UL};
	    /* value for mpu_build.i */
	static constexpr std::uint32_t kBcrMpuBuildI{0UL};
	    /* value for mpu_build.s */
	static constexpr std::uint32_t kBcrMpuBuildS{0UL};
	    /* value for mpu_build.regions */
	static constexpr std::uint32_t kBcrMpuBuildRegions{8UL};
	    /* value for mpu_build.version */
	static constexpr std::uint32_t kBcrMpuBuildVersion{3UL};
	    /* value for rf_build */
	static constexpr std::uint32_t kBcrRfBuild{0x00000102UL};
	    /* value for rf_build.version */
	static constexpr std::uint32_t kBcrRfBuildVersion{2UL};
	    /* value for rf_build.p */
	static constexpr std::uint32_t kBcrRfBuildP{1UL};
	    /* value for rf_build.e */
	static constexpr std::uint32_t kBcrRfBuildE{0UL};
	    /* value for rf_build.r */
	static constexpr std::uint32_t kBcrRfBuildR{0UL};
	    /* value for rf_build.b */
	static constexpr std::uint32_t kBcrRfBuildB{0UL};
	    /* value for rf_build.d */
	static constexpr std::uint32_t kBcrRfBuildD{0UL};
	    /* value for mmu_build */
	static constexpr std::uint32_t kBcrMmuBuild{0x04E1984AUL};
	    /* value for mmu_build.version */
	static constexpr std::uint32_t kBcrMmuBuildVersion{4UL};
	    /* value for mmu_build.sl */
	static constexpr std::uint32_t kBcrMmuBuildSl{1UL};
	    /* value for mmu_build.psz1 */
	static constexpr std::uint32_t kBcrMmuBuildPsz1{12UL};
	    /* value for mmu_build.psz0 */
	static constexpr std::uint32_t kBcrMmuBuildPsz0{3UL};
	    /* value for mmu_build.dl */
	static constexpr std::uint32_t kBcrMmuBuildDl{0UL};
	    /* value for mmu_build.ct */
	static constexpr std::uint32_t kBcrMmuBuildCt{0UL};
	    /* value for mmu_build.pae */
	static constexpr std::uint32_t kBcrMmuBuildPae{1UL};
	    /* value for mmu_build.ja */
	static constexpr std::uint32_t kBcrMmuBuildJa{2UL};
	    /* value for mmu_build.je */
	static constexpr std::uint32_t kBcrMmuBuildJe{0UL};
	    /* value for mmu_build.jes */
	static constexpr std::uint32_t kBcrMmuBuildJes{1UL};
	    /* value for mmu_build.itlb */
	static constexpr std::uint32_t kBcrMmuBuildItlb{1UL};
	    /* value for mmu_build.dtlb */
	static constexpr std::uint32_t kBcrMmuBuildDtlb{2UL};
	    /* value for d_cache_build */
	static constexpr std::uint32_t kBcrDCacheBuild{0x10226105UL};
	    /* value for d_cache_build.version */
	static constexpr std::uint32_t kBcrDCacheBuildVersion{5UL};
	    /* value for d_cache_build.assoc */
	static constexpr std::uint32_t kBcrDCacheBuildAssoc{1UL};
	    /* value for d_cache_build.capacity */
	static constexpr std::uint32_t kBcrDCacheBuildCapacity{6UL};
	    /* value for d_cache_build.bsize */
	static constexpr std::uint32_t kBcrDCacheBuildBsize{2UL};
	    /* value for d_cache_build.fl */
	static constexpr std::uint32_t kBcrDCacheBuildFl{2UL};
	    /* value for d_cache_build.ioc */
	static constexpr std::uint32_t kBcrDCacheBuildIoc{0UL};
	    /* value for d_cache_build.cp */
	static constexpr std::uint32_t kBcrDCacheBuildCp{0UL};
	    /* value for d_cache_build.u */
	static constexpr std::uint32_t kBcrDCacheBuildU{0UL};
	    /* value for d_cache_build.cycles */
	static constexpr std::uint32_t kBcrDCacheBuildCycles{2UL};
	    /* value for dccm_build */
	static constexpr std::uint32_t kBcrDccmBuild{0x00140704UL};
	    /* value for dccm_build.w */
	static constexpr std::uint32_t kBcrDccmBuildW{0UL};
	    /* value for dccm_build.cycles */
	static constexpr std::uint32_t kBcrDccmBuildCycles{2UL};
	    /* value for dccm_build.interleave */
	static constexpr std::uint32_t kBcrDccmBuildInterleave{0UL};
	    /* value for dccm_build.size1 */
	static constexpr std::uint32_t kBcrDccmBuildSize1{0UL};
	    /* value for dccm_build.size0 */
	static constexpr std::uint32_t kBcrDccmBuildSize0{7UL};
	    /* value for dccm_build.version */
	static constexpr std::uint32_t kBcrDccmBuildVersion{4UL};
	    /* value for timer_build */
	static constexpr std::uint32_t kBcrTimerBuild{0x00000506UL};
	    /* value for timer_build.sp1 */
	static constexpr std::uint32_t kBcrTimerBuildSp1{0UL};
	    /* value for timer_build.sp0 */
	static constexpr std::uint32_t kBcrTimerBuildSp0{0UL};
	    /* value for timer_build.p1 */
	static constexpr std::uint32_t kBcrTimerBuildP1{0UL};
	    /* value for timer_build.p0 */
	static constexpr std::uint32_t kBcrTimerBuildP0{0UL};
	    /* value for timer_build.st1 */
	static constexpr std::uint32_t kBcrTimerBuildSt1{0UL};
	    /* value for timer_build.st0 */
	static constexpr std::uint32_t kBcrTimerBuildSt0{0UL};
	    /* value for timer_build.rtc */
	static constexpr std::uint32_t kBcrTimerBuildRtc{1UL};
	    /* value for timer_build.rtsc_ver */
	static constexpr std::uint32_t kBcrTimerBuildRtscVer{0UL};
	    /* value for timer_build.rtsc */
	static constexpr std::uint32_t kBcrTimerBuildRtsc{0UL};
	    /* value for timer_build.t0 */
	static constexpr std::uint32_t kBcrTimerBuildT0{1UL};
	    /* value for timer_build.t1 */
	static constexpr std::uint32_t kBcrTimerBuildT1{0UL};
	    /* value for timer_build.version */
	static constexpr std::uint32_t kBcrTimerBuildVersion{6UL};
	    /* value for ap_build */
	static constexpr std::uint32_t kBcrApBuild{0x00000605UL};
	    /* value for ap_build.version */
	static constexpr std::uint32_t kBcrApBuildVersion{5UL};
	    /* value for ap_build.type */
	static constexpr std::uint32_t kBcrApBuildType{6UL};
	    /* value for i_cache_build */
	static constexpr std::uint32_t kBcrICacheBuild{0x00236204UL};
	    /* value for i_cache_build.version */
	static constexpr std::uint32_t kBcrICacheBuildVersion{4UL};
	    /* value for i_cache_build.assoc */
	static constexpr std::uint32_t kBcrICacheBuildAssoc{2UL};
	    /* value for i_cache_build.capacity */
	static constexpr std::uint32_t kBcrICacheBuildCapacity{6UL};
	    /* value for i_cache_build.bsize */
	static constexpr std::uint32_t kBcrICacheBuildBsize{3UL};
	    /* value for i_cache_build.fl */
	static constexpr std::uint32_t kBcrICacheBuildFl{2UL};
	    /* value for i_cache_build.d */
	static constexpr std::uint32_t kBcrICacheBuildD{0UL};
	    /* value for multiply_build */
	static constexpr std::uint32_t kBcrMultiplyBuild{0x00023206UL};
	    /* value for multiply_build.version16x16 */
	static constexpr std::uint32_t kBcrMultiplyBuildVersion16x16{2UL};
	    /* value for multiply_build.dsp */
	static constexpr std::uint32_t kBcrMultiplyBuildDsp{3UL};
	    /* value for multiply_build.cyc */
	static constexpr std::uint32_t kBcrMultiplyBuildCyc{0UL};
	    /* value for multiply_build.type */
	static constexpr std::uint32_t kBcrMultiplyBuildType{2UL};
	    /* value for multiply_build.version32x32 */
	static constexpr std::uint32_t kBcrMultiplyBuildVersion32x32{6UL};
	    /* value for swap_build */
	static constexpr std::uint32_t kBcrSwapBuild{0x00000003UL};
	    /* value for swap_build.version */
	static constexpr std::uint32_t kBcrSwapBuildVersion{3UL};
	    /* value for norm_build */
	static constexpr std::uint32_t kBcrNormBuild{0x00000003UL};
	    /* value for norm_build.version */
	static constexpr std::uint32_t kBcrNormBuildVersion{3UL};
	    /* value for minmax_build */
	static constexpr std::uint32_t kBcrMinmaxBuild{0x00000002UL};
	    /* value for minmax_build.version */
	static constexpr std::uint32_t kBcrMinmaxBuildVersion{2UL};
	    /* value for barrel_build */
	static constexpr std::uint32_t kBcrBarrelBuild{0x00000303UL};
	    /* value for barrel_build.version */
	static constexpr std::uint32_t kBcrBarrelBuildVersion{3UL};
	    /* value for barrel_build.shift_option */
	static constexpr std::uint32_t kBcrBarrelBuildShiftOption{3UL};
	    /* value for bpu_build */
	static constexpr std::uint32_t kBcrBpuBuild{0x00A91106UL};
	    /* value for bpu_build.version */
	static constexpr std::uint32_t kBcrBpuBuildVersion{6UL};
	    /* value for bpu_build.bce */
	static constexpr std::uint32_t kBcrBpuBuildBce{1UL};
	    /* value for bpu_build.pte */
	static constexpr std::uint32_t kBcrBpuBuildPte{2UL};
	    /* value for bpu_build.rse */
	static constexpr std::uint32_t kBcrBpuBuildRse{0UL};
	    /* value for bpu_build.ft */
	static constexpr std::uint32_t kBcrBpuBuildFt{1UL};
	    /* value for bpu_build.ts */
	static constexpr std::uint32_t kBcrBpuBuildTs{20UL};
	    /* value for bpu_build.tqe */
	static constexpr std::uint32_t kBcrBpuBuildTqe{2UL};
	    /* value for bpu_build.fbe */
	static constexpr std::uint32_t kBcrBpuBuildFbe{0UL};
	    /* value for bpu_build.bdb */
	static constexpr std::uint32_t kBcrBpuBuildBdb{0UL};
	    /* value for isa_config */
	static constexpr std::uint32_t kBcrIsaConfig{0x23E47402UL};
	    /* value for isa_config.res1 */
	static constexpr std::uint32_t kBcrIsaConfigRes1{0UL};
	    /* value for isa_config.d */
	static constexpr std::uint32_t kBcrIsaConfigD{2UL};
	    /* value for isa_config.res2 */
	static constexpr std::uint32_t kBcrIsaConfigRes2{0UL};
	    /* value for isa_config.f */
	static constexpr std::uint32_t kBcrIsaConfigF{0UL};
	    /* value for isa_config.c */
	static constexpr std::uint32_t kBcrIsaConfigC{3UL};
	    /* value for isa_config.l */
	static constexpr std::uint32_t kBcrIsaConfigL{1UL};
	    /* value for isa_config.n */
	static constexpr std::uint32_t kBcrIsaConfigN{1UL};
	    /* value for isa_config.a */
	static constexpr std::uint32_t kBcrIsaConfigA{1UL};
	    /* value for isa_config.b */
	static constexpr std::uint32_t kBcrIsaConfigB{0UL};
	    /* value for isa_config.addr_size */
	static constexpr std::uint32_t kBcrIsaConfigAddrSize{4UL};
	    /* value for isa_config.lpc_size */
	static constexpr std::uint32_t kBcrIsaConfigLpcSize{7UL};
	    /* value for isa_config.pc_size */
	static constexpr std::uint32_t kBcrIsaConfigPcSize{4UL};
	    /* value for isa_config.version */
	static constexpr std::uint32_t kBcrIsaConfigVersion{2UL};
	    /* value for stack_region_build */
	static constexpr std::uint32_t kBcrStackRegionBuild{0x00000002UL};
	    /* value for erp_build */
	static constexpr std::uint32_t kBcrErpBuild{0x050B4505UL};
	    /* value for erp_build.l */
	static constexpr std::uint32_t kBcrErpBuildL{0UL};
	    /* value for erp_build.wd */
	static constexpr std::uint32_t kBcrErpBuildWd{0UL};
	    /* value for erp_build.c */
	static constexpr std::uint32_t kBcrErpBuildC{0UL};
	    /* value for erp_build.app */
	static constexpr std::uint32_t kBcrErpBuildApp{0UL};
	    /* value for erp_build.mmu */
	static constexpr std::uint32_t kBcrErpBuildMmu{5UL};
	    /* value for erp_build.pipe_edc */
	static constexpr std::uint32_t kBcrErpBuildPipeEdc{0UL};
	    /* value for erp_build.vccm */
	static constexpr std::uint32_t kBcrErpBuildVccm{0UL};
	    /* value for erp_build.rf */
	static constexpr std::uint32_t kBcrErpBuildRf{0UL};
	    /* value for erp_build.pc */
	static constexpr std::uint32_t kBcrErpBuildPc{0UL};
	    /* value for erp_build.ic */
	static constexpr std::uint32_t kBcrErpBuildIc{5UL};
	    /* value for erp_build.dc */
	static constexpr std::uint32_t kBcrErpBuildDc{5UL};
	    /* value for erp_build.ip */
	static constexpr std::uint32_t kBcrErpBuildIp{0UL};
	    /* value for erp_build.dp */
	static constexpr std::uint32_t kBcrErpBuildDp{5UL};
	    /* value for erp_build.version */
	static constexpr std::uint32_t kBcrErpBuildVersion{5UL};
	    /* value for cluster_build */
	static constexpr std::uint32_t kBcrClusterBuild{0x40000107UL};
	    /* value for cluster_build.scu_trace */
	static constexpr std::uint32_t kBcrClusterBuildScuTrace{0UL};
	    /* value for cluster_build.gate */
	static constexpr std::uint32_t kBcrClusterBuildGate{1UL};
	    /* value for cluster_build.sm */
	static constexpr std::uint32_t kBcrClusterBuildSm{0UL};
	    /* value for cluster_build.sf */
	static constexpr std::uint32_t kBcrClusterBuildSf{0UL};
	    /* value for cluster_build.per */
	static constexpr std::uint32_t kBcrClusterBuildPer{0UL};
	    /* value for cluster_build.c */
	static constexpr std::uint32_t kBcrClusterBuildC{0UL};
	    /* value for cluster_build.num_entries */
	static constexpr std::uint32_t kBcrClusterBuildNumEntries{0UL};
	    /* value for cluster_build.sclk */
	static constexpr std::uint32_t kBcrClusterBuildSclk{0UL};
	    /* value for cluster_build.cc_wbuf */
	static constexpr std::uint32_t kBcrClusterBuildCcWbuf{0UL};
	    /* value for cluster_build.num_cores */
	static constexpr std::uint32_t kBcrClusterBuildNumCores{1UL};
	    /* value for cluster_build.version */
	static constexpr std::uint32_t kBcrClusterBuildVersion{7UL};
	    /* value for biu_build */
	static constexpr std::uint32_t kBcrBiuBuild{0x10008101UL};
	    /* value for biu_build.separate_clk */
	static constexpr std::uint32_t kBcrBiuBuildSeparateClk{0UL};
	    /* value for biu_build.bus_ecc_parity_option */
	static constexpr std::uint32_t kBcrBiuBuildBusEccParityOption{1UL};
	    /* value for biu_build.bus_ecc_data_option */
	static constexpr std::uint32_t kBcrBiuBuildBusEccDataOption{0UL};
	    /* value for biu_build.bus_ecc_en */
	static constexpr std::uint32_t kBcrBiuBuildBusEccEn{0UL};
	    /* value for biu_build.uslv_access_per1 */
	static constexpr std::uint32_t kBcrBiuBuildUslvAccessPer1{0UL};
	    /* value for biu_build.uslv_ioc_full_coh */
	static constexpr std::uint32_t kBcrBiuBuildUslvIocFullCoh{0UL};
	    /* value for biu_build.uslv_support_ioc */
	static constexpr std::uint32_t kBcrBiuBuildUslvSupportIoc{0UL};
	    /* value for biu_build.uslv_bus */
	static constexpr std::uint32_t kBcrBiuBuildUslvBus{0UL};
	    /* value for biu_build.dmi_bus */
	static constexpr std::uint32_t kBcrBiuBuildDmiBus{1UL};
	    /* value for biu_build.ioc_bus */
	static constexpr std::uint32_t kBcrBiuBuildIocBus{0UL};
	    /* value for biu_build.per_bus */
	static constexpr std::uint32_t kBcrBiuBuildPerBus{0UL};
	    /* value for biu_build.mem_bus */
	static constexpr std::uint32_t kBcrBiuBuildMemBus{1UL};
	    /* value for biu_build.version */
	static constexpr std::uint32_t kBcrBiuBuildVersion{1UL};
	    /* value for npu_build */
	static constexpr std::uint32_t kBcrNpuBuild{0x703CEC11UL};
	    /* value for npu_build.version */
	static constexpr std::uint32_t kBcrNpuBuildVersion{17UL};
	    /* value for npu_build.sl */
	static constexpr std::uint32_t kBcrNpuBuildSl{12UL};
	    /* value for npu_build.ecc */
	static constexpr std::uint32_t kBcrNpuBuildEcc{1UL};
	    /* value for npu_build.l2 */
	static constexpr std::uint32_t kBcrNpuBuildL2{1UL};
	    /* value for npu_build.l1 */
	static constexpr std::uint32_t kBcrNpuBuildL1{1UL};
	    /* value for npu_build.mc */
	static constexpr std::uint32_t kBcrNpuBuildMc{4UL};
	    /* value for npu_build.evt */
	static constexpr std::uint32_t kBcrNpuBuildEvt{1UL};
	    /* value for npu_build.vm */
	static constexpr std::uint32_t kBcrNpuBuildVm{4UL};
	    /* value for npu_build.am */
	static constexpr std::uint32_t kBcrNpuBuildAm{3UL};
	    /* value for ewdt_build */
	static constexpr std::uint32_t kBcrEwdtBuild{0xC0004402UL};
	    /* value for ewdt_build.separate_clock */
	static constexpr std::uint32_t kBcrEwdtBuildSeparateClock{1UL};
	    /* value for ewdt_build.parity_check */
	static constexpr std::uint32_t kBcrEwdtBuildParityCheck{1UL};
	    /* value for ewdt_build.ext_input */
	static constexpr std::uint32_t kBcrEwdtBuildExtInput{0UL};
	    /* value for ewdt_build.timer_size */
	static constexpr std::uint32_t kBcrEwdtBuildTimerSize{1UL};
	    /* value for ewdt_build.window */
	static constexpr std::uint32_t kBcrEwdtBuildWindow{1UL};
	    /* value for ewdt_build.num_timers */
	static constexpr std::uint32_t kBcrEwdtBuildNumTimers{0UL};
	    /* value for ewdt_build.version */
	static constexpr std::uint32_t kBcrEwdtBuildVersion{2UL};
	    /* value for rtt_build */
	static constexpr std::uint32_t kBcrRttBuild{0x00080108UL};
	    /* value for rtt_build.prod_src_num */
	static constexpr std::uint32_t kBcrRttBuildProdSrcNum{0UL};
	    /* value for rtt_build.fl */
	static constexpr std::uint32_t kBcrRttBuildFl{0UL};
	    /* value for rtt_build.pi */
	static constexpr std::uint32_t kBcrRttBuildPi{1UL};
	    /* value for rtt_build.version */
	static constexpr std::uint32_t kBcrRttBuildVersion{8UL};
	    /* value for irq_build */
	static constexpr std::uint32_t kBcrIrqBuild{0x02242702UL};
	    /* value for irq_build.raz */
	static constexpr std::uint32_t kBcrIrqBuildRaz{0UL};
	    /* value for irq_build.nmi */
	static constexpr std::uint32_t kBcrIrqBuildNmi{0UL};
	    /* value for irq_build.f */
	static constexpr std::uint32_t kBcrIrqBuildF{0UL};
	    /* value for irq_build.p */
	static constexpr std::uint32_t kBcrIrqBuildP{2UL};
	    /* value for irq_build.exts */
	static constexpr std::uint32_t kBcrIrqBuildExts{36UL};
	    /* value for irq_build.irqs */
	static constexpr std::uint32_t kBcrIrqBuildIrqs{39UL};
	    /* value for irq_build.version */
	static constexpr std::uint32_t kBcrIrqBuildVersion{2UL};
	    /* value for pct_build */
	static constexpr std::uint32_t kBcrPctBuild{0x00080503UL};
	    /* value for pct_build.version */
	static constexpr std::uint32_t kBcrPctBuildVersion{3UL};
	    /* value for pct_build.s */
	static constexpr std::uint32_t kBcrPctBuildS{1UL};
	    /* value for pct_build.i */
	static constexpr std::uint32_t kBcrPctBuildI{1UL};
	    /* value for pct_build.c */
	static constexpr std::uint32_t kBcrPctBuildC{8UL};
	    /* value for cc_build */
	static constexpr std::uint32_t kBcrCcBuild{0x007F0002UL};
	    /* value for cc_build.version */
	static constexpr std::uint32_t kBcrCcBuildVersion{2UL};
	    /* value for cc_build.cc */
	static constexpr std::uint32_t kBcrCcBuildCc{127UL};
	    /* value for isa_profile */
	static constexpr std::uint32_t kBcrIsaProfile{0x00011101UL};
	    /* value for isa_profile.g4 */
	static constexpr std::uint32_t kBcrIsaProfileG4{0UL};
	    /* value for isa_profile.g3 */
	static constexpr std::uint32_t kBcrIsaProfileG3{1UL};
	    /* value for isa_profile.g2 */
	static constexpr std::uint32_t kBcrIsaProfileG2{1UL};
	    /* value for isa_profile.g1 */
	static constexpr std::uint32_t kBcrIsaProfileG1{1UL};
	    /* value for isa_profile.version */
	static constexpr std::uint32_t kBcrIsaProfileVersion{1UL};
	    /* value for micro_arch_build */
	static constexpr std::uint32_t kBcrMicroArchBuild{0x00030302UL};
	    /* value for micro_arch_build.minor_rev */
	static constexpr std::uint32_t kBcrMicroArchBuildMinorRev{2UL};
	    /* value for micro_arch_build.major_rev */
	static constexpr std::uint32_t kBcrMicroArchBuildMajorRev{3UL};
	    /* value for micro_arch_build.product_family */
	static constexpr std::uint32_t kBcrMicroArchBuildProductFamily{3UL};
	    /* value for micro_arch_build.reserved */
	static constexpr std::uint32_t kBcrMicroArchBuildReserved{0UL};
	    /* value for smart_build */
	static constexpr std::uint32_t kBcrSmartBuild{0x00020004UL};
	    /* value for smart_build.version */
	static constexpr std::uint32_t kBcrSmartBuildVersion{4UL};
	    /* value for smart_build.stack_size */
	static constexpr std::uint32_t kBcrSmartBuildStackSize{128UL};
	    /* value for data_mem_attr */
	static constexpr std::uint32_t kCirDataMemAttr{0x00000003UL};
	    /* value for cluster_id */
	static constexpr std::uint32_t kCirClusterId{0x00000000UL};
	    /* value for cluster_id.cluster_num */
	static constexpr std::uint32_t kCirClusterIdClusterNum{0UL};
	/************* End of BCR/CIR Macros **********************/
	    /* value for family */
	static constexpr std::uint32_t kFamily{5UL};
	    /* value for core_version */
	static constexpr std::uint32_t kCoreVersion{4UL};
	    // coverity[autosar_cpp14_a3_9_1_violation]
	    /* value for family_name */
	static constexpr char const* const kFamilyName{"arcv2hs"};
	    /* value for uarch_rev_major */
	static constexpr std::uint32_t kUarchRevMajor{3UL};
	    /* value for uarch_rev_minor */
	static constexpr std::uint32_t kUarchRevMinor{2UL};
	    /* value for early_and_late_basic_alu */
	static constexpr std::uint32_t kEarlyAndLateBasicAlu{1UL};
	    /* value for code_density */
	static constexpr std::uint32_t kCodeDensity{1UL};
	    /* value for rgf_num_banks */
	static constexpr std::uint32_t kRgfNumBanks{1UL};
	    /* value for rgf_num_wr_ports */
	static constexpr std::uint32_t kRgfNumWrPorts{2UL};
	    // coverity[autosar_cpp14_a3_9_1_violation]
	    /* value for endian */
	static constexpr char const* const kEndian{"little"};
	    /* value for endian_little */
	static constexpr std::uint32_t kEndianLittle{1UL};
	    /* value for endian_big */
	static constexpr std::uint32_t kEndianBig{0UL};
	    /* value for lpc_size */
	static constexpr std::uint32_t kLpcSize{32UL};
	    /* value for pc_size */
	static constexpr std::uint32_t kPcSize{32UL};
	    /* value for addr_size */
	static constexpr std::uint32_t kAddrSize{32UL};
	    /* value for atomic */
	static constexpr std::uint32_t kAtomic{1UL};
	    /* value for ll64 */
	static constexpr std::uint32_t kLl64{1UL};
	    /* value for unaligned */
	static constexpr std::uint32_t kUnaligned{1UL};
	    // coverity[autosar_cpp14_a3_9_1_violation]
	    /* value for div_rem */
	static constexpr char const* const kDivRem{"radix4"};
	    /* value for div_rem_radix4 */
	static constexpr std::uint32_t kDivRemRadix4{1UL};
	    /* value for swap */
	static constexpr std::uint32_t kSwap{1UL};
	    /* value for bitscan */
	static constexpr std::uint32_t kBitscan{1UL};
	    // coverity[autosar_cpp14_a3_9_1_violation]
	    /* value for mpy_option */
	static constexpr char const* const kMpyOption{"qmpyh"};
	    /* value for mpy_option_num */
	static constexpr std::uint32_t kMpyOptionNum{9UL};
	    /* value for shift_assist */
	static constexpr std::uint32_t kShiftAssist{1UL};
	    /* value for barrel_shifter */
	static constexpr std::uint32_t kBarrelShifter{1UL};
	    /* value for timer0 */
	static constexpr std::uint32_t kTimer0{1UL};
	    /* value for timer0_level */
	static constexpr std::uint32_t kTimer0Level{0UL};
	    /* value for timer0.vector */
	static constexpr std::uint32_t kTimer0Vector{16UL};
	    /* value for rtc */
	static constexpr std::uint32_t kRtc{1UL};
	    /* value for action_points */
	static constexpr std::uint32_t kActionPoints{8UL};
	    /* value for stack_check */
	static constexpr std::uint32_t kStackCheck{1UL};
	    /* value for volatile_base */
	static constexpr std::uint32_t kVolatileBase{15UL};
	    /* value for volatile_limit */
	static constexpr std::uint32_t kVolatileLimit{0UL};
	    /* value for volatile_strict_ordering */
	static constexpr std::uint32_t kVolatileStrictOrdering{1UL};
	    /* value for bpu_bc_entries */
	static constexpr std::uint32_t kBpuBcEntries{512UL};
	    /* value for bpu_pt_entries */
	static constexpr std::uint32_t kBpuPtEntries{8192UL};
	    /* value for bpu_rs_entries */
	static constexpr std::uint32_t kBpuRsEntries{4UL};
	    /* value for bpu_bc_full_tag */
	static constexpr std::uint32_t kBpuBcFullTag{1UL};
	    /* value for bpu_bc_tag_size */
	static constexpr std::uint32_t kBpuBcTagSize{20UL};
	    /* value for bpu_tosq_entries */
	static constexpr std::uint32_t kBpuTosqEntries{5UL};
	    /* value for bpu_fb_entries */
	static constexpr std::uint32_t kBpuFbEntries{1UL};
	    /* value for smart_version */
	static constexpr std::uint32_t kSmartVersion{4UL};
	    /* value for smart_stack_entries */
	static constexpr std::uint32_t kSmartStackEntries{128UL};
	    /* value for mpu.present */
	static constexpr std::uint32_t kMpuPresent{1UL};
	    /* value for mpu_version */
	static constexpr std::uint32_t kMpuVersion{3UL};
	    /* value for mpuv3 */
	static constexpr std::uint32_t kMpuv3{1UL};
	    /* value for mpu.regions */
	static constexpr std::uint32_t kMpuRegions{8UL};
	    /* value for mmu_version */
	static constexpr std::uint32_t kMmuVersion{4UL};
	    /* value for mmuv4.present */
	static constexpr std::uint32_t kMmuv4Present{1UL};
	    /* value for mmuv4 */
	static constexpr std::uint32_t kMmuv4{1UL};
	    /* value for mmu_pgsz */
	static constexpr std::uint32_t kMmuPgsz{4096UL};
	    // coverity[autosar_cpp14_a3_9_1_violation]
	    /* value for mmu_pgsz */
	static constexpr char const* const kMmuPgsz_KM{"4K"};
	    /* value for mmu_ntlb_entries */
	static constexpr std::uint32_t kMmuNtlbEntries{256UL};
	    /* value for mmu_stlb_entries */
	static constexpr std::uint32_t kMmuStlbEntries{16UL};
	    /* value for mmu_super_pgsz */
	static constexpr std::uint32_t kMmuSuperPgsz{2097152UL};
	    // coverity[autosar_cpp14_a3_9_1_violation]
	    /* value for mmu_super_pgsz */
	static constexpr char const* const kMmuSuperPgsz_KM{"2M"};
	    /* value for mmu_pae40 */
	static constexpr std::uint32_t kMmuPae40{1UL};
	    /* value for mmu_sasid */
	static constexpr std::uint32_t kMmuSasid{1UL};
	    /* value for interrupts.present */
	static constexpr std::uint32_t kInterruptsPresent{1UL};
	    /* value for interrupts.number */
	static constexpr std::uint32_t kInterruptsNumber{39UL};
	    /* value for interrupts.priorities */
	static constexpr std::uint32_t kInterruptsPriorities{3UL};
	    /* value for interrupts.externals */
	static constexpr std::uint32_t kInterruptsExternals{36UL};
	    /* value for interrupts */
	static constexpr std::uint32_t kInterrupts{39UL};
	    /* value for interrupt_priorities */
	static constexpr std::uint32_t kInterruptPriorities{3UL};
	    /* value for ext_interrupts */
	static constexpr std::uint32_t kExtInterrupts{36UL};
	    /* value for interrupts.base */
	static constexpr std::uint32_t kInterruptsBase{0x0UL};
	    /* value for intvbase_ext */
	static constexpr std::uint32_t kIntvbaseExt{1UL};
	    /* value for dcache.present */
	static constexpr std::uint32_t kDcachePresent{1UL};
	    /* value for dcache.size */
	static constexpr std::uint32_t kDcacheSize{32768UL};
	    /* value for dcache.line_size */
	static constexpr std::uint32_t kDcacheLineSize{64UL};
	    /* value for dcache.ways */
	static constexpr std::uint32_t kDcacheWays{2UL};
	    /* value for dcache_version */
	static constexpr std::uint32_t kDcacheVersion{5UL};
	    /* value for dcache_feature */
	static constexpr std::uint32_t kDcacheFeature{2UL};
	    /* value for dcache_mem_cycles */
	static constexpr std::uint32_t kDcacheMemCycles{2UL};
	    /* value for icache.present */
	static constexpr std::uint32_t kIcachePresent{1UL};
	    /* value for icache.size */
	static constexpr std::uint32_t kIcacheSize{32768UL};
	    /* value for icache.line_size */
	static constexpr std::uint32_t kIcacheLineSize{64UL};
	    /* value for icache.ways */
	static constexpr std::uint32_t kIcacheWays{4UL};
	    /* value for icache_version */
	static constexpr std::uint32_t kIcacheVersion{4UL};
	    /* value for icache_feature */
	static constexpr std::uint32_t kIcacheFeature{2UL};
	    /* value for dccm.present */
	static constexpr std::uint32_t kDccmPresent{1UL};
	    /* value for dccm_size */
	static constexpr std::uint32_t kDccmSize{0x8000UL};
	    /* value for dccm_base */
	static constexpr std::uint32_t kDccmBase{0x70000000UL};
	    /* value for dccm_mem_cycles */
	static constexpr std::uint32_t kDccmMemCycles{2UL};
	    /* value for dccm_dmi */
	static constexpr std::uint32_t kDccmDmi{1UL};
	    /* value for dccm_sys_base_core0 */
	static constexpr std::uint32_t kDccmSysBaseCore0{0x42000000UL};
	    /* value for dccm_sys_base */
	static constexpr std::uint32_t kDccmSysBase{0x42000000UL};
	    /* value for watchdog_num */
	static constexpr std::uint32_t kWatchdogNum{1UL};
	    /* value for watchdog_parity */
	static constexpr std::uint32_t kWatchdogParity{1UL};
	    /* value for watchdog_clk */
	static constexpr std::uint32_t kWatchdogClk{1UL};
	    /* value for watchdog_size0 */
	static constexpr std::uint32_t kWatchdogSize0{32UL};
	    /* value for watchdog_win0 */
	static constexpr std::uint32_t kWatchdogWin0{1UL};
	    /* value for watchdog_clk_freq */
	static constexpr std::uint32_t kWatchdogClkFreq{200UL};
	    /* value for error_prot_ver */
	static constexpr std::uint32_t kErrorProtVer{5UL};
	    // coverity[autosar_cpp14_a3_9_1_violation]
	    /* value for dccm_prot */
	static constexpr char const* const kDccmProt{"ecc_01"};
	    // coverity[autosar_cpp14_a3_9_1_violation]
	    /* value for dccm_prot_level */
	static constexpr char const* const kDccmProtLevel{"data_only"};
	    /* value for dccm_prot_val */
	static constexpr std::uint32_t kDccmProtVal{5UL};
	    // coverity[autosar_cpp14_a3_9_1_violation]
	    /* value for ic_prot */
	static constexpr char const* const kIcProt{"ecc_01"};
	    // coverity[autosar_cpp14_a3_9_1_violation]
	    /* value for ic_prot_level */
	static constexpr char const* const kIcProtLevel{"data_only"};
	    /* value for ic_prot_val */
	static constexpr std::uint32_t kIcProtVal{5UL};
	    // coverity[autosar_cpp14_a3_9_1_violation]
	    /* value for dc_prot */
	static constexpr char const* const kDcProt{"ecc_01"};
	    // coverity[autosar_cpp14_a3_9_1_violation]
	    /* value for dc_prot_level */
	static constexpr char const* const kDcProtLevel{"data_only"};
	    /* value for dc_prot_val */
	static constexpr std::uint32_t kDcProtVal{5UL};
	    // coverity[autosar_cpp14_a3_9_1_violation]
	    /* value for mmu_prot */
	static constexpr char const* const kMmuProt{"ecc_01"};
	    // coverity[autosar_cpp14_a3_9_1_violation]
	    /* value for mmu_prot_level */
	static constexpr char const* const kMmuProtLevel{"data_only"};
	    /* value for mmu_prot_val */
	static constexpr std::uint32_t kMmuProtVal{5UL};
	    /* value for pct_counters */
	static constexpr std::uint32_t kPctCounters{8UL};
	    /* value for pct_interrupt */
	static constexpr std::uint32_t kPctInterrupt{1UL};
	    /* value for cluster_version */
	static constexpr std::uint32_t kClusterVersion{7UL};
	    /* value for cluster_num_cores */
	static constexpr std::uint32_t kClusterNumCores{1UL};
	    /* value for clock_gating */
	static constexpr std::uint32_t kClockGating{1UL};
	    /* value for data_memory_initiator */
	static constexpr std::uint32_t kDataMemoryInitiator{0UL};
	    /* value for clock_speed */
	static constexpr std::uint32_t kClockSpeed{800UL};
    } // namespace core_config

} // namespace snps_arc

#endif /* core_config_hpp */


