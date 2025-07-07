CCT_ACCL    =
CCT_ARC     =
CCT_SYS     =
CCT_ARCSYNC =
CCT_PWR_EN ?= 0
CCT_ADV_EN ?= 0

# Internal SRAM access
CCT_ARC     += am_ldst vm_ldst dm_ldst 
CCT_ACCL    += l2dm_ldst csm_ldst
CCT_ACCL    += npu_hwv_vmids
CCT_ACCL    += l2arc1_dm_ldst

# AXI ports traffics
CCT_ARC     += xm_ldst npu_slice_dmi_ldst

# DMA/STU data transfers
CCT_ACCL    += npu_slice_dma_3d_trans npu_slice_dma_1d_trans npu_slice_dma_init
CCT_ACCL    += stu3_csm0_xm
CCT_ACCL    += npu_stu_3d_trans npu_stu_1d_trans npu_stu_dma_paral

# Accelerator functions
CCT_ACCL    += npu_conv
CCT_ACCL    += npu_conv_prelu_pool_shallow

# Trace & Debug
CCT_ACCL    += npu_trace_swe 
CCT_ARC     += npu_trace_l2
CCT_ARC     += dbg_apb_rom_rd



# ARCSync control and sync
CCT_ARCSYNC += arcsync_npu_ctrl arcsync_gfrc arcsync_ac_ack1

# System memory map and access
CCT_ARC     += npu_dmi_ldst

# Safety
CCT_ARC     += vm_am_init
CCT_ARC     += vm_am_ecc
CCT_ARC     += dm_ecc
CCT_ARC     += csm_ecc


# HWV
CCT_ARC     += npx_hwv_evm

# Power management
CCT_ARCSYNC +=  pmu_slc_dmi
CCT_ARCSYNC +=  pmu_npx

# Power CCTs
CCT_PWR = 
CCT_PWR += npu_idle_pwr npu_conv_1x1_pwr_normal npu_conv_1x1_pwr_sparse npu_fused_pwr npu_full_accl_pwr_zebu
CCT_PWR += npu_conv_1x1_pwr_normal_fp npu_fused_pwr_fp

# BCR
CCT_ARC     += npu_bcr

# Advance CCTs
CCT_ADV =

# System level CCTs w/ long simulation time

CCT_ARC     += npu_mmu
CCT_ARC     += apex_evm_irq

# validate BPU memory replacement
CCT_ARC     += npu_dhrystone_sl0



ifneq ($(CCT_SYS_EN),0)
CCT_ACCL      += $(CCT_SYS)
endif
ifneq ($(CCT_PWR_EN),0)
CCT_ARC       += $(CCT_PWR)
endif
ifneq ($(CCT_ADV_EN),0)
CCT_ACCL      += $(CCT_ADV)
endif
CCT_LIST      := $(CCT_ACCL) $(CCT_ARC) $(CCT_ARCSYNC)
CCT_INST_LIST  = $(CCT_LIST) $(CCT_SYS) $(CCT_PWR) $(CCT_ADV)
