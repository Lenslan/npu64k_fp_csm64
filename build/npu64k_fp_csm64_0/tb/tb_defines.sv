/*
 * Copyright (C) 2021-2022 Synopsys, Inc. All rights reserved.
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


`ifndef NPU_TB_DEFINS_SV
`define NPU_TB_DEFINS_SV

`define SVT_AXI_MAX_ADDR_DELAY 1000  
`define SVT_AXI_MAX_WREADY_DELAY 1000
`define SVT_AXI_MAX_RVALID_DELAY 1000
`define SVT_AXI_MAX_RREADY_DELAY 1000
`define SVT_AXI_MAX_WRITE_RESP_DELAY 1000
`define SVT_AXI_MAX_ADDR_WIDTH 40
`define SVT_DISABLE_MSG 

`define ARC_ADDR_MSB 39

`ifdef IS_NPU_SLICE_TB
    `define TB_TOP         ns_tb_top
    `define NPU_SL0        `TB_TOP.u_npu_slice
`else //multi slices
  `ifdef TB_MSS
    `define TB_TOP         npu_tb_top.u_core_chip_tb
    `define CORE_CHIP      `TB_TOP.u_core_chip
    `define CORE_SYS       `CORE_CHIP.icore_sys
    `define CORE_SYS_STUB  `CORE_CHIP.icore_sys_stub
    `define ARCHIPELAGO    `CORE_SYS.icore_archipelago
    `define MSS_MEM         `CORE_SYS.ialb_mss_mem.u_rgon0_mem_inst.u_alb_mss_mem_ram
  `else
    `define TB_TOP         npu_tb_top.u_core_chip_tb
    `define ARCHIPELAGO    `TB_TOP.icore_archipelago
  `endif
    `define TB_HOST        `TB_TOP.i_host
    `define VPX_ARCHIPELAGO `ARCHIPELAGO.iarchipelago
    `define ARCHPLGO_STUB  `ARCHIPELAGO.icore_archipelago_stub
    `define TB_INTF        `TB_TOP.tb_if
    `define NPU_TOP        `ARCHIPELAGO.inpu_top
    `define NPU_AON        `NPU_TOP.u_npu_core.u_npu_core_aon.u_npu_top_aon
    `define CLN_AUX_REG    `NPU_TOP.u_npu_group0.u_cln_core.u_slv_aux.u_aux_regs
    `define ARCSYNC_PATH   `ARCHIPELAGO.iarcsync_top
    `define L2ARC_GRP      `NPU_TOP.u_npu_core.u_npu_core_pd.u_l2arc_grp
    `define NPU_GRP0      `NPU_TOP.u_npu_core.u_npu_core_pd.u_npu_group0
    `define CLN_GRP0      `NPU_GRP0.u_cln_grp_inst
    `define NPU_GRP1      `NPU_TOP.u_npu_core.u_npu_core_pd.u_npu_group1
    `define CLN_GRP1      `NPU_GRP1.u_cln_grp_inst
    `define NPU_GRP2      `NPU_TOP.u_npu_core.u_npu_core_pd.u_npu_group2
    `define CLN_GRP2      `NPU_GRP2.u_cln_grp_inst
    `define NPU_GRP3      `NPU_TOP.u_npu_core.u_npu_core_pd.u_npu_group3
    `define CLN_GRP3      `NPU_GRP3.u_cln_grp_inst
    `define L2_DPI_ARC     `NPU_TOP.u_npu_core.u_npu_core_pd.u_l2arc_grp.u_npu_l2_arc0
    `define L2_ARC         `NPU_TOP.u_npu_core.u_npu_core_pd.u_l2arc_grp.u_npu_l2_arc0
    `define L2_ARC_IF      `L2_ARC 
      `define L2_1_DPI_ARC     `NPU_TOP.u_npu_core.u_npu_core_pd.u_l2arc_grp.u_npu_l2_arc1
      `define L2_1_ARC         `NPU_TOP.u_npu_core.u_npu_core_pd.u_l2arc_grp.u_npu_l2_arc1
      `define L2_1_ARC_IF      `L2_1_ARC
    `define SL0_TOP     `NPU_TOP.u_l1core0
    `define NPU_SL0       `SL0_TOP.u_npu_slice
    `define SL1_TOP     `NPU_TOP.u_l1core1
    `define NPU_SL1       `SL1_TOP.u_npu_slice
    `define SL2_TOP     `NPU_TOP.u_l1core2
    `define NPU_SL2       `SL2_TOP.u_npu_slice
    `define SL3_TOP     `NPU_TOP.u_l1core3
    `define NPU_SL3       `SL3_TOP.u_npu_slice
    `define SL4_TOP     `NPU_TOP.u_l1core4
    `define NPU_SL4       `SL4_TOP.u_npu_slice
    `define SL5_TOP     `NPU_TOP.u_l1core5
    `define NPU_SL5       `SL5_TOP.u_npu_slice
    `define SL6_TOP     `NPU_TOP.u_l1core6
    `define NPU_SL6       `SL6_TOP.u_npu_slice
    `define SL7_TOP     `NPU_TOP.u_l1core7
    `define NPU_SL7       `SL7_TOP.u_npu_slice
    `define SL8_TOP     `NPU_TOP.u_l1core8
    `define NPU_SL8       `SL8_TOP.u_npu_slice
    `define SL9_TOP     `NPU_TOP.u_l1core9
    `define NPU_SL9       `SL9_TOP.u_npu_slice
    `define SL10_TOP     `NPU_TOP.u_l1core10
    `define NPU_SL10       `SL10_TOP.u_npu_slice
    `define SL11_TOP     `NPU_TOP.u_l1core11
    `define NPU_SL11       `SL11_TOP.u_npu_slice
    `define SL12_TOP     `NPU_TOP.u_l1core12
    `define NPU_SL12       `SL12_TOP.u_npu_slice
    `define SL13_TOP     `NPU_TOP.u_l1core13
    `define NPU_SL13       `SL13_TOP.u_npu_slice
    `define SL14_TOP     `NPU_TOP.u_l1core14
    `define NPU_SL14       `SL14_TOP.u_npu_slice
    `define SL15_TOP     `NPU_TOP.u_l1core15
    `define NPU_SL15       `SL15_TOP.u_npu_slice
    `define L2_CPU_TOP     `L2_ARC.ialb_cpu_top
    `define L2_ALB_CPU     `L2_CPU_TOP.u_alb_cpu
    `define L2_CORE        `L2_ALB_CPU.u_alb_pd1.u_alb_core
    `define L2_EXU         `L2_CORE.u_alb_exu
    `define L2_EXEC_PIPE   `L2_EXU.u_alb_exec_pipe
    `define L2_EXEC_EIA    `L2_EXEC_PIPE.u_alb_eia_pipe
    `define L2_EXEC_EVTM   `L2_EXEC_EIA.u_uxEventManage
    `define L2_EXEC_CMT    `L2_EXEC_PIPE.u_alb_commit
    `define L2_EXEC_EXCPN  `L2_EXEC_PIPE.u_alb_excpn_pipe
    `define L2_EXEC_CTRL   `L2_EXEC_PIPE.u_alb_exec_ctrl
    `define L2_EXEC_IRQ    `L2_EXEC_CTRL.irq_ack

    `define L2_1_CPU_TOP     `L2_1_ARC.ialb_cpu_top
    `define L2_1_ALB_CPU     `L2_1_CPU_TOP.u_alb_cpu
    `define L2_1_CORE        `L2_1_ALB_CPU.u_alb_pd1.u_alb_core
    `define L2_1_EXU         `L2_1_CORE.u_alb_exu
    `define L2_1_EXEC_PIPE   `L2_1_EXU.u_alb_exec_pipe
    `define L2_1_EXEC_CMT    `L2_1_EXEC_PIPE.u_alb_commit
    `define L2_1_EXEC_EXCPN  `L2_1_EXEC_PIPE.u_alb_excpn_pipe
    `define L2_1_EXEC_CTRL   `L2_1_EXEC_PIPE.u_alb_exec_ctrl
    `define L2_1_EXEC_IRQ    `L2_1_EXEC_CTRL.irq_ack

    `define ISTU0_TOP        `NPU_GRP0.u_stu0_top.u_npu_istu
    `define OSTU0_TOP        `NPU_GRP0.u_stu0_top.u_npu_ostu
    `define ISTU0_CTRL       `ISTU0_TOP.u_npu_istu_ctrl
    `define OSTU0_CTRL       `OSTU0_TOP.u_npu_ostu_ctrl
    `define STU0_TOP         `NPU_GRP0.u_l2ustu0

    `define VPXC0_ARC        `VPX_ARCHIPELAGO.ihs_cluster_top.ic0alb_cpu_top
    `define VPXC0_CORE       `VPXC0_ARC.u_alb_cpu.u_alb_pd1.u_alb_core
    `define VPXC0_EXU        `VPXC0_CORE.u_alb_exu
    `define VPXC0_EXEC_PIPE  `VPXC0_EXU.u_alb_exec_pipe
    `define VPXC0_EXEC_CMT   `VPXC0_EXEC_PIPE.u_alb_commit
    `define VPXC0_EXEC_EXCPN `VPXC0_EXEC_PIPE.u_alb_excpn_pipe
    
    `define VPXC1_ARC        `VPX_ARCHIPELAGO.ihs_cluster_top.ic1alb_cpu_top
    `define VPXC1_CORE       `VPXC1_ARC.u_alb_cpu.u_alb_pd1.u_alb_core
    `define VPXC1_EXU        `VPXC1_CORE.u_alb_exu
    `define VPXC1_EXEC_PIPE  `VPXC1_EXU.u_alb_exec_pipe
    `define VPXC1_EXEC_CMT   `VPXC1_EXEC_PIPE.u_alb_commit
    `define VPXC1_EXEC_EXCPN `VPXC1_EXEC_PIPE.u_alb_excpn_pipe

    `define MSS_MEM          `CORE_SYS.ialb_mss_mem.u_rgon0_mem_inst.u_alb_mss_mem_ram
    `ifdef NPU_USE_ASIC_MEMORIES
      `define VM_MEM_BANK(BNK) `NPU_SL0.u_npu_srams.vm_inst[BNK].u_npu_mem_vec_bank.u_npu_mem_vec_bank_macro.u_mem.uut.mem_core_array
    `else
      `define VM_MEM_BANK(BNK) `NPU_SL0.u_npu_srams.vm_inst[BNK].u_npu_mem_vec_bank.u_npu_mem_vec_bank_model.mem
    `endif
`endif
//TODO, following definitions should generated from config
`define PERI_BASE_ADDR 'hf000_0000
`define DM_BASE_ADDR   `PERI_BASE_ADDR
`define AM_BASE_ADDR   `PERI_BASE_ADDR + 'h10_0000
`define VM_BASE_ADDR   `PERI_BASE_ADDR + 'h20_0000
`define IDMA_MMIO_BASE `PERI_BASE_ADDR + 'h8_0000
`define ODMA_MMIO_BASE `PERI_BASE_ADDR + 'h8_1000
`define CONV_MMIO_BASE `PERI_BASE_ADDR + 'h8_2000
`define GTOA_MMIO_BASE `PERI_BASE_ADDR + 'h8_3000
`define MAX_VM_SIZE    'h20_0000
`define MAX_AM_SIZE    'h10_0000
`define MAX_DM_SIZE    'h8_0000
`define MAX_XM_SIZE    'h8000_0000

`define VIP_XM_MEM     `TB_TOP.tb_if.npu_sys_shared_mem_0

`define NPU_SLICE_NUM_VM_BANKS ``((8*`NPU_SLICE_VSIZE+32)/3``)

//SLICE 0
`define SL0_DPI_ARC     `NPU_SL0.u_npu_l1_arc
`define SL0_ARC         `NPU_SL0.u_npu_l1_arc
`define SL0_ARC_IF      `SL0_ARC 
`define SL0_CPU_TOP     `SL0_ARC.ialb_cpu_top
`define SL0_ALB_CPU     `SL0_CPU_TOP.u_alb_cpu
`define SL0_CORE        `SL0_ALB_CPU.u_alb_pd1.u_alb_core
`define SL0_EXU         `SL0_CORE.u_alb_exu
`define SL0_EXEC_PIPE   `SL0_EXU.u_alb_exec_pipe
`define SL0_EXEC_EIA    `SL0_EXEC_PIPE.u_alb_eia_pipe
`define SL0_EXEC_EVTM   `SL0_EXEC_EIA.u_uxEventManager
`define SL0_EXEC_CMT    `SL0_EXEC_PIPE.u_alb_commit
`define SL0_EXEC_EXCPN  `SL0_EXEC_PIPE.u_alb_excpn_pipe
`define SL0_EXEC_CTRL   `SL0_EXEC_PIPE.u_alb_exec_ctrl
`define SL0_EXEC_IRQ    `SL0_EXEC_CTRL.irq_ack
`define SL0_SRAM        `NPU_SL0.u_npu_srams

`define SL0_VM_MEM_INST    `SL0_SRAM.vm_inst[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL0_VM_BNK_MODEL   `SL0_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_macro
`else
`define SL0_VM_BNK_MODEL   `SL0_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_model
`endif
`define SL0_STRING_VM_BNK  `"`SL0_VM_BNK_MODEL`"
`define SL0_AM_MEM_INST    `SL0_SRAM.am_inst_bank[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL0_AM_BNK_MODEL   `SL0_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_macro
`else
`define SL0_AM_BNK_MODEL   `SL0_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_model
`endif
`define SL0_STRING_AM_BNK  `"`SL0_AM_BNK_MODEL`"

`define SL0_CONV        `NPU_SL0.u_npu_conv
`define SL0_GTOA        `NPU_SL0.u_npu_gtoa
`define SL0_IDMA        `NPU_SL0.u_npu_idma
`define SL0_ODMA        `NPU_SL0.u_npu_odma
`define SL0_CTRL_BUS    `NPU_SL0.u_ctrl_axi_routing

`define SL0_IDMA_CTRL    `SL0_IDMA.u_npu_idma_ctrl
`define SL0_ODMA_CTRL    `SL0_ODMA.u_npu_dma_ctrl
`define SL0_CONV_CTRL    `SL0_CONV.u_ctrl_inst
`define SL0_GTOA_CTRL    `SL0_GTOA.u_gtoa_ctrl_inst

//SLICE 1
`define SL1_DPI_ARC     `NPU_SL1.u_npu_l1_arc
`define SL1_ARC         `NPU_SL1.u_npu_l1_arc
`define SL1_ARC_IF      `SL1_ARC 
`define SL1_CPU_TOP     `SL1_ARC.ialb_cpu_top
`define SL1_ALB_CPU     `SL1_CPU_TOP.u_alb_cpu
`define SL1_CORE        `SL1_ALB_CPU.u_alb_pd1.u_alb_core
`define SL1_EXU         `SL1_CORE.u_alb_exu
`define SL1_EXEC_PIPE   `SL1_EXU.u_alb_exec_pipe
`define SL1_EXEC_EIA    `SL1_EXEC_PIPE.u_alb_eia_pipe
`define SL1_EXEC_EVTM   `SL1_EXEC_EIA.u_uxEventManager
`define SL1_EXEC_CMT    `SL1_EXEC_PIPE.u_alb_commit
`define SL1_EXEC_EXCPN  `SL1_EXEC_PIPE.u_alb_excpn_pipe
`define SL1_EXEC_CTRL   `SL1_EXEC_PIPE.u_alb_exec_ctrl
`define SL1_EXEC_IRQ    `SL1_EXEC_CTRL.irq_ack
`define SL1_SRAM        `NPU_SL1.u_npu_srams

`define SL1_VM_MEM_INST    `SL1_SRAM.vm_inst[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL1_VM_BNK_MODEL   `SL1_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_macro
`else
`define SL1_VM_BNK_MODEL   `SL1_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_model
`endif
`define SL1_STRING_VM_BNK  `"`SL1_VM_BNK_MODEL`"
`define SL1_AM_MEM_INST    `SL1_SRAM.am_inst_bank[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL1_AM_BNK_MODEL   `SL1_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_macro
`else
`define SL1_AM_BNK_MODEL   `SL1_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_model
`endif
`define SL1_STRING_AM_BNK  `"`SL1_AM_BNK_MODEL`"

`define SL1_CONV        `NPU_SL1.u_npu_conv
`define SL1_GTOA        `NPU_SL1.u_npu_gtoa
`define SL1_IDMA        `NPU_SL1.u_npu_idma
`define SL1_ODMA        `NPU_SL1.u_npu_odma
`define SL1_CTRL_BUS    `NPU_SL1.u_ctrl_axi_routing

`define SL1_IDMA_CTRL    `SL1_IDMA.u_npu_idma_ctrl
`define SL1_ODMA_CTRL    `SL1_ODMA.u_npu_dma_ctrl
`define SL1_CONV_CTRL    `SL1_CONV.u_ctrl_inst
`define SL1_GTOA_CTRL    `SL1_GTOA.u_gtoa_ctrl_inst

//SLICE 2
`define SL2_DPI_ARC     `NPU_SL2.u_npu_l1_arc
`define SL2_ARC         `NPU_SL2.u_npu_l1_arc
`define SL2_ARC_IF      `SL2_ARC 
`define SL2_CPU_TOP     `SL2_ARC.ialb_cpu_top
`define SL2_ALB_CPU     `SL2_CPU_TOP.u_alb_cpu
`define SL2_CORE        `SL2_ALB_CPU.u_alb_pd1.u_alb_core
`define SL2_EXU         `SL2_CORE.u_alb_exu
`define SL2_EXEC_PIPE   `SL2_EXU.u_alb_exec_pipe
`define SL2_EXEC_EIA    `SL2_EXEC_PIPE.u_alb_eia_pipe
`define SL2_EXEC_EVTM   `SL2_EXEC_EIA.u_uxEventManager
`define SL2_EXEC_CMT    `SL2_EXEC_PIPE.u_alb_commit
`define SL2_EXEC_EXCPN  `SL2_EXEC_PIPE.u_alb_excpn_pipe
`define SL2_EXEC_CTRL   `SL2_EXEC_PIPE.u_alb_exec_ctrl
`define SL2_EXEC_IRQ    `SL2_EXEC_CTRL.irq_ack
`define SL2_SRAM        `NPU_SL2.u_npu_srams

`define SL2_VM_MEM_INST    `SL2_SRAM.vm_inst[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL2_VM_BNK_MODEL   `SL2_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_macro
`else
`define SL2_VM_BNK_MODEL   `SL2_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_model
`endif
`define SL2_STRING_VM_BNK  `"`SL2_VM_BNK_MODEL`"
`define SL2_AM_MEM_INST    `SL2_SRAM.am_inst_bank[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL2_AM_BNK_MODEL   `SL2_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_macro
`else
`define SL2_AM_BNK_MODEL   `SL2_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_model
`endif
`define SL2_STRING_AM_BNK  `"`SL2_AM_BNK_MODEL`"

`define SL2_CONV        `NPU_SL2.u_npu_conv
`define SL2_GTOA        `NPU_SL2.u_npu_gtoa
`define SL2_IDMA        `NPU_SL2.u_npu_idma
`define SL2_ODMA        `NPU_SL2.u_npu_odma
`define SL2_CTRL_BUS    `NPU_SL2.u_ctrl_axi_routing

`define SL2_IDMA_CTRL    `SL2_IDMA.u_npu_idma_ctrl
`define SL2_ODMA_CTRL    `SL2_ODMA.u_npu_dma_ctrl
`define SL2_CONV_CTRL    `SL2_CONV.u_ctrl_inst
`define SL2_GTOA_CTRL    `SL2_GTOA.u_gtoa_ctrl_inst

//SLICE 3
`define SL3_DPI_ARC     `NPU_SL3.u_npu_l1_arc
`define SL3_ARC         `NPU_SL3.u_npu_l1_arc
`define SL3_ARC_IF      `SL3_ARC 
`define SL3_CPU_TOP     `SL3_ARC.ialb_cpu_top
`define SL3_ALB_CPU     `SL3_CPU_TOP.u_alb_cpu
`define SL3_CORE        `SL3_ALB_CPU.u_alb_pd1.u_alb_core
`define SL3_EXU         `SL3_CORE.u_alb_exu
`define SL3_EXEC_PIPE   `SL3_EXU.u_alb_exec_pipe
`define SL3_EXEC_EIA    `SL3_EXEC_PIPE.u_alb_eia_pipe
`define SL3_EXEC_EVTM   `SL3_EXEC_EIA.u_uxEventManager
`define SL3_EXEC_CMT    `SL3_EXEC_PIPE.u_alb_commit
`define SL3_EXEC_EXCPN  `SL3_EXEC_PIPE.u_alb_excpn_pipe
`define SL3_EXEC_CTRL   `SL3_EXEC_PIPE.u_alb_exec_ctrl
`define SL3_EXEC_IRQ    `SL3_EXEC_CTRL.irq_ack
`define SL3_SRAM        `NPU_SL3.u_npu_srams

`define SL3_VM_MEM_INST    `SL3_SRAM.vm_inst[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL3_VM_BNK_MODEL   `SL3_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_macro
`else
`define SL3_VM_BNK_MODEL   `SL3_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_model
`endif
`define SL3_STRING_VM_BNK  `"`SL3_VM_BNK_MODEL`"
`define SL3_AM_MEM_INST    `SL3_SRAM.am_inst_bank[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL3_AM_BNK_MODEL   `SL3_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_macro
`else
`define SL3_AM_BNK_MODEL   `SL3_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_model
`endif
`define SL3_STRING_AM_BNK  `"`SL3_AM_BNK_MODEL`"

`define SL3_CONV        `NPU_SL3.u_npu_conv
`define SL3_GTOA        `NPU_SL3.u_npu_gtoa
`define SL3_IDMA        `NPU_SL3.u_npu_idma
`define SL3_ODMA        `NPU_SL3.u_npu_odma
`define SL3_CTRL_BUS    `NPU_SL3.u_ctrl_axi_routing

`define SL3_IDMA_CTRL    `SL3_IDMA.u_npu_idma_ctrl
`define SL3_ODMA_CTRL    `SL3_ODMA.u_npu_dma_ctrl
`define SL3_CONV_CTRL    `SL3_CONV.u_ctrl_inst
`define SL3_GTOA_CTRL    `SL3_GTOA.u_gtoa_ctrl_inst

//SLICE 4
`define SL4_DPI_ARC     `NPU_SL4.u_npu_l1_arc
`define SL4_ARC         `NPU_SL4.u_npu_l1_arc
`define SL4_ARC_IF      `SL4_ARC 
`define SL4_CPU_TOP     `SL4_ARC.ialb_cpu_top
`define SL4_ALB_CPU     `SL4_CPU_TOP.u_alb_cpu
`define SL4_CORE        `SL4_ALB_CPU.u_alb_pd1.u_alb_core
`define SL4_EXU         `SL4_CORE.u_alb_exu
`define SL4_EXEC_PIPE   `SL4_EXU.u_alb_exec_pipe
`define SL4_EXEC_EIA    `SL4_EXEC_PIPE.u_alb_eia_pipe
`define SL4_EXEC_EVTM   `SL4_EXEC_EIA.u_uxEventManager
`define SL4_EXEC_CMT    `SL4_EXEC_PIPE.u_alb_commit
`define SL4_EXEC_EXCPN  `SL4_EXEC_PIPE.u_alb_excpn_pipe
`define SL4_EXEC_CTRL   `SL4_EXEC_PIPE.u_alb_exec_ctrl
`define SL4_EXEC_IRQ    `SL4_EXEC_CTRL.irq_ack
`define SL4_SRAM        `NPU_SL4.u_npu_srams

`define SL4_VM_MEM_INST    `SL4_SRAM.vm_inst[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL4_VM_BNK_MODEL   `SL4_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_macro
`else
`define SL4_VM_BNK_MODEL   `SL4_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_model
`endif
`define SL4_STRING_VM_BNK  `"`SL4_VM_BNK_MODEL`"
`define SL4_AM_MEM_INST    `SL4_SRAM.am_inst_bank[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL4_AM_BNK_MODEL   `SL4_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_macro
`else
`define SL4_AM_BNK_MODEL   `SL4_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_model
`endif
`define SL4_STRING_AM_BNK  `"`SL4_AM_BNK_MODEL`"

`define SL4_CONV        `NPU_SL4.u_npu_conv
`define SL4_GTOA        `NPU_SL4.u_npu_gtoa
`define SL4_IDMA        `NPU_SL4.u_npu_idma
`define SL4_ODMA        `NPU_SL4.u_npu_odma
`define SL4_CTRL_BUS    `NPU_SL4.u_ctrl_axi_routing

`define SL4_IDMA_CTRL    `SL4_IDMA.u_npu_idma_ctrl
`define SL4_ODMA_CTRL    `SL4_ODMA.u_npu_dma_ctrl
`define SL4_CONV_CTRL    `SL4_CONV.u_ctrl_inst
`define SL4_GTOA_CTRL    `SL4_GTOA.u_gtoa_ctrl_inst

//SLICE 5
`define SL5_DPI_ARC     `NPU_SL5.u_npu_l1_arc
`define SL5_ARC         `NPU_SL5.u_npu_l1_arc
`define SL5_ARC_IF      `SL5_ARC 
`define SL5_CPU_TOP     `SL5_ARC.ialb_cpu_top
`define SL5_ALB_CPU     `SL5_CPU_TOP.u_alb_cpu
`define SL5_CORE        `SL5_ALB_CPU.u_alb_pd1.u_alb_core
`define SL5_EXU         `SL5_CORE.u_alb_exu
`define SL5_EXEC_PIPE   `SL5_EXU.u_alb_exec_pipe
`define SL5_EXEC_EIA    `SL5_EXEC_PIPE.u_alb_eia_pipe
`define SL5_EXEC_EVTM   `SL5_EXEC_EIA.u_uxEventManager
`define SL5_EXEC_CMT    `SL5_EXEC_PIPE.u_alb_commit
`define SL5_EXEC_EXCPN  `SL5_EXEC_PIPE.u_alb_excpn_pipe
`define SL5_EXEC_CTRL   `SL5_EXEC_PIPE.u_alb_exec_ctrl
`define SL5_EXEC_IRQ    `SL5_EXEC_CTRL.irq_ack
`define SL5_SRAM        `NPU_SL5.u_npu_srams

`define SL5_VM_MEM_INST    `SL5_SRAM.vm_inst[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL5_VM_BNK_MODEL   `SL5_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_macro
`else
`define SL5_VM_BNK_MODEL   `SL5_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_model
`endif
`define SL5_STRING_VM_BNK  `"`SL5_VM_BNK_MODEL`"
`define SL5_AM_MEM_INST    `SL5_SRAM.am_inst_bank[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL5_AM_BNK_MODEL   `SL5_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_macro
`else
`define SL5_AM_BNK_MODEL   `SL5_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_model
`endif
`define SL5_STRING_AM_BNK  `"`SL5_AM_BNK_MODEL`"

`define SL5_CONV        `NPU_SL5.u_npu_conv
`define SL5_GTOA        `NPU_SL5.u_npu_gtoa
`define SL5_IDMA        `NPU_SL5.u_npu_idma
`define SL5_ODMA        `NPU_SL5.u_npu_odma
`define SL5_CTRL_BUS    `NPU_SL5.u_ctrl_axi_routing

`define SL5_IDMA_CTRL    `SL5_IDMA.u_npu_idma_ctrl
`define SL5_ODMA_CTRL    `SL5_ODMA.u_npu_dma_ctrl
`define SL5_CONV_CTRL    `SL5_CONV.u_ctrl_inst
`define SL5_GTOA_CTRL    `SL5_GTOA.u_gtoa_ctrl_inst

//SLICE 6
`define SL6_DPI_ARC     `NPU_SL6.u_npu_l1_arc
`define SL6_ARC         `NPU_SL6.u_npu_l1_arc
`define SL6_ARC_IF      `SL6_ARC 
`define SL6_CPU_TOP     `SL6_ARC.ialb_cpu_top
`define SL6_ALB_CPU     `SL6_CPU_TOP.u_alb_cpu
`define SL6_CORE        `SL6_ALB_CPU.u_alb_pd1.u_alb_core
`define SL6_EXU         `SL6_CORE.u_alb_exu
`define SL6_EXEC_PIPE   `SL6_EXU.u_alb_exec_pipe
`define SL6_EXEC_EIA    `SL6_EXEC_PIPE.u_alb_eia_pipe
`define SL6_EXEC_EVTM   `SL6_EXEC_EIA.u_uxEventManager
`define SL6_EXEC_CMT    `SL6_EXEC_PIPE.u_alb_commit
`define SL6_EXEC_EXCPN  `SL6_EXEC_PIPE.u_alb_excpn_pipe
`define SL6_EXEC_CTRL   `SL6_EXEC_PIPE.u_alb_exec_ctrl
`define SL6_EXEC_IRQ    `SL6_EXEC_CTRL.irq_ack
`define SL6_SRAM        `NPU_SL6.u_npu_srams

`define SL6_VM_MEM_INST    `SL6_SRAM.vm_inst[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL6_VM_BNK_MODEL   `SL6_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_macro
`else
`define SL6_VM_BNK_MODEL   `SL6_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_model
`endif
`define SL6_STRING_VM_BNK  `"`SL6_VM_BNK_MODEL`"
`define SL6_AM_MEM_INST    `SL6_SRAM.am_inst_bank[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL6_AM_BNK_MODEL   `SL6_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_macro
`else
`define SL6_AM_BNK_MODEL   `SL6_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_model
`endif
`define SL6_STRING_AM_BNK  `"`SL6_AM_BNK_MODEL`"

`define SL6_CONV        `NPU_SL6.u_npu_conv
`define SL6_GTOA        `NPU_SL6.u_npu_gtoa
`define SL6_IDMA        `NPU_SL6.u_npu_idma
`define SL6_ODMA        `NPU_SL6.u_npu_odma
`define SL6_CTRL_BUS    `NPU_SL6.u_ctrl_axi_routing

`define SL6_IDMA_CTRL    `SL6_IDMA.u_npu_idma_ctrl
`define SL6_ODMA_CTRL    `SL6_ODMA.u_npu_dma_ctrl
`define SL6_CONV_CTRL    `SL6_CONV.u_ctrl_inst
`define SL6_GTOA_CTRL    `SL6_GTOA.u_gtoa_ctrl_inst

//SLICE 7
`define SL7_DPI_ARC     `NPU_SL7.u_npu_l1_arc
`define SL7_ARC         `NPU_SL7.u_npu_l1_arc
`define SL7_ARC_IF      `SL7_ARC 
`define SL7_CPU_TOP     `SL7_ARC.ialb_cpu_top
`define SL7_ALB_CPU     `SL7_CPU_TOP.u_alb_cpu
`define SL7_CORE        `SL7_ALB_CPU.u_alb_pd1.u_alb_core
`define SL7_EXU         `SL7_CORE.u_alb_exu
`define SL7_EXEC_PIPE   `SL7_EXU.u_alb_exec_pipe
`define SL7_EXEC_EIA    `SL7_EXEC_PIPE.u_alb_eia_pipe
`define SL7_EXEC_EVTM   `SL7_EXEC_EIA.u_uxEventManager
`define SL7_EXEC_CMT    `SL7_EXEC_PIPE.u_alb_commit
`define SL7_EXEC_EXCPN  `SL7_EXEC_PIPE.u_alb_excpn_pipe
`define SL7_EXEC_CTRL   `SL7_EXEC_PIPE.u_alb_exec_ctrl
`define SL7_EXEC_IRQ    `SL7_EXEC_CTRL.irq_ack
`define SL7_SRAM        `NPU_SL7.u_npu_srams

`define SL7_VM_MEM_INST    `SL7_SRAM.vm_inst[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL7_VM_BNK_MODEL   `SL7_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_macro
`else
`define SL7_VM_BNK_MODEL   `SL7_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_model
`endif
`define SL7_STRING_VM_BNK  `"`SL7_VM_BNK_MODEL`"
`define SL7_AM_MEM_INST    `SL7_SRAM.am_inst_bank[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL7_AM_BNK_MODEL   `SL7_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_macro
`else
`define SL7_AM_BNK_MODEL   `SL7_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_model
`endif
`define SL7_STRING_AM_BNK  `"`SL7_AM_BNK_MODEL`"

`define SL7_CONV        `NPU_SL7.u_npu_conv
`define SL7_GTOA        `NPU_SL7.u_npu_gtoa
`define SL7_IDMA        `NPU_SL7.u_npu_idma
`define SL7_ODMA        `NPU_SL7.u_npu_odma
`define SL7_CTRL_BUS    `NPU_SL7.u_ctrl_axi_routing

`define SL7_IDMA_CTRL    `SL7_IDMA.u_npu_idma_ctrl
`define SL7_ODMA_CTRL    `SL7_ODMA.u_npu_dma_ctrl
`define SL7_CONV_CTRL    `SL7_CONV.u_ctrl_inst
`define SL7_GTOA_CTRL    `SL7_GTOA.u_gtoa_ctrl_inst

//SLICE 8
`define SL8_DPI_ARC     `NPU_SL8.u_npu_l1_arc
`define SL8_ARC         `NPU_SL8.u_npu_l1_arc
`define SL8_ARC_IF      `SL8_ARC 
`define SL8_CPU_TOP     `SL8_ARC.ialb_cpu_top
`define SL8_ALB_CPU     `SL8_CPU_TOP.u_alb_cpu
`define SL8_CORE        `SL8_ALB_CPU.u_alb_pd1.u_alb_core
`define SL8_EXU         `SL8_CORE.u_alb_exu
`define SL8_EXEC_PIPE   `SL8_EXU.u_alb_exec_pipe
`define SL8_EXEC_EIA    `SL8_EXEC_PIPE.u_alb_eia_pipe
`define SL8_EXEC_EVTM   `SL8_EXEC_EIA.u_uxEventManager
`define SL8_EXEC_CMT    `SL8_EXEC_PIPE.u_alb_commit
`define SL8_EXEC_EXCPN  `SL8_EXEC_PIPE.u_alb_excpn_pipe
`define SL8_EXEC_CTRL   `SL8_EXEC_PIPE.u_alb_exec_ctrl
`define SL8_EXEC_IRQ    `SL8_EXEC_CTRL.irq_ack
`define SL8_SRAM        `NPU_SL8.u_npu_srams

`define SL8_VM_MEM_INST    `SL8_SRAM.vm_inst[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL8_VM_BNK_MODEL   `SL8_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_macro
`else
`define SL8_VM_BNK_MODEL   `SL8_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_model
`endif
`define SL8_STRING_VM_BNK  `"`SL8_VM_BNK_MODEL`"
`define SL8_AM_MEM_INST    `SL8_SRAM.am_inst_bank[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL8_AM_BNK_MODEL   `SL8_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_macro
`else
`define SL8_AM_BNK_MODEL   `SL8_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_model
`endif
`define SL8_STRING_AM_BNK  `"`SL8_AM_BNK_MODEL`"

`define SL8_CONV        `NPU_SL8.u_npu_conv
`define SL8_GTOA        `NPU_SL8.u_npu_gtoa
`define SL8_IDMA        `NPU_SL8.u_npu_idma
`define SL8_ODMA        `NPU_SL8.u_npu_odma
`define SL8_CTRL_BUS    `NPU_SL8.u_ctrl_axi_routing

`define SL8_IDMA_CTRL    `SL8_IDMA.u_npu_idma_ctrl
`define SL8_ODMA_CTRL    `SL8_ODMA.u_npu_dma_ctrl
`define SL8_CONV_CTRL    `SL8_CONV.u_ctrl_inst
`define SL8_GTOA_CTRL    `SL8_GTOA.u_gtoa_ctrl_inst

//SLICE 9
`define SL9_DPI_ARC     `NPU_SL9.u_npu_l1_arc
`define SL9_ARC         `NPU_SL9.u_npu_l1_arc
`define SL9_ARC_IF      `SL9_ARC 
`define SL9_CPU_TOP     `SL9_ARC.ialb_cpu_top
`define SL9_ALB_CPU     `SL9_CPU_TOP.u_alb_cpu
`define SL9_CORE        `SL9_ALB_CPU.u_alb_pd1.u_alb_core
`define SL9_EXU         `SL9_CORE.u_alb_exu
`define SL9_EXEC_PIPE   `SL9_EXU.u_alb_exec_pipe
`define SL9_EXEC_EIA    `SL9_EXEC_PIPE.u_alb_eia_pipe
`define SL9_EXEC_EVTM   `SL9_EXEC_EIA.u_uxEventManager
`define SL9_EXEC_CMT    `SL9_EXEC_PIPE.u_alb_commit
`define SL9_EXEC_EXCPN  `SL9_EXEC_PIPE.u_alb_excpn_pipe
`define SL9_EXEC_CTRL   `SL9_EXEC_PIPE.u_alb_exec_ctrl
`define SL9_EXEC_IRQ    `SL9_EXEC_CTRL.irq_ack
`define SL9_SRAM        `NPU_SL9.u_npu_srams

`define SL9_VM_MEM_INST    `SL9_SRAM.vm_inst[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL9_VM_BNK_MODEL   `SL9_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_macro
`else
`define SL9_VM_BNK_MODEL   `SL9_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_model
`endif
`define SL9_STRING_VM_BNK  `"`SL9_VM_BNK_MODEL`"
`define SL9_AM_MEM_INST    `SL9_SRAM.am_inst_bank[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL9_AM_BNK_MODEL   `SL9_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_macro
`else
`define SL9_AM_BNK_MODEL   `SL9_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_model
`endif
`define SL9_STRING_AM_BNK  `"`SL9_AM_BNK_MODEL`"

`define SL9_CONV        `NPU_SL9.u_npu_conv
`define SL9_GTOA        `NPU_SL9.u_npu_gtoa
`define SL9_IDMA        `NPU_SL9.u_npu_idma
`define SL9_ODMA        `NPU_SL9.u_npu_odma
`define SL9_CTRL_BUS    `NPU_SL9.u_ctrl_axi_routing

`define SL9_IDMA_CTRL    `SL9_IDMA.u_npu_idma_ctrl
`define SL9_ODMA_CTRL    `SL9_ODMA.u_npu_dma_ctrl
`define SL9_CONV_CTRL    `SL9_CONV.u_ctrl_inst
`define SL9_GTOA_CTRL    `SL9_GTOA.u_gtoa_ctrl_inst

//SLICE 10
`define SL10_DPI_ARC     `NPU_SL10.u_npu_l1_arc
`define SL10_ARC         `NPU_SL10.u_npu_l1_arc
`define SL10_ARC_IF      `SL10_ARC 
`define SL10_CPU_TOP     `SL10_ARC.ialb_cpu_top
`define SL10_ALB_CPU     `SL10_CPU_TOP.u_alb_cpu
`define SL10_CORE        `SL10_ALB_CPU.u_alb_pd1.u_alb_core
`define SL10_EXU         `SL10_CORE.u_alb_exu
`define SL10_EXEC_PIPE   `SL10_EXU.u_alb_exec_pipe
`define SL10_EXEC_EIA    `SL10_EXEC_PIPE.u_alb_eia_pipe
`define SL10_EXEC_EVTM   `SL10_EXEC_EIA.u_uxEventManager
`define SL10_EXEC_CMT    `SL10_EXEC_PIPE.u_alb_commit
`define SL10_EXEC_EXCPN  `SL10_EXEC_PIPE.u_alb_excpn_pipe
`define SL10_EXEC_CTRL   `SL10_EXEC_PIPE.u_alb_exec_ctrl
`define SL10_EXEC_IRQ    `SL10_EXEC_CTRL.irq_ack
`define SL10_SRAM        `NPU_SL10.u_npu_srams

`define SL10_VM_MEM_INST    `SL10_SRAM.vm_inst[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL10_VM_BNK_MODEL   `SL10_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_macro
`else
`define SL10_VM_BNK_MODEL   `SL10_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_model
`endif
`define SL10_STRING_VM_BNK  `"`SL10_VM_BNK_MODEL`"
`define SL10_AM_MEM_INST    `SL10_SRAM.am_inst_bank[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL10_AM_BNK_MODEL   `SL10_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_macro
`else
`define SL10_AM_BNK_MODEL   `SL10_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_model
`endif
`define SL10_STRING_AM_BNK  `"`SL10_AM_BNK_MODEL`"

`define SL10_CONV        `NPU_SL10.u_npu_conv
`define SL10_GTOA        `NPU_SL10.u_npu_gtoa
`define SL10_IDMA        `NPU_SL10.u_npu_idma
`define SL10_ODMA        `NPU_SL10.u_npu_odma
`define SL10_CTRL_BUS    `NPU_SL10.u_ctrl_axi_routing

`define SL10_IDMA_CTRL    `SL10_IDMA.u_npu_idma_ctrl
`define SL10_ODMA_CTRL    `SL10_ODMA.u_npu_dma_ctrl
`define SL10_CONV_CTRL    `SL10_CONV.u_ctrl_inst
`define SL10_GTOA_CTRL    `SL10_GTOA.u_gtoa_ctrl_inst

//SLICE 11
`define SL11_DPI_ARC     `NPU_SL11.u_npu_l1_arc
`define SL11_ARC         `NPU_SL11.u_npu_l1_arc
`define SL11_ARC_IF      `SL11_ARC 
`define SL11_CPU_TOP     `SL11_ARC.ialb_cpu_top
`define SL11_ALB_CPU     `SL11_CPU_TOP.u_alb_cpu
`define SL11_CORE        `SL11_ALB_CPU.u_alb_pd1.u_alb_core
`define SL11_EXU         `SL11_CORE.u_alb_exu
`define SL11_EXEC_PIPE   `SL11_EXU.u_alb_exec_pipe
`define SL11_EXEC_EIA    `SL11_EXEC_PIPE.u_alb_eia_pipe
`define SL11_EXEC_EVTM   `SL11_EXEC_EIA.u_uxEventManager
`define SL11_EXEC_CMT    `SL11_EXEC_PIPE.u_alb_commit
`define SL11_EXEC_EXCPN  `SL11_EXEC_PIPE.u_alb_excpn_pipe
`define SL11_EXEC_CTRL   `SL11_EXEC_PIPE.u_alb_exec_ctrl
`define SL11_EXEC_IRQ    `SL11_EXEC_CTRL.irq_ack
`define SL11_SRAM        `NPU_SL11.u_npu_srams

`define SL11_VM_MEM_INST    `SL11_SRAM.vm_inst[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL11_VM_BNK_MODEL   `SL11_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_macro
`else
`define SL11_VM_BNK_MODEL   `SL11_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_model
`endif
`define SL11_STRING_VM_BNK  `"`SL11_VM_BNK_MODEL`"
`define SL11_AM_MEM_INST    `SL11_SRAM.am_inst_bank[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL11_AM_BNK_MODEL   `SL11_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_macro
`else
`define SL11_AM_BNK_MODEL   `SL11_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_model
`endif
`define SL11_STRING_AM_BNK  `"`SL11_AM_BNK_MODEL`"

`define SL11_CONV        `NPU_SL11.u_npu_conv
`define SL11_GTOA        `NPU_SL11.u_npu_gtoa
`define SL11_IDMA        `NPU_SL11.u_npu_idma
`define SL11_ODMA        `NPU_SL11.u_npu_odma
`define SL11_CTRL_BUS    `NPU_SL11.u_ctrl_axi_routing

`define SL11_IDMA_CTRL    `SL11_IDMA.u_npu_idma_ctrl
`define SL11_ODMA_CTRL    `SL11_ODMA.u_npu_dma_ctrl
`define SL11_CONV_CTRL    `SL11_CONV.u_ctrl_inst
`define SL11_GTOA_CTRL    `SL11_GTOA.u_gtoa_ctrl_inst

//SLICE 12
`define SL12_DPI_ARC     `NPU_SL12.u_npu_l1_arc
`define SL12_ARC         `NPU_SL12.u_npu_l1_arc
`define SL12_ARC_IF      `SL12_ARC 
`define SL12_CPU_TOP     `SL12_ARC.ialb_cpu_top
`define SL12_ALB_CPU     `SL12_CPU_TOP.u_alb_cpu
`define SL12_CORE        `SL12_ALB_CPU.u_alb_pd1.u_alb_core
`define SL12_EXU         `SL12_CORE.u_alb_exu
`define SL12_EXEC_PIPE   `SL12_EXU.u_alb_exec_pipe
`define SL12_EXEC_EIA    `SL12_EXEC_PIPE.u_alb_eia_pipe
`define SL12_EXEC_EVTM   `SL12_EXEC_EIA.u_uxEventManager
`define SL12_EXEC_CMT    `SL12_EXEC_PIPE.u_alb_commit
`define SL12_EXEC_EXCPN  `SL12_EXEC_PIPE.u_alb_excpn_pipe
`define SL12_EXEC_CTRL   `SL12_EXEC_PIPE.u_alb_exec_ctrl
`define SL12_EXEC_IRQ    `SL12_EXEC_CTRL.irq_ack
`define SL12_SRAM        `NPU_SL12.u_npu_srams

`define SL12_VM_MEM_INST    `SL12_SRAM.vm_inst[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL12_VM_BNK_MODEL   `SL12_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_macro
`else
`define SL12_VM_BNK_MODEL   `SL12_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_model
`endif
`define SL12_STRING_VM_BNK  `"`SL12_VM_BNK_MODEL`"
`define SL12_AM_MEM_INST    `SL12_SRAM.am_inst_bank[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL12_AM_BNK_MODEL   `SL12_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_macro
`else
`define SL12_AM_BNK_MODEL   `SL12_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_model
`endif
`define SL12_STRING_AM_BNK  `"`SL12_AM_BNK_MODEL`"

`define SL12_CONV        `NPU_SL12.u_npu_conv
`define SL12_GTOA        `NPU_SL12.u_npu_gtoa
`define SL12_IDMA        `NPU_SL12.u_npu_idma
`define SL12_ODMA        `NPU_SL12.u_npu_odma
`define SL12_CTRL_BUS    `NPU_SL12.u_ctrl_axi_routing

`define SL12_IDMA_CTRL    `SL12_IDMA.u_npu_idma_ctrl
`define SL12_ODMA_CTRL    `SL12_ODMA.u_npu_dma_ctrl
`define SL12_CONV_CTRL    `SL12_CONV.u_ctrl_inst
`define SL12_GTOA_CTRL    `SL12_GTOA.u_gtoa_ctrl_inst

//SLICE 13
`define SL13_DPI_ARC     `NPU_SL13.u_npu_l1_arc
`define SL13_ARC         `NPU_SL13.u_npu_l1_arc
`define SL13_ARC_IF      `SL13_ARC 
`define SL13_CPU_TOP     `SL13_ARC.ialb_cpu_top
`define SL13_ALB_CPU     `SL13_CPU_TOP.u_alb_cpu
`define SL13_CORE        `SL13_ALB_CPU.u_alb_pd1.u_alb_core
`define SL13_EXU         `SL13_CORE.u_alb_exu
`define SL13_EXEC_PIPE   `SL13_EXU.u_alb_exec_pipe
`define SL13_EXEC_EIA    `SL13_EXEC_PIPE.u_alb_eia_pipe
`define SL13_EXEC_EVTM   `SL13_EXEC_EIA.u_uxEventManager
`define SL13_EXEC_CMT    `SL13_EXEC_PIPE.u_alb_commit
`define SL13_EXEC_EXCPN  `SL13_EXEC_PIPE.u_alb_excpn_pipe
`define SL13_EXEC_CTRL   `SL13_EXEC_PIPE.u_alb_exec_ctrl
`define SL13_EXEC_IRQ    `SL13_EXEC_CTRL.irq_ack
`define SL13_SRAM        `NPU_SL13.u_npu_srams

`define SL13_VM_MEM_INST    `SL13_SRAM.vm_inst[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL13_VM_BNK_MODEL   `SL13_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_macro
`else
`define SL13_VM_BNK_MODEL   `SL13_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_model
`endif
`define SL13_STRING_VM_BNK  `"`SL13_VM_BNK_MODEL`"
`define SL13_AM_MEM_INST    `SL13_SRAM.am_inst_bank[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL13_AM_BNK_MODEL   `SL13_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_macro
`else
`define SL13_AM_BNK_MODEL   `SL13_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_model
`endif
`define SL13_STRING_AM_BNK  `"`SL13_AM_BNK_MODEL`"

`define SL13_CONV        `NPU_SL13.u_npu_conv
`define SL13_GTOA        `NPU_SL13.u_npu_gtoa
`define SL13_IDMA        `NPU_SL13.u_npu_idma
`define SL13_ODMA        `NPU_SL13.u_npu_odma
`define SL13_CTRL_BUS    `NPU_SL13.u_ctrl_axi_routing

`define SL13_IDMA_CTRL    `SL13_IDMA.u_npu_idma_ctrl
`define SL13_ODMA_CTRL    `SL13_ODMA.u_npu_dma_ctrl
`define SL13_CONV_CTRL    `SL13_CONV.u_ctrl_inst
`define SL13_GTOA_CTRL    `SL13_GTOA.u_gtoa_ctrl_inst

//SLICE 14
`define SL14_DPI_ARC     `NPU_SL14.u_npu_l1_arc
`define SL14_ARC         `NPU_SL14.u_npu_l1_arc
`define SL14_ARC_IF      `SL14_ARC 
`define SL14_CPU_TOP     `SL14_ARC.ialb_cpu_top
`define SL14_ALB_CPU     `SL14_CPU_TOP.u_alb_cpu
`define SL14_CORE        `SL14_ALB_CPU.u_alb_pd1.u_alb_core
`define SL14_EXU         `SL14_CORE.u_alb_exu
`define SL14_EXEC_PIPE   `SL14_EXU.u_alb_exec_pipe
`define SL14_EXEC_EIA    `SL14_EXEC_PIPE.u_alb_eia_pipe
`define SL14_EXEC_EVTM   `SL14_EXEC_EIA.u_uxEventManager
`define SL14_EXEC_CMT    `SL14_EXEC_PIPE.u_alb_commit
`define SL14_EXEC_EXCPN  `SL14_EXEC_PIPE.u_alb_excpn_pipe
`define SL14_EXEC_CTRL   `SL14_EXEC_PIPE.u_alb_exec_ctrl
`define SL14_EXEC_IRQ    `SL14_EXEC_CTRL.irq_ack
`define SL14_SRAM        `NPU_SL14.u_npu_srams

`define SL14_VM_MEM_INST    `SL14_SRAM.vm_inst[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL14_VM_BNK_MODEL   `SL14_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_macro
`else
`define SL14_VM_BNK_MODEL   `SL14_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_model
`endif
`define SL14_STRING_VM_BNK  `"`SL14_VM_BNK_MODEL`"
`define SL14_AM_MEM_INST    `SL14_SRAM.am_inst_bank[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL14_AM_BNK_MODEL   `SL14_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_macro
`else
`define SL14_AM_BNK_MODEL   `SL14_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_model
`endif
`define SL14_STRING_AM_BNK  `"`SL14_AM_BNK_MODEL`"

`define SL14_CONV        `NPU_SL14.u_npu_conv
`define SL14_GTOA        `NPU_SL14.u_npu_gtoa
`define SL14_IDMA        `NPU_SL14.u_npu_idma
`define SL14_ODMA        `NPU_SL14.u_npu_odma
`define SL14_CTRL_BUS    `NPU_SL14.u_ctrl_axi_routing

`define SL14_IDMA_CTRL    `SL14_IDMA.u_npu_idma_ctrl
`define SL14_ODMA_CTRL    `SL14_ODMA.u_npu_dma_ctrl
`define SL14_CONV_CTRL    `SL14_CONV.u_ctrl_inst
`define SL14_GTOA_CTRL    `SL14_GTOA.u_gtoa_ctrl_inst

//SLICE 15
`define SL15_DPI_ARC     `NPU_SL15.u_npu_l1_arc
`define SL15_ARC         `NPU_SL15.u_npu_l1_arc
`define SL15_ARC_IF      `SL15_ARC 
`define SL15_CPU_TOP     `SL15_ARC.ialb_cpu_top
`define SL15_ALB_CPU     `SL15_CPU_TOP.u_alb_cpu
`define SL15_CORE        `SL15_ALB_CPU.u_alb_pd1.u_alb_core
`define SL15_EXU         `SL15_CORE.u_alb_exu
`define SL15_EXEC_PIPE   `SL15_EXU.u_alb_exec_pipe
`define SL15_EXEC_EIA    `SL15_EXEC_PIPE.u_alb_eia_pipe
`define SL15_EXEC_EVTM   `SL15_EXEC_EIA.u_uxEventManager
`define SL15_EXEC_CMT    `SL15_EXEC_PIPE.u_alb_commit
`define SL15_EXEC_EXCPN  `SL15_EXEC_PIPE.u_alb_excpn_pipe
`define SL15_EXEC_CTRL   `SL15_EXEC_PIPE.u_alb_exec_ctrl
`define SL15_EXEC_IRQ    `SL15_EXEC_CTRL.irq_ack
`define SL15_SRAM        `NPU_SL15.u_npu_srams

`define SL15_VM_MEM_INST    `SL15_SRAM.vm_inst[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL15_VM_BNK_MODEL   `SL15_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_macro
`else
`define SL15_VM_BNK_MODEL   `SL15_VM_MEM_INST.u_npu_mem_vec_bank.u_npu_mem_vec_bank_model
`endif
`define SL15_STRING_VM_BNK  `"`SL15_VM_BNK_MODEL`"
`define SL15_AM_MEM_INST    `SL15_SRAM.am_inst_bank[%0d]
`ifdef NPU_USE_ASIC_MEMORIES
`define SL15_AM_BNK_MODEL   `SL15_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_macro
`else
`define SL15_AM_BNK_MODEL   `SL15_AM_MEM_INST.am_inst_slice[%0d].u_npu_mem_acc_bank.u_npu_mem_acc_bank_model
`endif
`define SL15_STRING_AM_BNK  `"`SL15_AM_BNK_MODEL`"

`define SL15_CONV        `NPU_SL15.u_npu_conv
`define SL15_GTOA        `NPU_SL15.u_npu_gtoa
`define SL15_IDMA        `NPU_SL15.u_npu_idma
`define SL15_ODMA        `NPU_SL15.u_npu_odma
`define SL15_CTRL_BUS    `NPU_SL15.u_ctrl_axi_routing

`define SL15_IDMA_CTRL    `SL15_IDMA.u_npu_idma_ctrl
`define SL15_ODMA_CTRL    `SL15_ODMA.u_npu_dma_ctrl
`define SL15_CONV_CTRL    `SL15_CONV.u_ctrl_inst
`define SL15_GTOA_CTRL    `SL15_GTOA.u_gtoa_ctrl_inst


`ifndef CLK_NS
`define CLK_NS 10
`endif
`define TB_HAS_MEM_ECC 
`define connect_fast_rascal(NAME, MDB_ID, PATH) \
  begin : fast_rascal_``NAME \
      wire        i_dbg_cmdval; \
      wire [31:0] i_dbg_address; \
      wire [ 3:0] i_dbg_be; \
      wire [ 1:0] i_dbg_cmd; \
      wire [31:0] i_dbg_wdata; \
      wire        i_dbg_rspack; \
      wire        i_pseldbg; \
      wire [31:0] i_paddrdbg; \
      wire        i_penabledbg; \
      wire        i_pwritedbg; \
      wire [31:0] i_pwdatadbg; \
      wire        i_dbgen; \
      wire        i_niden; \
      wire        i_dbg_prot_sel; \
      fast_rascal #( \
          .cpu_id      (MDB_ID) \
        , .halt_sig    (`"PATH.gb_sys_halt_r`") \
      ) i_fast_rascal_``NAME ( \
          .rst_a       (PATH.rst_a) \
        , .clk         (clk) \
        , .dbg_prot_sel(i_dbg_prot_sel) \
        , .preadydbg   (PATH.preadydbg) \
        , .prdatadbg   (PATH.prdatadbg) \
        , .pslverrdbg  (PATH.pslverrdbg) \
        , .pclkdbg_en  (~PATH.rst_a) \
        , .presetdbgn  (~PATH.rst_a) \
        , .pseldbg     (i_pseldbg) \
        , .paddrdbg    (i_paddrdbg[31:2]) \
        , .penabledbg  (i_penabledbg) \
        , .pwritedbg   (i_pwritedbg) \
        , .pwdatadbg   (i_pwdatadbg) \
        , .dbgen       (i_dbgen) \
        , .niden       (i_niden) \
        , .dbg_cmdack  (PATH.u_alb_pd1.core_dbg_cmdack) \
        , .dbg_rspval  (PATH.u_alb_pd1.core_dbg_rspval) \
        , .dbg_rdata   (PATH.u_alb_pd1.core_dbg_rdata) \
        , .dbg_reop    (PATH.u_alb_pd1.core_dbg_reop) \
        , .dbg_rerr    (PATH.u_alb_pd1.core_dbg_rerr) \
        , .dbg_cmdval  (i_dbg_cmdval) \
        , .dbg_eop     () \
        , .dbg_address (i_dbg_address) \
        , .dbg_be      (i_dbg_be) \
        , .dbg_cmd     (i_dbg_cmd) \
        , .dbg_wdata   (i_dbg_wdata) \
        , .dbg_rspack  (i_dbg_rspack) \
      ); \
      initial begin \
          force PATH.pclkdbg_en = ~PATH.rst_a; \
          force PATH.presetdbgn = ~PATH.rst_a; \
          force PATH.pseldbg = i_pseldbg; \
          force PATH.paddrdbg = i_paddrdbg[31:2]; \
          force PATH.penabledbg = i_penabledbg; \
          force PATH.pwritedbg = i_pwritedbg; \
          force PATH.pwdatadbg = i_pwdatadbg; \
          force PATH.dbgen = i_dbgen; \
          force PATH.niden = i_niden; \
          force PATH.dbg_prot_sel = i_dbg_prot_sel; \
          force PATH.dbg_cmdval = 'hZ; \
          force PATH.dbg_address = 'hZ; \
          force PATH.dbg_be = 'hZ; \
          force PATH.dbg_cmd = 'hZ; \
          force PATH.dbg_wdata = 'hZ; \
          force PATH.dbg_rspack = 'hZ; \
          force PATH.u_alb_pd1.dbg_cmdval = i_dbg_cmdval; \
          force PATH.u_alb_pd1.dbg_address = i_dbg_address; \
          force PATH.u_alb_pd1.dbg_be = i_dbg_be; \
          force PATH.u_alb_pd1.dbg_cmd = i_dbg_cmd; \
          force PATH.u_alb_pd1.dbg_wdata = i_dbg_wdata; \
          force PATH.u_alb_pd1.dbg_rspack = i_dbg_rspack; \
      end \
  end

`ifndef TB_SIM_MON_EN
  `define TB_SIM_MON_EN 32'hffffffff
`endif

 `define RASCAL `TB_TOP.ijtag_model.irascal

`endif

`define STRING_DEF(x) `"x`"
`define ASSERT_PROPERTY(name, clk, dis, expr, msg) \
  property name; \
    @(posedge clk) disable iff (dis) (expr); \
  endproperty \
  ast_``name: assert property(name) else $fatal(msg); \
  cover property (name); 

