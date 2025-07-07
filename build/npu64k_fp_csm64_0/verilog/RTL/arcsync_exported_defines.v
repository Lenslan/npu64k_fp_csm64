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

`ifndef ARCSYNC_EXPORTED_DEFINES_INCLUDED
`define ARCSYNC_EXPORTED_DEFINES_INCLUDED

`define ARCSYNC_NUM_CLUSTER           3
`define ARCSYNC_MAX_CORES_PER_CL      32
`define ARCSYNC_TYPE_CL_NPUSLICE      0
`define ARCSYNC_TYPE_CL_NPX           0
`define ARCSYNC_TYPE_CL_VPX           1
`define ARCSYNC_TYPE_CL_HOST          2
`define ARCSYNC_NUM_CORE_CL0          18
`define ARCSYNC_TYPE_CL0              0
`define ARCSYNC_ITF_CL0               0
`define ARCSYNC_ITF_STUB_CL0          0
`define ARCSYNC_PFX_CL0               
`define ARCSYNC_NUM_CORE_CL1          4
`define ARCSYNC_TYPE_CL1              1
`define ARCSYNC_ITF_CL1               1
`define ARCSYNC_ITF_STUB_CL1          1
`define ARCSYNC_PFX_CL1               v0
`define ARCSYNC_NUM_CORE_CL2          1
`define ARCSYNC_TYPE_CL2              2
`define ARCSYNC_ITF_CL2               1
`define ARCSYNC_ITF_STUB_CL2          1
`define ARCSYNC_PFX_CL2               h0
`define ARCSYNC_NUM_CORE_CL3          0
`define ARCSYNC_TYPE_CL3              0
`define ARCSYNC_ITF_CL3               0
`define ARCSYNC_ITF_STUB_CL3          0
`define ARCSYNC_PFX_CL3               
`define ARCSYNC_NUM_CORE_CL4          0
`define ARCSYNC_TYPE_CL4              0
`define ARCSYNC_ITF_CL4               0
`define ARCSYNC_ITF_STUB_CL4          0
`define ARCSYNC_PFX_CL4               
`define ARCSYNC_NUM_CORE_CL5          0
`define ARCSYNC_TYPE_CL5              0
`define ARCSYNC_ITF_CL5               0
`define ARCSYNC_ITF_STUB_CL5          0
`define ARCSYNC_PFX_CL5               
`define ARCSYNC_NUM_CORE_CL6          0
`define ARCSYNC_TYPE_CL6              0
`define ARCSYNC_ITF_CL6               0
`define ARCSYNC_ITF_STUB_CL6          0
`define ARCSYNC_PFX_CL6               
`define ARCSYNC_NUM_CORE_CL7          0
`define ARCSYNC_TYPE_CL7              0
`define ARCSYNC_ITF_CL7               0
`define ARCSYNC_ITF_STUB_CL7          0
`define ARCSYNC_PFX_CL7               
`define ARCSYNC_NUM_CORE_CL8          0
`define ARCSYNC_TYPE_CL8              0
`define ARCSYNC_ITF_CL8               0
`define ARCSYNC_ITF_STUB_CL8          0
`define ARCSYNC_PFX_CL8               
`define ARCSYNC_NUM_CORE_CL9          0
`define ARCSYNC_TYPE_CL9              0
`define ARCSYNC_ITF_CL9               0
`define ARCSYNC_ITF_STUB_CL9          0
`define ARCSYNC_PFX_CL9               
`define ARCSYNC_NUM_CORE_CL10          0
`define ARCSYNC_TYPE_CL10              0
`define ARCSYNC_ITF_CL10               0
`define ARCSYNC_ITF_STUB_CL10          0
`define ARCSYNC_PFX_CL10               
`define ARCSYNC_NUM_CORE_CL11          0
`define ARCSYNC_TYPE_CL11              0
`define ARCSYNC_ITF_CL11               0
`define ARCSYNC_ITF_STUB_CL11          0
`define ARCSYNC_PFX_CL11               
`define ARCSYNC_NUM_CORE_CL12          0
`define ARCSYNC_TYPE_CL12              0
`define ARCSYNC_ITF_CL12               0
`define ARCSYNC_ITF_STUB_CL12          0
`define ARCSYNC_PFX_CL12               
`define ARCSYNC_NUM_CORE_CL13          0
`define ARCSYNC_TYPE_CL13              0
`define ARCSYNC_ITF_CL13               0
`define ARCSYNC_ITF_STUB_CL13          0
`define ARCSYNC_PFX_CL13               
`define ARCSYNC_NUM_CORE_CL14          0
`define ARCSYNC_TYPE_CL14              0
`define ARCSYNC_ITF_CL14               0
`define ARCSYNC_ITF_STUB_CL14          0
`define ARCSYNC_PFX_CL14               
`define ARCSYNC_NUM_CORE_CL15          0
`define ARCSYNC_TYPE_CL15              0
`define ARCSYNC_ITF_CL15               0
`define ARCSYNC_ITF_STUB_CL15          0
`define ARCSYNC_PFX_CL15               

`define ARCSYNC_VIRT_MACHINES         8
`define ARCSYNC_NUM_IRQ_PER_CORE      1
`define ARCSYNC_NUM_EVT_PER_CORE      1
`define ARCSYNC_NUM_IRQ_PER_VPROC     1
`define ARCSYNC_NUM_EVT_PER_VPROC     1
`define ARCSYNC_VIRT_PROC             3

`define ARCSYNC_NUM_ATOMIC_CNT        64
`define ARCSYNC_NUM_GFRC              1
`define ARCSYNC_HAS_PMU               1
`define ARCSYNC_PMU_RESET_PMODE       1
`define ARCSYNC_CORE_CLK_ENA_RST      0

`define ARCSYNC_SAFETY_LEVEL          0

`define ARCSYNC_HAS_PAE40             1

`define ARCSYNC_ARC_DEV               0



`endif  //ARCSYNC_EXPORTED_DEFINES_INCLUDED

