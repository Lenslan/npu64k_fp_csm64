

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










// Version of the NPU and CNN:
// 1:  EV5x / CNN 1.0
// 2:  EV6x 2.00a Montreal / CNN v2.0 iplib
// 3:  EV6x 2.10a Tofino / CNN v3.0 iplib
// 4:  Bug fix for the DMA compression (2.12 = Tofino + fix for 9001328561)
// 5:  EV6x 2.20a Toronto / CNN v3.1 iplib
// 6:  EV7x 3.00a Vancouver / CNN v3.2 iplib
// 7 to 15: Reserved for future EV/CNN/DNN releases
//
// 16: NPX6 release 1.00a (NPU Victoria)
// 17: NPX release 2.00a-lca01 (Victoria2 LCA)
// 18: NPX release 2.00a (Victoria2 GA)
//
`define npuarc_NPU_VERSION 18

`define npuarc_NPU_HAS_SFTY_BCR            0
`define npuarc_NPU_MEM_ECC                 1
`define npuarc_NPU_SLICE_NUM               16

// L2 controller presence

// Always true for Victoria 1 and Victoria 2
`define npuarc_NPU_HAS_L2_CTRL             1
`define npuarc_NPU_HAS_L1_CTRL             1
`define npuarc_NPU_HAS_EVT_MGT             1

// Calculated values for the STU BCR
`define npuarc_NPU_STU_BCR         3

// Calculated values for the MAC BCR
`define npuarc_NPU_MAC_BCR  4

//Size of the Accumulator Memory in each of the NPU slices
//    0:   Reserved
//    1:   32KB  AM per NPU slice
//    2:   64KB  AM per NPU slice
//    3:   128KB AM per NPU slice
//    4:   256KB AM per NPU slice
//    5-7: Reserved
//Size of the Vector Memory in each of the NPU slices
//    0:   Reserved
//    1:   128KB VM per NPU slice
//    2:   256KB VM per NPU slice
//    3:   512KB VM per NPU slice
//    4:   1MB   VM per NPU slice
//    5-7: Reserved
`define npuarc_NPU_AM_SIZE_BCR             3
`define npuarc_NPU_VM_SIZE_BCR             3











