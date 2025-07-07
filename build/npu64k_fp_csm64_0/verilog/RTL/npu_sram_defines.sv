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

// -- Memory types (enum)
//
`define NPU_MEM_TARGET_AM          1
`define NPU_MEM_TARGET_VM          2


// -- Memory Initialize
`ifndef NPU_RANDOM_MEMORIES
  `define NPU_ZEROED_MEMORIES
`endif
//`define NPU_RANDOM_MEMORIES
//`define NPU_CORRUPT_MEMORIES
//`define NPU_ZEROED_MEMORIES
