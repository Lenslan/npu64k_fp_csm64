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

`ifndef NPU_CONV_MACROS_INCLUDED
`define NPU_CONV_MACROS_INCLUDED
`define DINO(name) name``i32o16
`define NINO(name) name``i16o16
`define VIVO(name) name``v2i8o8
`define FC(name)   name``i16o128
`endif
