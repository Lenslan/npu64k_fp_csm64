/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2021-2023 Synopsys, Inc.                              **/
/** All Rights Reserved.                                                **/
/**                                                                     **/
/** This Synopsys software and all associated documentation are         **/
/** proprietary to Synopsys, Inc. and may only be used pursuant to the  **/
/** terms and conditions of a written license agreement with Synopsys,  **/
/** Inc. All other use, reproduction, modification, or distribution of  **/
/** this Synopsys software or the associated documentation is strictly  **/
/** prohibited.                                                         **/
/**                                                                     **/
/*************************************************************************/

/*
 * npu_conv_hlapi.cpp
 *
 * File defining the convolution HLAPI functions
 *
 */

#include "npu_conv_hlapi.hpp"  // NOLINT [build/include_subdir]

#include <list>

//#define NPU_CONV_HLAPI_CPP_DEBUG
#ifdef  NPU_CONV_HLAPI_CPP_DEBUG
#define LDBGV(...) DBGV(__VA_ARGS__)
#else
#define LDBGV(...)
#endif


namespace npu_conv {
// encode data from a set of queues into a buffer and return the length
static void queue_encode(
                         array<list<coef_t>, NUM_COEF_QUEUE>&  // NOLINT [runtime/references]
                         vlist,                              // array of queues, one per bank
                         const xbuffer_t<ixpix_t>& obuf,       // output encoded coefficient tensor
                         size_t& olen,                          // size of used coefficient buffer in ixpix_t
                         coef_mode_t               coef_mode // coefficient compression mode uncompressed or compressed or sparse
                         ) {
  // find maximum list length
  olen = 0;
  if (coef_mode == coef_mode_compressed) {
    for (int i = 0; i < NUM_COEF_QUEUE; i++) {
      if (vlist[i].size() > olen) {
        olen = vlist[i].size();
      }
    }
    olen  = (olen+ISIZE-1)/ISIZE;
    olen *= NUM_COEF_QUEUE;
  }
  // encode the queues
  ixpix_t* ptr;
  ixpix_t v;
  int cnt = 0;
  for (int i = 0; i < NUM_COEF_QUEUE; i++) {
    ptr = obuf.get_base() + i;
    while (vlist[i].size() > 0) {
      for (int j = 0; j < ISIZE; j++) {
        if (vlist[i].size() > 0) {
          v[j] = vlist[i].front();
          vlist[i].pop_front();
        }
      }
      *ptr = v;
      // mem_write(ptr, v);
      cnt++;
      ptr += NUM_COEF_QUEUE;
    }
  }

  if (coef_mode != coef_mode_compressed) {
    olen = cnt;
  }
  assert(cnt <= static_cast<int>(obuf.get_size()));
}

#if 0
// FIXME: only for FC
static void queue_encode(
                         array<list<coef_t>, NUM_COEF_QUEUE>&  // NOLINT [runtime/references]
                         vlist,                              // array of queues, one per bank
                         const buffer_t<ixpix_t>& obuf,        // output encoded coefficient tensor
                         size_t& olen                          // size of used coefficient buffer in ixpix_t
                         ) {
  // find maximum list length
  olen = 0;
  for (int i = 0; i < NUM_COEF_QUEUE; i++) {
    if (vlist[i].size() > olen) {
      olen = vlist[i].size();
    }
  }
  olen  = (olen+ISIZE-1)/ISIZE;
  olen *= NUM_COEF_QUEUE;
  // encode the queues
  ixpix_t* ptr;
  ixpix_t v;
  int cnt = 0;
  for (int i = 0; i < NUM_COEF_QUEUE; i++) {
    ptr = obuf.get_base() + i;
    while (vlist[i].size() > 0) {
      for (int j = 0; j < ISIZE; j++) {
        if (vlist[i].size() > 0) {
          v[j] = vlist[i].front();
          vlist[i].pop_front();
        }
      }
      LDBGV(cout << "coef queue encode: " << v << endl;)
        // *ptr = v;
        mem_write(ptr, v);
      cnt++;
      ptr += NUM_COEF_QUEUE;
    }
  }

  LDBGV(cout << "cnt:" << cnt << " buf_size:" << obuf.get_size() << "\n";)
    assert(cnt <= static_cast<int>(obuf.get_size()));
}
#endif

using tensor::v200::get_shape_size;
#include "fm8cf8_enc.hpp"     // NOLINT [build/include_subdir]
#include "fm16cf8_enc.hpp"    // NOLINT [build/include_subdir]
#include "fm8cf16_enc.hpp"    // NOLINT [build/include_subdir]
#include "fm16cf16_enc.hpp"   // NOLINT [build/include_subdir]


//
// Exported coefficient encoding functions
//
// encode 16b coefficients without zero-point
void coef_enc(
              const tensor_t<coef_t, 7, xbuffer_t>& icf,   // input coefficients
              // [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp][Coef h/l]
              xbuffer_t<coef_t>&                  tbuf,      // temporary xbuf // NOLINT[runtime/references]
              // attributes
              conv_mode_t                        conv_mode,  // convolution mode
              bool                                fm_dbl,    // 16b feature-map
              // outputs, buffers preallocated by caller
              xbuffer_t<ixpix_t>&                            // NOLINT [runtime/references]
              obuf,                                          // output encoded coefficient tensor
              size_t&                             olen       // size of used coefficient buffer in bytes
              ) {
  switch (conv_mode) {
  case NINO(conv_mode_3x3dws1dl2):
    NINO(fm8cf16_3x3dws1dl2)(icf, tbuf, obuf, olen);
    break;
  case NINO(conv_mode_3x3dws1):
    NINO(fm8cf16_3x3dws1)(icf, tbuf, obuf, olen);
    break;
  case NINO(conv_mode_2x3dws2):
    NINO(fm8cf16_2x3dws2)(icf, tbuf, obuf, olen);
    break;
  case NINO(conv_mode_8x1dws1):
    NINO(fm8cf16_8x1dws1)(icf, tbuf, obuf, olen);
    break;
  case NINO(conv_mode_4x1dws1):
    NINO(fm8cf16_4x1dws1)(icf, tbuf, obuf, olen);
    break;
  case DINO(conv_mode_1x1):
  //#if NPU_VER_IS_VIC2_GA
    if (icf.get_dim(6) != 1) {
      // grouped convolution emulation
      if (fm_dbl) {
        DINO(gfm16cf16ns_1x1)(icf, tbuf, obuf, olen);
      } else {
        DINO(gfm8cf16ns_1x1)(icf, tbuf, obuf, olen);
      }   
    } else
  //#endif
    if (fm_dbl) {
      DINO(fm16cf16ns_1x1)(icf, tbuf, obuf, olen);
    } else {
      DINO(fm8cf16ns_1x1)(icf, tbuf, obuf, olen);
    }
    break;
  case NINO(conv_mode_2x1s1):
  case NINO(conv_mode_2x1s2):
  case NINO(conv_mode_2x1s1dl2):
    if (fm_dbl) {
      NINO(fm16cf16ns_2x1)(icf, tbuf, obuf, olen);
    } else {
      NINO(fm8cf16ns_2x1)(icf, tbuf, obuf, olen);
    }
    break;
  case NINO(conv_mode_1x1):
  case NINO(conv_mode_4x1g2s1dl2):
  case NINO(conv_mode_4x1g2s1):
  case NINO(conv_mode_2x1g2s2):
    assert(0);  // not supported with 16b coefficients
    break;
  default: assert(0);  // not implemented yet
  }
}

// encode 8b coefficients without zero-point
void coef_enc(
              const tensor_t<coef_t, 6, xbuffer_t>& icf,  // input coefficients
              // [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
              xbuffer_t<coef_t>&            tbuf,       // temporary xbuf  // NOLINT [runtime/references]
              // attributes
              conv_mode_t                   conv_mode,  // convolution mode
              coef_mode_t                   coef_mode,  // coefficient compression mode uncompressed
              // or compressed or sparse
              bool                          fm_dbl,     // 16b feature-map
              bool                          cf_4b,      // 4b coefficient encoding
              int                           inn,        // inner input loop
              int                           onn,        // inner output loop
              // outputs, buffers preallocated by caller
              xbuffer_t<ixpix_t>&                       // NOLINT [runtime/references]
              obuf,                                   // output encoded coefficient tensor
              size_t&                       olen        // size of used coefficient buffer in bytes
              ) {
  // allocate dummy zero points
  xbuffer_t<coef_t> cb = tbuf.split(static_cast<size_t>(icf.get_dim(4)*icf.get_dim(5)));
  tensor_t<coef_t, 1, xbuffer_t> zdummy(cb, {(aoffset_t)(icf.get_dim(4)*icf.get_dim(5))});
  switch (conv_mode) {
  case NINO(conv_mode_3x3dws1dl2):
    assert(coef_mode != coef_mode_sparse);
    NINO(fm8cf8_3x3dws1dl2)(icf, zdummy, tbuf, coef_mode, cf_4b, false/*cf_zp*/, obuf, olen);
    break;
  case NINO(conv_mode_3x3dws1):
    assert(coef_mode != coef_mode_sparse);
    NINO(fm8cf8_3x3dws1)(icf, zdummy, tbuf, coef_mode, cf_4b, false/*cf_zp*/, obuf, olen);
    break;
  case NINO(conv_mode_2x3dws2):
    assert(coef_mode != coef_mode_sparse);
    NINO(fm8cf8_2x3dws2)(icf, zdummy, tbuf, coef_mode, cf_4b, false/*cf_zp*/, obuf, olen);
    break;
  case NINO(conv_mode_8x1dws1):
    assert(coef_mode != coef_mode_sparse);
    NINO(fm8cf8_8x1dws1)(icf, zdummy, tbuf, coef_mode, cf_4b, false/*cf_zp*/, obuf, olen);
    break;
  case NINO(conv_mode_4x1dws1):
    assert (coef_mode != coef_mode_sparse);
    NINO(fm8cf8_4x1dws1)(icf, zdummy, tbuf, coef_mode, cf_4b, false/*cf_zp*/, obuf, olen);
    break;
  case DINO(conv_mode_1x1):
    if (icf.get_dim(5) != 1) {
      if (fm_dbl) {
        DINO(gfm16cf8ns_1x1)(icf, zdummy, tbuf, coef_mode, cf_4b, false/*cf_zp*/, obuf, olen);
      } else if ((icf.get_dim(4) == icf.get_dim(0)) && ((icf.get_dim(0) % (2*ISIZE)) == 0)) {
        DINO(fm8cf8ns_1x1)(icf, zdummy, tbuf, coef_mode, cf_4b, false/*cf_zp*/
                           , inn, onn, obuf, olen);
      } else {
        DINO(gfm8cf8ns_1x1)(icf, zdummy, tbuf, coef_mode, cf_4b, false/*cf_zp*/, obuf, olen);
      }
    } else if (coef_mode == coef_mode_sparse) {
      assert(!fm_dbl && "sparse mode not supported with 16b feature-map");
      DINO(fm8cf8s_1x1)(icf, zdummy, tbuf, false/*cf_zp*/, obuf, olen);
    } else if (fm_dbl) {
      DINO(fm16cf8ns_1x1)(icf, zdummy, tbuf, coef_mode, cf_4b, false/*cf_zp*/, obuf, olen);
    } else {
      DINO(fm8cf8ns_1x1)(icf, zdummy, tbuf, coef_mode, cf_4b, false/*cf_zp*/
                         , inn, onn, obuf, olen);
    }
    break;
  case NINO(conv_mode_1x1):
    assert(coef_mode != coef_mode_sparse && !fm_dbl);
    NINO(fm8cf8ns_1x1)(icf, zdummy, tbuf, coef_mode, cf_4b, false/*cf_zp*/, obuf, olen);
    break;
  case NINO(conv_mode_2x1s1):
  case NINO(conv_mode_2x1s2):
  case NINO(conv_mode_2x1s1dl2):
    assert(coef_mode != coef_mode_sparse);
    if (fm_dbl) {
      NINO(fm16cf8ns_2x1)(icf, zdummy, tbuf, coef_mode, cf_4b, false/*cf_zp*/, obuf, olen);
    } else {
      NINO(fm8cf8ns_2x1)(icf, zdummy, tbuf, coef_mode, cf_4b, false/*cf_zp*/, obuf, olen);
    }
    break;
  case NINO(conv_mode_2x1g2s2):
    assert(coef_mode != coef_mode_sparse && !fm_dbl);
    NINO(fm8cf8ns_2x1g2)(icf, zdummy, tbuf, coef_mode, cf_4b, false/*cf_zp*/, obuf, olen);
    break;
  case NINO(conv_mode_4x1g2s1dl2):
  case NINO(conv_mode_4x1g2s1):
    assert(coef_mode != coef_mode_sparse && !fm_dbl);
    NINO(fm8cf8ns_4x1g2)(icf, zdummy, tbuf, coef_mode, cf_4b, false/*cf_zp*/, obuf, olen);
    break;
  default: assert(0);  // not implemented yet
  }
}

// encode 8b coefficients with zero-point
void coef_enc(
              const tensor_t<coef_t, 6, xbuffer_t>& icf,  // input coefficients
              // [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
              const tensor_t<coef_t, 1, xbuffer_t>&     izp,       // input zero-points [Cout]
              xbuffer_t<coef_t>&        tbuf,       // temporary xbuf // NOLINT [runtime/references]
              // attributes
              conv_mode_t               conv_mode,  // convolution mode
              coef_mode_t               coef_mode,  // coefficient compression mode uncompressed
              // or compressed or sparse
              bool                      fm_dbl,     // 16b feature-map
              bool                      cf_4b,      // 4b coefficient encoding
              int                       inn,        // inner input loop
              int                       onn,        // inner output loop
              // outputs, buffers preallocated by caller
              xbuffer_t<ixpix_t>&                   // NOLINT [runtime/references]
              obuf,                               // output encoded coefficient tensor
              size_t&                   olen        // size of used coefficient buffer in bytes
              ) {
  switch (conv_mode) {
  case NINO(conv_mode_3x3dws1dl2):
    assert(coef_mode != coef_mode_sparse);
    NINO(fm8cf8_3x3dws1dl2)(icf, izp, tbuf, coef_mode, cf_4b, true/*cf_zp*/, obuf, olen);
    break;
  case NINO(conv_mode_3x3dws1):
    assert(coef_mode != coef_mode_sparse);
    NINO(fm8cf8_3x3dws1)(icf, izp, tbuf, coef_mode, cf_4b, true/*cf_zp*/, obuf, olen);
    break;
  case NINO(conv_mode_2x3dws2):
    assert(coef_mode != coef_mode_sparse);
    NINO(fm8cf8_2x3dws2)(icf, izp, tbuf, coef_mode, cf_4b, true/*cf_zp*/, obuf, olen);
    break;
  case NINO(conv_mode_8x1dws1):
    assert(coef_mode != coef_mode_sparse);
    NINO(fm8cf8_8x1dws1)(icf, izp, tbuf, coef_mode, cf_4b, true/*cf_zp*/, obuf, olen);
    break;
  case NINO(conv_mode_4x1dws1):
    assert (coef_mode != coef_mode_sparse);
    NINO(fm8cf8_4x1dws1)(icf, izp, tbuf, coef_mode, cf_4b, true/*cf_zp*/, obuf, olen);
    break;
  case DINO(conv_mode_1x1):
  //#if NPU_VER_IS_VIC2_GA
    if (icf.get_dim(5) != 1) {
      if (fm_dbl) {
        DINO(gfm16cf8ns_1x1)(icf, izp, tbuf, coef_mode, cf_4b, true/*cf_zp*/, obuf, olen);
      } else if ((icf.get_dim(4) == icf.get_dim(0)) && ((icf.get_dim(0) % (2*ISIZE)) == 0)) {
        DINO(fm8cf8ns_1x1)(icf, izp, tbuf, coef_mode, cf_4b, true
                           , inn, onn, obuf, olen);
      } else {
        DINO(gfm8cf8ns_1x1)(icf, izp, tbuf, coef_mode, cf_4b, true/*cf_zp*/, obuf, olen);
      }
    } else
  //#endif
    if (coef_mode == coef_mode_sparse) {
      assert(!fm_dbl && "sparse mode not supported with 16b feature-map");
      DINO(fm8cf8s_1x1)(icf, izp, tbuf, true/*cf_zp*/, obuf, olen);
    } else if (fm_dbl) {
      DINO(fm16cf8ns_1x1)(icf, izp, tbuf, coef_mode, cf_4b, true/*cf_zp*/, obuf, olen);
    } else {
      DINO(fm8cf8ns_1x1)(icf, izp, tbuf, coef_mode, cf_4b, true/*cf_zp*/, inn, onn, obuf, olen);
    }
    break;
  case NINO(conv_mode_1x1):
    assert(coef_mode != coef_mode_sparse && !fm_dbl);
    NINO(fm8cf8ns_1x1)(icf, izp, tbuf, coef_mode, cf_4b, true/*cf_zp*/, obuf, olen);
    break;
  case NINO(conv_mode_2x1s1):
  case NINO(conv_mode_2x1s2):
  case NINO(conv_mode_2x1s1dl2):
    assert(coef_mode != coef_mode_sparse);
    if (fm_dbl) {
      NINO(fm16cf8ns_2x1)(icf, izp, tbuf, coef_mode, cf_4b, true/*cf_zp*/, obuf, olen);
    } else {
      NINO(fm8cf8ns_2x1)(icf, izp, tbuf, coef_mode, cf_4b, true/*cf_zp*/, obuf, olen);
    }
    break;
  case NINO(conv_mode_4x1g2s1):
  case NINO(conv_mode_4x1g2s1dl2):
    assert(coef_mode != coef_mode_sparse && !fm_dbl);
    NINO(fm8cf8ns_4x1g2)(icf, izp, tbuf, coef_mode, cf_4b, true/*cf_zp*/, obuf, olen);
    break;
  case NINO(conv_mode_2x1g2s2):
    assert(coef_mode != coef_mode_sparse && !fm_dbl);
    NINO(fm8cf8ns_2x1g2)(icf, izp, tbuf, coef_mode, cf_4b, true/*cf_zp*/, obuf, olen);
    break;
  default: assert(0);  // not implemented yet
  }
}

//= FC
// -encode 16b coefficients fc
void coef_enc(
              const tensor_t<coef_t, 4, xbuffer_t>& icf,  // input coefficients
              // [Grp]Cout][Cin][coef h/l], 8b only
              xbuffer_t<coef_t>&                          // NOLINT [runtime/references]
              tbuf,                                       // memory allocator for temporary buffers
              // attributes
              int                       vs,               // VSIZE
              bool                      fm_dbl,           // 16b feature-map
              // outputs, buffers preallocated by caller
              xbuffer_t<ixpix_t>&                         // NOLINT [runtime/references]
              obuf,                                       // output encoded coefficient tensor
              size_t&                   olen              // size of used coefficient buffer in bytes
              ) {
  if (fm_dbl) {
    FC(fm16cf16ns)(icf, tbuf, vs, obuf, olen);
  } else {
    FC(fm8cf16ns)(icf, tbuf, vs, obuf, olen);
  }
}
// -encode 8b coefficients without zero-point
void coef_enc(
              const tensor_t<coef_t, 3, xbuffer_t>& icf,  // input coefficients [Grp][Cout][Cin], 8b only
              xbuffer_t<coef_t>&                          // NOLINT [runtime/references]
              tbuf,                                       // memory allocator for temporary buffers
              // attributes
              int                       vs,               // VSIZE
              coef_mode_t               coef_mode,        // coefficient compression mode uncompressed
              // or compressed (not sparse)
              bool                      fm_dbl,           // 16b feature-map
              bool                      cf_4b,            // 4b coefficient encoding
              // outputs, buffers preallocated by caller
              xbuffer_t<ixpix_t>&                         // NOLINT [runtime/references]
              obuf,                                       // output encoded coefficient tensor
              size_t&                   olen              // size of used coefficient buffer in bytes
              ) {
  xbuffer_t<coef_t> cb = tbuf.split(static_cast<size_t>(icf.get_dim(1)*icf.get_dim(2)));
  tensor_t<coef_t, 1, xbuffer_t> zdummy(cb, {(aoffset_t)(icf.get_dim(1)*icf.get_dim(2))});
  if (coef_mode == coef_mode_sparse) {
    assert(!fm_dbl && "sparse mode not supported with 16b feature-map");
    FC(fm8cf8s)(icf, zdummy, tbuf, vs, false/*cf_zp*/, obuf, olen);
  } else if (fm_dbl) {
    FC(fm16cf8ns)(icf, zdummy, tbuf, vs, coef_mode, cf_4b, false/*cf_zp*/, obuf, olen);
  } else {
    FC(fm8cf8ns)(icf, zdummy, tbuf, vs, coef_mode, cf_4b, false/*cf_zp*/, obuf, olen);
  }
}
// -encode 8b coefficients with zero-point
void coef_enc(
              const tensor_t<coef_t, 3, xbuffer_t>& icf,  // input coefficients [Grp][Cout][Cin], 8b only
              const tensor_t<coef_t, 1, xbuffer_t>& izp,  // input zero-points [Cout]
              xbuffer_t<coef_t>&                          // NOLINT [runtime/references]
              tbuf,                                     // memory allocator for temporary buffers
              // attributes
              int                       vs,               // VSIZE
              coef_mode_t               coef_mode,        // coefficient compression mode uncompressed
              // or compressed (not sparse)
              bool                      fm_dbl,           // 16b feature-map
              bool                      cf_4b,            // 4b coefficient encoding
              // outputs, buffers preallocated by caller
              xbuffer_t<ixpix_t>&                         // NOLINT [runtime/references]
              obuf,      // output encoded coefficient tensor
              size_t&                   olen              // size of used coefficient buffer in bytes
              ) {
  if (coef_mode == coef_mode_sparse) {
    assert(!fm_dbl && "sparse mode not supported with 16b feature-map");
    FC(fm8cf8s)(icf, izp, tbuf, vs, true/*cf_zp*/, obuf, olen);
  } else if (fm_dbl) {
    FC(fm16cf8ns)(icf, izp, tbuf, vs, coef_mode, cf_4b, true/*cf_zp*/, obuf, olen);
  } else {
    FC(fm8cf8ns)(icf, izp, tbuf, vs, coef_mode, cf_4b, true/*cf_zp*/, obuf, olen);
  }
}
}  // namespace npu_conv

#undef LDBGV
