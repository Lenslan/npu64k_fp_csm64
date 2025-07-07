#include <assert.h>
#ifdef RTL_DPI
// include header file from simulator
  #ifndef NPU_RTL_SIMULATOR
    #define NPU_RTL_SIMULATOR 0
  #endif
  #if NPU_RTL_SIMULATOR==1
    #include "xrun_hdrs.h"
  #elif NPU_RTL_SIMULATOR==2
    #include "sv2c.h"
  #else
    #include "vc_hdrs.h"
  #endif
#endif

#include "npu_defines.hpp"
