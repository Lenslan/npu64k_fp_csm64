#include "arc_program.hpp"
#ifdef RTL_DPI
//
// ARC HW abstraction for DPI simulation
//

#include <assert.h>
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
#include "vpi_user.h"

void irq_callback() {
  svScope sc = svGetScope();
  npu::arc_program* me = (npu::arc_program*)svGetUserData(sc, (void*) &irq_callback);
  if (me != NULL) {
    me->irq();
  }
}

void npu::arc_printf(const char* fmt, ...) {
  // print to simulator log
  va_list args;
  va_start(args, fmt);
  vpi_vprintf((PLI_BYTE8*)fmt, args);
  va_end(args);
}
#endif
