#ifndef HOST_UTILS
#define HOST_UTILS
 #define DBG_MEM_WRITE  0
 #define DBG_REG_WRITE  1
 #define DBG_AUX_WRITE  2
 #define DBG_CORE_RST   3
 #define DBG_MEM_READ   4
 #define DBG_REG_READ   5
 #define DBG_AUX_READ   6

#ifndef HOST_DPI
#define HOST_DPI
#endif
#include "dpi_reference.hpp"
#include "sys_config.hpp"
#include "../npu_mem_utils.hpp"
#include "../npu_mem_map_define.hpp"
#include "host_loapi.hpp"
//#include "arcsync_utils.hpp"
#include "../npu_sfty_define.hpp"

#endif
