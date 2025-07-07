#ifndef HOST_DPI_REFERENCE
#define HOST_DPI_REFERENCE

// include header file from simulator
#ifndef NPU_RTL_SIMULATOR
  #define NPU_RTL_SIMULATOR 0
#endif
#if NPU_RTL_SIMULATOR==1
  #include "xrun_hdrs.h"
  #define HOST_EXEC     int host_exec
  #define HOST_EXEC_RET return 0
#elif NPU_RTL_SIMULATOR==2
  #include "sv2c.h"
  #define HOST_EXEC     int host_exec
  #define HOST_EXEC_RET return 0
#else
  #include "vc_hdrs.h"
  #define HOST_EXEC     void host_exec
  #define HOST_EXEC_RET return
#endif
#include <iostream>
#include <cassert>
using namespace std;

//#define HOST_CFG_DMI_LOG 1

inline void set_sim_finish_flag(int err) {
    host_exit(err);
}

 //
// Memory read/write
//
template<typename T>
inline T mem_read(const T* p) {
  T      r;
  const char*  pv = reinterpret_cast<const char*>(p);
  char*  pr = reinterpret_cast<char*>(&r);
  size_t s = sizeof(T);
  int    m;
  long   d;
  char*  pd = reinterpret_cast<char*>(&d);

  while (s != 0) {
    // check start alignment
    m = 8-(reinterpret_cast<long long>(pv)&0x7);
    if (m == 8 && s < 8) {
      // cannot to do 64b
      m = 4;
    } // else can do 64b
    if (m < 8 && m >= 4) {
      if (s < 4) {
        // cannot to 32b
        m = 2;
      } else {
        // can do 32b
        m = 4;
      }
    }
    if (m < 4 && m >= 2) {
      if (s < 2) {
        // cannot do 16b
        m = 1;
      } else {
        // can do 16b
        m = 2;
      }
    }
    switch (m) {
    case 1: host_read((long long)reinterpret_cast<long long>(pv), 0); break;
    case 2: host_read((long long)reinterpret_cast<long long>(pv), 1); break;
    case 4: host_read((long long)reinterpret_cast<long long>(pv), 2); break;
    case 8: host_read((long long)reinterpret_cast<long long>(pv), 3); break;
    default: assert(0);
    }

    pv += m;
    s  -= m;

    d = get_retd((long long)reinterpret_cast<long long>(pd));
    for(int i=0; i<m; i++) {
      *pr++ = *pd++;
    }
  }
  return r;
}
template<typename T>
inline void mem_write(T* p, const T& d) {
  char*  pv = reinterpret_cast<char*>(p);
  const char* pr = reinterpret_cast<const char*>(&d);
  size_t s = sizeof(T);
  int    m;
  while (s != 0) {
    // check start alignment
    m = 8-(reinterpret_cast<long long>(pv)&0x7);
    if (m == 8 && s < 8) {
      // cannot do 64b
      m = 4;
    } // else can do 64b
    if (m < 8 && m >= 4) {
      if (s < 4) {
        // cannot to 32b
        m = 2;
      } else {
        // can do 32b
        m = 4;
      }
    }
    if (m < 4 && m >= 2) {
      if (s < 2) {
        // cannot do 16b
        m = 1;
      } else {
        // can do 16b
        m = 2;
      }
    }
    switch (m) {
    case 1: host_write_byte((long long)reinterpret_cast<long long>(pv), *pr); break;
    case 2: host_write_short((long long)reinterpret_cast<long long>(pv), *reinterpret_cast<const short*>(pr)); break;
    case 4: host_write_int((long long)reinterpret_cast<long long>(pv), *reinterpret_cast<const int*>(pr)); break;
    case 8: host_write_long((long long)reinterpret_cast<long long>(pv), *reinterpret_cast<const long long*>(pr)); break;
    default: assert(0);
    }
    pv += m;
    pr += m;
    s  -= m;
  }
}

inline int cfg_dmi_read(long long* p) {
    int d = mem_read((int*)p);
#ifdef HOST_CFG_DMI_LOG
    cout << hex << "      cfg_dmi_read "<<p<<" = 0x"<<d<<endl;
#endif
    return d;
}

inline void cfg_dmi_write(long long* p, int d) {
#ifdef HOST_CFG_DMI_LOG
    cout << hex << "      cfg_dmi_write "<<p<<"  0x"<<d<<endl;
#endif
    const int data = (const int)d;
    mem_write((int*)p, data);
}

inline int cfg_arcsync_read(int* p) {
    int d = mem_read(p);
    return d;
}

inline void cfg_arcsync_write(int* p, int d) {
    const int data = (const int)d;
    mem_write(p, data);
}

inline long long cfg_dmi_long_read(long long* p) {
    long long d = mem_read((long long*)p);
    return d;
}

inline void cfg_dmi_long_write(long long* p, long long d) {
    const long long data = d;
    mem_write((long long*)p, data);
}

#if NPU_HAS_JTAG
inline void set_dbg_id (int proc_id){
  int jtag_id = (proc_id == NPU_HAS_L2ARC+NPU_SLICE_NUM) ? DUO_L2ARC : proc_id + DUO_L2ARC;
  set_rascal_proc_id(jtag_id);
}

inline void dbg_write_mem(int addr, int data){
   issue_rascal_cmd(DBG_MEM_WRITE, addr, data);
}

inline void dbg_write_reg(int addr, int data){
   issue_rascal_cmd(DBG_REG_WRITE, addr, data);
}

inline void dbg_write_aux(int addr, int data){
   issue_rascal_cmd(DBG_AUX_WRITE, addr, data);
}

inline int dbg_read_mem(int addr){
   issue_rascal_cmd(DBG_MEM_READ, addr, 0);
   int d = host_read_int(addr);
   return d;
}
inline int dbg_read_reg(int addr){
   issue_rascal_cmd(DBG_REG_READ, addr, 0);
   int d = host_read_int(addr);
   return d;
}
inline int dbg_read_aux(int addr){
   issue_rascal_cmd(DBG_AUX_READ, addr, 0);
   int d = host_read_int(addr);
   return d;
}
#endif

#endif // HOST_DPI_REFERENCE
