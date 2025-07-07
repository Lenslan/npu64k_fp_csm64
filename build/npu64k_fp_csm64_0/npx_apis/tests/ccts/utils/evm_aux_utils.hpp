#ifndef EVM_AUX_UTILS
#define EVM_AUX_UTILS

#include "utils/npu_mem_utils.hpp"
#include "utils/arc_irq_expcn.hpp"

#define REG_READ_ONLY true
#define REG_READ_WRITE false


void aux_illegal_access(const uint32_t reg_addr, const bool can_read, const bool can_write, const bool need_previlege) {
  if(!can_read){
    clear_ecr();
    excpn_intention_flag = need_previlege ? 3 : 2 ;
    _lr(reg_addr);
    _sync();
    excpn_intention_flag = 0 ;
    // exception casue 
    uint32_t ecr = need_previlege ? ECR_PrivilegeV : ECR_ILLEGAL_INST;
    check_excpn_taken(ecr);
  }

  if(!can_write){
    clear_ecr();
    excpn_intention_flag = need_previlege ? 3 : 2 ;
    _sr(0x0, reg_addr);
    _sync();
    excpn_intention_flag = 0 ;
    // exception casue 
    uint32_t ecr = need_previlege ? ECR_PrivilegeV : ECR_ILLEGAL_INST;
    check_excpn_taken(ecr);
  }
}

void aux_access_test(const uint32_t reg_addr, const bool can_read, const bool can_write, const uint32_t rst_v, const uint32_t mask, const bool need_previlege) {
    //illegal access test
    aux_illegal_access(reg_addr, can_read, can_write, need_previlege);

    uint32_t v;
    //reset value check
    if(can_read) {
      v = _lr(reg_addr);
      do_compare(v, rst_v);
    }

    // read after write test
    if(can_read && can_write){
      uint32_t wv = 0xffffffff;
      uint32_t ref = mask & wv;

      _sr(wv, reg_addr);
      v = _lr(reg_addr);
      do_compare(v, ref);

      _sr(0, reg_addr);
      v = _lr(reg_addr);
      do_compare(v, 0);
    }
}

void evm_aux_rw_test(bool user_mode) {
  uint32_t evm_aux_base = 0x0F00;
  bool allow = not user_mode;

  //              /* Evt mannager AUX register addr */    /* can read  write */  /*reset value */  /* write mask */ /*need prilvilege*/
  aux_access_test(evm_aux_base + 0x00 /* EVT_VM_SEL */,     allow, allow, 0x0,      0xf,        true);
  aux_access_test(evm_aux_base + 0x01 /* EVT_VM_MAP */,     allow, allow, 0x0,      0x0,        true);
  if(allow) {
    _sr(0x10301800, evm_aux_base + 0x01);//default map
  }
  aux_access_test(evm_aux_base + 0x02 /* EVT_CTRL */,       true,  true,  0x0,      0x1,        false);
  aux_access_test(evm_aux_base + 0x03 /* EVT_IRQ */,        allow, allow, 0x0,      0x1,        true);
  aux_access_test(evm_aux_base + 0x04 /* EVT_FILTER_LO */,  true,  true,  0x0,      0xffffffff, false);
  aux_access_test(evm_aux_base + 0x05 /* EVT_FILTER_HI */,  true,  true,  0x0,      0xffffffff, false);
  aux_access_test(evm_aux_base + 0x06 /* RESERVED */,       false, false, 0x0,      0x0,        false);
  aux_access_test(evm_aux_base + 0x07 /* EVT_GRP_SEL */,    allow, allow, 0x0,      0x3,        true);
  aux_access_test(evm_aux_base + 0x08 /* EVT_SID */,        allow, allow, 0x0,      0xffffffff, true);
  aux_access_test(evm_aux_base + 0x09 /* EVT_SSID */,       allow, allow, 0x0,      0xffffffff, true);
  aux_access_test(evm_aux_base + 0x0a /* EVT_CNT_SEL */,    true,  true,  0x0,      0x3f,       false);
  aux_access_test(evm_aux_base + 0x0b /* EVT_CNT_VAL */,    true,  true,  0x0,      0xff,       false);
}


void set_grp_sid(int g=0, int sid=0xab135246, int ssid=0x38ce7652){
  _sr(g, 0xF07);    //EVT_GRP_SEL
  _sr(sid, 0xF08);  //EVT_SID
  _sr(ssid, 0xF09); //EVT_SSID
}

#endif
