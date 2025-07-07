// Library ARCv2HS-3.5.999999999



  ////////// EIA user extension external input signals ///////////////////////
  //
  input   [95:0]  EventManager_evm_event_a,
  input           EventManager_evm_sleep,

  ////////// EIA user extension external output signals //////////////////////
  //
  output          EventManager_evm_wakeup,
  output  [63:0]  EventManager_evm_send,
  output  [31:0]  EventManager_vm_grp0_sid,
  output  [31:0]  EventManager_vm_grp0_ssid,
  output  [31:0]  EventManager_vm_grp1_sid,
  output  [31:0]  EventManager_vm_grp1_ssid,
  output  [31:0]  EventManager_vm_grp2_sid,
  output  [31:0]  EventManager_vm_grp3_sid,
  output  [31:0]  EventManager_vm_grp2_ssid,
  output  [31:0]  EventManager_vm_grp3_ssid,
  output          EventManager_evt_vm_irq,
  output  [3:0]  EventManager_evt_vm_sel,
