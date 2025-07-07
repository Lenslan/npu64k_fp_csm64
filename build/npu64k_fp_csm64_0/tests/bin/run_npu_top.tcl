
#
# Tcl script for batch simulation runs using vsim
#
# Copyright (c) 2014 Synopsys, Inc. This processor model and the associated
# documentation are proprietary to Synopsys, Inc.  This model may only be
# used in accordance with the terms and conditions of a written license 
# agreement with Synopsys, Inc.  All other use, reproduction, or distribution 
# of this model are strictly prohibited.
#

set npu_rtl_simulator 0
set tb_vip 0
set tb_mdb 0

if { [info exists ::env(NPU_RTL_SIMULATOR) ] } {
  set npu_rtl_simulator $env(NPU_RTL_SIMULATOR)
}

if { [info exists ::env(TB_VIP)] } {
  set tb_vip $env(TB_VIP)
}

if { [info exists ::env(TB_MDB)] } {
  set tb_mdb $env(TB_MDB)
}

if { $tb_vip == 1 } {
  set top core_archipelago_tb 
} else {
  set top npu_tb_top
}

# vcs
if { $npu_rtl_simulator == 0 } {
  if { [info exists ::env(DUMP_WAVEFORM) ] } {
      if ($env(DUMP_WAVEFORM)) {
          set tname "wave"
          if { [info exists ::env(TESTNAME) ] } {
              set tname $env(TESTNAME)
          }
  
          dump -file ${tname}.fsdb -type FSDB
          dump -add $top -aggregates -fsdb_opt  +packedmda+struct
      }
  
  }

  #simulate 
  run 
  if { !${tb_mdb} } {
    #finish
    quit
  }
}

# xcelium
if { $npu_rtl_simulator == 1 } {
  if { [info exists ::env(DUMP_WAVEFORM) ] } {
    if ($env(DUMP_WAVEFORM)) {
      call fsdbDumpfile wave.fsdb 
      call fsdbDumpvars 0 $top +all
	}
  }

  #simulate 
  run 
  if { !${tb_mdb} } {
    #finish
    quit
  }
}

# questasim
if { $npu_rtl_simulator == 2 } {
  if { [info exists ::env(DUMP_WAVEFORM) ] } {
    if ($env(DUMP_WAVEFORM)) {
      fsdbDumpfile wave.fsdb 
      fsdbDumpvars 0 $top +all
	}
  }

  #simulate 
  run -all
  if { !${tb_mdb} } {
    #finish
    quit -sim
  }
}

