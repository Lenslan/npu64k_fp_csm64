#!/usr/bin/env python
"""
import os

npu_home = os.environ["NPU_HOME"]
api_file = open (npu_home+'/arch/arcsync/common/arcsync_utils.hpp')
for line in api_file.readlines():
  line= line.strip()
  #print (line)
  if (line.find("arcsync_")!= -1) & (line.find ('(')!= -1) & (line.find (')')!= -1):
    print (line)
"""
import argparse
parser = argparse.ArgumentParser()
parser.add_argument("-d", "--dir", help="test.hpp location")
args = parser.parse_args()
dir_loc = args.dir

## api lists
api_list = { # acs
              'arcsync_core_status'     : 0   
             ,'arcsync_core_run'        : 1
             ,'arcsync_core_halt'       : 2
             ,'arcsync_core_reset'      : 3
             ,'arcsync_core_intvbase'   : 4
             ,'arcsync_core_powerdown'  : 5
             ,'arcsync_core_powerdup'   : 6
             ,'arcsync_core_run_s0'     : 7
             ,'arcsync_core_halt_s0'    : 8
             # event and irq
             ,'arcsync_send_event'      :11
             ,'arcsync_send_irq'        :12 
             ,'arcsync_ack_irq'         :13
             ,'arcsync_event_waiting'   :14
             ,'arcsync_send_irq_s0'     :15 
             # ac (arcsync_atomic_cnt)
             ,'.configure'           :21
             ,'.get_count'           :22
             ,'.request_update'      :23
             ,'.get_status'          :24
             ,'.check_last_request'  :25
             ,'.decr_request'        :26
             ,'.incr_request'        :27
             ,'.wait_event'          :28
             ,'.decrement_check'     :29
             ,'.increment_check'     :30
             ,'arcsync_ack_ac_irq'   :31
             ,'arcsync_check_ac_irq' :31
             # mutx (arcsync_mutex)
             ,'.unlock'              :41
             ,'.try_lock'            :42
             ,'.lock'                :43
             ,'.lock_irq_notify'     :44
             # semaphore (arcsync_semaphore)
             ,'.release'             :51
             ,'.try_acquire'         :52
             ,'.acquire'             :53
             # barrier (arcsync_barrier)
             ,'.arrive'              :61
             ,'.wait'                :62
             ,'.arrive_and_wait'     :63
             # gfrc
             ,'arcsync_gfrc_enable'       : 71
             ,'arcsync_gfrc_status'       : 72
             ,'arcsync_gfrc_clear'        : 73
             ,'arcsync_gfrc_read'         : 74
             ,'arcsync_gfrc_read_low'     : 75
             ,'arcsync_gfrc_read_hi'      : 76
             # pmu
             ,'arcsync_pmu_pu_count_set'  : 81
             ,'arcsync_pmu_pu_count_get'  : 82
             ,'arcsync_pmu_pd_count_set'  : 83
             ,'arcsync_pmu_pd_count_get'  : 84
             ,'arcsync_pmu_rst_count_set' : 85
             ,'arcsync_pmu_rst_count_get' : 86
             #event_mgr
             ,'event_wait_any'      : 91
             ,'event_wait_all'      : 92
             ,'event_write'         : 93
             ,'event_read'          : 94
             ,'event_send_parent'   : 95
             ,'event_send_children' : 96
             ,'event_send_peers'    : 97
           }
count    = [0] * (max(api_list.values())+1)

run_l1    = 0

file_path = dir_loc+"/"+ "test.hpp"
print ("open file:" +file_path)
f = open( file_path )
comment_b = 0
comment_l = 0
cont_eid_irq_core = -1
corenum= -1


for line in f.readlines():
  line = line.strip()

  comment_l =0;
  if line.find("//",0,2) != -1:
    comment_l = 1;
  if line.find("/*") != -1:
    comment_b = 1
  if line.find("*/") != -1:
    comment_b = 0

  if line.find("//l2arc") != -1:
    corenum = 0
  elif line.find("//l1arc") != -1:
    corenum = 1

  for api_str, idx in api_list.items():
    if (comment_l | comment_b) ==0:
      if line.find(api_str) != -1:
        #print (line)
        if (run_l1 == 0 and api_str == 'arcsync_core_halt'):
          count[8] += 1
        elif (run_l1 == 1 and api_str == 'arcsync_core_run'):
          count[7] += 1
        elif (cont_eid_irq_core == corenum and api_str == 'arcsync_send_irq'):
          count[15] += 1
        else:
          count[idx] += 1
        if (api_str == 'arcsync_core_halt'):
          run_l1 = 0
        if (api_str == 'arcsync_core_run'):
          run_l1 = 1
        if (api_str == 'arcsync_send_irq'):
          cont_eid_irq_core = corenum

f.close();

## print out the match api count
cov_path = dir_loc+"/" + "arcsync_api_cov"
print ("open file:" +cov_path)
f = open (cov_path,"w")
for api in api_list:
  msg = api+ ' ' + str(count[api_list[api]])
  #print ("write msg::" + msg)
  f.write(msg+"\n");
f.close();
