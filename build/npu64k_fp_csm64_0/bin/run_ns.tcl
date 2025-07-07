
#
# Tcl script for batch simulation runs using vsim
#
# Copyright (c) 2014 Synopsys, Inc. This processor model and the associated
# documentation are proprietary to Synopsys, Inc.  This model may only be
# used in accordance with the terms and conditions of a written license 
# agreement with Synopsys, Inc.  All other use, reproduction, or distribution 
# of this model are strictly prohibited.
#

set top ns_tb_top

if { [info exists ::env(DUMP_WAVEFORM) ] } {
    if ($env(DUMP_WAVEFORM)) {
        set tname "wave"
        if { [info exists ::env(TESTNAME) ] } {
            set tname $env(TESTNAME)
        }

        dump -file ${tname}.fsdb -type FSDB
        dump -add $top -fsdb_opt +packedmda+struct -aggregates
    }

}

# Simulate 
run
#finish
quit


