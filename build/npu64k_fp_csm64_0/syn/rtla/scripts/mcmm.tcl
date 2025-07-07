puts "RM-info : Running script [info script]\n"

##########################################################################################
# Tool: IC Compiler II
# Script: mcmm_example.tcl
# This is a sample script to create one shared mode, two corners, and two scenarios.
# Version: K-2015.06-SP4 (Jan 11, 2016)
# Copyright (C) 2014-2016 Synopsys, Inc. All rights reserved.
##########################################################################################

## Note :
#  1. To see the full list of mode / corner / scenario specific commands,
#      refer to SolvNet 1777585 : "Multicorner-multimode constraint classification"
#
#  2. Corner operating conditions are recommended to be specified directly through
#     set_process_number, set_voltage and set_temperature
#
#	The PVT resolution function always finds the closest PVT match between the operating conditions and
#      	the library pane.
#	A Corner operating condition may be specified directly with the set_process_number, set_voltage and
#	set_temperature commands or indirectly with the set_operating_conditions command.
#	The set_process_label command may be used to distinguish between library panes with the same PVT
#	values but different process labels.

##############################################################################################
# The following is a sample script to create one shared mode, two corners, and two scenarios,
# which you can expand it to accomodate your design.
##############################################################################################

########################################
## Variables
########################################
## Parasitic files; expand it as needed
if {[file exists ${TCL_PARASITIC_SETUP_FILE}]} {
   puts "RM-info : Loading TCL_PARASITIC_SETUP_FILE ${TCL_PARASITIC_SETUP_FILE}"
   source -echo ${TCL_PARASITIC_SETUP_FILE}
}


## Mode constraints; expand it as needed
set mode1 				"functional" ;# name for mode1
set mode_constraints($mode1)            "" ;# for mode1 specific SDC constraints

## Worst case corner to get timing information
set corner1 				"wc" ;# name of corner1
set corner_constraints($corner1)        "${ARC_PRJ_DIR}/scripts/fc/rm_fc_scripts/wc_corner.sdc" ;# for corner1 specific SDC constraints

## Typical (nominal) corner, used for power analysis
set corner2 				"typ" ;# name of corner2
set corner_constraints($corner2)        "${ARC_PRJ_DIR}/scripts/fc/rm_fc_scripts/nc_corner.sdc" ;# for corner2 specific SDC constraints

## Best case corner
#set corner3 				"bc" ;# name of corner3
#set corner_constraints($corner3)        "${ARC_PRJ_DIR}/scripts/fc/rm_fc_scripts/bc_corner.sdc" ;# for corner3 specific SDC constraints

## Scenario constraints; expand it as needed; "::" is used as the separator following time.scenario_auto_name_separator default
set scenario1 				"${mode1}::${corner1}" ;# scenario1 with mode1 and corner1
set scenario_constraints($scenario1)    "${CONSTRAINTS_INPUT_FILE}" ;# for scenario1 specific SDC constraints

set scenario2 				"${mode1}::${corner2}" ;# scenario2 with mode1 and corner2
set scenario_constraints($scenario2)    "${CONSTRAINTS_INPUT_FILE}" ;# for scenario2 specific SDC constraints

#set scenario3 				"${mode1}::${corner3}" ;# scenario3 with mode1 and corner3
#set scenario_constraints($scenario3)    "${CONSTRAINTS_INPUT_FILE}" ;# for scenario3 specific SDC constraints


########################################
## Create modes, corners, and scenarios first
########################################
remove_modes -all; remove_corners -all; remove_scenarios -all

foreach m [array name mode_constraints] {
	echo "RM-info : create_mode $m"
	create_mode $m
}

foreach c [array name corner_constraints] {
	echo "RM-info : create_corner $c"
	create_corner $c
}

foreach s [array name scenario_constraints] {
	set m [lindex [split $s :] 0]
	set c [lindex [split $s :] end]
	create_scenario -name $s -mode $m -corner $c
}

########################################
## Populate constraints
########################################
## Populate mode contraints
foreach m [array name mode_constraints] {
	current_mode $m

	current_scenario [index_collection [get_scenarios -mode $m] 0]
	# ensures a current_scenario exists in case provided mode constraints are actually scenario specific

	echo "RM-info : current_mode $m"
	echo "RM-info : source '$mode_constraints($m)'"
	source -echo -verbose $mode_constraints($m)
}

## NB:  It is imperative that the corner constraints be read in after the scenario constraints
## The scenario constraints (i.e.  mapped/ARCsyn*final.sdc)  use -min and -max  and associated min and max libraries  in the set_operating_conditions and these resulting in confusion for
## ICC2, STAR  9001066113

## Populate scenario constraints
foreach s [array name scenario_constraints] {
	current_scenario $s
	echo "RM-info : current_scenario $s"
	echo "RM-info : source '$scenario_constraints($s)'"
	source -echo -verbose $scenario_constraints($s)
}

## Populate corner contraints
#  Please ensure parasitics are assigned to the corners properly
foreach c [array name corner_constraints] {
	current_corner $c

	current_scenario [index_collection [get_scenarios -corner $c] 0]
	# ensures a current_scenario exists in case provided corner constraints are actually scenario specific

	echo "RM-info : current_corner $c"
	echo "RM-info : source '$corner_constraints($c)'"
	source -echo -verbose $corner_constraints($c)
	# pls ensure $corner_constraints($c) includes set_parasitic_parameters command for the corresponding corner,
	# for example, set_parasitic_parameters -late_spec $parasitics -early_spec $parasitics1,
	# where the command points to the parasitics read earlier with the read_parasitics command
}


########################################
## Configures analysis settings for scenarios
########################################
# Examples : scenario1 is a setup scenario and scenario2 is a hold scenario
set_scenario_status $scenario1 -none -setup true  -hold false -leakage_power true -dynamic_power true  -max_transition true  -max_capacitance true  -min_capacitance false -active true
set_scenario_status $scenario2 -none -setup false -hold false -leakage_power true -dynamic_power true  -max_transition false -max_capacitance false -min_capacitance false -active true
#set_scenario_status $scenario3 -none -setup false -hold true  -leakage_power true -dynamic_power false -max_transition false -max_capacitance false -min_capacitance true  -active true

redirect -tee -file ${rptpfx}.scenarios.rpt    {report_scenarios}
#redirect -tee -file ${rptpfx}.corners.rpt      {report_corners}

## Note :
#  To remove duplicate modes, corners, and scenarios, and to improve runtime and capacity,
#  without loss of constraints, try the following command :
#	remove_duplicate_timing_contexts

puts "RM-info : Completed script [info script]\n"

