#!/bin/bash
# the next line restarts using tclsh \
exec tclsh "$0" "$@"

########################################################################################
#
# TCL Script to prepend SGLIB for Rams and StdCells to Spyglass file list
#
########################################################################################

# Open input file
set sglib_file [lindex $argv 0]

source scripts/options.tcl

########################################################
## Get Rams List
########################################################

set rams_list ""
set ram_libraries [glob -nocomplain lib/*.db]

foreach ram_db $ram_libraries {
    regsub {^lib\/([\w\d]+).db} $ram_db {\1} ram_db
    set rams_list "$rams_list $ram_db"
}

# Open input file as output
if [catch {open $sglib_file w} file_out] {
  puts "Can't open '${sglib_file}' for writing because of error '$file_out'"
  exit 1
}

########################################################
## Generate SGLIB libraries for each Ram
########################################################

foreach ram_name $rams_list {

    set ram_lib_name sglibs/${ram_name}.sglib

	# Only prepend SGLIB ram library if it exist
	if [file exists $ram_lib_name ] {
	  puts $file_out "read_file -type sglib $ram_lib_name"
	} else {
	  puts "Warning: $ram_lib_name does not exists"
	}
	
}

########################################################
## Generate SGLIB libraries for each StdCells
########################################################

if [info exists arc_max_library_name] {
  foreach tech_lib ${arc_max_library_name} {
    if [file exists sglibs/${tech_lib}.sglib ] {
      puts $file_out "read_file -type sglib sglibs/${tech_lib}.sglib"
    }
  }
}
close $file_out

exit

