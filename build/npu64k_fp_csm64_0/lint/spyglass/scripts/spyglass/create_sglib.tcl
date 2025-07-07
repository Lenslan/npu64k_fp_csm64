#!/bin/bash
# the next line restarts using tclsh \
exec tclsh "$0" "$@"

########################################################################################
#
# TCL Script to generate SGLIB for Rams and StdCells with SpyGlass Library Compiler tool
#
########################################################################################

exec mkdir -p sglibs

source scripts/options.tcl

########################################################
## Extract LIB file path from Database path
########################################################

set lib_file_path ""

if [info exists data_base_path] {
  regsub {^([\w\d\/]+)\/[\w]+.txt} $data_base_path {\1} lib_file_path
} else {
  puts "Warning: Technology library 'data_base_path' variable does not exist, no memory models included"
  exit
}

set lib_file_path ${lib_file_path}/LIB/


########################################################
## Get Rams List
########################################################

set rams_list ""
set ram_libraries [glob -nocomplain lib/*.db]

foreach ram_db $ram_libraries {
    regsub {^lib\/([\w\d]+).db} $ram_db {\1} ram_db
    set rams_list "$rams_list $ram_db"
}


########################################################
## Generate SGLIB libraries for each Ram
########################################################

foreach ram_name $rams_list {

    set ram_lib_name sglibs/${ram_name}.sglib
    set lib_file ${lib_file_path}${ram_name}.lib

	# Only create new SGLIB ram library if it doesn't already exist
	if {![file exists $ram_lib_name ]} {
	  # Catch mechanism needed since spyglass returns with a message
	  if [catch {exec spyglass_lc -gateslib $lib_file -outsglib $ram_lib_name} msg] {
	    puts "$msg"
	  }
	}
}

########################################################
## Generate SGLIB libraries for each Stdcell
########################################################
## The liberty models of std cells could be zipped or not or a mixture of both -hence checking against existence of .lib as well as .lib.gz

set clkgate_mapped [catch {exec grep -R CellLibraryClockGate verilog} msg]
if {$clkgate_mapped == "0"} {
  foreach tech_lib ${arc_max_library_name} {
    if {![file exists sglibs/${tech_lib}.sglib ]} {
      foreach tech_lib_path ${arc_tech_library_path} {
  	if  [file exists ${tech_lib_path}/${tech_lib}.lib]  {
          if [catch {exec spyglass_lc -gateslib ${tech_lib_path}/${tech_lib}.lib -outsglib sglibs/${tech_lib}.sglib} msg] {
            puts "$msg"
          }
	  }
	if  [file exists ${tech_lib_path}/${tech_lib}.lib.gz]  {  
         if [catch {exec spyglass_lc -gateslib ${tech_lib_path}/${tech_lib}.lib.gz -outsglib sglibs/${tech_lib}.sglib} msg] {
            puts "$msg"
          }
        }
      }
    }
  }
}

exit

