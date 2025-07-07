#!/bin/bash
# the next line restarts using tclsh \
exec tclsh "$0" "$@"

set stop_units_fname ./ram_sizes.txt
if [file exists ./lint_stop_units.txt] {
  set stop_units_fname ./lint_stop_units.txt
}
set stop_units_tcl ./scripts/spyglass/stop_units.tcl
puts "INOF: lint_stop_uints file = $stop_units_fname"
puts "INOF: lint_stop_uints tcl  = $stop_units_tcl"

# Read the stop_units_file
if [file readable $stop_units_fname] {
  set ramSizesFile [open "$stop_units_fname" r]
  set ramSizes [split [read $ramSizesFile] \n]
  close $ramSizesFile
} else {
  puts "File $stop_units_fname does not exist or is not readable"
  exit 1
}

if [catch {open "$stop_units_tcl" w} stopUnitFile] {
  puts "ERROR ($argv0): Can't create file $stop_units_tcl"
  exit 1
}  

foreach line $ramSizes {
  if [regexp "^\\s*(\\w+)\\s+.*" $line dummy stop_unit] {
    puts $stopUnitFile "set_option stop ${stop_unit}"
  }
}

