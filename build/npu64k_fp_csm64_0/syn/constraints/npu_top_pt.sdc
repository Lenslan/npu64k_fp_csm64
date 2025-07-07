# Note: This file is used in PrimeTime only for additional check.

# function to set maximum skew between bits of a vector
proc max_skew_vector { sig numbits maxskew } {
  if { $numbits == 0 } {
    puts "Warning: 0-bit signal in the list"
  }
  for { set i 0 } { $i < $numbits } { incr i } {
    for { set j 0 } { $j < $numbits } { incr j } {
      if { $i != $j } {
	# for easy debug
	set pin_i_name [get_attribute [index_collection $sig $i] full_name]
	set pin_j_name [get_attribute [index_collection $sig $j] full_name]
	set pin_ij_setup [expr -1.0*$maxskew]
	puts "set_data_check -from $pin_i_name -to $pin_j_name -setup $pin_ij_setup"
	set_data_check -from $pin_i_name -to $pin_j_name -setup $pin_ij_setup
      }
    }

    #NOTE: Uncomment the following lines to enable reporting timing of setup
    #	   User should check all data_check endpoints' setup slacks to make sure that the skew between bits is within the range
    #for { set i 0 } { $i < $numbits } { incr i } {
    #  set pin_i_name [get_attribute [index_collection $sig $i] full_name]
    #  report_timing -delay_type max -to $pin_i_name
    #}

  }
}

# Note: no additional checks in PT for non safety config

