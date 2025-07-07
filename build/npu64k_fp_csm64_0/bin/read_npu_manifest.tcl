
# Global variable NPU_HOME must be defined before calling these procedures.
# For example, by taking its value from the environment.
#    set NPU_HOME $::env(NPU_HOME)
#    set NPU_DEPS $::env(NPU_DEPS)

# Read a manifest file
#   - Dereference environment vartiables (subst)
#   - Recurse if some lines in the file point to another file with '-f'
#   - Optionally check if each file is valid
proc read_npu_manif {fname {strict 0}} {
    # Variables to use for substitution, if they are encountered in the manifest file
    variable NPU_HOME_RLS
    variable NPU_DEPS_RLS
    #variable NPU_HOME
    #variable NPU_DEPS
    ##variable ARC_PRJ_DIR
    variable EMBEDIT_SRAM
    if {$strict != 0} {
        puts "read_npu_manif(strict): $fname"
    } else {
    puts "read_npu_manif: $fname"
    }
    # Read the entire file into a list (one entry per line) while trying
    # to substitute $VAR strings encountered for their value
    set fp [open $fname r]
    set content [split [subst -nocommands -nobackslashes [read $fp]] "\n"]
    close $fp
    # Parse the lines one by one, appending all RTL file encountered in a list
    set rtl {}
    foreach line $content {
        # Trimmed line
        set tl [string trimright [string trimleft $line]]
        # Skip empty lines and comments (starting with either '#' or  '//')
        if {[regexp {^#|^//|^\s*$} $tl]} {
            #puts "    <SKIP> $tl"
        # Additonnal file to read with the '-f' directive
        } elseif {[regexp {^-f\s+(.*$)} $tl match extra_file]} {
            puts "    <READ> -f $extra_file'"
            if {[file exists $extra_file]} {
                # Recurse
                lappend rtl {*}[read_npu_manif $extra_file $strict]
            } else {
                puts "    < ERR> $tl"
                if {$strict != 0} {
                    puts stderr "Error: Extra file not found '$line;"
                    exit 1
                }
            }
        # Include directory with -incdir or +incdir+
        } elseif {[regexp {^[-+]incdir[+\s](.*$)} $tl match inc]} {
            puts "    <INCL> -incdir $inc"
        # Plain filename, potential source RTL file
        } elseif {[file exists $tl]} {
            #puts "    < ADD> $tl"
            # Make the path absolute
            lappend rtl [file join [pwd] $tl]
        # No match - ignore
        } else {
            puts "    <WARN> $tl"
            if {$strict != 0} {
                puts stderr "Error: manifest line not pointing to a file or with an unknown command"
                puts stderr "  --> '$line'"
                exit 1
            }
        }
    }
    return $rtl
}

# Write back a flat manifest file. If the file path contains string equal to variables
# such as NPU_HOME_RLS, put back ${NPU_HOME_RLS} in the path
proc write_npu_manifest {fname manif {strict 0}} {
    variable NPU_HOME_RLS
    puts "write_npu_manifest: $fname"
    set fp [open $fname w+]
    foreach src $manif {
        if {$strict != 0} {
            puts stderr "Error while writing $fname : file not found '$src'"
            close $fp
            exit 1
        }


        if {[file exists $src]} {
            set npu_src [string map "${NPU_HOME_RLS} \$\{NPU_HOME_RLS\}" $src]
            puts $fp "$npu_src"
        } else {
            if {$strict != 0} {
                puts stderr "Error while writing $fname : file not found '$src'"
                close $fp
                exit 1
            }
        }
    }
    close $fp
}

