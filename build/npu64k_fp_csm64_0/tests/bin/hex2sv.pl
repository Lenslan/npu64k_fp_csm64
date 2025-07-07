#!/usr/bin/perl -W
use strict;
use Getopt::Long;
my $record_addr=0xf; #64Byte aligned, should be aligned with cache line size

#  - Splits the following type of lines as shown below:
#         000007BC-000007BF / 2F200300 ;
#                      |
#                      V
#             000007BC / 2F200300 ;
#             000007BD / 2F200300 ;
#             000007BE / 2F200300 ;
#             000007BF / 2F200300 ;
#

sub align_to_cache_line_size() {
    my ($pre, $cur) = @_;
    my $fw_off = 0x0;
    my $lw_off = 0xf;

    if(($pre&0xf) != $lw_off ) { #previous one is not the last word in cache line
        #printf "pres %08x, cur %08x, pre_and_f: %08x, cur_and_f: %08x, fw_off: %08x\n", $pre, $cur, $pre&0xf, $cur&0xf, $fw_off;
      if(($cur&0xfffffffff0) != ($pre&0xfffffffff0)){  # not in same cache line
        for(my $i=$pre+1;$i<=($pre|0xf);$i=$i+1){
            printf FH2 "@%08X %08X\n", 4*$i, 0;
            #die;
        }
        if(($cur&0xf) != $fw_off){ # current one is not in the first word
          for(my $i=($cur&0xfffffffff0);$i<$cur;$i=$i+1){
              printf FH2 "@%08X %08X\n", 4*$i, 0;
              #die;
          }
        }
      }else{ #in same cache line
        #fullfill the words not covered in previous one
        for(my $i=$pre+1;$i<$cur;$i=$i+1){
          printf FH2 "@%08X %08X\n", 4*$i, 0;
          #die;
        }
      }
    }else{  #last word in cache line
      if(($cur&0xf) != $fw_off){ # next should be the start of cache line
        for(my $i=($cur&0xfffffffff0);$i<$cur;$i=$i+1){
            printf FH2 "@%08X %08X\n", 4*$i, 0;
            #die;
        }
      } 
    }
}


sub decode_lines {
    my $line = shift;
    #print $line;

    if($line =~ /(.*)-(.*)\s\/\s?(.*)\s;/)
    {
      #print ">$1< >$2< >$3<\n";
      my $from = hex $1;
      my $to = hex $2;
      my $data = $3;
      
      &align_to_cache_line_size($record_addr, $from);

      for(my $i=$from; $i<=$to; $i=$i+1)
      {
        printf FH2 "@%08X %08X\n", 4*$i, hex byte_reorder($data);
      }
      $record_addr = $to;
    }
    elsif($line =~ /(.*)\s\/\s?(.*)\s;/) {
        my $addr = hex $1;
        my $data = $2;
        &align_to_cache_line_size($record_addr, $addr);
        printf FH2 "@%08X %08X\n", 4*$addr, hex byte_reorder($data) ;
        $record_addr = $addr;
    }
    else{
        die "$line \nis not supported";
    }
}

sub byte_reorder {
    my $data = shift;

    if($data =~ /([0-9a-f]{2})([0-9a-f]{2})([0-9a-f]{2})([0-9a-f]{2})/i ){ #8 digtal
        return $4.$3.$2.$1;
    }else {
        die "$data is not supported, please pass 8 hex digital numbers";
    }
    
}


open(FH1, $ARGV[0]) || die("Cannot open");
open(FH2, ">$ARGV[0]_temp") || die("Cannot open");

while(<FH1>)
{
    decode_lines($_);
}
&align_to_cache_line_size($record_addr, 0);
close(FH1);
close(FH2);
system("rm -rf $ARGV[0]");
system("mv $ARGV[0]_temp $ARGV[0]");


sub printusage {

print<<USAGE_TEXT;

Convert a hex file into a hexfile that can be consumed by the RTE BFMs

hexfileconvert [-h] <-le|-be> <-infile <filename>.hex> [-outfile <filename>]

  -h|help   : prints this help message
  -le       : interpret hex file as a little endian hex file
  -be       : interpret hex file as a big endian hex file 
  -infile   : name of input .hex file
  -outfile  : name of  output converted hex file. Optional, the default output file name is <filename>.rhex
  -uve      : interpret the hexfile as using the UVE format

USAGE_TEXT

}


