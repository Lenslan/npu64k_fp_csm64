#!/usr/bin/env bash
set -e

mdb -pset=1 -psetname=L20 -rascal outs/l2.elf -OK -run
mdb -multifiles=L20 -cl -OK -run

#mdb -pset=1 -psetname=L20 -rascal outs/l2.elf -OK -run
#mdb -multifiles=L20 -cl -OK -cmd mdb.cmd

ret=$?
if [ $ret -eq 0 ]; then
  touch .PASS
fi

exit $ret

