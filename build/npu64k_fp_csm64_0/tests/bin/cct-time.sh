#!/usr/bin/env bash
set -e 

total=`make -C ${NPU_HOME}/build list-ccts | grep "CCTS:" | awk -F: '{print $2}' | xargs echo -n  | wc -w`
done=`find -L ${NPU_HOME}/build/tests/ccts -name simv.log | xargs -I{} grep -H 'CPU Time' {} | wc -l`
find -L ${NPU_HOME}/build/tests/ccts -name simv.log | xargs -I{} grep -H 'CPU Time' {} | awk -F: '{print $1":"$3}' | sed 's/;.*//' | column -t | sort -n -k 2
echo "Total: $total Done: $done"

exit 0
