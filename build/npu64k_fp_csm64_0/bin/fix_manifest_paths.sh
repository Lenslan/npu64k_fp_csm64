#/usr/bin/env bash

# NOTE: run this script after the NPU_HOME/NPU_DEPS are set
NCONFIG=$1
npu_home_dev=`grep -w '^NPU_HOME' ${NPU_HOME_RLS}/bin/.npu_dev_paths | awk -F= '{print $2}'`
npu_deps_dev=`grep -w '^NPU_DEPS' ${NPU_HOME_RLS}/bin/.npu_dev_paths | awk -F= '{print $2}'`
npu_home_rls=${NPU_HOME_RLS}
npu_deps_rls=${NPU_DEPS_RLS}
echo "npu_home_dev: ${npu_home_dev}"
echo "npu_deps_dev: ${npu_deps_dev}"
echo "npu_home_rls: ${npu_home_rls}"
echo "npu_deps_rls: ${npu_deps_rls}"
echo "NCONFIG     : ${NCONFIG}"

if [[ $npu_home_dev =~ ^${npu_home_rls}.* ]] ; then
    echo "WARNING: npu_home_rls is within npu_home_dev, some replacement might not work !"
fi

echo "find ${npu_home_rls}/manifest/ -name '*manifest*' -type f | xargs -I{} sed -i  -e "s#${npu_deps_dev}#${npu_deps_rls}#g" -e "s#${npu_home_dev}#${npu_home_rls}#g" {}"
find ${npu_home_rls}/manifest/ -name '*manifest*' -type f | xargs -I{} sed -i  -e "s#${npu_deps_dev}#${npu_deps_rls}#g" -e "s#${npu_home_dev}#${npu_home_rls}#g" {}

## fix synthesize manifest paths
#synth_mf=$(find ${npu_home_rls} -name "*_syn_*manifest*" | grep -v -E '\.sh$|\.old$')
#for mf in $synth_mf
#do
#    sed -r \
#        -e "s#${npu_home_dev}/iplib/packing/release/syn/rdf_replacement/npu_arc/verilog/#${npu_deps_rls}/npu_arc/project_npu_arc_base/build/verilog/#g" \
#        -e "s#${npu_home_dev}/iplib/packing/release/syn/rdf_replacement/npu_cln/verilog/#${npu_home_rls}/build/src/npu_core/ncln/nl2_/verilog/#g" \
#        -e "s#${npu_home_dev}/iplib/packing/release/#${npu_home_rls}/#g" \
#        ${mf} > ${mf}.new
#    if cmp -s ${mf} ${mf}.new ; then
#        #echo "$mf  :: No change"
#        rm -f ${mf}.new
#    else
#        echo "$mf  :: Edited"
#        mv -n ${mf} ${mf}.old
#        mv -f ${mf}.new ${mf}
#    fi
#done
#
#echo ""
#
## fix simulation manifest paths
#simul_mf=$(find ${npu_home_rls} -name "*_*manifest*" | grep -v -E '\.sh$|\.tcl$|\.v$|\.old$')
#for mf in $simul_mf
#do
#    sed -r \
#        -e "s#${npu_deps_dev}/#${npu_deps_rls}/#g" \
#        -e "s#${npu_home_dev}/#${npu_home_rls}/#g" \
#        ${mf} > ${mf}.new
#    if cmp -s ${mf} ${mf}.new ; then
#        #echo "$mf  :: No change"
#        rm -f ${mf}.new
#    else
#        echo "$mf  :: Edited"
#        mv -n ${mf} ${mf}.old
#        mv -f ${mf}.new ${mf}
#    fi
#done

#####################
exit 0
#####################

# fix synthesize manifest paths
#find ${npu_home_rls} -name "*_syn_*manifest*" | xargs -I{} sed -i "s#${npu_home_dev}/iplib/packing/release/syn/rdf_replacement/npu_arc/verilog/#${npu_deps_rls}/npu_arc/project_npu_arc_base/build/verilog/#g" {}
#find ${npu_home_rls} -name "*_syn_*manifest*" | xargs -I{} sed -i "s#${npu_home_dev}/iplib/packing/release/syn/rdf_replacement/npu_cln/verilog/#${npu_home_rls}/build/src/npu_core/ncln/nl2_/verilog/#g" {}
#find ${npu_home_rls} -name "*_syn_*manifest*" | xargs -I{} sed -i "s#${npu_home_dev}/iplib/packing/release/#${npu_home_rls}/#g" {}

# fix simulation manifest paths
#find ${npu_home_rls} -name "*_*manifest*" | xargs -I{} sed -i "s#${npu_home_dev}/#${npu_home_rls}/#g" {}
#find ${npu_home_rls} -name "*_*manifest*" | xargs -I{} sed -i "s#${npu_deps_dev}/#${npu_deps_rls}/#g" {}

