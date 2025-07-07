#!/usr/bin/env bash

set -e

NCONFIG="$1"
#NPU_HOME_DEV="$2"
#NPU_DEPS_DEV="$3"
BUILD=${NPU_HOME_RLS}

verb=""

# 1.1 copy npu_arc rdf files
S=${NPU_HOME_RLS}/syn/rdf_replacement/npu_arc/verilog
D=${BUILD}/verilog
echo "INFO: Copy npu_arc files for synthesis from ${S} into ${D}..."
for f in $(find $S -type f | grep -v "compile_manifest")
do
  bn=${f#$S/}
  bd=$(dirname $bn)
  [[ -d $D/$bd ]] && mkdir -p $D/$bd
  [[ ! -f $D/${bn}.old ]] && [[ -f $D/$bn ]] && cp $verb -f $D/$bn $D/${bn}.old
  #echo "  cp -vf $S/$bn $D/$bn"
  ln $verb -sf $S/$bn $D/$bn
done

if [[ -d ${NPU_HOME_RLS}/syn/rdf_replacement/npu_cln/verilog ]]; then
  # 1.2 copy npu_cln rdf files
  S=${NPU_HOME_RLS}/syn/rdf_replacement/npu_cln/verilog
  D=${BUILD}/verilog
  echo "INFO: Copy npu_cln files for synthesis from ${S} into ${D}..."
  for f in $(find $S -type f | grep -v "compile_manifest")
  do
    bn=${f#$S/}
    bd=$(dirname $bn)
    [[ -d $D/$bd ]] && mkdir -p $D/$bd
    [[ ! -f $D/${bn}.old ]] && [[ -f $D/$bn ]] && cp $verb -f $D/$bn $D/${bn}.old
    #echo "  cp -vf $S/$bn $D/$bn"
    ln $verb -sf $S/$bn $D/$bn
  done
fi

if [[ -d ${NPU_HOME_RLS}/syn/rdf_replacement/npu_amvm ]] ; then
  echo "INFO: Copy NPU AM/VM/BCM files for synthesis from ${S} into ${D}..."
  S=${NPU_HOME_RLS}/syn/rdf_replacement/npu_amvm/verilog
  D=${BUILD}/verilog
  for f in $(find $S -type f -name 'mem_*') $(find $S -type f -name '*bcm*v')
  do
    bn=${f#$S/}
    bd=$(dirname $bn)
    [[ ! -f $D/${bn}.old ]] && [[ -f $D/$bn ]] && cp $verb -f $D/$bn $D/${bn}.old
    ln $verb -sf $S/${bn} $D/${bn}
  done
fi

if [[ -d ${NPU_HOME_RLS}/syn/rdf_replacement/vpx ]]; then
  # 1.3 copy vpx rdf files
  S=${NPU_HOME_RLS}/syn/rdf_replacement/vpx/verilog
  D=${BUILD}/vpx/nu4500/project/build/verilog

  echo "INFO: Copy VPX files for synthesis from ${S} into ${D}..."
  for f in $(find $S -type f | grep -v "compile_manifest")
  do
    bn=${f#$S/}
    bd=$(dirname $bn)
    [[ -d $D/$bd ]] && mkdir -p $D/$bd
    [[ ! -f $D/${bn}.old ]] && [[ -f $D/$bn ]] && cp $verb -f $D/$bn $D/${bn}.old
    #echo "  cp -vf $S/$bn $D/$bn"
    ln $verb -sf $S/$bn $D/$bn
  done
fi

# FIXME: patch rtl files, these should be removed later
if [ -e ${NPU_HOME_RLS}/verilog/RTL/npuarc_hsls_defines.v ] ; then
  sed -i 's#\(.*npuarc_SAFETY_AINP_SYNC_STAGES\)#//\1#g' ${NPU_HOME_RLS}/verilog/RTL/npuarc_hsls_defines.v                || true
  sed -i 's#\(.*npuarc_SAFETY_AINP_SYNC_STAGES\)#//\1#g' ${NPU_HOME_RLS}/verilog/RTL/npuarc_hsls_exported_defines.v       || true
fi
sed -i 's#\(.*Mem_npu_vec_bank\)#//\1#g'               ${NPU_HOME_RLS}/verilog/RTL/{npu_defines.v,npu_exported_defines.v} || true
sed -i 's#\(.*Mem_npu_acc_bank\)#//\1#g'               ${NPU_HOME_RLS}/verilog/RTL/{npu_defines.v,npu_exported_defines.v} || true
sed -i 's#\(.*NPU_REPLACE_CLKGATE\)#//\1#g'            ${NPU_HOME_RLS}/verilog/RTL/{npu_defines.v,npu_exported_defines.v} || true
sed -i 's#\(.*CellLibraryClockGate\)#//\1#g'           ${NPU_HOME_RLS}/verilog/RTL/{npu_defines.v,npu_exported_defines.v} || true
sed -i '1i \`include "npu_rdf_defines.sv"'             ${NPU_HOME_RLS}/verilog/RTL/{npu_defines.v,npu_exported_defines.v} || true
cp $verb -f ${NPU_HOME_RLS}/config/npu_rdf_defines.sv  ${NPU_HOME_RLS}/verilog/RTL/

ls -1 ${NPU_HOME_RLS}/verilog/RTL/npu_rdf_defines.sv    > ${NPU_HOME_RLS}/syn/manifest.rtl.flat.tmp
ls -1 ${NPU_HOME_RLS}/verilog/RTL/npu_defines.v        >> ${NPU_HOME_RLS}/syn/manifest.rtl.flat.tmp
cat ${NPU_HOME_RLS}/config/manifest.rtl.flat           >> ${NPU_HOME_RLS}/syn/manifest.rtl.flat.tmp
echo "" >> ${NPU_HOME_RLS}/syn/manifest.rtl.flat.tmp
cat ${NPU_HOME_RLS}/syn/rdf_replacement/npu_arc/compile_manifest >> ${NPU_HOME_RLS}/syn/manifest.rtl.flat.tmp
[[ -d ${NPU_HOME_RLS}/syn/rdf_replacement/npu_cln ]]  && cat ${NPU_HOME_RLS}/syn/rdf_replacement/npu_cln/compile_manifest  >> ${NPU_HOME_RLS}/syn/manifest.rtl.flat.tmp
[[ -d ${NPU_HOME_RLS}/syn/rdf_replacement/vpx ]]      && cat ${NPU_HOME_RLS}/syn/rdf_replacement/vpx/compile_manifest      >> ${NPU_HOME_RLS}/syn/manifest.rtl.flat.tmp
[[ -d ${NPU_HOME_RLS}/syn/rdf_replacement/npu_amvm ]] && cat ${NPU_HOME_RLS}/syn/rdf_replacement/npu_amvm/compile_manifest >> ${NPU_HOME_RLS}/syn/manifest.rtl.flat.tmp
sed -i "s#/.*/verilog/RTL/\(.*\)#\${NPU_HOME_RLS}/verilog/RTL/\1#g" ${NPU_HOME_RLS}/syn/manifest.rtl.flat.tmp
sed -i "s#/.*/NPX_Release/\(.*\)#\${NPU_HOME_RLS}/\1#g" ${NPU_HOME_RLS}/syn/manifest.rtl.flat.tmp
${NPU_HOME_RLS}/bin/uniq_manifest.py ${NPU_HOME_RLS}/syn/manifest.rtl.flat.tmp ${NPU_HOME_RLS}/syn/manifest.rtl.flat

#echo "sed -i 's#${NPU_DEPS}#${NPU_DEPS_RLS}#g' ${NPU_HOME_RLS}/manifest/{rtl_manifest.v.flat,rtl_manifest.v.flat.search_paths}"
#sed -i "s#${NPU_DEPS}#${NPU_DEPS_RLS}#g" ${NPU_HOME_RLS}/manifest/{rtl_manifest.v.flat,rtl_manifest.v.flat.search_paths}
#echo "sed -i 's#${NPU_HOME}#${NPU_HOME_RLS}#g' ${NPU_HOME_RLS}/manifest/{rtl_manifest.v.flat,rtl_manifest.v.flat.search_paths}"
#sed -i "s#${NPU_HOME}#${NPU_HOME_RLS}#g" ${NPU_HOME_RLS}/manifest/{rtl_manifest.v.flat,rtl_manifest.v.flat.search_paths}

