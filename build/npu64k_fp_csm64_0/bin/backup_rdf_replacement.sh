#!/usr/bin/env bash

set -e

NCONFIG="$1"
ARC_RDF_PRJ="$2"
CLN_RDF_PRJ="$3"
AM_VM_RAM_MACROS="$4"
VPX_RDF_PRJ="$5"
RLS="$6"

CP="rsync -avR"

echo "INFO: CMD: $0 "
echo "INFO: NCONFIG=$1 ARC_RDF_PRJ=$2 CLN_RDF_PRJ=$3 AM_VM_RAM_MACROS=$4 VPX_RDF_PRJ=$5 RLS=$6"

if [[ -z "$RLS" || ! -d $RLS ]] ; then
    echo "Error missing RLS argument #4 : $RLS"
    exit 1
fi

if [[ -z "$ARC_RDF_PRJ" || ! -d "$ARC_RDF_PRJ" ]] ; then
    echo "Error ARC_RDF_PRJ not found : $ARC_RDF_PRJ"
    exit 1
fi

#if [[ -z "$CLN_RDF_PRJ" || ! -d "$CLN_RDF_PRJ" ]] ; then
#    echo "Error CLN_RDF_PRJ not found : $CLN_RDF_PRJ"
#    exit 1
#fi

## cleanup: let Makefile do it
#[[ -d ${RLS}/syn/rdf_replacement ]] && rm -rf ${RLS}/syn/rdf_replacement

#######################
# 1. copy arc rdf files
S=${ARC_RDF_PRJ}/build
D=${RLS}/syn/rdf_replacement/npu_arc

# 1.1 all *.old files
echo "INFO: Backup (npu_arc) replaced files from ${S} to ${D} ..."
for old in $(find $S/verilog/RTL -name '*.old')
do
    bn=$(basename $old .old)
    bn=$(basename $bn .v)
    bd=$(dirname  $bn)
    bd=${bd#$S/verilog/RTL}
    fname="${bn}.v"
    [[ ! -d $D/verilog/RTL/$bd ]] && mkdir -p $D/verilog/RTL/$bd
    cp -f $S/verilog/RTL/$fname $D/verilog/RTL/$fname
    echo "cp -f $S/verilog/RTL/$fname $D/verilog/RTL/$fname"
done

for f in $(find $S/verilog -name 'mem*wrapper*')
do
    bn=$(basename $f .v)
    bd=$(dirname  $bn)
    bd=${bd#$S/verilog}
    fname="${bn}.v"
    [[ ! -d $D/verilog/$bd ]] && mkdir -p $D/verilog/$bd
    cp -fL $S/verilog/$fname $D/verilog/$fname
    echo "cp -fL $S/verilog/$fname $D/verilog/$fname"
    #fn=${fname/_wrapper./.}
    #[[ -f $S/verilog/$fn ]] && cp -fL $S/verilog/$fn $D/verilog/$fn
done

for ramdef in $(find $S/verilog/RTL -name '*ramdef*' -o -name '*port_mappings.v')
do
    bd=$(dirname $ramdef)
    bd=${bd#$S/verilog/RTL}
    [[ ! -d $D/verilog/RTL/$bd ]] && mkdir -p $D/verilog/RTL/$bd
    cp -f $ramdef $D/verilog/RTL/
    echo "cp -f $ramdef $D/verilog/RTL/"
done

#- manifest
find `readlink -f $D/verilog` -name 'mem_*' -o -name '*port_mappings.v' > $D/compile_manifest

###########################
# 2. copy npu_cln_rdf files
if [[ -d "$CLN_RDF_PRJ" ]] ; then
    echo "Info: CLN_RDF_PRJ=$CLN_RDF_PRJ is found, backup"
    S=${CLN_RDF_PRJ}/nl2_
    D=${RLS}/syn/rdf_replacement/npu_cln
    #[[ -d ${D} ]] && rm -rf ${D}
    #mkdir -p ${D}/verilog/RTL

    for f in $(cat ${CLN_RDF_PRJ}/replace_rdf_manifest)
    do
        bn=$(basename $f .v)
        bd=$(dirname  $f)
        bd=${bd#$S/verilog}
        fname="${bn}.v"
        [[ ! -d $D/verilog/$bd ]] && mkdir -p $D/verilog/$bd
        cp -fL $S/verilog/$bd/$fname $D/verilog/$bd/$fname
        echo "cp -fL $S/verilog/$bd/$fname $D/verilog/$bd/$fname"
        #fn=${fname/_wrapper./.}
        #[[ -f $S/verilog/$fn ]] && cp -fL $S/verilog/$fn $D/verilog/$fn
    done

    ## 2.1 all *.old files
    #echo "INFO: Backup(npu_cln) replaced files from ${S} to ${D} ..."
    #for old in $(find $S/verilog/RTL -name '*.old')
    #do
    #    bn=$(basename $old .old)
    #    bn=$(basename $bn .v)
    #    fname="${bn}.v"
    #    bd=$(dirname  $bn)
    #    bd=${bd#$S/verilog/RTL}
    #    [[ ! -d $D/verilog/RTL/$bd ]] && mkdir -p $D/verilog/RTL/$bd
    #    cp -f $S/verilog/RTL/$fname $D/verilog/RTL/$fname
    #    echo "cp -f $S/verilog/RTL/$fname $D/verilog/RTL/$fname"
    #    cp -f $S/verilog/RTL/$fname $D/verilog/RTL/$fname
    #done
    #
    #for f in $(find $S/verilog -name 'mem*wrapper*')
    #do
    #    bn=$(basename $f .v)
    #    bd=$(dirname  $f)
    #    bd=${bd#$S/verilog}
    #    fname="${bn}.v"
    #    [[ ! -d $D/verilog/$bd ]] && mkdir -p $D/verilog/$bd
    #    cp -fL $S/verilog/$bd/$fname $D/verilog/$bd/$fname
    #    echo "cp -fL $S/verilog/$bd/$fname $D/verilog/$bd/$fname"
    #    #fn=${fname/_wrapper./.}
    #    #[[ -f $S/verilog/$fn ]] && cp -fL $S/verilog/$fn $D/verilog/$fn
    #done
    #
    #for ramdef in $(find $S/verilog/RTL -name '*ramdef*' -o -name '*port_mappings.v')
    #do
    #    bd=$(dirname $ramdef)
    #    bd=${bd#$S/verilog/RTL}
    #    [[ ! -d $D/verilog/RTL/$bd ]] && mkdir -p $D/verilog/RTL/$bd
    #    echo "cp -f $ramdef $D/verilog/RTL/"
    #    cp -f $ramdef $D/verilog/RTL/
    #done

    #FIXME: Why do we need the missing files here?
    ## 2.2 all other files exist in ${CLN_RDF_PRJ}/nl2_/verilog/RTL while not exist in ${RLS}/build/verilog/npu_cln/nl2_/verilog/RTL/
    #echo "INFO: Backup missing files from ${S} to ${D} ..."
    #for f in $(find ${S}/verilog/RTL -type f ! -name "*.old")
    #do
    #    #echo "f: $f"
    #    fname=${f#${S}/verilog/RTL/}
    #    bd=$(dirname $fname)
    #    [[ ! -d $D/verilog/RTL/${bd} ]] && mkdir -p ${bd}
    #    if [[ ! -f ${RLS}/build/verilog/npu_cln/nl2_/verilog/RTL/$fname ]] && [[ ! -f $D/verilog/RTL/$fname  ]]; then
    #        echo "$CP ${S}/verilog/RTL/./$fname $D/verilog/RTL/$fname"
    #        $CP ${S}/verilog/RTL/./$fname $D/verilog/RTL/$fname
    #        #echo "cp -f $f $D/verilog/RTL/$fname"
    #        #cp -f $f $D/verilog/RTL/$fname
    #    fi
    #done

    # 2.3 Instead of copying nl2_defines.v and nl2_exported_defines.v to rdf_replacement/npu_cln, remove the redudant `include statement in nl2_scm_dbank_sram.v
    find $D -name "*_scm_dbank_sram.v" | xargs -I{} sed -i 's#^`include[[:blank:]]\+"nl2_defines.v"#//`include "nl2_defines.v"#' {}
    [[ -f $D/verilog/RTL/nl2_defines.v ]] && rm -f $D/verilog/RTL/nl2_defines.v
    [[ -f $D/verilog/RTL/nl2_exported_defines.v ]] && rm -f $D/verilog/RTL/nl2_exported_defines.v

    #- manifest
    find `readlink -f $D/verilog` -name 'mem_*' -o -name '*port_mappings.v' > $D/compile_manifest
fi

################################
# 3. Copy NPU specific files 

# 3.1 Copy the AM VM wrapper file
if [[ -n "$AM_VM_RAM_MACROS" && -d $AM_VM_RAM_MACROS ]] ; then
    S=${AM_VM_RAM_MACROS}/rtl
    D=${RLS}/syn/rdf_replacement/npu_amvm
    mkdir -p $D/verilog/RTL
    for f in $(find $S -name 'mem_*wrapper*')
    do
        cp -vf $f $D/verilog/RTL
    done
fi
find `readlink -f $D/verilog` -name 'mem_*' > $D/compile_manifest

# 3.2 Copy the BCM99 wrappers with cell replacement
S=$NPU_HOME/arch/shared/RTL/DWbb/rdf
D=${RLS}/syn/rdf_replacement/npu_amvm
mkdir -p $D/verilog/RTL
cp -vf ${S}/*v $D/verilog/RTL


######################
# 4. copy VPX RDF files
if [[ -d ${NPU_HOME_RLS}/npu_deps/vpx ]]; then
S=${VPX_RDF_PRJ}/build
D=${RLS}/syn/rdf_replacement/vpx

# 4.1 all *.old files
echo "INFO: Backup replaced files from ${S} to ${D} ..."
for old in $(find $S/verilog/RTL -name '*.old')
do
    bn=$(basename $old .old)
    bn=$(basename $bn .v)
    bd=$(dirname  $bn)
    bd=${bd#$S/verilog/RTL}
    fname="${bn}.v"
    [[ ! -d $D/verilog/RTL/$bd ]] && mkdir -p $D/verilog/RTL/$bd
    cp -f $S/verilog/RTL/$fname $D/verilog/RTL/$fname
    echo "cp -f $S/verilog/RTL/$fname $D/verilog/RTL/$fname"
done

for f in $(find $S/verilog -name 'mem*wrapper*')
do
    bn=$(basename $f .v)
    bd=$(dirname  $bn)
    bd=${bd#$S/verilog}
    fname="${bn}.v"
    [[ ! -d $D/verilog/$bd ]] && mkdir -p $D/verilog/$bd
    cp -fL $S/verilog/$fname $D/verilog/$fname
    echo "cp -fL $S/verilog/$fname $D/verilog/$fname"
    #fn=${fname/_wrapper./.}
    #[[ -f $S/verilog/$fn ]] && cp -fL $S/verilog/$fn $D/verilog/$fn
done

for ramdef in $(find $S/verilog/RTL -name '*ramdef*' -o -name '*port_mappings.v')
do
    bd=$(dirname $ramdef)
    bd=${bd#$S/verilog/RTL}
    [[ ! -d $D/verilog/RTL/$bd ]] && mkdir -p $D/verilog/RTL/$bd
    cp -f $ramdef $D/verilog/RTL/
    echo "cp -f $ramdef $D/verilog/RTL/"
done

#- manifest
find `readlink -f $D/verilog` -name 'mem_*' -o -name '*port_mappings.v' > $D/compile_manifest

fi # VPX...

