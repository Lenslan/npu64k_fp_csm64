#!/usr/bin/env bash

set -e

flist=$1
ilist=${flist}.search_paths

search_paths=`cat ${flist}.search_paths | sed '/^\s*$/d' | sed '/^\s*#/d' | xargs`
files=`cat ${flist} | sed '/^\s*$/d' | sed '/^\s*#/d' | xargs`

echo "Copy search_paths......"
for s in ${search_paths}
do
  d="${s%/*}"
  b="${s##*/}"
  newd="${d/${NPU_DEPS}/${NPU_DEPS_RLS}}"
  newd="${newd/${NPU_HOME}/${NPU_HOME_RLS}}"
  #echo "s:$s d:$d b:$b newd:$newd"
  [[ ! -d $newd ]]  && mkdir -p $newd
  #FIXME: duplicated delete and copy of nested search paths, optimizations are pending
  [[ -d $newd/$b ]] && rm -rf $newd/$b
  echo "cp -rf $d/$b $newd/$b" && cp -rf $d/$b $newd/$b
  #[[ -d $newd/$b ]] && rm -rf $newd/$b && cp -rfv $d/$b $newd/$b
done

echo -e "\nCopy files......"
for f in $files
do
  d="${f%/*}"
  b="${f##*/}"
  newd="${d/${NPU_DEPS}/${NPU_DEPS_RLS}}"
  newd="${newd/${NPU_HOME}/${NPU_HOME_RLS}}"
  #echo "f:$f d:$d b:$b newd:$newd"
  [[ ! -d $newd ]]    && mkdir -p $newd
  [[ ! -d $newd/$b ]] && cp -rfv $d/$b $newd/$b
done

# copy manifest
mkdir -p ${NPU_HOME_RLS}/manifest
src_manif="${flist##*/}"
src_manif_dir="${flist%/*}"
cp -f ${src_manif_dir}/{rtl_${src_manif},rtl_${src_manif}.search_paths,${src_manif},${src_manif}.search_paths} ${NPU_HOME_RLS}/manifest
sed -i 's#${NPU_DEPS}#${NPU_DEPS_RLS}#g' ${NPU_HOME_RLS}/manifest/{rtl_${src_manif},rtl_${src_manif}.search_paths,${src_manif},${src_manif}.search_paths}
sed -i 's#${NPU_HOME}#${NPU_HOME_RLS}#g' ${NPU_HOME_RLS}/manifest/{rtl_${src_manif},rtl_${src_manif}.search_paths,${src_manif},${src_manif}.search_paths}

exit 0

