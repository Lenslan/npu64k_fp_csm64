#!/usr/bin/env python

import os
import sys

assert(len(sys.argv)>=3)
manifest=sys.argv[1]
output_manifest=sys.argv[2]
flist_txt=[]
with open(manifest, "r") as f:
    flist_txt = f.readlines()

flist = [l.strip() for l in flist_txt]
flist_len=len(flist)
fbaname_list=[os.path.basename(f) for  f in flist]

uniq_fbasenames = []
for i in range(flist_len):
    if fbaname_list[i] not in uniq_fbasenames:
        uniq_fbasenames.append(fbaname_list[i])
    else:
        flist[i] = "#%s" %(flist[i])

with open(output_manifest, "w") as f:
    for l in flist:
        if (len(l)>0) and (l[0]!='#'):
            f.write("%s\n" %(l))
        #else:
        #    print("Info: remove dumplicated source file %s" %(l))
        #    #f.write("\n" %(l))

