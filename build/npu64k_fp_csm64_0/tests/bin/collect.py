#!/usr/bin/env python
import sys
import os
import argparse
import glob
import re
nn_ref_path = os.environ["NPU_HOME"] + "/verif/common/npi/pref/Pylib/Ext"
sys.path.append(os.path.abspath(nn_ref_path))
import yaml
import csv
import pandas as pd

head_list = ["conv_mode","ni","no","oh","xc","fkr","fkc","pad","zp","coef_mode","useacc","pixbits","cfbits","cycle","test_path"]
key_list = []
row = ["conv_mode","ni","no","oh","xc","fkr","fkc","pad","zp","coef_mode","useacc","pixbits","cfbits","cycle","test_path"]

class check_result:
    def __init__(self,name="result",path="./"):
        self.name = name
        self.path = path
        self.test_list = glob.glob(self.path+'/type*')

    def update_list(self):
        for test in self.test_list:
            print(test)
            row = ["conv_mode","ni","no","oh","xc","fkr","fkc","pad","zp","coef_mode","useacc","pixbits","cfbits","cycle","test_path"]
            row[14] = test
            with open(test+"/simv.log") as status:
                for line in status.readlines():
                    if 'CONV CYCLE' in line:
                        a = line.split()
                        print(a[-1])
                row[13] = a[-1]
            self.yaml = yaml.load((open(test+"/test.yaml","r")),Loader=yaml.FullLoader)
            self.nodes = self.yaml["nodes"]
            for k,v in self.nodes.items():
                v["name"] = k
                ntype = v["ntype"]
                if ntype == "t_conv":
                    row[0] = v["name"]
                elif ntype == "t_fmap":
                    ipt = v["ipt"]
                    ipb = v["ipb"]
                    ipr = v["ipr"]
                    ipl = v["ipl"]
                    ih = v["ih"]
                    iw = v["iw"]
                elif ntype == "t_cba":
                    row[1] = v["fkid"]
                    row[2] = v["fkod"]
                    row[5] = v["fkr"]
                    row[6] = v["fkc"]
                    row[8] = v["zp"]
                    fkr = v["fkr"]
                    fkc = v["fkc"]
                    kr = v["kr"]
                    kc = v["kc"]
                    dl_c = v["dilation_c"]
                    dl_r = v["dilation_r"]
                    sr_c = v["stride_c"]
                    sr_r = v["stride_r"]
                    if(v["sparse"]==1):
                        row[9] = "coef_mode_fm"
                    else:
                        if(v["fccf"]==1):
                            row[9] = "coef_mode_compressed"
                        else:
                            row[9] = "coef_mode_uncompressed"
                    row[11] = v["pixbits"]
                    row[12] = v["fcbits"]
                elif ntype == "t_acc":
                    row[10] = v["useAcc"]
            if((ipl+ipr+ipb+ipt)> 0):
                row[7] = "1"
            else:
                row[7] = "0"
            row[3] = int((ih+ipt+ipb+sr_r-((fkr*kr-1)*dl_r+1)+sr_r-1)/sr_r)
            row[4] = int((iw+ipl+ipr+sr_c-((fkc*kc-1)*dl_c+1)+8*sr_c-1)/(8*sr_c))
            if 'fc' in row[0]:
                fc = 1
            else:
                fc = 0
            key_list.append(row)





            
    def create_new_csv(self):
        with open("./"+self.name+".vcs","w",newline='') as f:
            csv_write = csv.writer(f)
            csv_write.writerow(head_list)
            csv_write.writerows(key_list)


    #def load(self):




def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("-p","--path", type=str,required=True,
        help="path of test folder")
    parser.add_argument("-n","--name", type=str,required=True,
        help="test result excel name")
    args = parser.parse_args()
    return args

if __name__ == "__main__":
    opt = parse_args()
    check = check_result(name=opt.name,path=opt.path)
    check.update_list()
    check.create_new_csv()
    

