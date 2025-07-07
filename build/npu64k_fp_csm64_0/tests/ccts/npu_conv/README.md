```
This testcase is testing conv1x1i32o16, inputs/output sizes are shown below
          feature map   : 31 * 3 * 64 (Width * Height * Depth(NI)) 
          filter size   :  1 * 1 *  1 
          stride size   :  2 * 2 *  1 
          dilation size :  2 * 2 *  1
          output size   : 16 * 2 * 32 ((1+(W-F)/S) * (1+(H-F)/S) * NO)   

The values of feature-map are defined in feature-map/viImg.thex. It looks like: 
Depth  0 |    0    1    2    3    4    5   ----> Width 
    -----+----+----+----+----+----+----+-
       0 | 0001 0002 0003 0004 0005 0006 
       1 | 0020 0021 0022 0023 0024 0025 
Height 2 | 003f 0040 0041 0042 0043 0044 


Depth  1 |    0    1    2    3    4    5
    -----+----+----+----+----+----+----+-
       0 | 005e 005f 0060 0061 0062 0063 
       1 | 007d 007e 007f 0080 0081 0082 
Height 2 | 009c 009d 009e 009f 00a0 00a1

 
Weight size is determinated by filter * input depth * output depth , i.e. 1 * 64 * 32. The folder weight includes 32 files named vCBA_*.thex ,  here * represents output depth

Output size is : 16 * 2 * 32 acc_t (Width x Height x Depth) , so the output will be 8 vyixacc_t
	acc[0~15][0][0~7] (Depth,Height,Width) will be in 1st vyixacc_t
	acc[0~15][1][0~7]                      will be in 2nd vyixacc_t
	acc[0~15][0][8~15]                     will be in 3rd vyixacc_t
	acc[0~15][1][8~15]                     will be in 4th vyixacc_t
	acc[16~31][0][0~7]                     will be in 5th vyixacc_t
	acc[16~31][1][0~7]                     will be in 6th vyixacc_t
	acc[16~31][0][8~15]                    will be in 7th vyixacc_t
	acc[16~31][1][8~15]                    will be in 8th vyixacc_t

```
