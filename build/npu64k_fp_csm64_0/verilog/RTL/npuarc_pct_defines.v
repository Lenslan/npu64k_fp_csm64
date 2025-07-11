`define npuarc_EVT_NEVER         7'd0  //  never     hex = 64'h00000072_6576656e
`define npuarc_EVT_ALWAYS        7'd1  //  always    hex = 64'h00007379_61776c61
`define npuarc_EVT_IALL          7'd2  //  iall      hex = 64'h00000000_6c6c6169
`define npuarc_EVT_ISLEEP        7'd3  //  isleep    hex = 64'h00007065_656c7369
`define npuarc_EVT_IJMP          7'd4  //  ijmp      hex = 64'h00000000_706d6a69
`define npuarc_EVT_IJMPC         7'd5  //  ijmpc     hex = 64'h00000063_706d6a69
`define npuarc_EVT_IJMPU         7'd6  //  ijmpu     hex = 64'h00000075_706d6a69
`define npuarc_EVT_IJMPD         7'd7  //  ijmpd     hex = 64'h00000064_706d6a69
`define npuarc_EVT_IJMPTAK       7'd8  //  ijmptak   hex = 64'h006b6174_706d6a69
`define npuarc_EVT_ICALL         7'd9  //  icall     hex = 64'h0000006c_6c616369
`define npuarc_EVT_ILR           7'd10  //  ilr       hex = 64'h00000000_00726c69
`define npuarc_EVT_ISR           7'd11  //  isr       hex = 64'h00000000_00727369
`define npuarc_EVT_ILP           7'd12  //  ilp       hex = 64'h00000000_00706c69
`define npuarc_EVT_ILPEND        7'd13  //  ilpend    hex = 64'h0000646e_65706c69
`define npuarc_EVT_ILPIN         7'd14  //  ilpin     hex = 64'h0000006e_69706c69
`define npuarc_EVT_I2BYTE        7'd15  //  i2byte    hex = 64'h00006574_79623269
`define npuarc_EVT_I4BYTE        7'd16  //  i4byte    hex = 64'h00006574_79623469
`define npuarc_EVT_I2LBYTE       7'd17  //  i2lbyte   hex = 64'h00657479_626c3269
`define npuarc_EVT_I4LBYTE       7'd18  //  i4lbyte   hex = 64'h00657479_626c3469
`define npuarc_EVT_IMEMRD        7'd19  //  imemrd    hex = 64'h00006472_6d656d69
`define npuarc_EVT_IMEMWR        7'd20  //  imemwr    hex = 64'h00007277_6d656d69
`define npuarc_EVT_IMEMRDC       7'd21  //  imemrdc   hex = 64'h00636472_6d656d69
`define npuarc_EVT_IMEMWRC       7'd22  //  imemwrc   hex = 64'h00637277_6d656d69
`define npuarc_EVT_ITRAP         7'd23  //  itrap     hex = 64'h00000070_61727469
`define npuarc_EVT_ISWI          7'd24  //  iswi      hex = 64'h00000000_69777369
`define npuarc_EVT_ILLOCK        7'd25  //  illock    hex = 64'h00006b63_6f6c6c69
`define npuarc_EVT_ISCOND        7'd26  //  iscond    hex = 64'h0000646e_6f637369
`define npuarc_EVT_IALLJMP       7'd27  //  ialljmp   hex = 64'h00706d6a_6c6c6169
`define npuarc_EVT_IVEC          7'd28  //  ivec      hex = 64'h00000000_63657669
`define npuarc_EVT_IVGATHER      7'd29  //  ivgather  hex = 64'h72656874_61677669
`define npuarc_EVT_IVSCATT       7'd30  //  ivscatt   hex = 64'h00747461_63737669
`define npuarc_EVT_VGATHBC       7'd31  //  vgathbc   hex = 64'h00636268_74616776
`define npuarc_EVT_VSCATBC       7'd32  //  vscatbc   hex = 64'h00636274_61637376
`define npuarc_EVT_VSTALL        7'd33  //  vstall    hex = 64'h00006c6c_61747376
`define npuarc_EVT_VBSLOT        7'd34  //  vbslot    hex = 64'h0000746f_6c736276
`define npuarc_EVT_BWPCFLT       7'd35  //  bwpcflt   hex = 64'h00746c66_63707762
`define npuarc_EVT_BSTALL        7'd36  //  bstall    hex = 64'h00006c6c_61747362
`define npuarc_EVT_BFLUSH        7'd37  //  bflush    hex = 64'h00006873_756c6662
`define npuarc_EVT_BDEBUG        7'd38  //  bdebug    hex = 64'h00006775_62656462
`define npuarc_EVT_BISSUE        7'd39  //  bissue    hex = 64'h00006575_73736962
`define npuarc_EVT_BESLOT        7'd40  //  beslot    hex = 64'h0000746f_6c736562
`define npuarc_EVT_BDSLOT        7'd41  //  bdslot    hex = 64'h0000746f_6c736462
`define npuarc_EVT_BFLGSTAL      7'd42  //  bflgstal  hex = 64'h6c617473_676c6662
`define npuarc_EVT_BERRBRCH      7'd43  //  berrbrch  hex = 64'h68637262_72726562
`define npuarc_EVT_BUOPSTAL      7'd44  //  buopstal  hex = 64'h6c617473_706f7562
`define npuarc_EVT_BRGBANK       7'd45  //  brgbank   hex = 64'h006b6e61_62677262
`define npuarc_EVT_BAGUSTL       7'd46  //  bagustl   hex = 64'h006c7473_75676162
`define npuarc_EVT_BACCSTAL      7'd47  //  baccstal  hex = 64'h6c617473_63636162
`define npuarc_EVT_BZOLCNT       7'd48  //  bzolcnt   hex = 64'h00746e63_6c6f7a62
`define npuarc_EVT_BDATA64       7'd49  //  bdata64   hex = 64'h00343661_74616462
`define npuarc_EVT_BDCSTALL      7'd50  //  bdcstall  hex = 64'h6c6c6174_73636462
`define npuarc_EVT_BAUXFLSH      7'd51  //  bauxflsh  hex = 64'h68736c66_78756162
`define npuarc_EVT_BFIRQEX       7'd52  //  bfirqex   hex = 64'h00786571_72696662
`define npuarc_EVT_ETAKEN        7'd53  //  etaken    hex = 64'h00006e65_6b617465
`define npuarc_EVT_QTAKEN        7'd54  //  qtaken    hex = 64'h00006e65_6b617471
`define npuarc_EVT_ICM           7'd55  //  icm       hex = 64'h00000000_006d6369
`define npuarc_EVT_ICLL          7'd56  //  icll      hex = 64'h00000000_6c6c6369
`define npuarc_EVT_ICOFF         7'd57  //  icoff     hex = 64'h00000066_666f6369
`define npuarc_EVT_IVIC          7'd58  //  ivic      hex = 64'h00000000_63697669
`define npuarc_EVT_IVIL          7'd59  //  ivil      hex = 64'h00000000_6c697669
`define npuarc_EVT_ICWPM         7'd60  //  icwpm     hex = 64'h0000006d_70776369
`define npuarc_EVT_DCM           7'd61  //  dcm       hex = 64'h00000000_006d6364
`define npuarc_EVT_DCLM          7'd62  //  dclm      hex = 64'h00000000_6d6c6364
`define npuarc_EVT_DCSM          7'd63  //  dcsm      hex = 64'h00000000_6d736364
`define npuarc_EVT_DCPM          7'd64  //  dcpm      hex = 64'h00000000_6d706364
`define npuarc_EVT_DCBC          7'd65  //  dcbc      hex = 64'h00000000_63626364
`define npuarc_EVT_FLDC          7'd66  //  fldc      hex = 64'h00000000_63646c66
`define npuarc_EVT_FLDL          7'd67  //  fldl      hex = 64'h00000000_6c646c66
`define npuarc_EVT_IVDC          7'd68  //  ivdc      hex = 64'h00000000_63647669
`define npuarc_EVT_IVDL          7'd69  //  ivdl      hex = 64'h00000000_6c647669
`define npuarc_EVT_BPMP          7'd70  //  bpmp      hex = 64'h00000000_706d7062
`define npuarc_EVT_BPLATE        7'd71  //  bplate    hex = 64'h00006574_616c7062
`define npuarc_EVT_BPCMP         7'd72  //  bpcmp     hex = 64'h00000070_6d637062
`define npuarc_EVT_BPBTAMP       7'd73  //  bpbtamp   hex = 64'h00706d61_74627062
`define npuarc_EVT_BPSUBRT       7'd74  //  bpsubrt   hex = 64'h00747262_75737062
`define npuarc_EVT_BPERRBR       7'd75  //  bperrbr   hex = 64'h00726272_72657062
`define npuarc_EVT_BPBCM         7'd76  //  bpbcm     hex = 64'h0000006d_63627062
`define npuarc_EVT_MECC1         7'd77  //  mecc1     hex = 64'h00000031_6363656d
`define npuarc_EVT_EITLB         7'd78  //  eitlb     hex = 64'h00000062_6c746965
`define npuarc_EVT_EDTLB         7'd79  //  edtlb     hex = 64'h00000062_6c746465
`define npuarc_EVT_EVINST        7'd80  //  evinst    hex = 64'h00007473_6e697665
`define npuarc_EVT_IVGATH        7'd81  //  ivgath    hex = 64'h00006874_61677669
`define npuarc_EVT_IVSCAT        7'd82  //  ivscat    hex = 64'h00007461_63737669
`define npuarc_EVT_BVGATH        7'd83  //  bvgath    hex = 64'h00006874_61677662
`define npuarc_EVT_BVSCAT        7'd84  //  bvscat    hex = 64'h00007461_63737662
`define npuarc_EVT_CCDC2CM       7'd85  //  ccdc2cm   hex = 64'h006d6332_63646363
`define npuarc_EVT_CCSERIAL      7'd86  //  ccserial  hex = 64'h6c616972_65736363
`define npuarc_EVT_CCUPGRAD      7'd87  //  ccupgrad  hex = 64'h64617267_70756363
`define npuarc_EVT_CCRESPS       7'd88  //  ccresps   hex = 64'h00737073_65726363
`define npuarc_EVT_DCSTGRAD      7'd89  //  dcstgrad  hex = 64'h64617267_74736364
`define npuarc_EVT_DCLDFWD       7'd90  //  dcldfwd   hex = 64'h00647766_646c6364
`define npuarc_EVT_CRUN          7'd91  //  crun      hex = 64'h00000000_6e757263
`define npuarc_EVT_CRUNI         7'd92  //  cruni     hex = 64'h00000069_6e757263
`define npuarc_EVT_CDUALISS      7'd93  //  cdualiss  hex = 64'h7373696c_61756463
`define npuarc_EVT_CDUALCO       7'd94  //  cdualco   hex = 64'h006f636c_61756463
`define npuarc_EVT_UFLAG0        7'd95  //  uflag0    hex = 64'h00003067_616c6675
`define npuarc_EVT_UFLAG1        7'd96  //  uflag1    hex = 64'h00003167_616c6675
`define npuarc_EVT_UFLAG2        7'd97  //  uflag2    hex = 64'h00003267_616c6675
`define npuarc_EVT_UFLAG3        7'd98  //  uflag3    hex = 64'h00003367_616c6675
`define npuarc_EVT_UFLAG4        7'd99  //  uflag4    hex = 64'h00003467_616c6675
`define npuarc_EVT_UFLAG5        7'd100  //  uflag5    hex = 64'h00003567_616c6675
`define npuarc_EVT_UFLAG6        7'd101  //  uflag6    hex = 64'h00003667_616c6675
`define npuarc_EVT_UFLAG7        7'd102  //  uflag7    hex = 64'h00003767_616c6675
`define npuarc_EVT_UFLAG8        7'd103  //  uflag8    hex = 64'h00003867_616c6675
`define npuarc_EVT_UFLAG9        7'd104  //  uflag9    hex = 64'h00003967_616c6675
`define npuarc_EVT_UFLAG10       7'd105  //  uflag10   hex = 64'h00303167_616c6675
`define npuarc_EVT_UFLAG11       7'd106  //  uflag11   hex = 64'h00313167_616c6675
`define npuarc_EVT_UFLAG12       7'd107  //  uflag12   hex = 64'h00323167_616c6675
`define npuarc_EVT_UFLAG13       7'd108  //  uflag13   hex = 64'h00333167_616c6675
`define npuarc_EVT_UFLAG14       7'd109  //  uflag14   hex = 64'h00343167_616c6675
`define npuarc_EVT_UFLAG15       7'd110  //  uflag15   hex = 64'h00353167_616c6675
`define npuarc_EVT_UFLAG16       7'd111  //  uflag16   hex = 64'h00363167_616c6675
`define npuarc_EVT_UFLAG17       7'd112  //  uflag17   hex = 64'h00373167_616c6675
`define npuarc_EVT_UFLAG18       7'd113  //  uflag18   hex = 64'h00383167_616c6675
`define npuarc_EVT_UFLAG19       7'd114  //  uflag19   hex = 64'h00393167_616c6675
`define npuarc_EVT_UFLAG20       7'd115  //  uflag20   hex = 64'h00303267_616c6675
`define npuarc_EVT_UFLAG21       7'd116  //  uflag21   hex = 64'h00313267_616c6675
`define npuarc_EVT_UFLAG22       7'd117  //  uflag22   hex = 64'h00323267_616c6675
`define npuarc_EVT_UFLAG23       7'd118  //  uflag23   hex = 64'h00333267_616c6675
`define npuarc_EVT_UFLAG24       7'd119  //  uflag24   hex = 64'h00343267_616c6675
`define npuarc_EVT_UFLAG25       7'd120  //  uflag25   hex = 64'h00353267_616c6675
`define npuarc_EVT_UFLAG26       7'd121  //  uflag26   hex = 64'h00363267_616c6675
`define npuarc_EVT_UFLAG27       7'd122  //  uflag27   hex = 64'h00373267_616c6675
`define npuarc_EVT_UFLAG28       7'd123  //  uflag28   hex = 64'h00383267_616c6675
`define npuarc_EVT_UFLAG29       7'd124  //  uflag29   hex = 64'h00393267_616c6675
`define npuarc_EVT_UFLAG30       7'd125  //  uflag30   hex = 64'h00303367_616c6675
`define npuarc_EVT_UFLAG31       7'd126  //  uflag31   hex = 64'h00313367_616c6675
`define npuarc_PCT_CA_EVENTS       127
`define npuarc_PCT_CA_LSB          0
`define npuarc_PCT_CA_MSB          127
`define npuarc_PCT_CA_RANGE        126:0
`define npuarc_PCT_EVENTS_MSB       126
`define npuarc_PCT_EVENTS_LSB       0
`define npuarc_PCT_EVENTS_RANGE     126:0
`define npuarc_PCT_NUM_CONFIGS      127
`define npuarc_PCT_CONFIG_RANGE     7:0
`define npuarc_PCT_CONFIG_BITS      8
`define npuarc_PCT_IDX_RANGE        2:0
`define npuarc_PCT_IDX_BITS         3
