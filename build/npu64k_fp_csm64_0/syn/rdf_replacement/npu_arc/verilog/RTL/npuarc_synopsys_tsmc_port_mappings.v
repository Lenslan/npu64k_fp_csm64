
`define RAM_WEM_gf55npky1p11sadsl512s(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_gf55npky1p11sadsl512s(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_WEM_gf55npky1p11sassl512s(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_gf55npky1p11sassl512s(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
    
 ////////////////

`define RAM_WEM_gf55npky2p11asdrl32ks(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_gf55npky2p11asdrl32ks(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
    
    ////////
    ///////////////

    
`define RAM_WEM_gf55npky2p22sadsl512s(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_gf55npky2p22sadsl512s(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
    
    //////////////////
    

//Only 4 of the compilers have configurability of Periphery Vt and the option STANDARD and ULTRALOW doe not exist, There is an dditional option MIX
//in10njg41p11sasrl256sb02  periphery_Vt        = MIX  (default)          ( possible values are LOW, MIX & HIGH )
//in10njg41p11sassl01msb02  periphery_Vt        = LOW  (default)           (Allowed values are LOW and HIGH)
//in10njg42p11sasul01msb02  periphery_Vt        = "LOW" (default)        ( Allowed values are: LOW & HIGH  defines the threshold voltage of the transistors  )
//in10njg42p22sassl01msb01   periphery_Vt        = LOW  (default)          ( Allowed values are LOW and HIGH )
//Mix is mainly "standard", High is mainly Hvt and LOW is Lvt.
//The compilers which  do not (yet) have configurability of   the Periphery  Vt are  :
//in10njg41p11sadsl02msa10p1
//in10njg41p11sagrl128sb02/
//in10njg41p11saerl128sb02/

 `define RAM_WEM_in10njg41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_in10njg41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_in10njg41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_in10njg41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_in10njg41p11sasrl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
   instname ( \
       .Q(q), \
       .ADR(addr), \
       .D(data), \
       .WEM(wem), \
       .WE(we), \
       .ME(me), \
       .CLK(clk), \
       .LS(ls), \
       .DS(ds), \
       .SD(sd) \
     );
 `define RAM_WEM_CD_in10njg41p11sasrl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
   instname ( \
       .Q(q), \
       .ADR(addr), \
       .D(data), \
       .WEM(wem), \
       .WE(we), \
       .ME(me), \
       .CLK(clk), \
       .LS(ls), \
       .DS(ds), \
       .SD(sd) \
     );
 `define RAM_in10njg41p11sasrl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
   instname ( \
       .Q(q), \
       .ADR(addr), \
       .D(data), \
       .WE(we), \
       .ME(me), \
       .CLK(clk), \
       .LS(ls), \
       .DS(ds), \
       .SD(sd) \
     );
`define RAM_CD_in10njg41p11sasrl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
   instname ( \
       .Q(q), \
       .ADR(addr), \
       .D(data), \
       .WE(we), \
       .ME(me), \
       .CLK(clk), \
       .LS(ls), \
       .DS(ds), \
       .SD(sd) \
     );
 
 ////////////////////
 
 `define RAM_WEM_in10njg41p11sadsl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
   instname ( \
       .Q(q), \
       .ADR(addr), \
       .D(data), \
       .WEM(wem), \
       .WE(we), \
       .ME(me), \
       .CLK(clk), \
       .LS(ls), \
       .DS(ds), \
       .SD(sd) \
     );
 `define RAM_WEM_CD_in10njg41p11sadsl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
   instname ( \
       .Q(q), \
       .ADR(addr), \
       .D(data), \
       .WEM(wem), \
       .WE(we), \
       .ME(me), \
       .CLK(clk), \
       .LS(ls), \
       .DS(ds), \
       .SD(sd) \
     );
 `define RAM_in10njg41p11sadsl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
   instname ( \
       .Q(q), \
       .ADR(addr), \
       .D(data), \
       .WE(we), \
       .ME(me), \
       .CLK(clk), \
       .LS(ls), \
       .DS(ds), \
       .SD(sd) \
     );
 `define RAM_CD_in10njg41p11sadsl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
   instname ( \
       .Q(q), \
       .ADR(addr), \
       .D(data), \
       .WE(we), \
       .ME(me), \
       .CLK(clk), \
       .LS(ls), \
       .DS(ds), \
       .SD(sd) \
     );
     
   //gf22nsd41p10asdvl01msa01/gf22nsd41p10asdvl01msa01_custom.glb:periphery_Vt                     =  ULTRALOW                   /* string Allowed values are: ULTRALOW, LOW defines the threshold voltage of the transistors in the periphery */ 
//gf22nsd41p11sadcl02msa01/gf22nsd41p11sadcl02msa01_custom.glb:periphery_Vt                     =  ULTRALOW              /* string Allowed values are: ULTRALOW, LOW defines the threshold voltage of the transistors in the periphery */
//gf22nsd41p11sasrl128sa01/gf22nsd41p11sasrl128sa01_custom.glb:periphery_Vt                     =  ULTRALOW              /* string Allowed values are: LOW , ULTRALOW defines the threshold voltage of the transistors in the periphery */ 
//gf22nsd42p11sacul128sa01/gf22nsd42p11sacul128sa01_custom.glb:periphery_Vt                     =  ULTRALOW              /* string Allowed values are: ULTRALOW, LOW defines the threshold voltage of the transistors in the periphery */ 
//gf22nsd42p11sadrl128sa01/gf22nsd42p11sadrl128sa01_custom.glb:periphery_Vt                     =  ULTRALOW              /* string Allowed values are: ULTRALOW, LOW defines the threshold voltage of the transistors in the periphery */ 
//Automotive  Grade 1
//gf22nsd41p10s1dvl01msa02:periphery_Vt              =  ULTRALOW           /* string Allowed values are: ULTRALOW, LOW defines the threshold voltage of the transistors in the periphery */ 
//gf22nsd41p11s1dcl02msa02:periphery_Vt              =  ULTRALOW           /* string Allowed values are: ULTRALOW, LOW defines the threshold voltage of the transistors in the periphery */
//gf22nsd41p11s1srl256sa02:periphery_Vt              =  ULTRALOW           /* string Allowed values are: LOW , ULTRALOW defines the threshold voltage of the transistors in the periphery */ 
//gf22nsd42p11s1cul256sa02:periphery_Vt              =  ULTRALOW           /* string Allowed values are: ULTRALOW, LOW defines the threshold voltage of the transistors in the periphery */ 
//gf22nsd42p11s1drl128sa02:periphery_Vt              =  ULTRALOW           /* string Allowed values are: ULTRALOW, LOW defines the threshold voltage of the transistors in the periphery */ 

//New compiler that supports RBB and SVT periphery
// gf22nsd01p11s1psl02msa    periphery_Vt                     =  STANDARD              /* string Allowed values are: STANDARD, LOW defines the threshold voltage of the transistors in the periphery */

// New  compiler that supports voltage scaling
//gf22nsd81p11sadul02msa04p1/release.txt:PRODUCT_TYPE                        :    DesignWare Single Port Ultra High Density Leakage Control SRAM 2M Sync
//gf22nsd81p11sadul256sa03p1/release.txt:PRODUCT_TYPE                        :    DesignWare Single Port Ultra High Density Leakage Control Register File 256K Sync
//gf22nsd81p11saduv02msa03p1/release.txt:PRODUCT_TYPE                        :    DesignWare Single Port Ultra High Density Low Voltage Enabled SRAM 2M Sync
//gf22nsd81p11saduv256sa03p1/release.txt:PRODUCT_TYPE                        :    DesignWare Single Port Ultra High Density Low Voltage Enabled Register File 256K Sync
//gf22nsd81p11sadul02msa04p1_custom.glb:periphery_Vt			=  ULTRALOW		 /* string Allowed values are: ULTRALOW, LOW defines the threshold voltage of the transistors in the periphery */
//gf22nsd81p11sadul256sa03p1_custom.glb:periphery_Vt			=  ULTRALOW		 /* string Allowed values are: LOW , ULTRALOW defines the threshold voltage of the transistors in the periphery */ 
//gf22nsd81p11saduv02msa03p1_custom.glb:periphery_Vt			=  ULTRALOW		 /* string Allowed values are: ULTRALOW, LOW defines the threshold voltage of the transistors in the periphery */
//gf22nsd81p11saduv256sa03p1_custom.glb:periphery_Vt			=  ULTRALOW		 /* string Allowed values are: LOW , ULTRALOW defines the threshold voltage of the transistors in the periphery */ 


`define RAM_gf22nsd41p10asdvl01ms(instname,q,addr,data,we,me,clk,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_gf22nsd41p10asdvl01ms(instname,q,addr,data,we,me,clk,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_gf22nsd41p10asdvl01ms(instname,q,addr,data,wem,we,me,clk,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );

//  New ABB capabale  voltage scaling  compiler
`define RAM_WEM_gf22nsd81p11saduv02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .POFF(2'b00), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_WEM_CD_gf22nsd81p11saduv02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_gf22nsd81p11saduv02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
   );
`define RAM_CD_gf22nsd81p11saduv02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
    
 // end of    New ABB capabale  voltage scaling  compiler
 
 //  New ABB capabale  voltage scaling  compiler regfile
`define RAM_WEM_gf22nsd81p11saduv256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_WEM_CD_gf22nsd81p11saduv256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_gf22nsd81p11saduv256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
   );
`define RAM_CD_gf22nsd81p11saduv256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
    
 // end of    New ABB capabale  voltage scaling  compiler   regfile
// New  RBB capable  compiler
`define RAM_WEM_gf22nsd01p11s1psl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_WEM_CD_gf22nsd01p11s1psl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_gf22nsd01p11s1psl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
   );
`define RAM_CD_gf22nsd01p11s1psl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );

//     

 `define RAM_WEM_gf22nsd41p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_WEM_CD_gf22nsd41p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_gf22nsd41p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
   );
`define RAM_CD_gf22nsd41p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
 
`define RAM_gf22nsd41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_CD_gf22nsd41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );

`define RAM_WEM_gf22nsd41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
       );
`define RAM_WEM_CD_gf22nsd41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
//

    
`define RAM_WEM_gf22nsd42p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_gf22nsd42p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_gf22nsd42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_gf22nsd42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );   

  
///////////////////////////   automotive ///////////////    
     
     

`define RAM_gf22nsd41p10s1dvl01ms(instname,q,addr,data,we,me,clk,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_gf22nsd41p10s1dvl01ms(instname,q,addr,data,we,me,clk,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_gf22nsd41p10s1dvl01ms(instname,q,addr,data,wem,we,me,clk,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );
      
 `define RAM_WEM_gf22nsd41p11s1psl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_WEM_CD_gf22nsd41p11s1psl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_gf22nsd41p11s1psl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
   );
`define RAM_CD_gf22nsd41p11s1psl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
 
  `define RAM_WEM_gf22nsd41p11s1dcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_WEM_CD_gf22nsd41p11s1dcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_gf22nsd41p11s1dcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
   );
`define RAM_CD_gf22nsd41p11s1dcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_gf22nsd41p11s1srl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_CD_gf22nsd41p11s1srl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );

`define RAM_WEM_gf22nsd41p11s1srl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
       );
`define RAM_WEM_CD_gf22nsd41p11s1srl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
//

    
`define RAM_WEM_gf22nsd42p11s1drl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_gf22nsd42p11s1drl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_gf22nsd42p11s1drl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_gf22nsd42p11s1drl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );   

     
   
    
`define RAM_WEM_gf22nsd42p11s1cul256s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_gf22nsd42p11s1cul256s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_gf22nsd42p11s1cul256s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_gf22nsd42p11s1cul256s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );   
  
      
//////////N6 -Note  defaults are different to N7 //////////////
//ts06n0g41p10asdvd01msa01_custom.glb:periphery_Vt     =  LOW              /* string Allowed values are: LOW ,STANDARD defines the threshold voltage of the transistors in the periphery */ 
//ts06n0g41p11sacrl256sa01_custom.glb:periphery_Vt     =  LOW              /* string Allowed values are: LOW , STANDARD defines the threshold voltage of the transistors in the periphery */ 
//ts06n0g41p11sasrl256sa01_custom.glb:periphery_Vt     =  ULTRALOW          /* string Allowed values are: LOW , ULTRALOW defines the threshold voltage of the transistors in the periphery */ 
//ts06n0g41p11sacul10ks   -DOES NOT EXIST in  N6 only in N7
//ts06n0g41p11sadcl02msa01_custom.glb:periphery_Vt     =  LOW              /* string Allowed values are: STANDARD , LOW defines the threshold voltage of the transistors in the periphery */
//ts06n0g41p11sadul02msa01_custom.glb:periphery_Vt     =  LOW              /* string Allowed values are: STANDARD , LOW defines the threshold voltage of the transistors in the periphery */ 
//ts06n0g41p11sassl01msa01_custom.glb:periphery_Vt     =  ULTRALOW          /* string Allowed values are: LOW , ULTRALOW defines the threshold voltage of the transistors in the periphery */ 
//ts06n0g42p11sadrl128sa01_custom.glb:periphery_Vt     =  ULTRALOW          /* string Allowed values are: ULTRALOW, LOW, STANDARD defines the threshold voltage of the transistors in the periphery */ 

//New:   sarel256s  -re-use  sacul10ks template from N7 for this
//ts06n0g41p11sarel256sa01_custom.glb:periphery_Vt     =  LOW           /* string Allowed values are: LOW , STANDARD defines the threshold voltage of the transistors  in the periphery  */ 

//Not supported in  N7 yet
//ts06n0g42p11sasul01msa01_custom.glb:periphery_Vt     =  ULTRALOW          /* string Allowed values are: LOW , ULTRALOW defines the threshold voltage of the transistors  in the periphery  */ 
//ts06n0g42p22sadsl01msa01_custom.glb:periphery_Vt    =   LOW       /* string Allowed values are: LOW , STANDARD , ULTRALOW defines the threshold voltage of the transistors  in the periphery  */ 
//ts06n0g42p11sacul256sa01_custom.glb:periphery_Vt    =  LOW            /* string Allowed values are: LOW , STANDARD defines the threshold voltage of the transistors in the periphery */ 
    
  `define RAM_ts06n0g41p10asdvd01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts06n0g41p10asdvd01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_ts06n0g41p10asdvd01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );


`define RAM_WEM_ts06n0g41p11sacrl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_ts06n0g41p11sacrl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts06n0g41p11sacrl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts06n0g41p11sacrl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_ts06n0g41p11sasrl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_ts06n0g41p11sasrl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts06n0g41p11sasrl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts06n0g41p11sasrl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );


`define RAM_ts06n0g41p11sarel256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
    
    
`define RAM_WEM_CD_ts06n0g41p11sacul0ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts06n0g41p11sarel256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
 `define RAM_WEM_ts06n0g41p11sarel256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_ts06n0g41p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts06n0g41p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts06n0g41p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
   );
`define RAM_CD_ts06n0g41p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls) \
    );
    
    
`define RAM_WEM_ts06n0g41p11sadul02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts06n0g41p11sadul02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts06n0g41p11sadul02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts06n0g41p11sadul02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
/////////

    
`define RAM_WEM_ts06n0g41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts06n0g41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts06n0g41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts06n0g41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
//////////////    
`define RAM_WEM_ts06n0g42p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts06n0g42p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts06n0g42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts06n0g42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );   
  
///// END N6 /////////
     
/////////////////////////TSMC 7nm //////
//7nm FF P-Optional Vt/Cell Std Vt
//ts07n0g41p11sacrl256sa06_custom.glb:SiWare Single Port High Density and Performance Leakage Control Register File 256K Sync       periphery_Vt             =           LOW         /* string Allowed values are: LOW , STANDARD defines the threshold voltage of the transistors  in the periphery  */ 
// ts07n0g41p11sasrl256sa12p2         SiWare Single Port High Speed Leakage Control Register File 256K Sync                        periphery_Vt                     =  ULTRALOW              /* string Allowed values are: LOW , ULTRALOW defines the threshold voltage of the transistors in the periphery */

///ts07n0g41p11sacul10ksa02_custom.glb:SiWare Single Port Ultra High Density and Performance Leakage Control Register File 10K Sync periphery_Vt             =           LOW         /* string Allowed values are: LOW , STANDARD defines the threshold voltage of the transistors  in the periphery  */ 
//ts07n0g41p11sadcl02msa10_custom.glb:SiWare Single Port High Density and Performance Leakage Control SRAM 2M Sync           periphery_Vt             =           LOW         /* string Allowed values are: LOW , STANDARD defines the threshold voltage of the transistors  in the periphery  */ 
//ts07n0g41p11sadul02msa04_custom.glb::  SiWare Single Port Ultra High Density Leakage Control SRAM 2M Sync               periphery_Vt             =           LOW         /* string Allowed values are: LOW , STANDARD defines the threshold voltage of the transistors  in the periphery  */

//ts07n0g42p11sadrl128sa11_custom.glb: SiWare Two Port High Density Leakage Control Register File 128K Sync                         periphery_Vt               =           LOW           /* string Allowed values are:  LOW , STANDARD and ULTRALOW defines the threshold voltage of the transistors  in the periphery  */ 

//ts07n0g41p10asdvd01msa08p1     SiWare Single Port High Density Via MD ROM 1M Sync                                                 periphery_Vt                    =               LOW             /* string Allowed values are: ULTRALOW , LOW , STANDARD defines the threshold voltage of the transistors  in the periphery  */ 
// wrapper  t.b.d.
//ts07n0g42p11sacul256sa10_custom.glb: SiWare Single Port Ultra High Density and Performance Leakage Control Register File 10K Sync   periphery_Vt               =           LOW           /* string Allowed values are: LOW , STANDARD defines the threshold voltage of the transistors  in the periphery  */ 

//Automotive compilers
//ts07n0g41p10s1dvd01msa01    periphery_Vt             =  LOW           /* string Allowed values are: LOW ,STANDARD defines the threshold voltage of the transistors in the periphery */ 
//ts07n0g41p11s1crl256sa01    periphery_Vt             =  LOW           /* string Allowed values are: LOW , STANDARD defines the threshold voltage of the transistors in the periphery */ 
//ts07n0g41p11s1dcl02msa01    periphery_Vt             =  LOW           /* string Allowed values are: STANDARD , LOW defines the threshold voltage of the transistors in the periphery */
//ts07n0g41p11s1srl256sa01    periphery_Vt             =  ULTRALOW          /* string Allowed values are: LOW , ULTRALOW defines the threshold voltage of the transistors in the periphery */ 
//ts07n0g41p11s1ssl01msa01    periphery_Vt             =  ULTRALOW          /* string Allowed values are: LOW , ULTRALOW defines the threshold voltage of the transistors in the periphery */ 
//ts07n0g42p11s1cul256sa01    periphery_Vt            =  LOW          /* string Allowed values are: LOW , STANDARD defines the threshold voltage of the transistors in the periphery */ 
//ts07n0g42p11s1drl128sa01    periphery_Vt             =  ULTRALOW          /* string Allowed values are: ULTRALOW, LOW, STANDARD defines the threshold voltage of the transistors in the periphery */ 
//ts07n0g42p11s1sul01msa01    periphery_Vt                  =          ULTRALOW           /* string Allowed values are: LOW , ULTRALOW defines the threshold voltage of the transistors  in the periphery  */ 


///////////////////////////////////
`define RAM_ts07n0g41p10asdvd01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts07n0g41p10asdvd01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_ts07n0g41p10asdvd01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );
////////Automotive Grade 2
`define RAM_ts07n0g41p10s1dvd01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts07n0g41p10s1dvd01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_ts07n0g41p10s1dvd01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );

////////////////////////////////

`define RAM_WEM_ts07n0g41p11sacrl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_ts07n0g41p11sacrl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts07n0g41p11sacrl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts07n0g41p11sacrl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
////////////Automotive Garade 2

`define RAM_WEM_ts07n0g41p11s1crl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_ts07n0g41p11s1crl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts07n0g41p11s1crl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts07n0g41p11s1crl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
///////////////////////
`define RAM_WEM_ts07n0g41p11sasrl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_ts07n0g41p11sasrl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts07n0g41p11sasrl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts07n0g41p11sasrl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

///////// Automotive Garde 2
`define RAM_WEM_ts07n0g41p11s1srl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_ts07n0g41p11s1srl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts07n0g41p11s1srl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts07n0g41p11s1srl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    ////////////////////////////////
`define RAM_ts07n0g41p11sacul10ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
    
    
`define RAM_WEM_CD_ts07n0g41p11sacul0ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts07n0g41p11sacul10ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
 `define RAM_WEM_ts07n0g41p11sacul10ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_ts07n0g41p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts07n0g41p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts07n0g41p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
   );
`define RAM_CD_ts07n0g41p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls) \
    );
//////////////// Automotive
`define RAM_WEM_ts07n0g41p11s1dcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts07n0g41p11s1dcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts07n0g41p11s1dcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
   );
`define RAM_CD_ts07n0g41p11s1dcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls) \
    );
///////////////    
    
`define RAM_WEM_ts07n0g41p11sadul02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts07n0g41p11sadul02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts07n0g41p11sadul02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts07n0g41p11sadul02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
/////////

    
`define RAM_WEM_ts07n0g41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts07n0g41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts07n0g41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts07n0g41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
//////////////////Automotive Grade 2
    
    
    
`define RAM_WEM_ts07n0g41p11s1ssl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts07n0g41p11s1ssl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts07n0g41p11s1ssl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts07n0g41p11s1ssl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
    //////////////////////
//////////////    
`define RAM_WEM_ts07n0g42p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts07n0g42p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts07n0g42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts07n0g42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );   
    
////Automotive Garde 2
`define RAM_WEM_ts07n0g42p11s1drl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts07n0g42p11s1drl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts07n0g42p11s1drl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts07n0g42p11s1drl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );   
 //////////////////

///////////////////

//ts12n0c41p10asdv101ms:periphery_Vt  =       LOW          /*string               Allowed values are: STANDARD, LOW defines the threshold voltage of the transistors    */
//ts12n0c41p11sadcl02ms:periphery_Vt  = LOW          /*string                Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors    */
//ts12n0c41p11sassl01ms:periphery_Vt   =        LOW          /*string                Allowed values are: LOW, ULTRALOW                              */ 
//ts12n0c42p11sacul128s:periphery_Vt  =       LOW          /*string                Allowed values are: STANDARD, LOW defines the threshold voltage of the transistors    */
//ts12n0c42p11sadrl128s:periphery_Vt  =        LOW          /*string            Allowed values are: LOW , STANDARD defines the threshold voltage of the transistors          */
//ts12n0c42p22sadsl01ms:periphery_Vt  =        LOW          /*string    Allowed values are:   STANDARD, LOW defines the threshold voltage of the transistors              */
//ts12n0c41p11sadel02ms:periphery_Vt  = LOW          /*string                Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors    */
//ts12n0c41p11sacrl128s:periphery_Vt   =        LOW          /*string                Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors    */
//ts12n0c41p11sasrl128s:periphery_Vt  =       LOW          /*string                Allowed values are: LOW, ULTRALOW defines the threshold voltage of the transistors    */
//ts12n0c41p11sarel256s:periphery_Vt  =       LOW          /*string                Allowed values are: STANDARD, LOW, ULTRALOW defines the threshold voltage of the transistors    */

//TSMC  12FFC+
//ts12n0v01p11sacrl128s:periphery_Vt   =	LOW		   /*string	   Allowed values are: STANDARD and ULTRALOW, LOW  defines the threshold voltage of the transistors    */
//ts12n0v01p11sadcl02ms:periphery_Vt		= LOW		  /*string			    Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors    */
//ts12n0v01p11sasrl128s:periphery_Vt  = 	 LOW		  /*string			    Allowed values are: LOW, ULTRALOW defines the threshold voltage of the transistors    */
//ts12n0v01p11sassl01ms:periphery_Vt   =       LOW		  /*string			    Allowed values are: LOW, ULTRALOW						      */ 
//ts12n0v02p11sacul128s:periphery_Vt  = 	 LOW		  /*string			    Allowed values are: STANDARD and ULTRALOW, LOW defines the threshold voltage of the transistors    */
//ts12n0v02p11sadrl128s:periphery_Vt  =       LOW	      /*string  	      Allowed values are: ULTRALOW ,LOW , STANDARD defines the threshold voltage of the transistors		*/

// TSMC 12FFC+ ULL
//ts12n0zs1p11sadcl01msa03:output_drive             = STANDARD        /*string                          Allowed values are: STANDARD, HIGH defines the output driver strength */

////////////////////////

`define RAM_ts12n0c41p10asdv101ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts12n0c41p10asdv101ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_ts12n0c41p10asdv101ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );
 `define RAM_WEM_ts12n0c41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts12n0c41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts12n0c41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts12n0c41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

//12FFCP
 `define RAM_WEM_ts12n0v01p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts12n0v01p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts12n0v01p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts12n0v01p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
///////
 `define RAM_WEM_ts12n0c41p11sadel02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts12n0c41p11sadel02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts12n0c41p11sadel02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_CD_ts12n0c41p11sadel02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .QP(), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );



`define RAM_WEM_ts12n0c41p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts12n0c41p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts12n0c41p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
   );
`define RAM_CD_ts12n0c41p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
    // 12FFC+ ULL
    
`define RAM_WEM_ts12n0zs1p11sadcl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts12n0zs1p11sadcl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts12n0zs1p11sadcl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
   );
`define RAM_CD_ts12n0zs1p11sadcl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    // end of 12FFC+ULL
//// 12FFCP


`define RAM_WEM_ts12n0v01p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts12n0v01p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts12n0v01p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
   );
`define RAM_CD_ts12n0v01p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

//// end  12FFCP

`define RAM_WEM_ts12n0c42p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_CD_ts12n0c42p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_ts12n0c42p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_CD_ts12n0c42p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );


`define RAM_WEM_ts12n0c41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_ts12n0c41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts12n0c41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts12n0c41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

//  12FFCP


`define RAM_WEM_ts12n0v01p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_ts12n0v01p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts12n0v01p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts12n0v01p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

// endo fo 12FFCP


`define RAM_WEM_ts12n0c41p11sacrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_ts12n0c41p11sacrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts12n0c41p11sacrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts12n0c41p11sacrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
//12FFCP


`define RAM_WEM_ts12n0v01p11sacrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_ts12n0v01p11sacrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts12n0v01p11sacrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts12n0v01p11sacrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

/// end of  12FFCP

`define RAM_WEM_ts12n0c42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,wem_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem_a), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts12n0c42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,wem_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
       .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem_a), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts12n0c42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts12n0c42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
       .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

// 12FFCP

`define RAM_WEM_ts12n0v02p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,wem_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem_a), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts12n0v02p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,wem_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
       .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem_a), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts12n0v02p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts12n0v02p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
       .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

// end of 12FFCP

 `define RAM_WEM_ts12n0c42p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts12n0c42p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts12n0c42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts12n0c42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
    
    //  12FFCP
    
    
 `define RAM_WEM_ts12n0v02p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts12n0v02p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts12n0v02p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts12n0v02p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
    // end of  12FFCP
`define RAM_WEM_ts12n0c41p11sarel256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
       );

`define RAM_WEM_CD_ts12n0c41p11sarel256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
       );

`define RAM_ts12n0c41p11sarel256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
       );

`define RAM_CD_ts12n0c41p11sarel256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
       );


//16nm FFC P-Optional Vt/Cell Std Vt
//ts16n0c41p10asdv101ms     :  SiWare Single Port High Density Via 12 ROM 1M Sync                           periphery_Vt  =       LOW       Allowed values are: STANDARD, LOW defines the threshold voltage of the transistors 
//ts16n0c41p11sadcl02ms       :  SiWare Single Port High Density and Performance Leakage Control SRAM 2M Sync           periphery_Vt  =       LOW      Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors
//ts16n0c41p11sassl01ms     :  SiWare Single Port High Speed Leakage Control SRAM 1M Sync                       periphery_Vt  =       LOW     Allowed values are: LOW, ULTRALOW                              
//ts16n0c42p11sacul128s     :  SiWare Two Port Ultra High Density and Performance Leakage Control Register File 128K Sync periphery_Vt  =       LOW      Allowed values are: STANDARD, LOW defines the threshold voltage of the transistors  
//ts16n0c42p11sadrl128s       :  SiWare Two Port High Density Leakage Control Register File 128K Sync               periphery_Vt  =       LOW      Allowed values are: LOW , STANDARD defines the threshold voltage of the transistors
//ts16n0c42p22sadsl01ms     :  SiWare Dual Port High Density Leakage Control SRAM 1M Sync                       periphery_Vt  =       LOW        Allowed values are:   STANDARD, LOW defines the threshold voltage of the transistors       
//ts16n0c41p11sadel02ms     :  SiWare Single Port Extreme High Density Leakage Control SRAM 2M Sync                        periphery_Vt  =       LOW        Allowed values are:   STANDARD, LOW defines the threshold voltage of the transistors


`define RAM_ts16n0c41p10asdv101ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts16n0c41p10asdv101ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_ts16n0c41p10asdv101ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );
 `define RAM_WEM_ts16n0c41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts16n0c41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts16n0c41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts16n0c41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

 `define RAM_WEM_ts16n0c41p11sadel02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts16n0c41p11sadel02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts16n0c41p11sadel02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_CD_ts16n0c41p11sadel02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .QP(), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

 `define RAM_WEM_ts16n0c41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts16n0c41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts16n0c41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts16n0c41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_ts16n0c41p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts16n0c41p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts16n0c41p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
   );
`define RAM_CD_ts16n0c41p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_ts16n0c42p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_CD_ts16n0c42p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_ts16n0c42p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_CD_ts16n0c42p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );


`define RAM_WEM_ts16n0c41p11sacrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_ts16n0c41p11sacrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts16n0c41p11sacrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts16n0c41p11sacrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

////
`define RAM_WEM_ts16n0c41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_ts16n0c41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts16n0c41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts16n0c41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

////

`define RAM_WEM_ts16n0c42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,wem_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem_a), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts16n0c42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,wem_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
       .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem_a), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts16n0c42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts16n0c42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
       .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );


 `define RAM_WEM_ts16n0c42p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts16n0c42p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts16n0c42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts16n0c42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
    


// Following compilers are supported here forUMC 40 LP
//
//um40npk41p10asdv101ms                   :  SiWare Single Port High Density Contact/Via 12 ROM 1M Sync
//um40npk41p11sadrl32ks                   :  SiWare Single Port High Density Leakage Control Register File 32K Sync
//um40npk41p11sadsl512s                   :  SiWare Single Port High Density Leakage Control SRAM 512K Sync
//um40npk41p11sasrl64ks                  :  SiWare Single Port High Speed Leakage Control Register File 64K Sync
//um40npk41p11sassl512s                   :  SiWare Single Port High Speed Leakage Control SRAM 512K Sync
//um40npk42p11sadrl32ks                   :  SiWare Two Port High Density Leakage Control Register File 32K Sync
//um40npk42p22sadsl512s                   :  SiWare Dual Port High Density Leakage Control SRAM 512K Sync
`define RAM_WEM_um40npk41p11sadrl32ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_um40npk41p11sadrl32ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_um40npk41p11sadrl32ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_um40npk41p11sadrl32ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_um40npk41p11sasrl64ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_um40npk41p11sasrl64ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_um40npk41p11sasrl64ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_um40npk41p11sasrl64ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_um40npk41p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_um40npk41p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_um40npk41p11sadsl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_um40npk41p11sadsl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_um40npk41p11sassl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_um40npk41p11sassl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_um40npk41p11sassl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_um40npk41p11sassl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
 `define RAM_WEM_um40npk42p11sadrl32ks(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_um40npk42p11sadrl32ks(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_um40npk42p11sadrl32ks(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_um40npk42p11sadrl32ks(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    ); 
    
`define RAM_WEM_um40npk42p22sadsl512s(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_CD_um40npk42p22sadsl512s(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_um40npk42p22sadsl512s(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_CD_um40npk42p22sadsl512s(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );    


// Following compilers are supported here for GF40 LP
//
//gf40npk41p10asdv101ms                   :  SiWare Single Port High Density Contact/Via 12 ROM 1M Sync
//gf40npk41p11sadrl32ks                   :  SiWare Single Port High Density Leakage Control Register File 32K Sync
//gf40npk41p11sadsl512s                   :  SiWare Single Port High Density Leakage Control SRAM 512K Sync
//gf40npk41p11sasrl64ks                  :  SiWare Single Port High Speed Leakage Control Register File 64K Sync
//gf40npk41p11sassl512s                   :  SiWare Single Port High Speed Leakage Control SRAM 512K Sync
//gf40npk42p11sadrl32ks                   :  SiWare Two Port High Density Leakage Control Register File 32K Sync
//gf40npk42p22sadsl512s                   :  SiWare Dual Port High Density Leakage Control SRAM 512K Sync
`define RAM_WEM_gf40npk41p11sadrl32ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_gf40npk41p11sadrl32ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_gf40npk41p11sadrl32ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_gf40npk41p11sadrl32ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_gf40npk41p11sasrl64ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_gf40npk41p11sasrl64ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_gf40npk41p11sasrl64ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_gf40npk41p11sasrl64ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_gf40npk41p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_gf40npk41p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_gf40npk41p11sadsl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_gf40npk41p11sadsl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_gf40npk41p11sassl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_gf40npk41p11sassl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_gf40npk41p11sassl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_gf40npk41p11sassl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
 `define RAM_WEM_gf40npk42p11sadrl32ks(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_gf40npk42p11sadrl32ks(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_gf40npk42p11sadrl32ks(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_gf40npk42p11sadrl32ks(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    ); 
    
`define RAM_WEM_gf40npk42p22sadsl512s(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_CD_gf40npk42p22sadsl512s(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_gf40npk42p22sadsl512s(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_CD_gf40npk42p22sadsl512s(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );    
      

// Following compilers are supported here for 40ULP
//ts40nuk41p10asdv101ms  SiWare Single Port High Density Via 12 ROM 1M Sync
//ts40nuk41p11sadrl32ks  SiWare Single Port High Density Leakage Control Register File 32K Sync
//ts40nuk41p11sadsl512s  SiWare Single Port High Density Leakage Control SRAM 512K Sync
`define RAM_WEM_ts40nuk41p11sadrl32ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts40nuk41p11sadrl32ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts40nuk41p11sadrl32ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts40nuk41p11sadrl32ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
 `define RAM_WEM_ts40nuk41p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts40nuk41p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts40nuk41p11sadsl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts40nuk41p11sadsl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );   

////// SMIC
//sm40nuk41p10asdv101ms  SiWare Single Port High Density Via 12 ROM 1M Sync
//sm40nuk41p11sadrl32ks  SiWare Single Port High Density Leakage Control Register File 32K Sync
//sm40nuk41p11sadsl512s  SiWare Single Port High Density Leakage Control SRAM 512K Sync
`define RAM_WEM_sm40nuk41p11sadrl32ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_sm40nuk41p11sadrl32ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_sm40nuk41p11sadrl32ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_sm40nuk41p11sadrl32ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
 `define RAM_WEM_sm40nuk41p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_sm40nuk41p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_sm40nuk41p11sadsl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_sm40nuk41p11sadsl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );   

/////////// END SMIC

  
////  TSMC  22ULL
// 22 ULP rams have SVT periphery by default. If HVT cells are used with SVT and the compiler is one of the 6 types supporting  HIGH periphery_vt, we will configure HVT. 
// If 1-port RAM,  configure  HIGH if HVT in the mix , but no SVT;  Configure  ULTRAHIGH as periphery if UHVT in the mix bt no SVT, otherwise  STANDARD 
//ts22nlh41p10asdvl01ms    periphery_Vt  =           STANDARD     Allowed values are: STANDARD, LOW defines the threshold voltage of the transistors     */
//ts22nlh41p11sadrl128s    periphery_Vt  =           STANDARD     Allowed values are: STANDARD, HIGH, ULTRAHIGH defines the threshold voltage of the transistors    */ 
//ts22nlh41p11sadul02ms    periphery_Vt  =           STANDARD     Allowed values are: STANDARD, HIGH, ULTRAHIGH defines the threshold voltage of the transistors    */
//ts22nlh42p11sadul128s    periphery_Vt  =           STANDARD     Allowed values are: STANDARD, HIGH defines the threshold voltage of the transistors    */

`define ROM_ts22nlh41p10asdvl01ms(instname,q,addr,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define ROM_CD_ts22nlh41p10asdvl01ms(instname,q,addr,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );



`define RAM_ts22nlh41p10asdvl01ms(instname,q,addr,data,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts22nlh41p10asdvl01ms(instname,q,addr,data,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_ts22nlh41p10asdvl01ms(instname,q,addr,data,wem,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );


 `define RAM_WEM_ts22nlh41p11sadul02ms(instname,q,addr,data,wem,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts22nlh41p11sadul02ms(instname,q,addr,data,wem,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts22nlh41p11sadul02ms(instname,q,addr,data,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts22nlh41p11sadul02ms(instname,q,addr,data,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    ); 
    
`define RAM_WEM_ts22nlh41p11sadrl128s(instname,q,addr,data,wem,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts22nlh41p11sadrl128s(instname,q,addr,data,wem,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts22nlh41p11sadrl128s(instname,q,addr,data,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
`define RAM_CD_ts22nlh41p11sadrl128s(instname,q,addr,data,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );       
 `define RAM_WEM_ts22nlh42p11sadul128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts22nlh42p11sadul128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts22nlh42p11sadul128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );     
 ////////  22ULP
//#ts22nuh71p11sadgl128sa04  =          STANDARD          /*string   Allowed values are: STANDARD, HIGH defines the threshold voltage of the transistors    */
//#ts22nuh71p11sadsl02msa01  =          STANDARD          /*string   Allowed values are: STANDARD, HIGH defines the threshold voltage of the transistors    */
//#ts22nuh72p11sadrl128sa05  =          STANDARD          /*string   Allowed values are: STANDARD, HIGH defines the threshold voltage of the transistors    */
//#ts22nuh71p10asdvl01msa03  =          STANDARD              /*string   Allowed values are: STANDARD, LOW defines the threshold voltage of the transistors    */
//#ts22nuh71p11sadul02msa06  =          STANDARD          /*string   Allowed values are: STANDARD, HIGH defines the threshold voltage of the transistors    */
//#ts22nuh71p11sasrl128sa04  =          STANDARD          /*string   Allowed values are: STANDARD, LOW defines the threshold voltage of the transistors    */
//#ts22nuh71p11sassl01msa01  =          STANDARD          /*string   Allowed values are: STANDARD, LOW defines the threshold voltage of the transistors    */
//#ts22nuh72p11sadul01msa01  =          STANDARD          /*string   Allowed values are: STANDARD, HIGH defines the threshold voltage of the transistors    */
//#ts22nuh72p11sadul128sa04  =          STANDARD          /*string   Allowed values are: STANDARD, HIGH defines the threshold voltage of the transistors    */
//#ts22nuh72p22sadsl01msa06  =          STANDARD          /*string   Allowed values are: STANDARD, HIGH defines the threshold voltage of the transistors    */



`define ROM_ts22nuh71p10asdvl01ms(instname,q,addr,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define ROM_CD_ts22nuh71p10asdvl01ms(instname,q,addr,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );



`define RAM_ts22nuh71p10asdvl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts22nuh71p10asdvl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_ts22nuh71p10asdvl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

   
 `define RAM_WEM_ts22nuh71p11sadsl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts22nuh71p11sadsl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts22nuh71p11sadsl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts22nuh71p11sadsl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );


 `define RAM_WEM_ts22nuh71p11sadul02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts22nuh71p11sadul02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts22nuh71p11sadul02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts22nuh71p11sadul02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );



//sadu
    
    
`define RAM_ts22nuh71p11sadgl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts22nuh71p11sadgl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
    
`define RAM_WEM_ts22nuh71p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts22nuh71p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts22nuh71p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts22nuh71p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
 
     
`define RAM_WEM_ts22nuh71p11sadrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts22nuh71p11sadrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts22nuh71p11sadrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
`define RAM_CD_ts22nuh71p11sadrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );   
    ///sadr
 `define RAM_WEM_ts22nuh72p11sadul128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts22nuh72p11sadul128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts22nuh72p11sadul128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );   
    
`define RAM_WEM_ts22nuh72p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts22nuh72p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts22nuh72p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );   
    
    `define RAM_WEM_ts22nuh71p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts22nuh71p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts22nuh71p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts22nuh71p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

 
 `define RAM_CD_ts22nuh72p11sadul128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );

    
`define RAM_WEM_ts22nuh72p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_CD_ts22nuh72p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_ts22nuh72p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_CD_ts22nuh72p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );



//// 22ULP   

// Following compilers are supported here for 28nm HPC+

//ts28nph41p11sad2l02ms  SiWare Single Port Ultra High Density Gen2 Leakage Control SRAM 2M Sync
//ts28nph41p11sadgl128s  SiWare Single Port High Density Gen2 Leakage Control Register File 128K Sync
//ts28nph41p11sasrl128s  SiWare Single Port High Speed Leakage Control Register File 128K Sync
//ts28nph41p11sassl01ms  SiWare Single Port High Speed Leakage Control SRAM 1M Sync

//ts28nph42p11sadgl128s  SiWare Two Port High Density Gen2 Leakage Control Register File 128K Sync
//ts28nph42p11sadul128s  SiWare Two Port Ultra High Density Leakage Control Register File 128K Sync
//ts28nph42p22sadsl01ms  SiWare Dual Port High Density Leakage Control SRAM 1M Sync


    
    `define RAM_WEM_ts28nph41p11sad2l02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts28nph41p11sad2l02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts28nph41p11sad2l02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28nph41p11sad2l02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );


    
    
`define RAM_ts28nph41p11sadgl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28nph41p11sadgl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
    
`define RAM_WEM_ts28nph41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts28nph41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts28nph41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28nph41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
 `define RAM_WEM_ts28nph42p11sadul128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts28nph42p11sadul128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts28nph42p11sadul128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );   
    
`define RAM_WEM_ts28nph42p11sadgl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts28nph42p11sadgl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts28nph42p11sadgl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );   
    
    `define RAM_WEM_ts28nph41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts28nph41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts28nph41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28nph41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
 
 
 `define RAM_CD_ts28nph42p11sadul128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLK(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .CLKB(clk_rd), \
      .MEB(me_rd) \
    );

    
`define RAM_WEM_ts28nph42p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_CD_ts28nph42p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_ts28nph42p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_CD_ts28nph42p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
    
    

// Following compilers are supported here for 28nm HPC

//ts28nzh41p11sadul02ms  SiWare Single Port Ultra High Density Leakage Control SRAM 2M Sync
//ts28nzh41p11sad2l02ms  SiWare Single Port Ultra High Density Gen2 Leakage Control SRAM 2M Sync

//ts28nzh41p11sadrl128s  SiWare Single Port High Density Leakage Control Register File 128K Sync
//ts28nzh41p11sadgl128s  SiWare Single Port High Density Gen2 Leakage Control Register File 128K Sync
//ts28nzh41p11sasrl128s  SiWare Single Port High Speed Leakage Control Register File 128K Sync

//ts28nzh42p11sadgl128s  SiWare Two Port High Density Gen2 Leakage Control Register File 128K Sync
//ts28nzh42p11sadul128s  SiWare Two Port Ultra High Density Leakage Control Register File 128K Sync

//ts28nzh41p11sassl01ms  SiWare Single Port High Speed Leakage Control SRAM 1M Sync

//ts28nzh42p11sadul01ms  SiWare Two Port Ultra High Density Leakage Control SRAM 1M Sync

//ts28nzh42p22sadsl01ms  SiWare Dual Port High Density Leakage Control SRAM 1M Sync


`define RAM_WEM_ts28nzh41p11sadul02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts28nzh41p11sadul02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts28nzh41p11sadul02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28nzh41p11sadul02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
    `define RAM_WEM_ts28nzh41p11sad2l02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts28nzh41p11sad2l02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts28nzh41p11sad2l02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28nzh41p11sad2l02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );


`define RAM_ts28nzh41p11sadrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28nzh41p11sadrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
    
`define RAM_ts28nzh41p11sadgl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28nzh41p11sadgl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
    
`define RAM_WEM_ts28nzh41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts28nzh41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts28nzh41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28nzh41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
 `define RAM_WEM_ts28nzh42p11sadul128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLK(clk_rd) \
    );
`define RAM_WEM_CD_ts28nzh42p11sadul128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .DS(ds), \
      .SD(sd), \
            .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLK(clk_rd) \
    );
`define RAM_ts28nzh42p11sadul128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .DS(ds), \
      .SD(sd), \
            .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLK(clk_rd) \
    );   
    
`define RAM_WEM_ts28nzh42p11sadgl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .DS(ds), \
      .SD(sd), \
            .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKA(clk_wr), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts28nzh42p11sadgl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .DS(ds), \
      .SD(sd), \
            .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKA(clk_wr), \
      .CLKB(clk_rd) \
    );
`define RAM_ts28nzh42p11sadgl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .DS(ds), \
      .SD(sd), \
            .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKA(clk_wr), \
      .CLKB(clk_rd) \
    );   
    
    `define RAM_WEM_ts28nzh41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts28nzh41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts28nzh41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28nzh41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
 //For the 2-port SRAM in 28nm HPC (ts28nzh42p11sadul01ms), a fake clkb pin is use on the port map to allow this choose of compiler to be interchanged with 2-port regfile (ts28nmh42p11sadrl128s)    
 `define RAM_ts28nzh42p11sadul01ms(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_wr,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLK(clk_wr), \
      .DS(ds), \
      .SD(sd), \
            .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd) \
      );
 
 //For the 2-port SRAM in 28nm HPC (ts28nzh42p11sadul01ms), a fake clkb pin is use on the port map to allow this choose of compiler to be interchanged with 2-port regfile (ts28nmh42p11sadrl128s)    
 
 `define RAM_CD_ts28nzh42p11sadul01ms(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_wr,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLK(clk_wr), \
      .DS(ds), \
      .SD(sd), \
            .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd) \
    );

    
`define RAM_WEM_ts28nzh42p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .DS(ds), \
      .SD(sd), \
            .LS(ls), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_CD_ts28nzh42p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .DS(ds), \
      .SD(sd), \
            .LS(ls), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_ts28nzh42p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .DS(ds), \
      .SD(sd), \
            .LS(ls), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_CD_ts28nzh42p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .DS(ds), \
      .SD(sd), \
            .LS(ls), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );

///////////////
//gf14nlg41p10asdv101msa03p3:periphery_Vt  =         LOW          /*string              Allowed values are: STANDARD, LOW defines the threshold voltage of the transistors    */
//gf14nlg41p11sadcl02msa04p3:periphery_Vt  =          LOW          /*string              Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors    */
//gf14nlg42p11sacul128sa06p1:periphery_Vt  =         LOW          /*string              Allowed values are: STANDARD, LOW defines the threshold voltage of the transistors    */
//gf14nlg42p11sadrl128sa03p3:periphery_Vt  =         LOW             /*string                        Allowed values are: LOW , STANDARD defines the threshold voltage of the transistors             */

///////////////
`define RAM_gf14nlg41p10asdv101ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_gf14nlg41p10asdv101ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_gf14nlg41p10asdv101ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_gf14nlg41p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_gf14nlg41p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_gf14nlg41p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_gf14nlg41p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
`define RAM_WEM_gf14nlg42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,wem_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem_a), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_gf14nlg42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,wem_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
       .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem_a), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_gf14nlg42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_gf14nlg42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
       .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_gf14nlg42p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_gf14nlg42p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_gf14nlg42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_gf14nlg42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );

////////////////////

////////////////////////////////
    
//Following compilers to be additionally supported :
// ts16nxq41p11sassl01ms    16nm FF+ GL  SiWare Single Port High Speed Leakage Control SRAM 1M Sync   DONE 
// ts16nxq42p11sadrl128sa01    16nm FF+ GL   SiWare Two Port High Density Leakage Control Register File 128K Sync
// ts16nxq41p11sacrl128sa01    16nm FF+ GL SiWare Single Port High Density and Performance Leakage Control Register File 128K Sync
// ts16nxq41p11sasrl128sa01   16nm FF+ GL SiWare Single Port High Speed Leakage Control Register File 128K Sync
// ts16nxq42p11sasul01ms  16nm FF+ GL SiWare Two Port High Speed and Ultra High Density 1M Sync

//ts16nxq41p10asdv101ms  :periphery_Vt  =         LOW        /*string      Allowed values are: STANDARD, LOW defines the threshold voltage of the transistors    */
//ts16nxq41p11sacgl128s  :periphery_Vt   =      LOW         /*string      Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors    */
//ts16nxq41p11sacrl128s  :periphery_Vt   =      LOW         /*string      Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors    */
//ts16nxq41p11sadcl02ms  :periphery_Vt  =      LOW         /*string      Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors    */
//ts16nxq41p11sasrl128s  :periphery_Vt  =      LOW          /*string      Allowed values are: LOW, ULTRALOW defines the threshold voltage of the transistors */
//ts16nxq41p11sassl01ms  :periphery_Vt   =      LOW         /*string      Allowed values are: LOW, ULTRALOW                            */ 
//ts16nxq42p11assrl16ka  :periphery_Vt  =      LOW          /*string      Allowed values are: LOW, ULTRALOW defines the threshold voltage of the transistors    */
//ts16nxq42p11sacul128s  :periphery_Vt  =      LOW          /*string      Allowed values are: STANDARD, LOW defines the threshold voltage of the transistors    */
//ts16nxq42p11sadrl128s  :periphery_Vt  =     LOW        /*string     Allowed values are: LOW , STANDARD defines the threshold voltage of the transistors         */
//ts16nxq42p11sasul01ms  :periphery_Vt  =        LOW        /*string    Allowed values are: LOW, ULTRALOW  defines the threshold voltage of the transistors   */
//ts16nxq42p22sadsl01ms  :periphery_Vt  =        LOW        /*string    Allowed values are:   STANDARD, LOW defines the threshold voltage of the transistors            */
               
////////////
//ts16ngq41p10asdv101ms    :periphery_Vt  = LOW        Allowed values are: STANDARD, LOW defines the threshold voltage of the transistors    */
//ts16ngq41p11sacrl128s    :periphery_Vt  = LOW        Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors    */
//ts16ngq41p11sadcl02ms    :periphery_Vt  = LOW        Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors    */
//ts16ngq41p11sasrl128s    :periphery_Vt  =  LOW       Allowed values are: LOW, ULTRALOW defines the threshold voltage of the transistors    */
//ts16ngq41p11sassl01ms    :periphery_Vt  = LOW       Allowed values are: LOW, ULTRALOW                        */ 
//ts16ngq42p11sacul128s    :periphery_Vt  =  LOW       Allowed values are: STANDARD, LOW defines the threshold voltage of the transistors  */
//ts16ngq42p11sadrl128s    :periphery_Vt  =   LOW      Allowed values are: LOW , STANDARD defines the threshold voltage of the transistors           */
//ts16ngq42p11sasul01ms    :periphery_Vt  =   LOW      Allowed values are: LOW, ULTRALOW  defines the threshold voltage of the transistors   */
//ts16ngq42p22sadsl01ms    :periphery_Vt  =   LOW    Allowed values are:   STANDARD, LOW defines the threshold voltage of the transistors             */


`define RAM_WEM_ts16ngq42p11sacul128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_WEM_CD_ts16ngq42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,wem_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem_a), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts16ngq42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,wem_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem_a), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts16ngq42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
       .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );


///////////


`define RAM_WEM_ts16nxq41p11sacrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_ts16nxq41p11sacrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts16nxq41p11sacrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts16nxq41p11sacrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

//////////
    
`define RAM_WEM_ts16nxq41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_WEM_CD_ts16nxq41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_ts16nxq41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_CD_ts16nxq41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );

`define RAM_WEM_ts16nxq41p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
    
 
`define RAM_WEM_CD_ts16nxq41p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_ts16nxq41p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_CD_ts16nxq41p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );

/////
`define RAM_WEM_ts16ngq41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_WEM_CD_ts16ngq41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_ts16ngq41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_CD_ts16ngq41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );

//////////////// support fpr ROM
`define RAM_WEM_ts16ngq41p10asdv101ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .SD(sd) \
    );

`define RAM_ts16ngq41p10asdv101ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .SD(sd) \
    );
        
`define RAM_CD_ts16ngq41p10asdv101ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .SD(sd) \
    );
 
`define RAM_WEM_CD_ts16ngq41p10asdv101ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .SD(sd) \
    );
   
////////////  Support for  ts16ngq41p11sasrl128s  - high speed single port regfile
`define RAM_WEM_ts16ngq41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_WEM_CD_ts16ngq41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_ts16ngq41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_CD_ts16ngq41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );


/////////////// support for ts16ngq41p11sacrl128s   - High density single port regfile

`define RAM_WEM_ts16ngq41p11sacrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_WEM_CD_ts16ngq41p11sacrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_ts16ngq41p11sacrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_CD_ts16ngq41p11sacrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );

////////////////////

`define RAM_WEM_ts16ngq41p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_WEM_CD_ts16ngq41p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_ts16ngq41p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_CD_ts16ngq41p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );

`define RAM_WEM_ts16ngq42p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts16ngq42p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts16ngq42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts16ngq42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );

`define RAM_WEM_ts16nxq42p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_CD_ts16nxq42p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_ts16nxq42p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_CD_ts16nxq42p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );

//ts16ngq42p22sadsl01ms is not yet released.
`define RAM_WEM_ts16ngq42p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_CD_ts16ngq42p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_ts16ngq42p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_CD_ts16ngq42p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );

`define RAM_WEM_ts16nxq41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_WEM_CD_ts16nxq41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_ts16nxq41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );
`define RAM_CD_ts16nxq41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd) \
    );


`define RAM_WEM_ts16nxq42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,wem_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem_a), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts16nxq42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,wem_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
       .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem_a), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts16nxq42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
`define RAM_CD_ts16nxq42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .ADRB(read_adr), \
       .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
        
/////////////////

`define RAM_WEM_ts28nmh42p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts28nmh42p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts28nmh42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
//////NEW 28nm gen2 register file component
`define RAM_ts28nmh42p11sadgl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts28nmh42p11sadgl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_ts28nmh42p11sadgl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts28nmh42p11sadgl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );

///////////////////////// UHVT


`define RAM_WEM_ts28nmhr2p11sadgl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts28nmhr2p11sadgl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
 `define RAM_CD_ts28nmhr2p11sadgl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts28nmhr2p11sadgl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
//////////////////////    
    
    
 //For the 2-port SRAM in 28nm HPM (ts28nmh42p11sadul01ms), a fake clkb pin is use on the port map to allow this choose of compiler to be interchanged with 2-port regfile (ts28nmh42p11sadrl128s,ls)    
 `define RAM_ts28nmh42p11sadul01ms(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_wr,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLK(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd) \
      );
 
 //For the 2-port SRAM in 28nm HPM (ts28nmh42p11sadul01ms), a fake clkb pin is use on the port map to allow this choose of compiler to be interchanged with 2-port regfile (ts28nmh42p11sadrl128s,ls)    
 
 `define RAM_CD_ts28nmh42p11sadul01ms(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_wr,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLK(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd) \
    );
         
`define RAM_CD_ts28nmh42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );

`define RAM_CD_ts28nmh42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
    
`define RAM_WEM_ts28nmh42p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
    

`define RAM_WEM_CD_ts28nmh42p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_ts28nmh42p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_CD_ts28nmh42p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
//////////////////////// UHVT 
`define RAM_WEM_ts28nmhr2p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_CD_ts28nmhr2p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_ts28nmhr2p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_CD_ts28nmhr2p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
////////////////////////////////

`define RAM_WEM_ts28nmh41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts28nmh41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts28nmh41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28nmh41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
            .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
 /////////////// UHVT
 `define RAM_WEM_ts28nmhr1p11sadrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts28nmhr1p11sadrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts28nmhr1p11sadrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28nmhr1p11sadrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
            .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
 
 ///////////////// UHVT    

    `define RAM_WEM_ts28npt41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
            .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts28npt41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
            .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts28npt41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
            .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28npt41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
            .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

/////////// UHVT

`define RAM_WEM_ts28nmhr1p11sadul02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
            .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts28nmhr1p11sadul02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
            .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_ts28nmhr1p11sadul02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
            .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28nmhr1p11sadul02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
            .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
/////////////////////
`define RAM_WEM_ts28nmh41p11sadul02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
            .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts28nmh41p11sadul02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
            .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts28nmh41p11sadul02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
            .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28nmh41p11sadul02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
            .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
    
`define RAM_WEM_ts28nmh41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
            .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts28nmh41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
            .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts28nmh41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
            .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28nmh41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
            .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
    
    `define RAM_WEM_ts28nih42p11sasul01ms(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLK(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd) \
    );
`define RAM_WEM_CD_ts28nih42p11sasul01ms(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLK(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd) \
    );
`define RAM_ts28nih42p11sasul01ms(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLK(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd) \
    );
`define RAM_CD_ts28nih42p11sasul01ms(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLK(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd) \
    );

    
`define RAM_WEM_ts28nih42p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts28nih42p11sadrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts28nih42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts28nih42p11sadrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );

`define RAM_WEM_ts28nih42p22sassl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_CD_ts28nih42p22sassl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_ts28nih42p22sassl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_CD_ts28nih42p22sassl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );

`define RAM_WEM_ts28nih42p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_CD_ts28nih42p22sadsl01ms(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_ts28nih42p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_CD_ts28nih42p22sadsl01ms(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );

`define RAM_WEM_ts28nih41p11sadrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts28nih41p11sadrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts28nih41p11sadrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28nih41p11sadrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_ts28nih41p11sadsl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts28nih41p11sadsl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts28nih41p11sadsl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28nih41p11sadsl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_ts28npt41p11sadul02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts28npt41p11sadul02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts28npt41p11sadul02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28npt41p11sadul02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );


`define RAM_WEM_ts28npt41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts28npt41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts28npt41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28npt41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
    
  
`define RAM_WEM_ts28nih41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts28nih41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts28nih41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts28nih41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_ts40npk41p11sadrl32ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts40npk41p11sadrl32ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts40npk41p11sadrl32ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts40npk41p11sadrl32ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_ts40npk41p11sasrl64ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts40npk41p11sasrl64ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts40npk41p11sasrl64ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts40npk41p11sasrl64ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_ts40npk41p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts40npk41p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts40npk41p11sadsl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts40npk41p11sadsl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_ts40npk41p11sassl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts40npk41p11sassl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts40npk41p11sassl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts40npk41p11sassl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
 //Dual rail voltage scalable   TSMC 40 ULP e-Flash
 
 
 `define RAM_WEM_ts40n8ka1p11saldl512w(instname,q,addr,data,wem,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts40n8ka1p11saldl512w(instname,q,addr,data,wem,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts40n8ka1p11saldl512w(instname,q,addr,data,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts40n8ka1p11saldl512w(instname,q,addr,data,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    // end of  Dual rail voltage scalable   TSMC 40 ULP e-Flash
/// TSMC 40 ULP e-Flash

 `define RAM_WEM_ts40n8k41p11sadcl512s(instname,q,addr,data,wem,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts40n8k41p11sadcl512s(instname,q,addr,data,wem,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts40n8k41p11sadcl512s(instname,q,addr,data,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts40n8k41p11sadcl512s(instname,q,addr,data,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

 `define RAM_WEM_ts40n8k41p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts40n8k41p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts40n8k41p11sadsl512s(instname,q,addr,data,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts40n8k41p11sadsl512s(instname,q,addr,data,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls) \
    );
`define RAM_WEM_ts40n8k41p11sasrl64ks(instname,q,addr,data,wem,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts40n8k41p11sasrl64ks(instname,q,addr,data,wem,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts40n8k41p11sasrl64ks(instname,q,addr,data,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts40n8k41p11sasrl64ks(instname,q,addr,data,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );  
    
    `define RAM_WEM_ts40n8k41p11sadrl32ks(instname,q,addr,data,wem,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts40n8k41p11sadrl32ks(instname,q,addr,data,wem,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts40n8k41p11sadrl32ks(instname,q,addr,data,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts40n8k41p11sadrl32ks(instname,q,addr,data,we,me,clk,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );  
   
    
    
    
/// TSMC 40LP e-Flash

`define ROM_ts40n7k41p10asdv101ms(instname,q,addr,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define ROM_CD_ts40n7k41p10asdv101ms(instname,q,addr,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_ts40n7k41p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts40n7k41p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts40n7k41p11sadsl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts40n7k41p11sadsl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_ts40n7k41p11sasrl64ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts40n7k41p11sasrl64ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts40n7k41p11sasrl64ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts40n7k41p11sasrl64ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );      
    
    /////SMIC 40LP
`define RAM_WEM_sm40nck41p11sadrl32ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_sm40nck41p11sadrl32ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_sm40nck41p11sadrl32ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_sm40nck41p11sadrl32ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_sm40nck41p11sasrl64ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_sm40nck41p11sasrl64ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_sm40nck41p11sasrl64ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_sm40nck41p11sasrl64ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_sm40nck41p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_sm40nck41p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_sm40nck41p11sadsl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_sm40nck41p11sadsl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_sm40nck41p11sassl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_sm40nck41p11sassl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_sm40nck41p11sassl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_sm40nck41p11sassl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );    
    /// END SMIC 40LP
    
`define RAM_WEM_ts45nkkb1p11sadrl32ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts45nkkb1p11sadrl32ks(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts45nkkb1p11sadrl32ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts45nkkb1p11sadrl32ks(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_ts45nkka1p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts45nkka1p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts45nkka1p11sadsl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts45nkka1p11sadsl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_ts45nkkb1p11sassl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts45nkkb1p11sassl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts45nkkb1p11sassl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts45nkkb1p11sassl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_ts65npkb1p11sadsl512s(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_ts65npkb1p11sadsl512s(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_WEM_ts65npkb1p11sassl512s(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_ts65npkb1p11sassl512s(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
    
 ////////////////
    
    `define RAM_WEM_sm65nckb1p11sadsl512s(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_sm65nckb1p11sadsl512s(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_WEM_sm65nckb1p11sassl512s(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_sm65nckb1p11sassl512s(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
    ////////////////
`define RAM_WEM_ts65njkb1p11sadsl512s(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_ts65njkb1p11sadsl512s(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_WEM_ts65njkb1p11sassl512s(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_ts65njkb1p11sassl512s(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );

`define RAM_WEM_ts40npk42p11sadrl32ks(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts40npk42p11sadrl32ks(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts40npk42p11sadrl32ks(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts40npk42p11sadrl32ks(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_ts45nkkb2p11sadrl32ks(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts45nkkb2p11sadrl32ks(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts45nkkb2p11sadrl32ks(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts45nkkb2p11sadrl32ks(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
    
 `define RAM_WEM_ts45nkkb2p11sadul32ks(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .WEMA(wem), \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLK(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd) \
    );
`define RAM_WEM_CD_ts45nkkb2p11sadul32ks(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .WEMA(wem), \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLK(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd) \
    ); 

// In the level above, clk_rd and clk_wr are both driven by the same clock (clk_main).
//Hence it is arbitrary whether clk_rd or clk_wr drives the single pin ".CLK"       
`define RAM_ts45nkkb2p11sadul32ks(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLK(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd) \
    );
`define RAM_CD_ts45nkkb2p11sadul32ks(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLK(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd) \
    );    
`define RAM_WEM_ts45nkkb2p11assrl16ka(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .ADRB(read_adr) \
    );
`define RAM_WEM_CD_ts45nkkb2p11assrl16ka(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr) \
    );
`define RAM_ts45nkkb2p11assrl16ka(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr) \
    );
`define RAM_CD_ts45nkkb2p11assrl16ka(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr) \
    );
`define RAM_WEM_ts65npkb2p11asdrl32ks(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts65npkb2p11asdrl32ks(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
    
    ////////
    `define RAM_WEM_sm65nckb2p11asdrl32ks(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_sm65nckb2p11asdrl32ks(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
    
    
    ///////////////
`define RAM_WEM_ts65njkb2p11asdrl32ks(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts65njkb2p11asdrl32ks(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );

`define RAM_WEM_ts40npk42p22sadsl512s(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_CD_ts40npk42p22sadsl512s(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_ts40npk42p22sadsl512s(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_CD_ts40npk42p22sadsl512s(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_ts45nkkb2p22sadsl512s(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_CD_ts45nkkb2p22sadsl512s(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_ts45nkkb2p22sadsl512s(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_CD_ts45nkkb2p22sadsl512s(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_ts45nkkb2p22sassl512s(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_CD_ts45nkkb2p22sassl512s(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_ts45nkkb2p22sassl512s(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_CD_ts45nkkb2p22sassl512s(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b,ds,sd,ls) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_ts65npkb2p22sadsl512s(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_ts65npkb2p22sadsl512s(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
    
    //////////////////
    
    `define RAM_WEM_sm65nckb2p22sadsl512s(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_sm65nckb2p22sadsl512s(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
    
    ///////////////////
`define RAM_WEM_ts65njkb2p22sadsl512s(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_ts65njkb2p22sadsl512s(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );

`define RAM_WEM_um28npk41p11sasrl128s(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls) \
    );
`define RAM_WEM_CD_um28npk41p11sasrl128s(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls) \
    );
`define RAM_um28npk41p11sasrl128s(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls) \
    );
`define RAM_CD_um28npk41p11sasrl128s(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls) \
    );
`define RAM_WEM_um28npk41p11sadul02ms(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls) \
    );
`define RAM_WEM_CD_um28npk41p11sadul02ms(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls) \
    );
`define RAM_um28npk41p11sadul02ms(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls) \
    );
`define RAM_CD_um28npk41p11sadul02ms(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls) \
    );
`define RAM_WEM_um28npk41p11sassl01ms(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls) \
    );
`define RAM_WEM_CD_um28npk41p11sassl01ms(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls) \
    );
`define RAM_um28npk41p11sassl01ms(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls) \
    );
`define RAM_CD_um28npk41p11sassl01ms(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls) \
    );
    
`define RAM_WEM_ts90npki1p11asdcs512s(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .RME(1'b0), \
      .RM(4'b0010), \
      .TEST1(1'b0) \
    );
`define RAM_ts90npki1p11asdcs512s(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .RME(1'b0), \
      .RM(4'b0010), \
      .TEST1(1'b0) \
    );
`define RAM_WEM_ts90npkd1p11asssr512s(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .RME(1'b0), \
      .RM(4'b0010), \
      .TEST1(1'b0) \
    );
`define RAM_ts90npkd1p11asssr512s(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .RME(1'b0), \
      .RM(4'b0010), \
      .TEST1(1'b0) \
    );
`define RAM_WEM_ts90ngkt1p11asdsr512s(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .RME(1'b0), \
      .RM(4'b0010), \
      .TEST1(1'b0) \
    );
`define RAM_ts90ngkt1p11asdsr512s(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .RME(1'b0), \
      .RM(4'b0010), \
      .TEST1(1'b0) \
    );
`define RAM_WEM_ts90ngkt1p11asssr512s(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .RST(), \
      .RME(1'b0), \
      .RM(4'b0010), \
      .TEST1(1'b0) \
    );
`define RAM_ts90ngkt1p11asssr512s(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .RST(), \
      .RME(1'b0), \
      .RM(4'b0010), \
      .TEST1(1'b0) \
    );
`define RAM_WEM_ts13g1p11hds(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .OE(1'b1), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_ts13g1p11hds(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .OE(1'b1), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_WEM_ts13g1p11hss(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .OE(1'b1), \
      .ME(me), \
      .CLK(clk), \
      .RM(4'b0010) \
    );
`define RAM_ts13g1p11hss(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .OE(1'b1), \
      .ME(me), \
      .CLK(clk), \
      .RM(4'b0010) \
    );
`define RAM_WEM_ts13g1p11rfs(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_ts13g1p11rfs(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_WEM_ts13ugfs1p11assrf16ks(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_ts13ugfs1p11assrf16ks(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk) \
    );
    
`define RAM_WEM_ts90npki2p11asdrf32ks(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd), \
      .RMB(4'b0010), \
      .RMEB(1'b0) \
    );
`define RAM_ts90npki2p11asdrf32ks(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd), \
      .RMB(4'b0010), \
      .RMEB(1'b0) \
    );
`define RAM_WEM_ts90ngkt2p11asdur512s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLK(clk_wr), \
      .RME(1'b0), \
      .RM(4'b0010), \
      .ADRB(read_adr), \
      .MEB(me_rd)  \
    );
`define RAM_ts90ngkt2p11asdur512s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLK(clk_wr), \
      .RME(1'b0), \
      .RM(4'b0010), \
      .ADRB(read_adr), \
      .MEB(me_rd) \
    );
`define RAM_WEM_ts90ngkt2p11asdrf32ks(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd), \
      .RMB(4'b0010), \
      .RMEB(1'b0) \
    );
`define RAM_ts90ngkt2p11asdrf32ks(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd), \
      .RMB(4'b0010), \
      .RMEB(1'b0) \
    );
`define RAM_WEM_ts13g2p11rfs(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .ADRB(read_adr), \
      .OEB(1'b1), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts13g2p11rfs(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .ADRB(read_adr), \
      .OEB(1'b1), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
    
`define RAM_WEM_ts90npki2p22asdsr512s(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .RSTA(), \
      .RMA(4'b0010), \
      .RMEA(1'b0), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b), \
      .RSTB(), \
      .RMB(4'b0010), \
      .RMEB(1'b0) \
    );
`define RAM_ts90npki2p22asdsr512s(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .RSTA(), \
      .RMA(4'b0010), \
      .RMEA(1'b0), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b), \
      .RSTB(), \
      .RMB(4'b0010), \
      .RMEB(1'b0) \
    );
`define RAM_WEM_ts90npkd2p22asssr512s(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .RMEA(1'b0), \
      .RMA(4'b0010), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b), \
      .RMEB(1'b0), \
      .RMB(4'b0010) \
    );
`define RAM_ts90npkd2p22asssr512s(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .RMEA(1'b0), \
      .RMA(4'b0010), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b), \
      .RMEB(1'b0), \
      .RMB(4'b0010) \
    );
`define RAM_WEM_ts90ngkt2p22asdsr512s(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADDRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .ADDRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_ts90ngkt2p22asdsr512s(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADDRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .ADDRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_ts90ngkt2p22asssr512s(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .RMEA(1'b0), \
      .RMA(4'b0010), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b), \
      .RMEB(1'b0), \
      .RMB(4'b0010) \
    );
`define RAM_ts90ngkt2p22asssr512s(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .RMEA(1'b0), \
      .RMA(4'b0010), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .MEB(me_b), \
      .CLKB(clk_b), \
      .RMEB(1'b0), \
      .RMB(4'b0010) \
    );
`define RAM_WEM_ts13g2p22hds(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .OEA(1'b1), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .OEB(1'b1), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_ts13g2p22hds(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .OEA(1'b1), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .OEB(1'b1), \
      .MEB(me_b), \
      .CLKB(clk_b) \
    );
`define RAM_WEM_ts13g2p22hss(instname,qa,qb,addr_a,data_a,wem_a,we_a,me_a,clk_a,addr_b,data_b,wem_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEMA(wem_a), \
      .WEA(we_a), \
      .OEA(1'b1), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .RMA(4'b0010), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEMB(wem_b), \
      .WEB(we_b), \
      .OEB(1'b1), \
      .MEB(me_b), \
      .CLKB(clk_b), \
      .RMB(4'b0010) \
    );
`define RAM_ts13g2p22hss(instname,qa,qb,addr_a,data_a,we_a,me_a,clk_a,addr_b,data_b,we_b,me_b,clk_b) \
  instname ( \
      .QA(qa), \
      .QB(qb), \
      .ADRA(addr_a), \
      .DA(data_a), \
      .WEA(we_a), \
      .OEA(1'b1), \
      .MEA(me_a), \
      .CLKA(clk_a), \
      .RMA(4'b0010), \
      .ADRB(addr_b), \
      .DB(data_b), \
      .WEB(we_b), \
      .OEB(1'b1), \
      .MEB(me_b), \
      .CLKB(clk_b), \
      .RMB(4'b0010) \
    );

`define RAM_WEM_ts18upfs1p11aspul512s(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .OE(1'b1), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_ts18upfs1p11aspul512s(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .OE(1'b1), \
      .ME(me), \
      .CLK(clk) \
    );

`define RAM_WEM_ts18ugfs1p11aspul512s(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .OE(1'b1), \
      .ME(me), \
      .CLK(clk) \
    );
`define RAM_ts18ugfs1p11aspul512s(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .OE(1'b1), \
      .ME(me), \
      .CLK(clk) \
    );

`define RAM_WEM_ts18ugfs1p11asssr512s(instname,q,addr,data,wem,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .OE(1'b1), \
      .ME(me), \
      .CLK(clk), \
      .RM(4'b0010) \
    );
`define RAM_ts18ugfs1p11asssr512s(instname,q,addr,data,we,me,clk) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .OE(1'b1), \
      .ME(me), \
      .CLK(clk), \
      .RM(4'b0010) \
    );

//ts05p0g41p10asdvd01ms:periphery_Vt               =  LOW            /* string Allowed values are: LOW ,STANDARD defines the threshold voltage of the transistors in the periphery */ 
//ts05p0g41p11sadcl02ms:periphery_Vt               =  LOW            /* string Allowed values are: LOW , ULTRALOW , STANDARD defines the threshold voltage of the transistors in the periphery */ 
//ts05p0g41p11sadul02ms:periphery_Vt               =  LOW            /* string Allowed values are: STANDARD , LOW ,ULTRALOW ;defines the threshold voltage of the transistors in the periphery */ 
//ts05p0g41p11sacrl256s:periphery_Vt             =  ULTRALOW        /* string Allowed values are: LOW , ULTRALOW defines the threshold voltage of the transistors in the periphery */ 
//ts05p0g41p11sassl01ms:periphery_Vt             =  ULTRALOW        /* string Allowed values are: STANDARD, LOW , ULTRALOW defines the threshold voltage of the transistors in the periphery */ 
//ts05p0g42p11sacul256s:periphery_Vt             =  LOW              /* string Allowed values are: LOW , STANDARD defines the threshold voltage of the transistors in the periphery */ 
// new in  5nm - not in 7nm 
//ts05p0g41p11sagrl256s periphery_Vt                 =  ULTRALOW                   /* string Allowed values are: EXTREMELOW, LOW, ULTRALOW defines the threshold voltage of the transistors in the periphery */ 
//ts05p0g42p11sasul01ms: periphery_Vt                =  ULTRALOW                   /* string Allowed values are: EXTREMELOW, LOW, ULTRALOW defines the threshold voltage of the transistors in the periphery */ 
  
 `define RAM_ts05p0g41p10asdvd01ms(instname,q,addr,data,we,me,clk,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts05p0g41p10asdvd01ms(instname,q,addr,data,we,me,clk,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_ts05p0g41p10asdvd01ms(instname,q,addr,data,wem,we,me,clk,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );
//N5A     ts05p0g41p10asdvd01ms  -> ts05n0g41p10s2dvd01ms
  `define RAM_ts05n0g41p10s2dvd01ms(instname,q,addr,data,we,me,clk,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts05n0g41p10s2dvd01ms(instname,q,addr,data,we,me,clk,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_ts05n0g41p10s2dvd01ms(instname,q,addr,data,wem,we,me,clk,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );   
 ////////////////// end of N5A  ROM
`define RAM_WEM_ts05p0g41p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts05p0g41p11sadcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts05p0g41p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
   );
`define RAM_CD_ts05p0g41p11sadcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .LS(ls) \
    );
`define RAM_WEM_ts05p0g41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts05p0g41p11sassl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts05p0g41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts05p0g41p11sassl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
 // N5A High speed
    `define RAM_WEM_ts05n0g41p11s2ssl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts05n0g41p11s2ssl01ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts05n0g41p11s2ssl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts05n0g41p11s2ssl01ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
      ); 
 ///////////////////  end of  N5A High speed     
`define RAM_WEM_ts05p0g41p11sadul02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts05p0g41p11sadul02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts05p0g41p11sadul02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts05p0g41p11sadul02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
// N5A  ultra high density 
`define RAM_WEM_ts05n0g41p11s2dul02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts05n0g41p11s2dul02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts05n0g41p11s2dul02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts05n0g41p11s2dul02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
////  end of  N5A  ultra high density
// N5A   high density 
`define RAM_WEM_ts05n0g41p11s2dcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts05n0g41p11s2dcl02ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts05n0g41p11s2dcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts05n0g41p11s2dcl02ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
////  end of  N5A   high density


    `define RAM_WEM_ts05p0g41p11sagrl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_ts05p0g41p11sagrl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts05p0g41p11sagrl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts05p0g41p11sagrl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
    
    `define RAM_WEM_ts05p0g41p11sacul256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_ts05p0g41p11sacul256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts05p0g41p11sacul256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts05p0g41p11sacul256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
     
`define RAM_WEM_ts05p0g41p11sacrl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_ts05p0g41p11sacrl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts05p0g41p11sacrl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts05p0g41p11sacrl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
 // N5A ts05p0g41p11sacrl256s ->   ts05n0g41p11s2srl256s
 
 `define RAM_WEM_ts05n0g41p11s2srl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_ts05n0g41p11s2srl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts05n0g41p11s2srl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts05n0g41p11s2srl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
 // end of N5A ts05p0g41p11sacrl256s ->   ts05n0g41p11s2srl256s  
 
  // N5A ts05n0g41p11s2srl256s ->   ts05n0g41p11s2crl256s
 
 `define RAM_WEM_ts05n0g41p11s2crl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_ts05n0g41p11s2crl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts05n0g41p11s2crl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts05n0g41p11s2crl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
 // end of N5A ts05n0g41p11s2srl256s->   ts05n0g41p11s2crl256s
  `define RAM_WEM_ts05p0g42p11sasul01ms(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts05p0g42p11sasul01ms(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts05p0g42p11sasul01ms(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts05p0g42p11sasul01ms(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );   
    
    
`define RAM_WEM_ts05p0g42p11sacrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts05p0g42p11sacrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts05p0g42p11sacrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts05p0g42p11sacrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    ); 
    
    // N5A ts05p0g42p11sacrl128s  -> ts05n0g42p11s2crl128s
        
`define RAM_WEM_ts05n0g42p11s2crl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts05n0g42p11s2crl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts05n0g42p11s2crl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts05n0g42p11s2crl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    ); 
    // end of N5A 
      
`define RAM_WEM_ts05p0g42p11sacul256s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts05p0g42p11sacul256s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts05p0g42p11sacul256s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts05p0g42p11sacul256s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );   
   
   //  N5A ts05p0g42p11sacul256s -> ts05n0g42p11s2cul256s
        
`define RAM_WEM_ts05n0g42p11s2cul256s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts05n0g42p11s2cul256s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts05n0g42p11s2cul256s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts05n0g42p11s2cul256s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );   
   //
     
//ts03nxg41p10assvd640sa01/ts03nxg41p10assvd640sa01:       SiWare Single Port High Speed Via MD ROM 1M Sync                               ppa_selector     =  DEF
//ts03nxg41p11sacrl256sa01/ts03nxg41p11sacrl256sa01:      SiWare Single Port High Density and Performance Leakage Control Register File 256K Sync           ppa_selector     =  DEF  /* string Allowed values are: DEF ,HPE dfines the threshold voltage of the transistors in the periphery */ 
//ts03nxg41p11sacul256sa01/ts03nxg41p11sacul256sa01:      SiWare Single Port Ultra High Density and Performance Leakage Control Register File 256K Sync        ppa_selector     =  DEF       /* string Allowed values are: LLE ,DEF ,PE (Req. license) defines the threshold voltage of the transistors in the periphery */
//ts03nxg41p11sadcl1m2sa01p1/ts03nxg41p11sadcl1m2sa01p1:  SiWare Single Port High Density and Performance Leakage Control SRAM 1M Sync                 ppa_selector      =  DEF     /* string Allowed values are: DEF & HPE ,defines the threshold voltage of the transistors in the periphery */ 
//ts03nxg41p11sadul1m2sa01/ts03nxg41p11sadul1m2sa01:      SiWare Single Port Ultra High Density Leakage Control SRAM 1M Sync                       ppa_selector     =  DEF       /* string Allowed values are: LLE ,DEF ,PE defines the threshold voltage of the transistors in the periphery */
//ts03nxg41p11sasrl288sa01p1/ts03nxg41p11sasrl288sa01p1:  SiWare Single Port High Speed Leakage Control Register File 256K Sync                    ppa_selector      =  HPE     /* string Allowed values are: DEF,HPE defines the threshold voltage of the transistors in the periphery */ 
//ts03nxg41p11sassl640sa01/ts03nxg41p11sassl640sa01:      SiWare Single Port High Speed Leakage Control SRAM 512K Sync                         ppa_selector     =  HPE       /* string Allowed values are: HPE & DEF efines the threshold voltage of the transistors in the periphery */ 
//ts03nxg42p11sacul256sa01p1/ts03nxg42p11sacul256sa01p1:  SiWare Pseudo Two Port High Density and Performance Leakage Control Register File 256K Sync           ppa_selector      =  DEF      /* string Allowed values are: LLE ,DF ,HPE defines the threshold voltage of the transistors in the periphery */
//ts03nxg42p11sasrl128a01p1/ts03nxg42p11sasrl128a01p1:  SiWare Two Port High Speed Leakage Control Register File 128K Sync                       ppa_selector      =  HPE      /* string Allowed values are: LLE ,DF ,HPE defines the threshold voltage of the transistors in the periphery */
//ts03nxg42p11sasul640sa01/ts03nxg42p11sasul640sa01:    SiWare Pseudo Two Port High Speed 512K Sync                                      ppa_selector          =  HPE        /* string Allowed values are: HPE & DEF defines the threshold voltage of the transistors in the periphery */ 
`define RAM_ts03nxg41p10assvd640s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts03nxg41p10assvd640s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_ts03nxg41p10assvd640s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .SD(sd), \
      .LS(ls) \
    );
////////////////
    
    `define RAM_WEM_ts03nxg41p11sacrl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
       );
`define RAM_WEM_CD_ts03nxg41p11sacrl256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_ts03nxg41p11sacrl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_CD_ts03nxg41p11sacrl256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
    
`define RAM_ts03nxg41p11sacul256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );

`define RAM_CD_ts03nxg41p11sacul256s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
 `define RAM_WEM_ts03nxg41p11sacul256s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );    
 //////
 `define RAM_WEM_ts03nxg41p11sadcl1m2s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_WEM_CD_ts03nxg41p11sadcl1m2s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_ts03nxg41p11sadcl1m2s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
   );
`define RAM_CD_ts03nxg41p11sadcl1m2s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
   //////////
    //////   
`define RAM_WEM_ts03nxg41p11sadul1m2s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts03nxg41p11sadul1m2s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts03nxg41p11sadul1m2s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts03nxg41p11sadul1m2s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );    
 ///////
 //////
`define RAM_WEM_ts03nxg41p11sasrl288s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
       );
`define RAM_WEM_CD_ts03nxg41p11sasrl288s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_ts03nxg41p11sasrl288s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
`define RAM_CD_ts03nxg41p11sasrl288s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls)\
    );
/////

`define RAM_WEM_ts03nxg41p11sassl640s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_ts03nxg41p11sassl640s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_ts03nxg41p11sassl640s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_ts03nxg41p11sassl640s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
     .CLK(clk), \
      .TPR(1'b0),\
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );    
/////
`define RAM_WEM_ts03nxg42p11sacul256s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts03nxg42p11sacul256s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts03nxg42p11sacul256s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts03nxg42p11sacul256s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );   
        
////
`define RAM_WEM_ts03nxg42p11sasrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts03nxg42p11sasrl128s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts03nxg42p11sasrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts03nxg42p11sasrl128s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );  
////////////

   
  `define RAM_WEM_ts03nxg42p11sasul640s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_WEM_CD_ts03nxg42p11sasul640s(instname,q,write_adr,data,wem,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_ts03nxg42p11sasul640s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );
`define RAM_CD_ts03nxg42p11sasul640s(instname,q,write_adr,data,we,me_wr,clk_wr,read_adr,me_rd,clk_rd,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(we), \
      .MEA(me_wr), \
      .CLKA(clk_wr), \
      .LS(ls), \
      .DS(ds), \
      .SD(sd), \
      .ADRB(read_adr), \
      .MEB(me_rd), \
      .CLKB(clk_rd) \
    );    
       
///  Samsung 8nm  - no ULVT periphery  possible 
//sa08nlg41p10asdv101msa03:periphery_Vt           = LOW         /*string               Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors    */
//sa08nlg41p11sadrl128sa03:periphery_Vt           = LOW           /*string              Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors   */
//sa08nlg41p11sadsl512sa03:periphery_Vt           = LOW         /*string               Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors*/
//sa08nlg41p11sasrl128sa03:periphery_Vt           = LOW           /*string              Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors   */
//sa08nlg41p11sassl512sa03:periphery_Vt           = LOW           /*string              Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors   */
//sa08nlg42p11sacul128sa03:periphery_Vt           = LOW           /*string              Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors   */
//sa08nlg42p11sasrl64ksa03:periphery_Vt           = LOW           /*string              Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors   */
//sa08nlg42p22sassl512sa03:periphery_Vt       =    LOW       /*string               Allowed values are: LOW, STANDARD defines the threshold voltage of the transistors  */

`define ROM_sa08nlg41p10asdv101ms(instname,q,addr,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_sa08nlg41p10asdv101ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_sa08nlg41p10asdv101ms(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_sa08nlg41p10asdv101ms(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .ME(me), \
      .CLK(clk), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_sa08nlg41p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .DS(ds), \
      .SD(sd), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .LS(ls) \
    );
    
    
    
`define RAM_sa08nlg41p11sadrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_sa08nlg41p11sadrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    
   `define RAM_WEM_sa08nlg41p11sadrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_sa08nlg41p11sadrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
     
    

`define RAM_WEM_CD_sa08nlg41p11sadsl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_sa08nlg41p11sadsl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_sa08nlg41p11sadsl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );


////   
`define RAM_WEM_sa08nlg41p11sassl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_sa08nlg41p11sassl512s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_sa08nlg41p11sassl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_sa08nlg41p11sassl512s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
    `define RAM_sa08nlg41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_sa08nlg41p11sasrl128s(instname,q,addr,data,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );

`define RAM_WEM_sa08nlg41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
       );
`define RAM_WEM_CD_sa08nlg41p11sasrl128s(instname,q,addr,data,wem,we,me,clk,ds,sd,ls) \
  instname ( \
      .Q(q), \
      .ADR(addr), \
      .D(data), \
      .WEM(wem), \
      .WE(we), \
      .ME(me), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
//
    
`define RAM_WEM_sa08nlg42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,wem_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem_a), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_WEM_CD_sa08nlg42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,wem_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
       .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEMA(wem_a), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_sa08nlg42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .POFF(2'b00), \
      .SWTE(1'b0), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
`define RAM_CD_sa08nlg42p11sacul128s(instname,q,write_adr,data,mem_en_a,wr_en_a,clk,read_adr,mem_en_b,clk,ds,sd,ls) \
  instname ( \
      .QB(q), \
      .ADRA(write_adr), \
      .DA(data), \
      .WEA(wr_en_a), \
      .MEA(mem_en_a), \
      .MEB(mem_en_b), \
      .CLK(clk), \
      .SWTE(1'b0), \
      .POFF(2'b00), \
      .ADRB(read_adr), \
      .DS(ds), \
      .SD(sd), \
      .LS(ls) \
    );
