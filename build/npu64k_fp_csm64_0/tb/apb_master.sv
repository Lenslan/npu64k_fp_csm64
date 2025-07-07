interface apb_master();

logic          PCLK   ;
logic          PRESETn;
logic  [31:0]  PADDR  ; 
logic          PWRITE ;
logic          PSEL   ;
logic          PENABLE;
logic  [31:0]  PWDATA ;

logic  [31:0]  PRDATA ;
logic          PREADY ;
logic          PSLVERR;


 bit [9:0] pready_count;

initial
begin
 forever
 begin
  if (PRESETn == 0)
  begin
   #0;
   PADDR    = 32'b0;
   PWRITE   = 1'b0 ;
   PSEL     = 1'b0 ;
   PENABLE  = 1'b0 ;
   PWRITE   = 1'b0 ;
   PWDATA   = 32'b0;
  end
  @ (posedge PCLK);
 end
end


//==========================================================
// Write APB task which takes ADDRESS and DATA and drives
// APB 
//==========================================================
task write_apb(input bit [31:0] ADDR,input bit [31:0] DATA);
  check_reset();
  setup_phase(ADDR,1'b1,DATA);
  access_phase();
  PSEL    = 1'b0;
  PENABLE = 1'b0;
  PWRITE  = 1'b0;
endtask
//==========================================================

//==========================================================
// Read APB task which takes ADDRESS and DATA and drives
// APB 
//==========================================================
task read_apb(input bit [31:0] ADDR,output bit [31:0] DATA);
  check_reset();
  setup_phase(ADDR,1'b0);
  access_phase();
  DATA    = PRDATA;
  PSEL    = 1'b0;
  PENABLE = 1'b0;
endtask
//==========================================================


//==========================================================
// Remain Here untill reset is released
//==========================================================
task check_reset();
forever 
begin
 if (PRESETn == 1) break;
 @(posedge PCLK);
 #0;
end
endtask
//==========================================================

//==========================================================
// Setup Phase 
//==========================================================
task setup_phase(input bit [31:0] ADDR, input bit WR,input bit [31:0] DATA=0);
 @(posedge PCLK);
 #0;
 PADDR   = ADDR;
 PWRITE  = WR;
 PSEL    = 1;
 if (WR)
  PWDATA = DATA;
endtask
//==========================================================

//==========================================================
// Access Phase 
//==========================================================
task access_phase();
 @(posedge PCLK);
 #0;
 PENABLE = 1;
 check_for_ready();
endtask
//==========================================================

//==========================================================
// Check for ready 
//==========================================================
task check_for_ready();
 pready_count = 0;
 @(posedge PCLK);
 #0;
 if (PREADY == 0)
 begin
   forever
   begin
    @(posedge PCLK);
    #0;
    pready_count++;
    if (PREADY == 1 || pready_count > 300)
    begin
     //if (pready_count > 300)
     // $error($time," DID NOT GET PREADY FROM APB SLAVE ");
     break;
    end
   end
 end
 //if (PSLVERR)
 //  $error($time," GOT SLAVE ERROR FOR APB ADDRESS %0h ",PADDR);
endtask
//==========================================================


endinterface
