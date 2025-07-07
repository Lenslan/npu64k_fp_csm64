// This  will Generate Async clock 
// ip_clk
// op_clk - Is geneated with respect to the op_clk_div_mul_factor 

`include "tb_defines.sv"
interface async_clk_gen_if();

 wire     ip_clk      ; // IP
 bit      op_clk      ; // OP
 realtime clock_period;
 realtime granularity;
 bit      stop;
 int      op_clk_div_mul_factor;
 bit      div_mul;
 int      op_clk_div_mul_factor_d;
 bit      div_mul_d;
 realtime op_clk_period;
 int      max_gran;
 realtime start_time;

 bit start_clock;


 // Start of the out put clock  with respect to the input clock depends on the following parameters
 // Clock frequence=y and granularity ( how many divisions we consider with in one clock) 
 task start_the_clock();
   forever 
   begin
    if (stop) 
    begin
     start_clock = 0;
     stop        = 0;
     break;
    end
    if (op_clk_div_mul_factor_d != op_clk_div_mul_factor || div_mul_d != div_mul)
      init();
    #(op_clk_period / 2)  op_clk = ~op_clk;
   end
 endtask

 task init();
  start_clock = 1;
  //FIXME: this is forced in host_dpi.sv
  //clock_period = `CLK_NS;
  if (clock_period == 0) clock_period = 10;
  if (granularity  == 0) granularity  = 10;
   // Randomize the clock division factor - TODO take theses ranges from IO's
   if (op_clk_div_mul_factor == 0)
    op_clk_div_mul_factor = $urandom_range(1,5);

   if (div_mul) // Division
    op_clk_period     = real'(clock_period * op_clk_div_mul_factor);
   else         // Multipled clock
    op_clk_period     = real'(clock_period / op_clk_div_mul_factor);
   @(posedge ip_clk);
   max_gran = clock_period / granularity;
   start_time = $urandom_range(1,max_gran);
   #(start_time);
   op_clk = 0;
   op_clk_div_mul_factor_d = op_clk_div_mul_factor;
   div_mul_d               = div_mul;
 endtask

 covergroup dbg_apb_clk_ratio_cov @ (posedge ip_clk);
   apb_async_clk_div_fac: coverpoint op_clk_div_mul_factor {
                                                          bins clk_div_mul_factor[] = {1,2,3,4,5};
                                                        } 
  // apb_async_clk_mul_div : coverpoint div_mul;
  //apb_async_clk_mul_div_fac_X_apb_async_clk_mul_div: cross apb_async_clk_mul_div_fac,apb_async_clk_mul_div {
  //                                                        ignore_bins div_1_5 = binsof(apb_async_clk_mul_div)  intersect{1,5} &&  binsof(apb_async_clk_mul_div_fac)  intersect{1};
  //                                                   }
 endgroup

 dbg_apb_clk_ratio_cov  dbg_apb_clk_ratio_cov_inst = new();
 
endinterface
