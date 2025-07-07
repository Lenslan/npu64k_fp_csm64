#include "../npu_mem_utils.hpp"
enum comp_type {CORE=0,GRP=1,SLICE=2};


class sfty_reg_access {

protected :
    long long baddr;
    uint32_t sfty_build_aux_reg, sfty_error_status_reg, sfty_e2e_error_status_reg, sfty_dcls_error_status_reg, sfty_tmr_err_info_reg, sfty_diag_info_reg, sfty_diag_reg;
    comp_type component; 

public :

    //TODO: Add error address for Group level registers
    long long SFTY_PASSWD_ADDR, SFTY_CTRL_ADDR, SFTY_DIAG_ADDR, SFTY_ERROR_STATUS_ADDR, SFTY_E2E_ERROR_STATUS_ADDR , SFTY_DCLS_ERROR_STATUS_ADDR , SFTY_ENABLE_INFO_ADDR, SFTY_DIAG_INFO_ADDR , SFTY_TMR_ERR_INFO_ADDR , SFTY_BUILD_AUX_ADDR, SFTY_BUS_ECC_ERROR_STATUS_ADDR, SFTY_STL_CTRL, NPU_ERP_CTRL, NPU_ESYN, NPU_VM_STATUS0, NPU_VM_STATUS1, NPU_VM_STATUS2, NPU_AM_STATUS0, NPU_AM_STATUS1, NPU_AM_STATUS2, NPU_ESYN_CTRL, NPU_SBE_CNT, NPU_ERP_BUILD , DBANK_ECC_CTRL , SFTY_SB_ERROR_STATUS_ADDR;
    long long cfg_dmi_base;
    int grp, slc , ec; 
    char* comp_name;
    

    void set_comp_name(){
    if(component == CORE )  comp_name = "CORE" ;
    if(component == GRP )  comp_name = "GRP" ;
    if(component == SLICE )  comp_name = "SLICE" ;
    }

    void assign_address() {

        if(component == SLICE){
            SFTY_PASSWD_ADDR =            baddr+SLICE_SFTY_PASSWD;
			SFTY_CTRL_ADDR =			  baddr+SLICE_SFTY_CTRL;
            SFTY_DIAG_ADDR =              baddr+SLICE_SFTY_DIAG;
            SFTY_ERROR_STATUS_ADDR =      baddr+SLICE_SFTY_ERROR_STATUS;
            SFTY_E2E_ERROR_STATUS_ADDR =  baddr+SLICE_SFTY_E2E_ERROR_STATUS;
            SFTY_DCLS_ERROR_STATUS_ADDR = baddr+SLICE_SFTY_DCLS_ERROR_STATUS;
            SFTY_ENABLE_INFO_ADDR =       baddr+SLICE_SFTY_ENABLE_INFO;
            SFTY_DIAG_INFO_ADDR =         baddr+SLICE_SFTY_DIAG_INFO;
            SFTY_TMR_ERR_INFO_ADDR =      baddr+SLICE_SFTY_TMR_ERR_INFO;
            SFTY_BUILD_AUX_ADDR =         baddr+SLICE_SFTY_BUILD_AUX;
            SFTY_STL_CTRL =               baddr+SLICE_SFTY_STL_CTRL; 
            SFTY_SB_ERROR_STATUS_ADDR =   baddr+SLICE_SFTY_SB_ERROR_STATUS;
			SFTY_BUS_ECC_ERROR_STATUS_ADDR = 0xDEAD;
      	    NPU_ERP_CTRL    =    baddr+SLICE_NPU_ERP_CTRL;  	
      	    NPU_ESYN 		=    baddr+SLICE_NPU_ESYN; 	  
      	    NPU_VM_STATUS0	=    baddr+SLICE_NPU_VM_STATUS0;
      	    NPU_VM_STATUS1	=    baddr+SLICE_NPU_VM_STATUS1;
      	    NPU_VM_STATUS2	=    baddr+SLICE_NPU_VM_STATUS2;
      	    NPU_AM_STATUS0	=    baddr+SLICE_NPU_AM_STATUS0;
      	    NPU_AM_STATUS1	=    baddr+SLICE_NPU_AM_STATUS1;
      	    NPU_AM_STATUS2	=    baddr+SLICE_NPU_AM_STATUS2;
      	    NPU_ESYN_CTRL	=    baddr+SLICE_NPU_ESYN_CTRL; 
      	    NPU_SBE_CNT     =    baddr+SLICE_NPU_SBE_CNT;   
      	    NPU_ERP_BUILD   =    baddr+SLICE_NPU_ERP_BUILD; 

		}

        if(component == GRP){
            SFTY_PASSWD_ADDR =            baddr+GRP_SFTY_PASSWD;            
			SFTY_CTRL_ADDR =			  baddr+GRP_SFTY_CTRL;             
            SFTY_DIAG_ADDR =              baddr+GRP_SFTY_DIAG;             
            SFTY_ERROR_STATUS_ADDR =      baddr+GRP_SFTY_ERROR_STATUS;     
            SFTY_E2E_ERROR_STATUS_ADDR =  baddr+GRP_SFTY_E2E_ERROR_STATUS; 
            SFTY_DCLS_ERROR_STATUS_ADDR = baddr+GRP_SFTY_DCLS_ERROR_STATUS;
            SFTY_ENABLE_INFO_ADDR =       baddr+GRP_SFTY_ENABLE_INFO;      
            SFTY_DIAG_INFO_ADDR =         baddr+GRP_SFTY_DIAG_INFO;        
            SFTY_TMR_ERR_INFO_ADDR =      baddr+GRP_SFTY_TMR_ERR_INFO;     
            SFTY_BUILD_AUX_ADDR =         baddr+GRP_SFTY_BUILD_AUX;       
            SFTY_SB_ERROR_STATUS_ADDR =        baddr+GRP_SFTY_SB_ERROR_STATUS; 
            SFTY_STL_CTRL =               0xDEAD;        
            DBANK_ECC_CTRL=               baddr+GRP_DBANK_ECC_CTRL;
            SFTY_SB_ERROR_STATUS_ADDR =   baddr+GRP_SFTY_SB_ERROR_STATUS;
        }

        else if(component == CORE) {
            SFTY_PASSWD_ADDR =            baddr+CORE_SFTY_PASSWD; 
			SFTY_CTRL_ADDR =			  baddr+CORE_SFTY_CTRL;
            SFTY_DIAG_ADDR =              baddr+CORE_SFTY_DIAG;
            SFTY_ERROR_STATUS_ADDR =      baddr+CORE_SFTY_ERROR_STATUS;
            SFTY_E2E_ERROR_STATUS_ADDR =  baddr+CORE_SFTY_E2E_ERROR_STATUS;
            SFTY_DCLS_ERROR_STATUS_ADDR = baddr+CORE_SFTY_DCLS_ERROR_STATUS;
            SFTY_BUS_ECC_ERROR_STATUS_ADDR = baddr+CORE_SFTY_BUS_ECC_ERROR_STATUS;
            SFTY_ENABLE_INFO_ADDR =       baddr+CORE_SFTY_ENABLE_INFO;
            SFTY_DIAG_INFO_ADDR =         baddr+CORE_SFTY_DIAG_INFO;
            SFTY_TMR_ERR_INFO_ADDR =      baddr+CORE_SFTY_TMR_ERR_INFO;
            SFTY_BUILD_AUX_ADDR =         baddr+CORE_SFTY_BUILD_AUX;
            SFTY_SB_ERROR_STATUS_ADDR =        baddr+CORE_SFTY_SB_ERROR_STATUS; 
            SFTY_STL_CTRL =               0xDEAD; 
            SFTY_SB_ERROR_STATUS_ADDR =   baddr+CORE_SFTY_SB_ERROR_STATUS;
        }
        
    }
    
    sfty_reg_access(comp_type component,int G=0,int S=0)
    {
        this->component = component;
        this->cfg_dmi_base = CFG_DMI_BASE;
        this->grp = G ;
        this->slc = S ;
        this->ec = 0;
        set_baddr();
        this->assign_address();
        this->set_comp_name();
        //cout << "comp_name" << comp_name << endl;
    }
    
    sfty_reg_access()
    {
    //dummy constructor
    }

    virtual void set_baddr()
    {
        if (component == CORE ) {
            baddr = cfg_dmi_base + 0x84000; 
        }
        else if (component == SLICE ) {
            baddr = cfg_dmi_base + grp*0x20000 + 0x4000 +slc*0x2000;
        }
        else if (component == GRP ) {
            baddr  = cfg_dmi_base + grp* 0x20000;
        }
    }

    void print_rw_info(char * type,char* addr_name, long long addr, uint32_t val)
    {
        if(type == "READ_REG" || type == "DMI READ_REG" )
        {
            if(component == SLICE ) printf("[%s] %s G%dS%d- %s [ %llX ] %x \n",comp_name,type,grp,slc,addr_name, addr, val);  
            if(component == GRP ) printf("[%s] %s G%d- %s [ %llX ] %x \n",comp_name,type,grp,addr_name, addr, val);  
            if(component == CORE ) printf("[%s] %s - %s [ %llX ] %x \n",comp_name,type,addr_name, addr, val);  
        }
        if(type == "WRITE_REG" ||type == "DMI WRITE_REG" )
        {
            if(component == SLICE ) printf("[%s] %s G%dS%d- %s [ %llX ] %x \n",comp_name,type,grp,slc,addr_name, addr, val);  
            if(component == GRP ) printf("[%s] %s G%d- %s [ %llX ] %x \n",comp_name,type,grp,addr_name, addr, val);  
            if(component == CORE ) printf("[%s] %s - %s [ %llX ] %x \n",comp_name,type,addr_name, addr, val);  
        }
        
    }

    virtual uint32_t  read_reg(char* addr_name,long long addr)
    {
        uint32_t readval;
        readval = cfg_dmi_read((long long*)(addr));
        //this->print_rw_info("READ_REG",addr_name,addr,readval);
        return readval;
    }
    
    virtual void write_reg(char* addr_name,long long addr,uint32_t data)
    {
        cfg_dmi_write((long long*) addr,data);
        //this->print_rw_info("WRITE_REG",addr_name,addr,data);
    }

    void write_with_password(char* addr_name,long long addr,uint32_t data)
    {
        this->write_reg("SFTY_PASSWD",this->SFTY_PASSWD_ADDR,0x2);
        this->write_reg(addr_name,addr,data);
    }
	
	void write_with_password_rd(char* addr_name,long long addr,uint32_t data)
    {
        this->write_reg("SFTY_PASSWD",this->SFTY_PASSWD_ADDR,0x2);
		read_reg("SFTY_PASSWD",this->SFTY_PASSWD_ADDR);
        this->write_reg(addr_name,addr,data);
		read_reg(addr_name,addr);
		read_reg("SFTY_PASSWD",this->SFTY_PASSWD_ADDR);

    }
   void write_with_password_rand_seq(char* addr_name,long long addr,uint32_t data)
    {
        this->write_reg("SFTY_PASSWD",this->SFTY_PASSWD_ADDR,0x2);
        this->write_reg("SFTY_PASSWD",this->SFTY_PASSWD_ADDR,0x2);
		read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
		set_expect_resp(2);
		write_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR,0xFF);
		set_expect_resp(0);
        this->write_reg(addr_name,addr,data);
		if(addr == this->SFTY_STL_CTRL || addr == this->SFTY_SB_ERROR_STATUS_ADDR) {
			set_expect_resp(0);}
		else {
		set_expect_resp(2);
		}
        this->write_reg(addr_name,addr,data);
        set_expect_resp(0);
        this->write_reg("SFTY_PASSWD",this->SFTY_PASSWD_ADDR,0x2);
		read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
		set_expect_resp(2);
		write_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR,0xFF);
		set_expect_resp(0);
        this->write_reg(addr_name,addr,data);
    }

    void check_sfty_enb_condition(){
    if (component == SLICE ){
       while((read_reg("SFTY_ENABLE_INFO",this->SFTY_ENABLE_INFO_ADDR)) != 0x3F); 
        }
    if (component == CORE ){
       while(((read_reg("SFTY_ENABLE_INFO",this->SFTY_ENABLE_INFO_ADDR)) & 0x1F) != 0x1F);
        }
    if (component == GRP ){
       while((read_reg("SFTY_ENABLE_INFO",this->SFTY_ENABLE_INFO_ADDR) & 0xF) == 0x0);
       while(((read_reg("SFTY_ENABLE_INFO",this->SFTY_ENABLE_INFO_ADDR)) & 0x3FFF0) != 0x3FFF0);
        }

    }
 
    int has_hw_err_inj_en()
    {
        uint32_t bit_check;
        uint32_t dummy_num = 1;
        if(component == CORE )  bit_check = 15 ;
        if(component == GRP )  bit_check = 15 ;
        if(component == SLICE )  bit_check = 15 ;
		if (((read_reg("SFTY_BUILD_AUX",this->SFTY_BUILD_AUX_ADDR)) & (dummy_num << bit_check)) == (dummy_num << bit_check )) {
            cout << "INFO: HW ERR INJ IS PRESENT IN THE BUILD";
            return 1;
        }
        else {
            cout << "INFO: HW ERR INJ IS NOT PRESENT IN THE BUILD";
            return 0;
        };

        
    }
   void program_hw_err_inj(uint32_t val)
    {
        long long addr = this->SFTY_DIAG_ADDR;
        if(has_hw_err_inj_en() == 1){
            check_sfty_enb_condition(); 
            cout << "INFO: Driving lock reset" << endl;
            write_with_password("SFTY_DIAG",addr,0x95555556);
            cout << "INFO: Program the diag register" << endl;
            write_with_password("SFTY_DIAG",addr,val);
            cout << "INFO: Wait for End of Injection i.e poll for error status register" << endl; 
            while((read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR)& 0x80000000)== 0 ){
            read_reg("SFTY_DIAG_INFO",this->SFTY_DIAG_INFO_ADDR);
            }
            cout << "INFO: Disabling Safety" << endl;
            write_with_password("SFTY_CTRL",this->SFTY_CTRL_ADDR,0x00000001);
            cout << "INFO: Driving lock reset" << endl;
            write_with_password("SFTY_DIAG",addr,0x95555556);
            cout << "INFO: Disable HW error injection" << endl;
            write_with_password("SFTY_DIAG",addr,0x55555555);
            write_with_password("SFTY_CTRL",this->SFTY_CTRL_ADDR,0x00000002);
            for (int i=0; i<2 ; i++) {
            if(read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR)!=0)
            ec++;
            }
        }
    }

     virtual void program_hw_err_inj_disable_en(uint32_t val)
    {
        long long addr = this->SFTY_DIAG_ADDR;
        if(has_hw_err_inj_en() == 1){
           // check_sfty_enb_condition(); 
            cout << "INFO: Driving lock reset" << endl;
            write_with_password("SFTY_DIAG",addr,0x95555556);
            cout << "INFO: Program the diag register" << endl;
            write_with_password("SFTY_DIAG",addr,val);
            cout << "INFO: Wait for End of Injection i.e poll for error status register" << endl; 
            while((read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR)& 0x80000000)== 0 ){
            read_reg("SFTY_DIAG_INFO",this->SFTY_DIAG_INFO_ADDR);
            }
            cout << "INFO: Disabling Safety" << endl;
            write_with_password("SFTY_CTRL",this->SFTY_CTRL_ADDR,0x00000001);
            cout << "INFO: Driving lock reset" << endl;
            write_with_password("SFTY_DIAG",addr,0x95555556);
            cout << "INFO: Disable HW error injection" << endl;
            write_with_password("SFTY_DIAG",addr,0x55555555);
            write_with_password("SFTY_CTRL",this->SFTY_CTRL_ADDR,0x00000002);
            for (int i=0; i<2 ; i++) {
            if(read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR)!=0)
            ec++;
            }
        }
    }

	void rd_after_write(char* addr_name,long long addr,uint32_t data)
	{
        this->write_reg("SFTY_PASSWD",this->SFTY_PASSWD_ADDR,0x2);
        this->write_reg(addr_name,addr,data);
		this->read_reg(addr_name,addr);
	}
	
	void passwd_with_safety_diag_non_dual_write (uint32_t wdata)
	{
		long long addr = this-> SFTY_DIAG_ADDR;
        write_with_password("SFTY_DIAG",addr,wdata);
		read_reg("SFTY_DIAG",this->SFTY_DIAG_ADDR);
		//run_cycles(3);
		read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
        write_with_password("SFTY_DIAG",addr,0x55555556);
		read_reg("SFTY_DIAG",this->SFTY_DIAG_ADDR);
		//run_cycles(3);
		read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
	}
   	void safety_passwd_non_dual_write (uint32_t wdata)
	{
		long long addr = this-> SFTY_PASSWD_ADDR;
        write_reg("SFTY_PASSWD",addr,wdata);
		read_reg("SFTY_PASSWD",this->SFTY_PASSWD_ADDR);
		//run_cycles(3);
		read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
        write_reg("SFTY_PASSWD",addr,0x2);
		read_reg("SFTY_PASSWD",this->SFTY_PASSWD_ADDR);
		//run_cycles(3);
		read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
        write_with_password("SFTY_DIAG",this->SFTY_DIAG_ADDR,0x55555556);
		//run_cycles(3);
		read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);

	}
	void passwd_with_safety_stl_non_dual_write (uint32_t wdata)
	{
		long long addr = this-> SFTY_STL_CTRL;
        write_with_password("SFTY_STL_CTRL",addr,wdata);
		read_reg("SFTY_STL_CTRL",this->SFTY_STL_CTRL);
		//run_cycles(3);
		read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
        write_with_password("SFTY_STL_CTRL",addr,0x50000000);
		read_reg("SFTY_STL_CTRL",this->SFTY_STL_CTRL);
		//run_cycles(3);
		read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
        write_with_password("SFTY_DIAG",this->SFTY_DIAG_ADDR,0x55555556);
		//run_cycles(3);
		read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
	//	read_value = mem_read (&sfty_ctrl_regs->npu_sfty_stl_ctrl);
 	//	cout << "DEBUG: read value of addr" << &sfty_ctrl_regs->npu_sfty_stl_ctrl << "read value is " << read_value << endl;   
	}
	void passwd_with_safety_ctrl_non_dual_write (uint32_t wdata)
	{
		long long addr = this-> SFTY_CTRL_ADDR;
        write_with_password("SFTY_CTRL",addr,wdata);
		read_reg("SFTY_CTRL",this->SFTY_CTRL_ADDR);
		//run_cycles(3);
		read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
        write_with_password("SFTY_CTRL",addr,0x00000001);
		read_reg("SFTY_CTRL",this->SFTY_CTRL_ADDR);
        write_with_password("SFTY_DIAG",this->SFTY_DIAG_ADDR,0x55555556);

        write_with_password("SFTY_CTRL",addr,wdata);
		read_reg("SFTY_CTRL",this->SFTY_CTRL_ADDR);
		//run_cycles(3);
		read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
        write_with_password("SFTY_CTRL",addr,0x00000002);
		read_reg("SFTY_CTRL",this->SFTY_CTRL_ADDR);
		//run_cycles(3);
		read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
        write_with_password("SFTY_DIAG",this->SFTY_DIAG_ADDR,0x55555556);
		read_reg("SFTY_CTRL",this->SFTY_CTRL_ADDR);
		//run_cycles(3);
		read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
	//	read_value = mem_read (&sfty_ctrl_regs->npu_sfty_stl_ctrl);
 	//	cout << "DEBUG: read value of addr" << &sfty_ctrl_regs->npu_sfty_stl_ctrl << "read value is " << read_value << endl;   
	}

    // add for ss test
    uint32_t  read_sfty_enable_reg ()
    {
        uint32_t readval;

        readval = read_reg("SFTY_ENABLE_INFO",this->SFTY_ENABLE_INFO_ADDR);
        //this->print_rw_info("READ_REG","SFTY_ENABLE_INFO",this->SFTY_ENABLE_INFO_ADDR,readval);
        return readval;
    }
    
    void write_diag (uint32_t data)
    {
        this->write_reg("SFTY_PASSWD",this->SFTY_PASSWD_ADDR,0x2);
        this->write_reg("SFTY_DIAG",this->SFTY_DIAG_ADDR,data);
    }
    

    void check_l2_sfty_regs () { // 
        uint32_t readval;
    
        readval = read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR,readval);
        readval = read_reg("SFTY_E2E_ERROR_STATUS",this->SFTY_E2E_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_E2E_ERROR_STATUS",this->SFTY_E2E_ERROR_STATUS_ADDR ,readval);
        readval = read_reg("SFTY_DCLS_ERROR_STATUS",this->SFTY_DCLS_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_DCLS_ERROR_STATUS",this->SFTY_DCLS_ERROR_STATUS_ADDR,readval);
        readval = read_reg("SFTY_BUS_ECC_ERROR_STATUS",this->SFTY_BUS_ECC_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_BUS_ECC_ERROR_STATUS",this->SFTY_BUS_ECC_ERROR_STATUS_ADDR,readval);
        readval = read_reg("SFTY_TMR_ERR_INFO",this->SFTY_TMR_ERR_INFO_ADDR);
        print_rw_info("READ_REG","SFTY_TMR_ERR_INFO",this->SFTY_TMR_ERR_INFO_ADDR,readval);
        readval = read_reg("SFTY_SB_ERROR_STATUS",this->SFTY_SB_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_SB_ERROR_STATUS",this->SFTY_SB_ERROR_STATUS_ADDR,readval);
    }
    
    void check_grp_sfty_regs () { // 
        uint32_t readval;
    
        readval = read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR,readval);
        readval = read_reg("SFTY_E2E_ERROR_STATUS",this->SFTY_E2E_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_E2E_ERROR_STATUS",this->SFTY_E2E_ERROR_STATUS_ADDR ,readval);
        readval = read_reg("SFTY_DCLS_ERROR_STATUS",this->SFTY_DCLS_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_DCLS_ERROR_STATUS",this->SFTY_DCLS_ERROR_STATUS_ADDR,readval);
        readval = read_reg("SFTY_TMR_ERR_INFO",this->SFTY_TMR_ERR_INFO_ADDR);
        print_rw_info("READ_REG","SFTY_TMR_ERR_INFO",this->SFTY_TMR_ERR_INFO_ADDR,readval);
        readval = read_reg("SFTY_SB_ERROR_STATUS",this->SFTY_SB_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_SB_ERROR_STATUS",this->SFTY_SB_ERROR_STATUS_ADDR,readval);
        readval = read_reg("DBANK_ECC_ERROR",this->DBANK_ECC_CTRL);
        print_rw_info("READ_REG","DBANK_ECC_ERROR",this->DBANK_ECC_CTRL,readval);

    }
    
    void check_slc_sfty_regs () { // 
        uint32_t readval;
    
        readval = read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR,readval);
        readval = read_reg("SFTY_E2E_ERROR_STATUS",this->SFTY_E2E_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_E2E_ERROR_STATUS",this->SFTY_E2E_ERROR_STATUS_ADDR ,readval);
        readval = read_reg("SFTY_DCLS_ERROR_STATUS",this->SFTY_DCLS_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_DCLS_ERROR_STATUS",this->SFTY_DCLS_ERROR_STATUS_ADDR,readval);
        readval = read_reg("SFTY_TMR_ERR_INFO",this->SFTY_TMR_ERR_INFO_ADDR);
        print_rw_info("READ_REG","SFTY_TMR_ERR_INFO",this->SFTY_TMR_ERR_INFO_ADDR,readval);
        readval = read_reg("SFTY_SB_ERROR_STATUS",this->SFTY_SB_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_SB_ERROR_STATUS",this->SFTY_SB_ERROR_STATUS_ADDR,readval);
        readval = read_reg("NPU_ERP_CTRL",this->NPU_ERP_CTRL);
        print_rw_info("READ_REG","NPU_ERP_CTRL",this->NPU_ERP_CTRL,readval);
        readval = read_reg("NPU_SBE_CNT",this->NPU_SBE_CNT);
        print_rw_info("READ_REG","NPU_SBE_CNT",this->NPU_SBE_CNT,readval);

    }
    
    uint32_t check_l2_err_sta_regs (uint32_t expval) { // 
        uint32_t readval;
    
        readval = read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR,readval);

        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }
    }
    
    uint32_t check_l2_e2e_err_regs (uint32_t expval) { // 
        uint32_t readval;
        
        readval = read_reg("SFTY_E2E_ERROR_STATUS",this->SFTY_E2E_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_E2E_ERROR_STATUS",this->SFTY_E2E_ERROR_STATUS_ADDR ,readval);
        
        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }
    }
    
    uint32_t check_l2_dcls_err_regs (uint32_t expval) { // 
        uint32_t readval;
        
        readval = read_reg("SFTY_DCLS_ERROR_STATUS",this->SFTY_DCLS_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_DCLS_ERROR_STATUS",this->SFTY_DCLS_ERROR_STATUS_ADDR,readval);
        
        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }
    }
    
    uint32_t check_l2_bus_ecc_regs (uint32_t expval) { // 
        uint32_t readval;
        
        readval = read_reg("SFTY_BUS_ECC_ERROR_STATUS",this->SFTY_BUS_ECC_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_BUS_ECC_ERROR_STATUS",this->SFTY_BUS_ECC_ERROR_STATUS_ADDR,readval);
        
        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }
    }
    
    uint32_t check_l2_tmr_err_regs (uint32_t expval) { // 
        uint32_t readval;
        
        readval = read_reg("SFTY_TMR_ERR_INFO",this->SFTY_TMR_ERR_INFO_ADDR);
        print_rw_info("READ_REG","SFTY_TMR_ERR_INFO",this->SFTY_TMR_ERR_INFO_ADDR,readval);
        
        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }
    }
    
    uint32_t check_l2_sb_err_regs (uint32_t expval) { // 
        uint32_t readval;
        
        readval = read_reg("SFTY_SB_ERROR_STATUS",this->SFTY_SB_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_SB_ERROR_STATUS",this->SFTY_SB_ERROR_STATUS_ADDR,readval);
        
        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }
    }
    
    uint32_t check_grp_err_sta_regs (uint32_t expval) { // 
        uint32_t readval;
    
        readval = read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR,readval);
        
        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }
    }
    
    uint32_t check_grp_e2e_err_regs (uint32_t expval) { // 
        uint32_t readval;
    
        readval = read_reg("SFTY_E2E_ERROR_STATUS",this->SFTY_E2E_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_E2E_ERROR_STATUS",this->SFTY_E2E_ERROR_STATUS_ADDR ,readval);
        
        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }
    }
    
    uint32_t check_grp_dcls_err_regs (uint32_t expval) { // 
        uint32_t readval;
        
        readval = read_reg("SFTY_DCLS_ERROR_STATUS",this->SFTY_DCLS_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_DCLS_ERROR_STATUS",this->SFTY_DCLS_ERROR_STATUS_ADDR,readval);
        
        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }
    }
    
    uint32_t check_grp_tmr_err_regs (uint32_t expval) { // 
        uint32_t readval;

        readval = read_reg("SFTY_TMR_ERR_INFO",this->SFTY_TMR_ERR_INFO_ADDR);
        print_rw_info("READ_REG","SFTY_TMR_ERR_INFO",this->SFTY_TMR_ERR_INFO_ADDR,readval);
        
        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }
    }
    
    uint32_t check_grp_sb_err_regs (uint32_t expval) { // 
        uint32_t readval;

        readval = read_reg("SFTY_SB_ERROR_STATUS",this->SFTY_SB_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_SB_ERROR_STATUS",this->SFTY_SB_ERROR_STATUS_ADDR,readval);
        
        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }
    }
    
    uint32_t check_grp_dbnk_regs (uint32_t expval) { // 
        uint32_t readval;

        readval = read_reg("DBANK_ECC_ERROR",this->DBANK_ECC_CTRL);
        print_rw_info("READ_REG","DBANK_ECC_ERROR",this->DBANK_ECC_CTRL,readval);
        
        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }

    }
    
    uint32_t check_slc_err_sta_regs (uint32_t expval) { // 
        uint32_t readval;
    
        readval = read_reg("SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_ERROR_STATUS",this->SFTY_ERROR_STATUS_ADDR,readval);
        
        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }
    }
    
    uint32_t check_slc_e2e_err_regs (uint32_t expval) { // 
        uint32_t readval;
    

        readval = read_reg("SFTY_E2E_ERROR_STATUS",this->SFTY_E2E_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_E2E_ERROR_STATUS",this->SFTY_E2E_ERROR_STATUS_ADDR ,readval);
        
        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }
    }
    
    uint32_t check_slc_dcls_err_regs (uint32_t expval) { // 
        uint32_t readval;

        readval = read_reg("SFTY_DCLS_ERROR_STATUS",this->SFTY_DCLS_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_DCLS_ERROR_STATUS",this->SFTY_DCLS_ERROR_STATUS_ADDR,readval);
        
        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }
    }
    
    uint32_t check_slc_tmr_err_regs (uint32_t expval) { // 
        uint32_t readval;

        readval = read_reg("SFTY_TMR_ERR_INFO",this->SFTY_TMR_ERR_INFO_ADDR);
        print_rw_info("READ_REG","SFTY_TMR_ERR_INFO",this->SFTY_TMR_ERR_INFO_ADDR,readval);
        
        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }
    }
    
    uint32_t check_slc_sb_err_regs (uint32_t expval) { // 
        uint32_t readval;

        readval = read_reg("SFTY_SB_ERROR_STATUS",this->SFTY_SB_ERROR_STATUS_ADDR);
        print_rw_info("READ_REG","SFTY_SB_ERROR_STATUS",this->SFTY_SB_ERROR_STATUS_ADDR,readval);
        
        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }
    }
    
    uint32_t check_slc_erp_ctrl_regs (uint32_t expval) { // 
        uint32_t readval;

        readval = read_reg("NPU_ERP_CTRL",this->NPU_ERP_CTRL);
        print_rw_info("READ_REG","NPU_ERP_CTRL",this->NPU_ERP_CTRL,readval);
        
        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }
    }
    
    uint32_t check_slc_sbe_cnt_regs (uint32_t expval) { // 
        uint32_t readval;

        readval = read_reg("NPU_SBE_CNT",this->NPU_SBE_CNT);
        print_rw_info("READ_REG","NPU_SBE_CNT",this->NPU_SBE_CNT,readval);
        
        if (expval != readval) {
            return 1;
        } else {
            return 0; 
        }

    }

    
};


class sfty_dmi_reg_access : public sfty_reg_access 
{
  public:  
    sfty_dmi_reg_access(comp_type component,int G=0,int S=0)
    {
        this->component = component;
        this->cfg_dmi_base = NPX_DMI_BASE;
        this->grp = G ;
        this->slc = S ;
        this->ec = 0;
        set_baddr();
        this->assign_address();
        this->set_comp_name();
        cout << "comp_name" << comp_name << endl;
    }

    uint32_t  read_reg(char* addr_name,long long addr)
    {
        uint32_t readval;   
        cout << "READ REG "<<  addr << endl;

        readval = mem_read((long long*)(addr));
        //this->print_rw_info("DMI READ_REG",addr_name,addr,readval);
        return readval;
    }
    
    void write_reg(char* addr_name,long long addr,uint32_t data)
    {
        cout << "WRITE REG "<< addr << endl;
        do_write((uint32_t *) addr,(int)1,(uint32_t)data);
        //this->print_rw_info("DMI WRITE_REG",addr_name,addr,data);
    }

    void set_baddr()
    {   // dmi access is only for slice registers
        if (component == CORE ) {
           // baddr = cfg_dmi_base + 0x84000;  
        }
        else if (component == SLICE ) {
            //baddr = cfg_dmi_base +   grp*0x1000000 + slc * 0x400000 + L1_SFTY_MMIO_OFFSET;
            baddr = NPX_DMI_BASE+ 0x00084000 + 0x00400000 * (grp*4+slc);
        }
        else if (component == GRP ) {
            //baddr  = cfg_dmi_base + grp* 0x20000;
        }
    }

};
void wr_arcsync_aux_addr (char* addr_name, int offset, int data) {
  int* ptr;
  ptr = ARCSYNC_BASE + offset;
  cfg_arcsync_write(ptr, data);
  printf("[ARCSYNC] WRITE_REG - %s [ %llX ] %x \n",addr_name, ptr, data);
}

int rd_arcsync_aux_addr (char* addr_name, int offset) {
  int* ptr;
  int data;
  ptr = ARCSYNC_BASE + offset;
  data = cfg_arcsync_read((int*)ptr);
  printf("[ARCSYNC] READ_REG - %s [ %llX ] %x \n",addr_name, ptr, data);
  return data;
}

void wr_with_pwd_arcsync_aux_addr (char* addr_name, int offset, int data) {
  int* ptr;
  ptr = ARCSYNC_BASE + offset;
  wr_arcsync_aux_addr ("ARCSYNC_SFTY_PWD",ARCSYNC_SFTY_PASSWD,2);
  cfg_arcsync_write(ptr, data);
  printf("[ARCSYNC] WRITE_REG - %s [ %llX ] %x \n",addr_name, ptr, data);
}

void passwd_with_arcsync_safety_ctrl_non_dual_write (uint32_t wdata)
	{
		long long addr = ARCSYNC_SFTY_CTRL;
        //writing non-dualrail values 
        wr_with_pwd_arcsync_aux_addr("ARCSYNC_SFTY_CTRL",addr,wdata);
		rd_arcsync_aux_addr("ARCSYNC_SFTY_CTRL",ARCSYNC_SFTY_CTRL);
        rd_arcsync_aux_addr("ARCSYNC_SFTY_STATUS",ARCSYNC_SFTY_STATUS);
        wr_with_pwd_arcsync_aux_addr("ARCSYNC_SFTY_CTRL",ARCSYNC_SFTY_CTRL,2);

        // lock reset
		wr_with_pwd_arcsync_aux_addr("ARCSYNC_SFTY_DIAG",ARCSYNC_SFTY_DIAG,0x55555556);
        rd_arcsync_aux_addr("ARCSYNC_SFTY_STATUS",ARCSYNC_SFTY_STATUS);

        rd_arcsync_aux_addr("ARCSYNC_SFTY_CTRL",ARCSYNC_SFTY_CTRL);

	}

void passwd_with_arcsync_safety_diag_non_dual_write (uint32_t wdata)
	{
		long long addr = ARCSYNC_SFTY_DIAG;
        //writing non-dualrail values 
        wr_with_pwd_arcsync_aux_addr("ARCSYNC_SFTY_DIAG",addr,wdata);
		rd_arcsync_aux_addr("ARCSYNC_SFTY_DIAG",ARCSYNC_SFTY_DIAG);
        rd_arcsync_aux_addr("ARCSYNC_SFTY_STATUS",ARCSYNC_SFTY_STATUS);
        
        // lock reset
		wr_with_pwd_arcsync_aux_addr("ARCSYNC_SFTY_DIAG",ARCSYNC_SFTY_DIAG,0x55555556);
        rd_arcsync_aux_addr("ARCSYNC_SFTY_STATUS",ARCSYNC_SFTY_STATUS);

        
	}

void passwd_with_arcsync_safety_pswd_non_dual_write (uint32_t wdata)
	{
		long long addr = ARCSYNC_SFTY_PASSWD;
        //writing non-dualrail values 
        wr_arcsync_aux_addr("ARCSYNC_SFTY_PASSWD",addr,wdata);
		rd_arcsync_aux_addr("ARCSYNC_SFTY_PASSWD",ARCSYNC_SFTY_PASSWD);
        rd_arcsync_aux_addr("ARCSYNC_SFTY_STATUS",ARCSYNC_SFTY_STATUS);
        wr_arcsync_aux_addr("ARCSYNC_SFTY_PASSWD",ARCSYNC_SFTY_PASSWD,2);

        // lock reset
		wr_with_pwd_arcsync_aux_addr("ARCSYNC_SFTY_DIAG",ARCSYNC_SFTY_DIAG,0x55555556);
        rd_arcsync_aux_addr("ARCSYNC_SFTY_STATUS",ARCSYNC_SFTY_STATUS);

        rd_arcsync_aux_addr("ARCSYNC_SFTY_PASSWD",ARCSYNC_SFTY_PASSWD);

	}

