module Project2Sim();
    reg      Clock;
    reg     reset;
    wire IROut;
    wire timer_out;
    wire ARF_outD, memwr, irlh, iren, irfun, arfreg, arffun, timerfun, mem_ref_op,  opcode,
              addressing,
              regsel, 
              op_address,
              destreg,
              srcreg1,
              srcreg2,
              IRhalf,
              PCOut;
              assign PCOut=comp.alusys.arf1.PCOut;
    assign mem_ref_op=comp.mem_ref_op;
    assign opcode=comp.opcode;
    assign addressing=comp.addressing;
    assign regsel=comp.regsel;
    assign op_address=comp.op_address;
    assign destreg=comp.destreg;
    assign srcreg1=comp.srcreg1;
    assign srcreg2=comp.srcreg2;
    assign memwr= comp.Mem_WR;
    assign irlh=comp.IR_LH;
    assign iren= comp.IR_Enable;
    assign irfun=comp.IR_Funsel;
    assign arfreg= comp.ARF_RegSel;
    assign arffun=comp.ARF_FunSel;
    assign timerfun= comp.timerFunSel;
    assign IRhalf=comp.IRhalf;
    
    assign ARF_outD= comp.ARF_OutDSel;
    assign IROut= comp.IR_Out;
    assign timer_out=comp.timerOut;
    //Clock Signal Generation
    always 
    begin
        Clock = 1; #5; Clock = 0; #5; // 10ns period
    end
    
    //reset at start
    initial 
    begin
        reset = 1; #10; reset = 0;
    end
    
    //total operation takes 1085 ns, if testing a code different from given in the hw, delete or change the waiting time
   
    
    //print after each timerFunSel + 10ns
    //this is not reliable and might show results that will be updated in the next tick, but at that time opcode etc. resets
    //correct results can be seen from the simulation graph
    
    always @(posedge comp.timerFunSel)
    begin
        #10;
        $display("SEcuence Counter: %d", comp.timerOut);
       $display("Register File: OutASel: %d, OutBSel: %d, FunSel: %b, Regsel: %b", comp.RF_OutASel, comp.RF_OutBSel, comp.RF_FunSel, comp.RF_RegSel);            
       $display("ALU FunSel: %b", comp.ALU_FunSel);
        $display("Addres Register File: OutCSel: %d, OutDSel: %d, FunSel: %b, Regsel: %b", comp.ARF_OutCSel, comp.ARF_OutDSel, comp.ARF_FunSel, comp.ARF_RegSel);            
        $display("Instruction Register: LH: %d, Enable: %d, FunSel: %b", comp.IR_LH, comp.IR_Enable, comp.IR_Funsel);            
       $display("Memory: WR: %d, CS: %d", comp.Mem_WR, comp.Mem_CS);
        $display("MuxASel: %b, MuxBSel: %b, MuxCSel: %b", comp.MuxASel, comp.MuxBSel, comp.MuxCSel);
        
        $display("");
        $display("Register File: AOut: %d, BOut: %d", comp.AOut, comp.BOut);            
        $display("ALUOut: %d, ALUOutFlag: %b, ALUOutFlags: Z:%d, C:%d, N:%d, O:%d,", comp.ALUOut, comp.ALUOutFlag, comp.ALUOutFlag[3],comp.ALUOutFlag[2],comp.ALUOutFlag[1],comp.ALUOutFlag[0]);
        $display("Address Register File: COut: %d, DOut (Address): %d", comp.ARF_COut, comp.Address);            
        $display("Memory Out: %d", comp.MemoryOut);            
        $display("IROut: %h", comp.IR_Out);
        $display("MuxAOut: %d, MuxBOut: %d, MuxCOut: %d", comp.MuxAOut, comp.MuxBOut, comp.MuxCOut);
        
        $display("");
        $display("opcode: %h", comp.opcode);
        if(comp.mem_ref_op)
        begin
            $display("adressing: %b", comp.addressing);   
            $display("op address: %h", comp.op_address);
            $display("regsel: %h", comp.regsel);
        end
        else
        begin
            $display("destreg: %b, srcreg1: %b, srcreg2: %b", comp.destreg, comp.srcreg1, comp.srcreg2);
        end
        $display("R1: %h, R2: %h, R3: %h, R4: %h", comp.alusys.rf.R1O, comp.alusys.rf.R2O, comp.alusys.rf.R3O, comp.alusys.rf.R4O);
        $display("PC: %h, AR: %h, SP: %h", comp.alusys.arf1.PCOut, comp.alusys.arf1.AROut, comp.alusys.arf1.SPOut);
        
        $display("");
        $display("");
    end
     initial
       begin
           #1100; $finish;
       end
    BasicComputer comp(Clock, reset);

endmodule
