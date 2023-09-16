`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 30.03.2023 11:20:20
// Design Name: 
// Module Name: test
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////
module register_tb();
        reg en,clk;
        reg[1:0] funsel;
        reg[7:0] in;
        wire[7:0] out;
        
        n_bit_register #(8) register(en, funsel, in, out, clk);
        initial begin
        clk=0;
        in = 8'b10111010;
        en=1; funsel = 2'd1; #50;
        en=1; funsel = 2'd3; #50;
        en=1; funsel = 2'd2; #50;
        en=1; funsel = 2'd3; #50;
        en=1; funsel = 2'd0; #50;
        en=0; funsel = 2'd3; #50;
        in = 8'b01010111;
        en=1; funsel = 2'd1; #50;
        $finish;
        end
        always begin
        #25; clk = ~clk;
        end
        endmodule
    
module test2_a(
       
    );
    reg en,clk;
    reg [1:0]funsel;
    reg [7:0]i;
    reg [1:0]low_high;
    wire [15:0]o;
    
    
    
    two_a two_bit2a(en,clk,funsel,i,low_high,o);
        
    initial begin   
    clk=0;
    en = 1 ;  funsel[0] = 1  ; funsel[1] = 0  ; i = 8'b00001111 ;low_high = 0;#50;    //ilk 7 sayý yükleme
    en = 1 ;  funsel[0] = 1  ; funsel[1] = 0  ; i = 8'b00011111 ;low_high = 1;#50;    //7-14 yüðkleme
    en = 1 ;  funsel[0] = 0  ; funsel[1] = 1  ; i = 8'b00001111 ;low_high = 0;#50;  //çýkarma
    en = 1 ;  funsel[0] = 1  ; funsel[1] = 1  ; i = 8'b00001111 ;low_high = 0;#50;    //toplama
    en = 1 ;  funsel[0] = 0  ; funsel[1] = 0  ; i = 8'b00001111 ;low_high = 0;#50;    //sýfýrlama
    en = 0 ;  funsel[0] = 1  ; funsel[1] = 1  ; i = 8'b00001111 ;low_high = 0;#50;    //enable 0
    $finish;
    end
    always begin
    clk = ~clk; #25;
   
    end
   
    
endmodule



module part_2c();
    reg clk;
    reg [1:0]funsel, asel, bsel;
    reg [3:0]Rsel;
    
    reg [7:0]i;
    wire [7:0]oa,ob;
    
    
    
    ARF uut(clk,i,funsel,Rsel,asel,bsel,oa,ob);
        
    initial begin   
    clk = 0 ; 
    i = 8'b10100101;
    asel = 2'b00;   bsel = 2'b00 ;  funsel = 2'b01; Rsel = 4'b1111; #50;
    asel = 2'b00;   bsel = 2'b00 ;  funsel = 2'b10; Rsel = 4'b1111; #50;
    asel = 2'b00;   bsel = 2'b00 ;  funsel = 2'b11; Rsel = 4'b1111; #50;
    asel = 2'b00;   bsel = 2'b00 ;  funsel = 2'b00; Rsel = 4'b1111; #50;
    asel = 2'b10;   bsel = 2'b00 ;  funsel = 2'b01; Rsel = 4'b1111; #50;
    asel = 2'b00;   bsel = 2'b01 ;  funsel = 2'b11; Rsel = 4'b1111; #50;
    asel = 2'b00;   bsel = 2'b00 ;  funsel = 2'b10; Rsel = 4'b1111; #50;
    
  
    $finish;
    end
    always begin
    clk = ~clk; #10;
    
    end
 
endmodule


module part_2b_tb();

    reg[7:0] IN;
    reg[2:0] O1Sel,O2Sel;
    reg[1:0] FunSel;
    reg[3:0] RSel;
    reg[3:0] TSel;
    reg clk;
    wire[7:0] O1,O2;
    
    part_2b uut(IN,O1Sel,O2Sel,FunSel,RSel,TSel,O1,O2, clk);
    always #25 clk = ~clk;
    initial begin
        clk = 0;
        IN = 8'b10101111;
    
        O1Sel = 3'd0; O2Sel = 3'd4; FunSel = 2'd1; RSel = 4'b1111; TSel = 4'b1111;#50;
        IN = 8'b10100011;
        O1Sel = 3'd0; O2Sel = 3'd4; FunSel = 2'd1; RSel = 4'b1111; TSel = 4'b1111;#50;
        IN = 8'b10100000;
        O1Sel = 3'd1; O2Sel = 3'd5; FunSel = 2'd1; RSel = 4'b1111; TSel = 4'b1111;#50;
        O1Sel = 3'd2; O2Sel = 3'd6; FunSel = 2'd3; RSel = 4'b1111; TSel = 4'b1111;#50;
        O1Sel = 3'd3; O2Sel = 3'd7; FunSel = 2'd3; RSel = 4'b1111; TSel = 4'b1111;#50;
        O1Sel = 3'd0; O2Sel = 3'd4; FunSel = 2'd2; RSel = 4'b1111; TSel = 4'b1111;#50;
        O1Sel = 3'd1; O2Sel = 3'd5; FunSel = 2'd2; RSel = 4'b1111; TSel = 4'b1111;#50;
        
        O1Sel = 3'd2; O2Sel = 3'd6; FunSel = 2'd2; RSel = 4'b0010; TSel = 4'b0010;#50;
        O1Sel = 3'd3; O2Sel = 3'd7; FunSel = 2'd0; RSel = 4'b0001; TSel = 4'b0001;#50;
        O1Sel = 3'd0; O2Sel = 3'd4; FunSel = 2'd3; RSel = 4'b0000; TSel = 4'b0000;#50;
        
        O1Sel = 3'd1; O2Sel = 3'd5; FunSel = 2'd3; RSel = 4'b0000; TSel = 4'b0000;#50;
        O1Sel = 3'd2; O2Sel = 3'd6; FunSel = 2'd3; RSel = 4'b0000; TSel = 4'b0000;#50;
        IN = 8'b10100000;
        O1Sel = 3'd3; O2Sel = 3'd7; FunSel = 2'd1; RSel = 4'b0001; TSel = 4'b0001;#50;
       
        $finish;       
    end
endmodule

module part3_test();
reg [7:0] A, B;
wire[7:0] Out;
wire[3:0] Flag;

reg [3:0]Funsel; 
reg cflag;

ALU Alu1(A,B,Funsel,cflag, Out,Flag);


initial begin

cflag= 0;
A=8'b00001010;
B=8'b00001001;
cflag= Flag[2]; Funsel=4'd0; #50;
cflag= Flag[2]; Funsel=4'd1; #50;
cflag= Flag[2];Funsel=4'd2; #50;
cflag= Flag[2];Funsel=4'd3; #50;
cflag= Flag[2];Funsel=4'd4; #50;
cflag= Flag[2];Funsel=4'd5; #50;
cflag= Flag[2];Funsel=4'd7; #50;
cflag= Flag[2];Funsel=4'd8; #50;
cflag= Flag[2];Funsel=4'd9; #50;
cflag= Flag[2];Funsel=4'd10; #50;
cflag= Flag[2];Funsel=4'd11; #50;
cflag= Flag[2];Funsel=4'd12; #50;
cflag= Flag[2];Funsel=4'd13; #50;
cflag= Flag[2];Funsel=4'd14; #50;
cflag= Flag[2];Funsel=4'd15; #50;
cflag= Flag[2];Funsel=4'd13; #50;
A=8'b10000000;
B=8'b10011111;
cflag= Flag[2];Funsel=4'd0; #50;
cflag= Flag[2];Funsel=4'd4; #50;
cflag= Flag[2];Funsel=4'd5; #50;
cflag= Flag[2];Funsel=4'd6; #50;
cflag= Flag[2];Funsel=4'd7; #50;

$finish;


end

endmodule

module Project1Test();
    //Input Registers of ALUSystem
    reg[2:0] RF_O1Sel; 
    reg[2:0] RF_O2Sel; 
    reg[1:0] RF_FunSel;
    reg[3:0] RF_RSel;
    reg[3:0] RF_TSel;
    reg[3:0] ALU_FunSel;
    reg[1:0] ARF_OutASel; 
    reg[1:0] ARF_OutBSel; 
    reg[1:0] ARF_FunSel;
    reg[3:0] ARF_RSel;
    reg      IR_LH;
    reg      IR_Enable;
    reg[1:0]      IR_Funsel;
    reg      Mem_WR;
    reg      Mem_CS;
    reg[1:0] MuxASel;
    reg[1:0] MuxBSel;
    reg MuxCSel;
    reg      Clock;
    
    //Test Bench Connection of ALU System
    ALU_System _ALUSystem(
    .RF_OutASel(RF_O1Sel), 
    .RF_OutBSel(RF_O2Sel), 
    .RF_FunSel(RF_FunSel),
    .RF_RSel(RF_RSel),
    .RF_TSel(RF_TSel),
    .ALU_FunSel(ALU_FunSel),
    .ARF_OutCSel(ARF_OutASel), 
    .ARF_OutDSel(ARF_OutBSel), 
    .ARF_FunSel(ARF_FunSel),
    .ARF_RegSel(ARF_RSel),
    .IR_LH(IR_LH),
    .IR_Enable(IR_Enable),
    .IR_Funsel(IR_Funsel),
    .Mem_WR(Mem_WR),
    .Mem_CS(Mem_CS),
    .MuxASel(MuxASel),
    .MuxBSel(MuxBSel),
    .MuxCSel(MuxCSel),
    .Clock(Clock)
    );
    
    //Test Vector Variables
    reg [41:0] VectorNum, Errors, TotalLine; 
    reg [41:0] TestVectors[3:0];
    reg Reset, Operation;
    initial begin
        Reset = 0;
    end
    //Clock Signal Generation
    always 
    begin
        Clock = 1; #5; Clock = 0; #5; // 10ns period
    end
    
    //Read Test Bench Values
    initial begin
        $readmemb("TestBench.mem", TestVectors); // Read vectors
        VectorNum = 0; Errors = 0; TotalLine=0; Reset=0;// Initialize
    end
    
    // Apply test vectors on rising edge of clock
    always @(posedge Clock)
    begin
        #1; 
        {Operation, RF_O1Sel, RF_O2Sel, RF_FunSel, 
        RF_RSel, RF_TSel, ALU_FunSel, ARF_OutASel, ARF_OutBSel, 
        ARF_FunSel, ARF_RSel, IR_LH, IR_Enable, IR_Funsel, 
        Mem_WR, Mem_CS, MuxASel, MuxBSel, MuxCSel} = TestVectors[VectorNum];
    end
    
    // Check results on falling edge of clk
    always @(negedge Clock)
        if (~Reset) // skip during reset
        begin
            $display("Input Values:");
            $display("Operation: %d", Operation);
            $display("Register File: O1Sel: %d, O2Sel: %d, FunSel: %d, RSel: %d, TSel: %d", RF_O1Sel, RF_O2Sel, RF_FunSel, RF_RSel, RF_TSel);            
            $display("ALU FunSel: %d", ALU_FunSel);
            $display("Addres Register File: OutASel: %d, OutBSel: %d, FunSel: %d, Regsel: %d", ARF_OutASel, ARF_OutBSel, ARF_FunSel, ARF_RSel);            
            $display("Instruction Register: LH: %d, Enable: %d, FunSel: %d", IR_LH, IR_Enable, IR_Funsel);            
            $display("Memory: WR: %d, CS: %d", Mem_WR, Mem_CS);
            $display("MuxASel: %d, MuxBSel: %d, MuxCSel: %d", MuxASel, MuxBSel, MuxCSel);
            
            $display("");
            $display("Output Values:");
            $display("Register File: AOut: %d, BOut: %d", _ALUSystem.AOut, _ALUSystem.BOut);            
            $display("ALUOut: %d, ALUOutFlag: %d, ALUOutFlags: Z:%d, C:%d, N:%d, O:%d,", _ALUSystem.ALUOut, _ALUSystem.ALUOutFlag, _ALUSystem.ALUOutFlag[3],_ALUSystem.ALUOutFlag[2],_ALUSystem.ALUOutFlag[1],_ALUSystem.ALUOutFlag[0]);
            $display("Address Register File: AOut: %d, BOut (Address): %d", _ALUSystem.AOut, _ALUSystem.Address);            
            $display("Memory Out: %d", _ALUSystem.MemoryOut);            
            $display("Instruction Register: IROut: %d", _ALUSystem.IROut);            
            $display("MuxAOut: %d, MuxBOut: %d, MuxCOut: %d", _ALUSystem.MuxAOut, _ALUSystem.MuxBOut, _ALUSystem.MuxCOut);
            
            // increment array index and read next testvector
            VectorNum = VectorNum + 1;
            if (TestVectors[VectorNum] === 42'bx)
            begin
                $display("%d tests completed.",
                VectorNum);
                $finish; // End simulation
            end
        end
endmodule
