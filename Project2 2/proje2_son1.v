`timescale 1ns / 1ps



module mux8to1( Out, Sel, In1, In2, In3, In4, In5, In6, In7, In8); 


input [7:0]  In1, In2, In3, In4, In5, In6, In7, In8; //The eight 8-bit input lines of the Mux 
input [2:0] Sel;
output [7:0] Out; 

reg [7:0] Out; 
always @ (*) 

begin 

 case (Sel) 

  3'b000 : Out = In1; 

  3'b001 : Out = In2; 

  3'b010 : Out = In3; 

  3'b011 : Out = In4; 

  3'b100 : Out = In5; 

  3'b101 : Out = In6; 

  3'b110 : Out = In7; 

  3'b111 : Out = In8; 

  default : Out = 8'bx; 


 endcase 

end  

endmodule


module Memory(
    input wire[7:0] address,
    input wire[7:0] data,
    input wire wr, //Read = 0, Write = 1
    input wire cs, //Chip is enable when cs = 0
    input wire clock,
    output reg[7:0] o // Output
);
    //Declaration o f the RAM Area
    reg[7:0] RAM_DATA[0:255];
    //Read Ram data from the file
    initial $readmemh("RAM.mem", RAM_DATA);
    //Read the selected data from RAM
    always @(*) begin
        o = ~wr && ~cs ? RAM_DATA[address] : 8'hZ;
    end
    
    //Write the data to RAM
    always @(posedge clock) begin
        if (wr && ~cs) begin
            RAM_DATA[address] <= data; 
        end
    end
endmodule


module mux4to1( Out, Sel, In1, In2, In3, In4); 
output reg [7:0] Out; 
input [1:0] Sel;
input [7:0]  In1, In2, In3, In4; //The four 8-bit input lines of the Mux 

always @ (*) 

begin 

 case (Sel) 
  2'b00 : Out = In1; 
  2'b01 : Out = In2; 
  2'b10 : Out = In3; 
  2'b11 : Out = In4; 
 
 endcase 
end  
endmodule


module mux2to1( Out, Sel, In1, In2); 


input [7:0]  In1, In2; //The two 8-bit input lines of the Mux 
input  Sel;
output reg [7:0] Out; 


always @ (*) 

begin 

 case (Sel) 
  1'b0 : Out = In1; 
  1'b1 : Out = In2; 
 endcase 

end  
endmodule



    
    
    

module n_bit_register #(parameter n = 8)(
    input en, 
    input [1:0]FunSel,
    input [n-1:0]I,
    output reg [n-1:0]O,
    input clk
    );
    
    
    

    always @(posedge clk)begin
            
            if (en == 1'b0) begin
                
            end else if(FunSel== 2'b00)
            begin
                O <= 0;
                
            end else if(FunSel == 2'b01)
            begin
                O <= I;
               
            end else if(FunSel == 2'b10)
            begin
                O <= O - 1;
            end else if(FunSel == 2'b11)
            begin
                O <= O + 1;
            end
            
            
           
            
        end
      
        endmodule
  
  
  
module two_a(
                    input wire E,clock,
                    input wire [1:0]FunSel,
                    input wire [7:0]I,
                    input lh,
                    output wire [15:0]IR
                    );
                 
                    reg [15:0] data;
                
                     always @(*)
            begin
            case(lh)
            1'b0:   begin
                    data = {I,IR[7:0]};
                    end
            1'b1:    begin
                    data = {IR[15:8],I};
                    end
             endcase
             
        
             end
             n_bit_register #(16) IRRegister(E , FunSel, data, IR, clock);
                        
            endmodule                
            
    
module part_2b(IN, O1Sel, O2Sel, FunSel, RSel, TSel, RF_AOut, RF_BOut,clk);
                
                
                input [7:0] IN;
                input [2:0] O1Sel, O2Sel;
                input [1:0] FunSel;
                input [3:0] RSel, TSel;
                output reg[7:0] RF_AOut, RF_BOut;
                wire[7:0] mux1out, mux2out, R1O, R2O, R3O, R4O, T1O, T2O, T3O, T4O;
                input clk;
                
                
                n_bit_register #(8) R1( RSel[3], FunSel, IN, R1O, clk);
                n_bit_register #(8) R2( RSel[2], FunSel, IN, R2O, clk);
                n_bit_register #(8) R3( RSel[1], FunSel, IN, R3O, clk);
                n_bit_register #(8) R4( RSel[0], FunSel, IN, R4O, clk);
                n_bit_register #(8) T1( TSel[3], FunSel, IN, T1O, clk);
                n_bit_register #(8) T2( TSel[2], FunSel, IN, T2O, clk);
                n_bit_register #(8) T3( TSel[1], FunSel, IN, T3O, clk);
                n_bit_register #(8) T4( TSel[0], FunSel, IN, T4O, clk);
                
                mux8to1 mux1(mux1out, O1Sel, T1O, T2O, T3O, T4O, R1O, R2O, R3O, R4O );
                mux8to1 mux2(mux2out, O2Sel, T1O, T2O, T3O, T4O, R1O, R2O, R3O, R4O );
                always @(*)
                begin
                RF_AOut=mux1out;
                RF_BOut=mux2out;
                end
                
                endmodule
                
                
module ARF( input clk,
                            input [7:0] inData, 
                            input [1:0] FunSel, 
                            input [3:0] RSel, 
                            input [1:0] OutASel, OutBSel,
                            output  reg [7:0] ARF_AOut, ARF_BOut
                        );
                          
                          wire [7:0] PCOut, AROut, SPOut,PCPastOut, muxaout, muxbout; // multiplexer output signals
                        
                          n_bit_register #(8) RegPC(RSel[3], FunSel, inData, PCOut, clk ); // registers for each address register
                          n_bit_register #(8) RegAR(RSel[2], FunSel, inData, AROut, clk );
                          n_bit_register #(8) RegSP(RSel[1], FunSel, inData, SPOut, clk );
                          n_bit_register #(8) PCPast(RSel[0], FunSel, inData, PCPastOut, clk);
                          // mux for selecting OutA
                           mux4to1 amux(muxaout,OutASel, AROut,SPOut,  PCPastOut, PCOut);
                           mux4to1 bmux(muxbout,OutBSel, AROut,SPOut,  PCPastOut, PCOut);
                          always@(*)
                          begin
                          
                          ARF_AOut=muxaout;
                          // mux for selecting OutB
                          ARF_BOut=muxbout;
                          end
                        endmodule


module ALU( 
input [7:0]A, 
input [7:0]B, 
input[3:0] FunSel,
input CarryFlag,
output reg  [7:0] OutAlu, 
output reg [3:0]Flag

);
reg[7:0] sum, dif, negA, negB, log;

reg[8:0] temp;
initial Flag = 0000;
always @(*)
begin
  

case(FunSel)
        4'b0000:  begin
        
            OutAlu = A; 
            
            if(A) begin Flag[3]=0; end
            else begin Flag[3]=1; end
            if (A[7]) begin  Flag[1]=1;  end
            else begin Flag[1]=0; end
             end
            
           
        4'b0001: begin
           
           if(B) begin Flag[3]=0; end
           else begin Flag[3]=1; end
           
           if(B[7]) begin Flag[1]=1; end
           else begin Flag[1]=0; end
           OutAlu = B ;
           end
        4'b0010: begin
            OutAlu = ~A;
            if(~A) begin Flag[3]=0; end
            else begin Flag[3]=1; end
           
            if(~A[7]) Flag[1]=1;
            else Flag[1]=0;
            end
        4'b0011: begin
           OutAlu = ~B;
            if(~B) begin Flag[3]=0; end
            else begin Flag[3]=1; end
           
            if(~B[7]) begin Flag[1]=1; end
            else begin Flag[1]=0; end
            end
        4'b0100:  begin
           OutAlu = A+B;
           sum = A+B;
           temp = A+B;
           
           //check is Zero
            if((A+B)==8'd0) begin Flag[3]=1; end
            else begin Flag[3]<=0;end
           
           //Carry Flag
           Flag[2]= temp[7];
          
           //check negative(for signed)
            if (A[7]) begin negA = ~A + 8'd1; end
            else negA = A;
            if(B[7]) begin  negB = ~B +8'd1; end
            else negB=B;
            sum = negA+negB;
            Flag[1]=sum[7];
            
            //check overflow
            if (~A[7] && ~B[7] && sum[7]) begin Flag[0]=1; end //pos+pos =neg
            else if(A[7] && B[7] && ~sum[7]) begin Flag[0]=1; end //neg + neg = pos
            else begin Flag[0]<=0; end
            end


         4'b0101:  begin
           OutAlu = A-B;
           dif = A-B;
           temp = A-B;
           
           //check Zero Flag
           if(dif==8'd0) begin Flag[3]<=1; end
           else begin Flag[3]<=0; end
           
           //Carry(borrow)
           Flag[2]= ~temp[8];
           
           //Negative Flag
             if (A[7]) begin negA = ~A + 8'd1; end
                    else negA = A;
                    if(B[7]) begin  negB = ~B +8'd1; end
                    else negB=B;
                    dif = negA-negB;
                    Flag[1]=sum[7];

            if (~A[7] && B[7] && dif[7]) begin Flag[0]<=1; end//pos-neg =neg
            else if(A[7] && ~B[7] && ~dif[7]) begin Flag[0]<=1; end //neg - pos = pos
            else begin Flag[0]<=0; end
            end
        
         4'b0110:  begin //COMPARE
             dif=A-B;
             temp=A-B;            
             if(temp[8]) begin
               OutAlu=A; 
        
                if(A==8'd0) begin Flag[3]<=1; end
                else begin Flag[3]<=0; end
                Flag[2]=0;
                Flag[1]=0;
                Flag[0]=0;
                
   
            
            end
            else begin
               OutAlu<=8'd0;
               //negative flag
               Flag[1]<=1;
               //carry flag
               Flag[2]=1;
               //zero flag
               Flag[3]<=1;
               //overflow
               if (~A[7] && B[7] && dif[7]) begin Flag[0]<=1; end//pos-neg =neg
               else if(A[7] && ~B[7] && ~dif[7]) begin Flag[0]<=1; end //neg - pos = pos
               else begin Flag[0]<=0; end
               
            end
         end

           
         4'b0111: begin // Logical and
           OutAlu = A & B;
           log = A&B;
           if(log==8'd0) begin Flag[3]=1; end
           else begin Flag[3]=0; end
           
           if(log[7])begin  Flag[1]=1; end
           else begin Flag[1]=0; end
           end

          4'b1000: begin //  Logical or
            OutAlu = A | B;
            log = A|B;
             if((A|B)==8'd0) begin Flag[3]=1; end
           else begin Flag[3]=0; end
           
           if(log[7]) begin Flag[1]=1; end
           else begin Flag[1]=0; end
           end
          4'b1001: begin//  Logical nand
           OutAlu = ~(A & B);
           log = ~(A & B);
            if( log == 8'd0 ) begin Flag[3]=1; end
           else begin Flag[3]=0; end
           
           if(log[7]) begin Flag[1]=1; end
           else begin Flag[1]=0; end
           end
          4'b1010:begin //  Logical xor
           OutAlu <= A ^ B;
           log = A ^ B;
           if(log==8'd0) begin Flag[3]<=1; end
           else begin  Flag[3]<=0; end
           
           if(log[7]) begin Flag[1]<=1; end
           else  begin Flag[1]<=0; end
          end  //carry
          4'b1011: begin //  Logical shift left
           Flag[2]=A[7]; //set the carry flag
           log = (A<<1);
           
           OutAlu = log;
           if((A<<1)==8'd0)begin Flag[3]<=1; end
           else begin Flag[3]<=0; end
           
           if(log[7]) begin Flag[1]<=1; end
           else begin Flag[1]<=0; end
          end
          4'b1100: begin// Logical shift right 
           Flag[2]<=A[0];
           
           log= (A>>1);
           
           OutAlu =log;

           if((A>>1)==8'd0) begin Flag[3]<=1; end
           else  begin Flag[3]=0; end
           
           if(log[7]) begin Flag[1]=1; end
           else begin Flag[1]=0; end
          end
         
          4'b1101: begin  // Arithmetic shift left
            log = (A<<1);
            OutAlu = log;
          
           
            if(log==8'd0)begin Flag[3]=1; end //overflow
            else begin Flag[3]=0; end
           
           if(A[6])begin Flag[1]=1; end
           else begin Flag[1]=0; end
           
           if (A[6]^A[7]) begin Flag[0] = 1; end
           
           
            end
         
          4'b1110: begin// Arithmetic shift right
          OutAlu = {A[7],A[7:1]};
          if({A[7],A[7:1]}==8'd0)begin  Flag[3]<=1; end
           else begin Flag[3]<=0; end
           
           if(A[7]) begin Flag[1]<=1; end
           else begin Flag[1]<=0; end
           end
          4'b1111: begin //Circular shift 
            OutAlu <={CarryFlag, A[7:1]};
            Flag[2] <= A[0]; //flag control
            if({CarryFlag, A[7:1]}==8'd0)begin  Flag[3]<=1; end
            else begin Flag[3]<=0; end
           
            if(CarryFlag)begin  Flag[1]<=1; end
            else begin Flag[1]<=0; end
           
            end
            
endcase
end

endmodule


module ALU_System(
    input [2:0]RF_OutASel,
    input [2:0]RF_OutBSel,
    input [1:0]RF_FunSel,
    input [3:0]RF_RSel,
    input [3:0]RF_TSel,
    input [3:0]ALU_FunSel,
    input [1:0]ARF_OutCSel,
    input [1:0]ARF_OutDSel,
    input [1:0]ARF_FunSel,
    input [3:0]ARF_RegSel,
    input IR_LH,
    input IR_Enable,
    input [1:0]IR_Funsel,
    input Mem_WR,
    input Mem_CS,
    input [1:0]MuxASel,
    input [1:0]MuxBSel,
    input MuxCSel,
    input Clock
    
    );
    
    wire [7:0] MemoryOut, MuxAOut, MuxCOut, alu_input_b, ALUOut;
    wire [7:0] MuxBOut, ARF_COut, Address,AOut,BOut;
    
    wire [7:0]IROut;
    wire [3:0]ALUOutFlag;
    wire [15:0]output_2a;

    Memory m1( Address, ALUOut, Mem_WR, Mem_CS, Clock, MemoryOut );
    
    assign IROut = output_2a[7:0];
    mux4to1 muxA( MuxAOut , MuxASel , ALUOut , MemoryOut , IROut, ARF_COut );
    mux4to1 muxB( MuxBOut , MuxBSel , ALUOut , MemoryOut , IROut , ARF_COut ); //3 m  4 m  olcak
    
    mux2to1 mucC( MuxCOut , MuxCSel , AOut, ARF_COut );
    ALU a1( MuxCOut, BOut , ALU_FunSel , ALUOutFlag[2] , ALUOut , ALUOutFlag );
    part_2b rf( MuxAOut, RF_OutASel , RF_OutBSel , RF_FunSel , RF_RSel,RF_TSel , AOut, BOut, Clock );
    ARF arf1(Clock, MuxBOut , ARF_FunSel , ARF_RegSel , ARF_OutCSel , ARF_OutDSel , ARF_COut, Address );
   two_a twoo(IR_Enable, Clock ,IR_Funsel , MemoryOut , IR_LH , output_2a);
endmodule

//project2
module timer_8_bit(clock, funsel, out);

input wire clock;
input wire funsel;
output reg[7:0] out;
always @(posedge clock)
begin
    case(funsel)
        1'b0: begin out <= 8'd0; end
        1'b1: begin out <= out+1; end
    endcase
end
endmodule


module HardwiredControlUnit(
    IR_Out,// innstruction 
    ALUFlag,
    RF_OutASel,
    RF_OutBSel,
    RF_FunSel,
    RF_RSel,
    ALU_FunSel,
    ARF_OutCSel,
    ARF_OutDSel,
    ARF_FunSel,
    ARF_RegSel,
    IR_LH,
     IR_Enable,
    IR_Funsel,
    Mem_WR,
    Mem_CS,
    MuxASel,
    MuxBSel,
    MuxCSel,

    operation_code,
    addresing_mode,
    regsel,
    op_address,
    destination_register,
    source_register1,
    source_register2,
    timer_funsel,
    timer_out,
    reset,
    mem_ref_op,
    Clock
    
    
);
input wire [15:0] IR_Out;
output reg[2:0] RF_OutASel;
output reg[2:0] RF_OutBSel;
output reg[1:0] RF_FunSel;
output reg[3:0] RF_RSel;
output reg[3:0] ALU_FunSel, ALUFlag;
output reg[1:0] ARF_OutCSel;
output reg[1:0] ARF_OutDSel;
output reg[1:0] ARF_FunSel, IR_Funsel;
 output reg[3:0] ARF_RegSel;

output reg IR_LH, IR_Enable, Mem_CS, Mem_WR;
output reg[1:0] MuxASel, MuxBSel;
output reg MuxCSel;

output wire addresing_mode;
output wire[1:0] regsel; 
output wire[7:0] op_address;
output wire[3:0] operation_code;
output wire[3:0] destination_register, source_register1, source_register2;
output wire mem_ref_op;
assign mem_ref_op = operation_code == 4'hA || operation_code == 4'h9 || operation_code == 4'hF || operation_code == 4'hE || operation_code == 4'hD || operation_code == 4'hC;

assign addresing_mode = IR_Out[10];
assign regsel= IR_Out[9:8];
assign op_address=IR_Out[7:0];
assign operation_code=IR_Out[15:12];
assign destination_register=IR_Out[11:8];
assign source_register1=IR_Out[7:4];
assign source_register2=IR_Out[3:0];
//bunlar? eklemeli miyiz
input wire reset;
input wire Clock;



output reg timer_funsel;
output wire[7:0] timer_out;
// MEM CS VE CLEAR EKLENECEK

      
always@(*)

begin
    if(~reset)
        begin
       RF_FunSel = 2'bZ;
       RF_RSel = 4'b0000;
       ARF_FunSel = 2'bZ;
       ARF_RegSel = 4'b1000;
       IR_LH = 1'bZ;
        IR_Enable = 0;
        IR_Funsel = 1'bZ;
        Mem_WR = 1'bZ;
       Mem_CS = 1'b0;
         
        
            if(timer_out==8'd0)
            begin
               
               
                ARF_OutDSel=2'b11;//Address = PC
                //PC=PC+1
                ARF_RegSel=4'b1000;
                ARF_FunSel=2'b11;
                
                timer_funsel=1;//increase timer
                
                
                // IR low load
                IR_LH=1'b0;
                IR_Enable=1'b1;
                IR_Funsel=2'b01;
                
                Mem_WR=0;//Memory Read

               

            end

            if(timer_out==8'd1)
            begin
                //same with T0 but load IR high
                //Address = PC
                ARF_OutDSel=2'b11;
                 //PC=PC+1
                ARF_RegSel=4'b1000;
                ARF_FunSel=2'b11;
                
                timer_funsel=1;//increase timer
                //Memory Read
               
                
                // IR high load  
                IR_LH=1'b1;
                IR_Enable=1'b1;
                IR_Funsel=2'b01;
              
                Mem_WR=0;
                
                
            
            //we have an instruction code now
                 
            end
            
            if(mem_ref_op==1 && timer_out==8'd2)//
            begin
                MuxBSel=2'b10;
                ARF_RegSel=4'b0100;//Select AR
                ARF_FunSel=2'b01;//Load Address to AR
                ARF_OutDSel=2'b00;
                timer_funsel=1;//increase timer
               
            end
           
            else
            begin
            
           case(operation_code)
            
                        4'h0: 
                        begin
                                //mux a n?n seçimi ne olucak ilgilendirmiyormu? ab?ata uyazarken seçmem gerek sadece
                                //RF_RSel = 4'b1111; //r1,r2,r3,r3 is enable hepsi mi olmal? bilemedim hepsini nonenable yap sadece yükleyece?ini enable yap ve tekrar eski
                                 //jühaline getir sonunda
                                
                                MuxCSel = 0; //rf outputu seçiyoruz
                                ALU_FunSel <= 4'b0111; //alu içinde and i?lemini seçtik
                                //muxsela ne olacak mevcut durumda m? kal?cak
                                //funsel ne olucak load m? yoksa o anki i?lem mi
                                if(timer_out==8'd2)
                                begin
                                    case(source_register1)
                                        4'h0:begin RF_OutASel = 3'b100;end
                                        4'h1:  begin RF_OutASel = 3'b101; end
                                        4'h2: begin RF_OutASel = 3'b110;   end
                                        4'h3: begin RF_OutASel = 3'b111;     end
                                   endcase
                                    case(source_register2)
                                         4'h0: begin RF_OutBSel = 3'b100;    end
                                         4'h1: begin RF_OutBSel = 3'b101;       end
                                         4'h2:begin RF_OutBSel = 3'b110;         end
                                         4'h3: begin RF_OutBSel = 3'b111;       end
                                    endcase
                                    if(destination_register[2]==1)//destreg in in arf
                                                            begin//destreg is in ARF
                                                                                        //MuxBsel
                                                                                        MuxBSel=2'b00;
                                                                                        //ARFregsel
                                                                                        case(destination_register)
                                                                                        4'b0100:
                                                                                        begin
                                                                                            ARF_RegSel=4'b0010;//SP
                                                                                        end
                                                                                        4'b0101:
                                                                                        begin
                                                                                            ARF_RegSel=4'b0100;//AR
                                                                                        end
                                                                                        4'b0110:
                                                                                        begin
                                                                                            ARF_RegSel=4'b1000;//PC
                                                                                        end
                                                                                        4'b0111:
                                                                                        begin
                                                                                            ARF_RegSel=4'b1000;//PC
                                                                                        end
                                                                                        endcase
                                                            
                                                                                        ARF_FunSel=2'b01;
                                                                                        //ARF funsel
                                                                                        timer_funsel=0;//reset
                                                                                    end
                                                                                    
                                      else
                                      begin
                                                            
                                    
                                     timer_funsel=1;//increase timer
                                    MuxASel= 2'b00;
                                     end
                                end
                               
                          
                               if(timer_out==8'd3) 
                               begin
                                            
                                            RF_FunSel <= 2'b01; 
                                            case(destination_register)
                                                 4'h0: begin RF_RSel <= 4'b1000;   end //sadece load lanaca?? enable yap yazd?rmana gerek yok
                                                 4'h1: begin RF_RSel <= 4'b0100;      end
                                                 4'h2:begin RF_RSel <= 4'b0010;        end
                                                 4'h3: begin RF_RSel <= 4'b0001;       end
                                            endcase   
                                            timer_funsel=0;//clear timer      
                                           
                               end
                                            
                                
                         end
                        4'h1: 
                        begin
                                    
                        
                            
                            if(timer_out==8'd2)
                            MuxCSel = 0; //rf outputu seçiyoruz
                            ALU_FunSel = 4'b1000; //alu içinde and i?lemini seçtik
                            //muxsela ne olacak mevcut durumda m? kal?cak
                            
                                begin
                                    case(source_register1)
                                        4'h0:begin RF_OutASel = 3'b100;end
                                        4'h1:  begin RF_OutASel = 3'b101; end
                                        4'h2: begin RF_OutASel = 3'b110;   end
                                        4'h3: begin RF_OutASel = 3'b111;     end
                                    endcase
                                    case(source_register2)
                                         4'h0: begin RF_OutBSel = 3'b100;    end
                                         4'h1: begin RF_OutBSel = 3'b101;       end
                                         4'h2:begin RF_OutBSel = 3'b110;         end
                                         4'h3: begin RF_OutBSel = 3'b111;       end
                                    endcase
                                end
                                
                                if(destination_register[2]==1)//destreg in in arf
                                                                                begin//destreg is in ARF
                                                                                                            //MuxBsel
                                                                                                            MuxBSel=2'b00;
                                                                                                            //ARFregsel
                                                                                                            case(destination_register)
                                                                                                            4'b0100:
                                                                                                            begin
                                                                                                                ARF_RegSel=4'b0010;//SP
                                                                                                            end
                                                                                                            4'b0101:
                                                                                                            begin
                                                                                                                ARF_RegSel=4'b0100;//AR
                                                                                                            end
                                                                                                            4'b0110:
                                                                                                            begin
                                                                                                                ARF_RegSel=4'b1000;//PC
                                                                                                            end
                                                                                                            4'b0111:
                                                                                                            begin
                                                                                                                ARF_RegSel=4'b1000;//PC
                                                                                                            end
                                                                                                            endcase
                                                                                
                                                                                                            ARF_FunSel=2'b01;
                                                                                                            //ARF funsel
                                                                                                            timer_funsel=0;//reset
                                                                                                        end
                                                                                                        
                                                          else
                                                          begin
                                                                                
                                                        
                                                         timer_funsel=1;//increase timer
                                                        MuxASel= 2'b00;
                                                         end
                                                    
                                                  
                        
               //             MuxASel= 2'b00;
               //             timer_funsel=1;//increase timer
                            
                            if(timer_out==8'd3)
                            begin
                                RF_FunSel = 2'b01; //load ilkindeki i?lem bir önceki ile ayn? 
                                case(destination_register)
                                     4'h0: begin RF_RSel = 4'b1000;   end //sadece load lanaca?? enable yap yazd?rmana gerek yok
                                     4'h1: begin RF_RSel = 4'b0100;      end
                                     4'h2:begin RF_RSel = 4'b0010;        end
                                     4'h3: begin RF_RSel = 4'b0001;       end
                                endcase    
                             timer_funsel=0;//clear timer

                            end
                        end
                        4'h2: 
                        begin
                                  
                        MuxCSel = 0; //rf outputu seçiyoruz
                        ALU_FunSel = 4'b0010; //alu içinde not i?lemini seçtik
                        //muxsela ne olacak mevcut durumda m? kal?cak
                        if(timer_out==8'd2)
                        begin
                        case(source_register1)
                            4'h0:begin RF_OutASel = 3'b100;end
                            4'h1:  begin RF_OutASel = 3'b101; end
                            4'h2: begin RF_OutASel = 3'b110;   end
                            4'h3: begin RF_OutASel = 3'b111;     end
                       endcase
                                if(destination_register[2]==1)//destreg in in arf
                                                                       begin//destreg is in ARF
                                                                                                   //MuxBsel
                                                                                                   MuxBSel=2'b00;
                                                                                                   //ARFregsel
                                                                                                   case(destination_register)
                                                                                                   4'b0100:
                                                                                                   begin
                                                                                                       ARF_RegSel=4'b0010;//SP
                                                                                                   end
                                                                                                   4'b0101:
                                                                                                   begin
                                                                                                       ARF_RegSel=4'b0100;//AR
                                                                                                   end
                                                                                                   4'b0110:
                                                                                                   begin
                                                                                                       ARF_RegSel=4'b1000;//PC
                                                                                                   end
                                                                                                   4'b0111:
                                                                                                   begin
                                                                                                       ARF_RegSel=4'b1000;//PC
                                                                                                   end
                                                                                                   endcase
                                                                       
                                                                                                   ARF_FunSel=2'b01;
                                                                                                   //ARF funsel
                                                                                                   timer_funsel=0;//reset
                                                                                               end
                                                                                               
                                                 else
                                                 begin
                                                                       
                                               
                                                timer_funsel=1;//increase timer
                                               MuxASel= 2'b00;
                                                end
                            end
                             
                            if(timer_out==8'd3)
                        begin
                        RF_FunSel = 2'b01; //load
                        case(destination_register)
                        4'h0: begin RF_RSel = 4'b1000;   end //sadece load lanaca?? enable yap yazd?rmana gerek yok
                        4'h1: begin RF_RSel = 4'b0100;      end
                        4'h2:begin RF_RSel = 4'b0010;        end
                        4'h3: begin RF_RSel = 4'b0001;       end
                        endcase    
                           //operation bitince timerfunseli resetle
                       
                        timer_funsel=0;//clear timer   
                         end
                         
                        end
                    4'h3: 
                        begin
                                  
                        MuxCSel = 0; //rf outputu seçiyoruz
                        ALU_FunSel = 4'b0100; //alu içinde + i?lemini seçtik
            
                        if(timer_out==8'd2)
                        begin
                        case(source_register1)
                            4'h0:begin RF_OutASel = 3'b100;end
                            4'h1:  begin RF_OutASel = 3'b101; end
                            4'h2: begin RF_OutASel = 3'b110;   end
                            4'h3: begin RF_OutASel = 3'b111;     end
                       endcase
                        case(source_register2)
                             4'h0: begin RF_OutBSel = 3'b100;    end
                             4'h1: begin RF_OutBSel = 3'b101;       end
                             4'h2:begin RF_OutBSel = 3'b110;         end
                             4'h3: begin RF_OutBSel = 3'b111;       end
                        endcase
                                if(destination_register[2]==1)//destreg in in arf
                                                                        begin//destreg is in ARF
                                                                                                    //MuxBsel
                                                                                                    MuxBSel=2'b00;
                                                                                                    //ARFregsel
                                                                                                    case(destination_register)
                                                                                                    4'b0100:
                                                                                                    begin
                                                                                                        ARF_RegSel=4'b0010;//SP
                                                                                                    end
                                                                                                    4'b0101:
                                                                                                    begin
                                                                                                        ARF_RegSel=4'b0100;//AR
                                                                                                    end
                                                                                                    4'b0110:
                                                                                                    begin
                                                                                                        ARF_RegSel=4'b1000;//PC
                                                                                                    end
                                                                                                    4'b0111:
                                                                                                    begin
                                                                                                        ARF_RegSel=4'b1000;//PC
                                                                                                    end
                                                                                                    endcase
                                                                        
                                                                                                    ARF_FunSel=2'b01;
                                                                                                    //ARF funsel
                                                                                                    timer_funsel=0;//reset
                                                                                                end
                                                                                                
                                                  else
                                                  begin
                                                                        
                                                
                                                 timer_funsel=1;//increase timer
                                                MuxASel= 2'b00;
                                                 end
                                         
                        end
                            
                            if(timer_out==8'd3)
                        begin
                            RF_FunSel = 2'b01; //load
                            case(destination_register)
                                 4'h0: begin RF_RSel = 4'b1000;   end //sadece load lanaca?? enable yap yazd?rmana gerek yok
                                 4'h1: begin RF_RSel = 4'b0100;      end
                                4'h2:begin RF_RSel = 4'b0010;        end
                                 4'h3: begin RF_RSel = 4'b0001;       end
                            endcase      
                            timer_funsel=0;//clear timer
                        end
                            
                        end
                        4'h4: begin 
                       
                        
                        MuxCSel = 0; //rf outputu seçiyoruz
                        ALU_FunSel = 4'b0101; //alu içinde and i?lemini seçtik
                        //muxsela ne olacak mevcut durumda m? kal?cak
                        if(timer_out==8'd2)
                        begin
                            case(source_register1)
                                4'h0:begin RF_OutASel = 3'b100;end
                                4'h1:  begin RF_OutASel = 3'b101; end
                                4'h2: begin RF_OutASel = 3'b110;   end
                                4'h3: begin RF_OutASel = 3'b111;     end
                           endcase
                            case(source_register2)
                                 4'h0: begin RF_OutBSel = 3'b100;    end
                                 4'h1: begin RF_OutBSel = 3'b101;       end
                                 4'h2:begin RF_OutBSel = 3'b110;         end
                                 4'h3: begin RF_OutBSel = 3'b111;       end
                            endcase
                                if(destination_register[2]==1)//destreg in in arf
                                                                            begin//destreg is in ARF
                                                                                                        //MuxBsel
                                                                                                        MuxBSel=2'b00;
                                                                                                        //ARFregsel
                                                                                                        case(destination_register)
                                                                                                        4'b0100:
                                                                                                        begin
                                                                                                            ARF_RegSel=4'b0010;//SP
                                                                                                        end
                                                                                                        4'b0101:
                                                                                                        begin
                                                                                                            ARF_RegSel=4'b0100;//AR
                                                                                                        end
                                                                                                        4'b0110:
                                                                                                        begin
                                                                                                            ARF_RegSel=4'b1000;//PC
                                                                                                        end
                                                                                                        4'b0111:
                                                                                                        begin
                                                                                                            ARF_RegSel=4'b1000;//PC
                                                                                                        end
                                                                                                        endcase
                                                                            
                                                                                                        ARF_FunSel=2'b01;
                                                                                                        //ARF funsel
                                                                                                        timer_funsel=0;//reset
                                                                                                    end
                                                                                                    
                                                      else
                                                      begin
                                                                            
                                                    
                                                     timer_funsel=1;//increase timer
                                                    MuxASel= 2'b00;
                                                     end
                        end
                           
                            
                            if(timer_out==8'd3)
                        begin
                            RF_FunSel = 2'b01; //load ilkindeki i?lem bir önceki ile ayn? 
                            case(destination_register)
                             4'h0: begin RF_RSel = 4'b1000;   end //sadece load lanaca?? enable yap yazd?rmana gerek yok
                             4'h1: begin RF_RSel = 4'b0100;      end
                             4'h2:begin RF_RSel = 4'b0010;        end
                             4'h3: begin RF_RSel = 4'b0001;       end
                            endcase        
                             timer_funsel=0;//clear timer
                        end
                       
                            
                        end
                        4'h5: 
                        begin
                               
                        MuxCSel = 0; //rf outputu seçiyoruz
                        ALU_FunSel = 4'b1100; //alu içinde lsr i?lemini seçtik
                        //muxsela ne olacak mevcut durumda m? kal?cak
                        if(timer_out==8'd2)
                        begin
                            case(source_register1)
                                4'h0:begin RF_OutASel = 3'b100;end
                                4'h1:  begin RF_OutASel = 3'b101; end
                                4'h2: begin RF_OutASel = 3'b110;   end
                                4'h3: begin RF_OutASel = 3'b111;     end
                           endcase 
                                if(destination_register[2]==1)//destreg in in arf
                                                                           begin//destreg is in ARF
                                                                                                       //MuxBsel
                                                                                                       MuxBSel=2'b00;
                                                                                                       //ARFregsel
                                                                                                       case(destination_register)
                                                                                                       4'b0100:
                                                                                                       begin
                                                                                                           ARF_RegSel=4'b0010;//SP
                                                                                                       end
                                                                                                       4'b0101:
                                                                                                       begin
                                                                                                           ARF_RegSel=4'b0100;//AR
                                                                                                       end
                                                                                                       4'b0110:
                                                                                                       begin
                                                                                                           ARF_RegSel=4'b1000;//PC
                                                                                                       end
                                                                                                       4'b0111:
                                                                                                       begin
                                                                                                           ARF_RegSel=4'b1000;//PC
                                                                                                       end
                                                                                                       endcase
                                                                           
                                                                                                       ARF_FunSel=2'b01;
                                                                                                       //ARF funsel
                                                                                                       timer_funsel=0;//reset
                                                                                                   end
                                                                                                   
                                                     else
                                                     begin
                                                                           
                                                   
                                                    timer_funsel=1;//increase timer
                                                   MuxASel= 2'b00;
                                                    end
                       end
                           
                            
                          if(timer_out==8'd3)
                          begin
                            RF_FunSel = 2'b01; //load ilkindeki i?lem bir önceki ile ayn? 
                        case(destination_register)
                                 4'h0: begin RF_RSel = 4'b1000;   end //sadece load lanaca?? enable yap yazd?rmana gerek yok
                                 4'h1: begin RF_RSel = 4'b0100;      end
                                 4'h2:begin RF_RSel = 4'b0010;        end
                                 4'h3: begin RF_RSel = 4'b0001;       end
                        endcase    
                          timer_funsel=0;//clear timer
                        end 
                        
                        end
                        4'h6: 
                        begin
                                   
                        MuxCSel = 0; //rf outputu seçiyoruz
                        ALU_FunSel = 4'b1011; //alu içinde lsr i?lemini seçtik
                        //muxsela ne olacak mevcut durumda m? kal?cak
                        if(timer_out==8'd2)
                        begin
                        case(source_register1)
                            4'h0:begin RF_OutASel = 3'b100;end
                            4'h1:  begin RF_OutASel = 3'b101; end
                            4'h2: begin RF_OutASel = 3'b110;   end
                            4'h3: begin RF_OutASel = 3'b111;     end
                       endcase 
                            MuxASel= 2'b00;
                            timer_funsel=1;//increase timer
                          end  
                            if(timer_out==8'd3)
                            begin
                                RF_FunSel = 2'b01; //load ilkindeki i?lem bir önceki ile ayn? 
                                case(destination_register)
                                         4'h0: begin RF_RSel = 4'b1000;   end //sadece load lanaca?? enable yap yazd?rmana gerek yok
                                         4'h1: begin RF_RSel = 4'b0100;      end
                                         4'h2:begin RF_RSel = 4'b0010;        end
                                         4'h3: begin RF_RSel = 4'b0001;       end
                                endcase      
                            
                                timer_funsel=0;//clear timer
                            end
                        end
                        4'h7: //DSTREG<-SREG1+1
                                    begin
                                        
                                        if(timer_out==8'd2)
                                        begin
                                            if (source_register1[2]==0)//source register is in RF
                                            begin
                                                //RFOUTB
                                                RF_OutBSel={1'b1, source_register1[1:0]};
                                                
                                                //ALU FUNSEL
                                                ALU_FunSel=4'b0001;
                                                if(destination_register[2]==0)//destreg in in rf
                                                begin
                                                
                                                    //MuxASel
                                                    MuxASel=2'b00;
                                                    //RF regsel
                                                    case(destination_register)
                                                        4'b0000:
                                                        begin
                                                            RF_RSel=4'b1000;
                                                        end
                                                        4'b0001:
                                                        begin
                                                            RF_RSel=4'b0100;
                                                        end
                                                        4'b0010:
                                                        begin
                                                            RF_RSel=4'b0010;
                                                        end
                                                        4'b0011:
                                                        begin
                                                            RF_RSel=4'b0001;
                                                        end
                                                    endcase
                                                    //RF funsel
                                                    RF_FunSel=2'b01;
                                                end
                                                else
                                                begin//destreg is in ARF
                                                    //MuxBsel
                                                    MuxBSel=2'b00;
                                                    //ARFregsel
                                                    case(destination_register)
                                                    4'b0100:
                                                    begin
                                                        ARF_RegSel=4'b0010;//SP
                                                    end
                                                    4'b0101:
                                                    begin
                                                        ARF_RegSel=4'b0100;//AR
                                                    end
                                                    4'b0110:
                                                    begin
                                                        ARF_RegSel=4'b1000;//PC
                                                    end
                                                    4'b0111:
                                                    begin
                                                        ARF_RegSel=4'b1000;//PC
                                                    end
                                                    endcase
                        
                                                    ARF_FunSel=2'b01;
                                                    //ARF funsel
                                                end
                        
                                            end
                                        else //source register is in ARF
                                        begin
                                                //ARFOUTA
                                                case(source_register1)
                                                4'b0100:
                                                begin
                                                    ARF_OutCSel=2'b01;
                                                end
                                                4'b0101:
                                                begin
                                                    ARF_OutCSel=2'b00;
                                                end
                                                4'b0110:
                                                begin
                                                
                                                    ARF_OutCSel=2'b11;
                                                end
                                                4'b0111:
                                                begin
                                                    ARF_OutCSel=2'b11;
                                                end
                                                endcase
                                                if(destination_register[2]==0)//destreg in in rf
                                                begin
                                                
                                                    //MuxASel
                                                    MuxASel=2'b11;//ARFOUT
                                                    //RF regsel
                                                    
                                                    case(destination_register)
                                                    4'b0000:
                                                    begin
                                                        RF_RSel=4'b1000;
                                                    end
                                                    4'b0001:
                                                    begin
                                                        RF_RSel=4'b0100;
                                                    end
                                                    4'b0010:
                                                    begin
                                                        RF_RSel=4'b0010;
                                                    end
                                                    4'b0011:
                                                    begin
                                                        RF_RSel=4'b0001;
                                                    end
                                                    endcase
                                                    //RF funsel
                                                    RF_FunSel=2'b01;
                                                    
                                                end
                                                else
                                                begin//destreg is in ARF
                                                    //MuxBsel
                                                    MuxBSel=2'b11;
                                                    //ARFregsel
                                                    case(destination_register)
                                                    4'b0100:
                                                    begin
                                                        ARF_RegSel=4'b0010;//SP
                                                    end
                                                    4'b0101:
                                                    begin
                                                        ARF_RegSel=4'b0100;//AR
                                                    end
                                                    4'b0110:
                                                    begin
                                                        ARF_RegSel=4'b1000;//PC
                                                    end
                                                    4'b0111:
                                                    begin
                                                        ARF_RegSel=4'b1000;//PC
                                                    end
                                                    endcase
                        
                                                    ARF_FunSel=2'b01;
                                                    //ARF funsel
                                                end
                                            end
                                            timer_funsel=1;
                                        end
                                        if(timer_out==3)
                                        begin
                                            if(destination_register[2]==0)//destreg in rf
                                            begin
                                                                                           case(destination_register)
                                                                                           4'b0000:
                                                                                           begin
                                                                                               RF_RSel=4'b1000;
                                                                                           end
                                                                                           4'b0001:
                                                                                           begin
                                                                                               RF_RSel=4'b0100;
                                                                                           end
                                                                                           4'b0010:
                                                                                           begin
                                                                                               RF_RSel=4'b0010;
                                                                                           end
                                                                                           4'b0011:
                                                                                           begin
                                                                                               RF_RSel=4'b0001;
                                                                                           end
                                                                                           endcase
                                                                                           //RF funsel
                                                                                           RF_FunSel=2'b11;//increment                                   
                                        end
                                        else//destreg in ARF
                                        begin
                                                                                            case(destination_register)
                                                                                            4'b0100:
                                                                                            begin
                                                                                                ARF_RegSel=4'b0010;//SP
                                                                                            end
                                                                                            4'b0101:
                                                                                            begin
                                                                                                ARF_RegSel=4'b0100;//AR
                                                                                            end
                                                                                            4'b0110:
                                                                                            begin
                                                                                                ARF_RegSel=4'b1000;//PC
                                                                                            end
                                                                                            4'b0111:
                                                                                            begin
                                                                                                ARF_RegSel=4'b1000;//PC
                                                                                            end
                                                                                            endcase
                                                                
                                                                                            ARF_FunSel=2'b11;//increment
                                                                                            //ARF funsel                                       
                                        end
                                   
                                    timer_funsel=0;
                                     end
                                    end
                        4'h8: //DSTREG<-SREG1-1
 begin
                                                               
                                                               if(timer_out==8'd2)
                                                               begin
                                                                   if (source_register1[2]==0)//source register is in RF
                                                                   begin
                                                                       //RFOUTB
                                                                       RF_OutBSel={1'b1, source_register1[1:0]};
                                                                       
                                                                       //ALU FUNSEL
                                                                       ALU_FunSel=4'b0001;
                                                                       if(destination_register[2]==0)//destreg in in rf
                                                                       begin
                                                                       
                                                                           //MuxASel
                                                                           MuxASel=2'b00;
                                                                           //RF regsel
                                                                           case(destination_register)
                                                                               4'b0000:
                                                                               begin
                                                                                   RF_RSel=4'b1000;
                                                                               end
                                                                               4'b0001:
                                                                               begin
                                                                                   RF_RSel=4'b0100;
                                                                               end
                                                                               4'b0010:
                                                                               begin
                                                                                   RF_RSel=4'b0010;
                                                                               end
                                                                               4'b0011:
                                                                               begin
                                                                                   RF_RSel=4'b0001;
                                                                               end
                                                                           endcase
                                                                           //RF funsel
                                                                           RF_FunSel=2'b01;
                                                                       end
                                                                       else
                                                                       begin//destreg is in ARF
                                                                           //MuxBsel
                                                                           MuxBSel=2'b00;
                                                                           //ARFregsel
                                                                           case(destination_register)
                                                                           4'b0100:
                                                                           begin
                                                                               ARF_RegSel=4'b0010;//SP
                                                                           end
                                                                           4'b0101:
                                                                           begin
                                                                               ARF_RegSel=4'b0100;//AR
                                                                           end
                                                                           4'b0110:
                                                                           begin
                                                                               ARF_RegSel=4'b1000;//PC
                                                                           end
                                                                           4'b0111:
                                                                           begin
                                                                               ARF_RegSel=4'b1000;//PC
                                                                           end
                                                                           endcase
                                               
                                                                           ARF_FunSel=2'b01;
                                                                           //ARF funsel
                                                                       end
                                               
                                                                   end
                                                               else //source register is in ARF
                                                               begin
                                                                       //ARFOUTA
                                                                       case(source_register1)
                                                                       4'b0100:
                                                                       begin
                                                                           ARF_OutCSel=2'b01;
                                                                       end
                                                                       4'b0101:
                                                                       begin
                                                                           ARF_OutCSel=2'b00;
                                                                       end
                                                                       4'b0110:
                                                                       begin
                                                                       
                                                                           ARF_OutCSel=2'b11;
                                                                       end
                                                                       4'b0111:
                                                                       begin
                                                                           ARF_OutCSel=2'b11;
                                                                       end
                                                                       endcase
                                                                       if(destination_register[2]==0)//destreg in in rf
                                                                       begin
                                                                       
                                                                           //MuxASel
                                                                           MuxASel=2'b11;//ARFOUT
                                                                           //RF regsel
                                                                           
                                                                           case(destination_register)
                                                                           4'b0000:
                                                                           begin
                                                                               RF_RSel=4'b1000;
                                                                           end
                                                                           4'b0001:
                                                                           begin
                                                                               RF_RSel=4'b0100;
                                                                           end
                                                                           4'b0010:
                                                                           begin
                                                                               RF_RSel=4'b0010;
                                                                           end
                                                                           4'b0011:
                                                                           begin
                                                                               RF_RSel=4'b0001;
                                                                           end
                                                                           endcase
                                                                           //RF funsel
                                                                           RF_FunSel=2'b01;
                                                                           
                                                                       end
                                                                       else
                                                                       begin//destreg is in ARF
                                                                           //MuxBsel
                                                                           MuxBSel=2'b11;
                                                                           //ARFregsel
                                                                           case(destination_register)
                                                                           4'b0100:
                                                                           begin
                                                                               ARF_RegSel=4'b0010;//SP
                                                                           end
                                                                           4'b0101:
                                                                           begin
                                                                               ARF_RegSel=4'b0100;//AR
                                                                           end
                                                                           4'b0110:
                                                                           begin
                                                                               ARF_RegSel=4'b1000;//PC
                                                                           end
                                                                           4'b0111:
                                                                           begin
                                                                               ARF_RegSel=4'b1000;//PC
                                                                           end
                                                                           endcase
                                               
                                                                           ARF_FunSel=2'b01;
                                                                           //ARF funsel
                                                                       end
                                                                   end
                                                                   timer_funsel=1;
                                                               end
                                                               if(timer_out==3)
                                                               begin
                                                                   if(destination_register[2]==0)//destreg in rf
                                                                   begin
                                                                                                                  case(destination_register)
                                                                                                                  4'b0000:
                                                                                                                  begin
                                                                                                                      RF_RSel=4'b1000;
                                                                                                                  end
                                                                                                                  4'b0001:
                                                                                                                  begin
                                                                                                                      RF_RSel=4'b0100;
                                                                                                                  end
                                                                                                                  4'b0010:
                                                                                                                  begin
                                                                                                                      RF_RSel=4'b0010;
                                                                                                                  end
                                                                                                                  4'b0011:
                                                                                                                  begin
                                                                                                                      RF_RSel=4'b0001;
                                                                                                                  end
                                                                                                                  endcase
                                                                                                                  //RF funsel
                                                                                                                  RF_FunSel=2'b10;//increment                                   
                                                               end
                                                               else//destreg in ARF
                                                               begin
                                                                                                                   case(destination_register)
                                                                                                                   4'b0100:
                                                                                                                   begin
                                                                                                                       ARF_RegSel=4'b0010;//SP
                                                                                                                   end
                                                                                                                   4'b0101:
                                                                                                                   begin
                                                                                                                       ARF_RegSel=4'b0100;//AR
                                                                                                                   end
                                                                                                                   4'b0110:
                                                                                                                   begin
                                                                                                                       ARF_RegSel=4'b1000;//PC
                                                                                                                   end
                                                                                                                   4'b0111:
                                                                                                                   begin
                                                                                                                       ARF_RegSel=4'b1000;//PC
                                                                                                                   end
                                                                                                                   endcase
                                                                                       
                                                                                                                   ARF_FunSel=2'b10;//increment
                                                                                                                   //ARF funsel                                       
                                                               end
                                                          
                                                           timer_funsel=0;
                                                            end
                                                            end                                               
                                                
            4'h9: //PC<-VALUE
            begin
                //ARFOUTB<-Address - Indirect
                if(timer_out==8'd3)
                begin
                ARF_OutDSel=2'b00;//out AR
                Mem_WR = 0;//Memory Read
                MuxBSel=2'b01;//Mux B <- Memory
                // Load PC
                ARF_RegSel=4'b0100;//select AR
                ARF_FunSel=2'b01;//Load Address to AR
                timer_funsel=1;
                end
                if(timer_out==8'd4)
                begin
                    ARF_OutDSel=2'b00;//out AR
                    Mem_WR=0;//Memory Read
                    MuxBSel=2'b01;//Mux B <- Memory
                    // Load PC
                    ARF_RegSel=4'b1000;//select PC
                    ARF_FunSel=2'b01;//Load Address to PC
                    timer_funsel=0;
                end
                end
            
            4'hA: //IF Z=0 THEN PC?VALUE
            begin
                if(ALUFlag[3]==0)//Z==0
                begin
                    if(timer_out==8'd3)
                    begin
                        ARF_OutDSel=2'b00;//out AR
                        Mem_WR=0;//Memory Read
                        MuxBSel=2'b01;//Mux B <- Memory
                        // Load PC
                        ARF_RegSel=4'b0100;//select AR
                        ARF_FunSel=2'b01;//Load Address to AR
                        timer_funsel=1;
                    end
                    if(timer_out==8'd4)
                    begin
                        ARF_OutDSel=2'b00;//out AR
                        Mem_WR=0;//Memory Read
                        MuxBSel=2'b01;//Mux B <- Memory
                        // Load PC
                        ARF_RegSel=4'b1000;//select PC
                        ARF_FunSel=2'b01;//Load Address to PC
                        timer_funsel=0;
                    end
                end
            end
        
            4'hB: //DSTREG<-SREG1
            begin
               
                if(timer_out==8'd3)
                begin
                    if (source_register1[2]==0)//source register is in RF
                    begin
                        //RFOUTB
                        RF_OutBSel={1'b1, source_register1[1:0]};
                        
                        //ALU FUNSEL
                        ALU_FunSel=4'b0001;
                        if(destination_register[2]==0)//destreg in in rf
                        begin
                        ;
                            //MuxASel
                            MuxASel=2'b00;
                            //RF regsel
                            case(destination_register)
                                4'b0000:
                                begin
                                    RF_RSel=4'b1000;
                                end
                                4'b0001:
                                begin
                                    RF_RSel=4'b0100;
                                end
                                4'b0010:
                                begin
                                    RF_RSel=4'b0010;
                                end
                                4'b0011:
                                begin
                                    RF_RSel=4'b0001;
                                end
                            endcase
                            //RF funsel
                            RF_FunSel=2'b01;
                        end
                        else
                        begin//destreg is in ARF
                            //MuxBsel
                            MuxBSel=2'b00;
                            //ARFregsel
                            case(destination_register)
                            4'b0100:
                            begin
                                ARF_RegSel=4'b0010;//SP
                            end
                            4'b0101:
                            begin
                                ARF_RegSel=4'b0100;//AR
                            end
                            4'b0110:
                            begin
                                ARF_RegSel=4'b1000;//PC
                            end
                            4'b0111:
                            begin
                                ARF_RegSel=4'b1000;//PC
                            end
                            endcase

                            ARF_FunSel=2'b01;
                            //ARF funsel
                        end

                    end
                else //source register is in ARF
                begin
                        //ARFOUTA
                        case(source_register1)
                        4'b0100:
                        begin
                            ARF_OutCSel=2'b01;
                        end
                        4'b0101:
                        begin
                            ARF_OutCSel=2'b00;
                        end
                        4'b0110:
                        begin
                        
                            ARF_OutCSel=2'b11;
                        end
                        4'b0111:
                        begin
                            ARF_OutCSel=2'b11;
                        end
                        endcase
                        if(destination_register[2]==0)//destreg in in rf
                        begin
                        
                            //MuxASel
                            MuxASel=2'b11;//ARFOUT
                            //RF regsel
                            
                            case(destination_register)
                            4'b0000:
                            begin
                                RF_RSel=4'b1000;
                            end
                            4'b0001:
                            begin
                                RF_RSel=4'b0100;
                            end
                            4'b0010:
                            begin
                                RF_RSel=4'b0010;
                            end
                            4'b0011:
                            begin
                                RF_RSel=4'b0001;
                            end
                            endcase
                            //RF funsel
                            RF_FunSel=2'b01;
                            
                        end
                        else
                        begin//destreg is in ARF
                            //MuxBsel
                            MuxBSel=2'b11;
                            //ARFregsel
                            case(destination_register)
                            4'b0100:
                            begin
                                ARF_RegSel=4'b0010;//SP
                            end
                            4'b0101:
                            begin
                                ARF_RegSel=4'b0100;//AR
                            end
                            4'b0110:
                            begin
                                ARF_RegSel=4'b1000;//PC
                            end
                            4'b0111:
                            begin
                                ARF_RegSel=4'b1000;//PC
                            end
                            endcase

                            ARF_FunSel=2'b01;
                            //ARF funsel
                        end
                    end
                    timer_funsel=0;
                end
            end
            4'hC: //Rx?VALUE 
            begin
                //address in outB de olud?unu varsay
                //read value from memory
                if(timer_out==8'd3)
                begin
                    
                    if(addresing_mode==1)
                    begin
                       //do nothing
                    end   
                    else 
                    begin
                       
                        
                        Mem_WR<=0;
                        MuxBSel<=2'b01;
                        ARF_RegSel<=4'b0100;//Select AR
                        ARF_FunSel=2'b01;//Load Address to AR
                        
                    end 
                    timer_funsel=1;
                end
                if(timer_out==8'd4)
                begin
                    
                    //address is ready now
                        ARF_OutDSel=2'b00;//out AR
                        Mem_WR=0;//Memory Read
                        MuxASel=2'b01;//MuxAOut<-Value
                        //Select Rx
                        case(regsel)
                        2'b00:
                        begin
                            RF_RSel=4'b1000;
                        end
                        2'b01:
                        begin
                            RF_RSel=4'b0100;
                        end
                        2'b10:
                        begin
                            RF_RSel=4'b0010;
                        end
                        2'b11:
                        begin
                            RF_RSel=4'b0001;
                        end
                        endcase
                        //Load the value to the Rx
                        RF_FunSel=2'b01;
                   timer_funsel=0;
                   
            end
            end
            4'hD: //VALUE?Rx
            begin
                if(timer_out==8'd3)
                begin
                   
                    //Memory read the value
                    Mem_WR=0;
                    //AR<-Value
                    MuxBSel=2'b01;
                    ARF_RegSel=4'b0100;//Select AR
                    ARF_FunSel=2'b01;//Load Address to AR
                    timer_funsel=1;
                end
                if(timer_out==8'd4)
                begin
                    
                    //select RFO2SEL
                    RF_OutBSel = {1'b1,regsel};
                    ALU_FunSel=4'b0001; //ALU Out direct B
                    //write 
                    ARF_OutDSel=2'b00;//out AR
                    Mem_WR=1;
                    timer_funsel=0;
                end
                
            end
            4'hE: //SP ? SP + 1, Rx ? M[SP]
            begin
                if(timer_out==8'd3)
                begin
                    ARF_OutDSel=2'b01;//out SP
                    Mem_WR=0;//read M[SP]
                    MuxASel=2'b01;//MuxAOut<-M[SP]
                    case(regsel)//select Rx
                        2'b00:
                        begin
                            RF_RSel=4'b1000;
                        end
                        2'b01:
                        begin
                            RF_RSel=4'b0100;
                        end
                        2'b10:
                        begin
                            RF_RSel=4'b0010;
                        end
                        2'b11:
                        begin
                            RF_RSel=4'b0001;
                        end
                        endcase
                        //Load the M[SP] to the Rx
                        RF_FunSel=2'b01;
                        timer_funsel=1;
                end
                if(timer_out==8'd4)
                begin
                    ARF_RegSel=4'b0010;
                    ARF_FunSel=2'b11;//increase SP
                    timer_funsel=0;
                end
            end
            
            4'hF: //M[SP] ? Rx, SP ? SP - 1
            begin
                if(timer_out==8'd3)
                begin
                    ARF_RegSel=4'b0010;
                    ARF_FunSel=2'b10;//decrease SP
                    timer_funsel=1;
                end
                
                if(timer_out==8'd4)
                begin
                    ARF_OutDSel=2'b01;//Out SP
                    RF_OutBSel={1'b1,regsel};
                    ALU_FunSel=4'b0001; //ALU Out direct B
                    //write 
                    Mem_WR<=1;
                    timer_funsel=0;
                end
            end
            

            endcase
          end
          
       end
       
       else
                begin
                            timer_funsel = 0;
                            RF_RSel= 4'b1111;
                            RF_FunSel= 2'b00;
                            ARF_RegSel= 4'b1111;
                            ARF_FunSel= 2'b00;
                            IR_Enable= 1;
                            IR_Funsel= 2'b00;
                           
                  end
end

timer_8_bit sequencecounter(Clock, timer_funsel,timer_out);
endmodule


module CPUSystem(Clock, Reset, T);
    input wire Clock;
    input wire Reset;
    wire[2:0] RF_OutASel; 
    wire[2:0] RF_OutBSel; 
    wire[1:0] RF_FunSel;
    wire[3:0] RF_RegSel;
    wire[3:0] RF_TSel;
    wire[3:0] ALU_FunSel;
    wire[1:0] ARF_OutCSel; 
    wire[1:0] ARF_OutDSel; 
    wire[1:0] ARF_FunSel;
    wire[3:0] ARF_RegSel;
    wire IR_LH;
    wire IR_Enable;
    wire[1:0] IR_Funsel;
    wire Mem_WR;
    wire Mem_CS;
    wire[1:0] MuxASel;
    wire[1:0] MuxBSel;
    wire MuxCSel;
       
    wire [7:0] AOut, BOut;
    assign AOut=alusys.AOut;
    assign BOut=alusys.BOut;
    wire [7:0] ALUOut;
    assign ALUOut=alusys.ALUOut;
    wire [3:0] ALUOutFlag;
    assign ALUOutFlag= alusys.ALUOutFlag;
    wire [7:0] ARF_COut;
    assign ARF_COut=alusys.ARF_COut;
    wire [7:0] Address;
    wire [7:0] MemoryOut;
    assign MemoryOut=alusys.MemoryOut;
    wire [15:0] IR_Out;
    wire [7:0] IRhalf;
    assign IRhalf=alusys.IROut;
    assign IR_Out=alusys.output_2a;
    
    
    wire [7:0] MuxAOut, MuxBOut, MuxCOut; 
    assign MuxAOut=alusys.MuxAOut;
    assign MuxBOut=alusys.MuxBOut;
    assign MuxCOut=alusys.MuxCOut; 
    assign Address= alusys.Address;
    //wires below are used for debug, they can be deleted from outputs of hcu
    wire [3:0] opcode;
    wire addressing;
    wire [7:0] op_address;
    wire [1:0] regsel;
    wire [3:0] destreg, srcreg1, srcreg2;
    wire mem_ref_op;
    wire timerFunSel;
    output wire [7:0] T;
    
     
     
     ALU_System alusys(
        RF_OutASel,
        RF_OutBSel,
        RF_FunSel,
        RF_RegSel,
        RF_TSel,
        ALU_FunSel,
        ARF_OutCSel,
        ARF_OutDSel,
        ARF_FunSel,
        ARF_RegSel,
        IR_LH,
        IR_Enable,
        IR_Funsel,
        Mem_WR,
        Mem_CS,
        MuxASel,
        MuxBSel,
        MuxCSel,
        Clock
        );
    

    HardwiredControlUnit hcu(
           
            IR_Out,
            ALUOutFlag,
            
            RF_OutASel, 
            RF_OutBSel, 
            RF_FunSel,
            RF_RegSel,
            ALU_FunSel,
            ARF_OutCSel, 
            ARF_OutDSel, 
            ARF_FunSel,
            ARF_RegSel,
            IR_LH,
            IR_Enable,
            IR_Funsel,
            Mem_WR,
            Mem_CS,
            MuxASel,
            MuxBSel,
            MuxCSel,
            
            
            opcode,
            addressing,
            regsel, 
            op_address,
            destreg,
            srcreg1,
            srcreg2,
            
            timerFunSel,
            T, 
            Reset,
            mem_ref_op,
            Clock);
    
    
    
endmodule
