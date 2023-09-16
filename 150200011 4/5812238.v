`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 30.03.2023 09:47:26
// Design Name: 
// Module Name: modules_for_register
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
            
            if (en == 0) begin
                
            end else if(FunSel== 00)
            begin
                O = 0;
                
            end else if(FunSel == 01)
            begin
                O = I;
               
            end else if(FunSel == 10)
            begin
                O = O - 1;
            end else if(FunSel == 11)
            begin
                O = O + 1;
            end
            
            
        end
        endmodule
  
module two_a(
            input en,clk,
            input [1:0]funsel,
            input [7:0]I,
            input low_high,
            output reg [15:0]O
            );
         
            
        
            always @(posedge clk)begin
                    
                    if (en == 0) begin
                    O = O;
                    end else if(funsel[0] == 0 && funsel[1] == 0)
                    begin
                        O = 0;
                        
                    end else if(funsel[0] == 1 && funsel[1] == 0)
                    begin
                        if(low_high == 0)
                        begin
                            O[7:0] = I;
                        end else if(low_high == 1)
                        begin
                              O[15:8] = I;
                        end
                        
                       
                    end
                    else if(funsel[0] == 0 && funsel[1] == 1)
                    begin
                        O = O - 1;
                    end else if(funsel[0] == 1 && funsel[1] == 1)
                    begin
                        O = O + 1;
                    end
                end
                
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
            output  [7:0] ARF_AOut, ARF_BOut
        );
          
          wire [7:0] PCOut, AROut, SPOut,PCPastOut; // multiplexer output signals
        
          n_bit_register #(8) PC(RSel[3], FunSel, inData, PCOut, clk ); // registers for each address register
          n_bit_register #(8) AR(RSel[2], FunSel, inData, AROut, clk );
          n_bit_register #(8) SP(RSel[1], FunSel, inData, SPOut, clk );
          n_bit_register #(8) PCPast(RSel[0], FunSel, inData, PCPastOut, clk);
          // mux for selecting OutA
            mux4to1 amux(ARF_AOut,OutASel, AROut,SPOut,  PCPastOut, PCOut);
          
          // mux for selecting OutB
          mux4to1 bmux(ARF_BOut,OutBSel, AROut,SPOut,  PCPastOut, PCOut);
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

reg[8:0] temp;;
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
           OutAlu <= ~B;
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
    wire [15:0]output_2a;
    wire [7:0]IROut;
    wire [3:0]ALUOutFlag;
 

    Memory m1( Address, ALUOut, Mem_WR, Mem_CS, Clock, MemoryOut );
    two_a twoo(IR_Enable, Clock ,IR_Funsel , MemoryOut , IR_LH , output_2a);
    assign IROut = output_2a[7:0];
    mux4to1 muxA( MuxAOut , MuxASel , ALUOut , MemoryOut , IROut, ARF_COut );
    mux4to1 muxB( MuxBOut , MuxBSel , ALUOut , MemoryOut , IROut , ARF_COut ); //3 m  4 m  olcak
    ARF arf1(Clock, MuxBOut , ARF_FunSel , ARF_RegSel , ARF_OutCSel , ARF_OutDSel , ARF_COut, Address );
    part_2b b2( MuxAOut, RF_OutASel , RF_OutBSel , RF_FunSel , RF_RSel,RF_TSel , AOut, BOut, Clock );
    mux2to1 mucC( MuxCOut , MuxCSel , AOut, ARF_COut );
    ALU a1( MuxCOut, BOut , ALU_FunSel , ALUOutFlag[2] , ALUOut , ALUOutFlag );
   
   
    
    
    

endmodule
