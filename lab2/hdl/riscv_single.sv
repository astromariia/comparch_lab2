
// riscvsingle.sv

// RISC-V single-cycle processor
// From Section 7.6 of Digital Design & Computer Architecture
// 27 April 2020
// David_Harris@hmc.edu 
// Sarah.Harris@unlv.edu

// run 210
// Expect simulator to print "Simulation succeeded"
// when the value 25 (0x19) is written to address 100 (0x64)

//   Instruction  opcode    funct3    funct7
//   add          0110011   000       0000000
//   sub          0110011   000       0100000
//   and          0110011   111       0000000
//   or           0110011   110       0000000
//   slt          0110011   010       0000000
//   addi         0010011   000       immediate
//   andi         0010011   111       immediate
//   ori          0010011   110       immediate
//   slti         0010011   010       immediate
//   beq          1100011   000       immediate
//   lw	          0000011   010       immediate
//   sw           0100011   010       immediate
//   jal          1101111   immediate immediate

// xor            0110011  100        0000000
// xori           0010011  100        0000000
//sll             0110011  001        0000000
//lui             0110111

module testbench();

   logic        clk;
   logic        reset;

   logic [31:0] WriteData;
   logic [31:0] DataAdr;
   logic        MemWrite;

   // instantiate device to be tested
   top dut(clk, reset, WriteData, DataAdr, MemWrite);

   initial
     begin
	string memfilename;
        memfilename = {"../testing/sh.memfile"};
        $readmemh(memfilename, dut.imem.RAM);
     end

   
   // initialize test
   initial
     begin
	reset <= 1; # 22; reset <= 0;
     end

   // generate clock to sequence tests
   always
     begin
	clk <= 1; # 5; clk <= 0; # 5;
     end

   // check results
   always @(negedge clk)
     begin
	if(MemWrite) begin
           if(DataAdr === 100 & WriteData === 25) begin
              $display("Simulation succeeded");
              $stop;
           end else if (DataAdr !== 96) begin
              $display("Simulation failed");
              $stop;
           end
	end
     end
endmodule // testbench

module riscvsingle (input  logic        clk, reset,
		    output logic [31:0] PC,
		    input  logic [31:0] Instr,
		    output logic 	MemWrite,
		    output logic [31:0] ALUResult, WriteData,
        output logic [1:0] loadcontrol,
		    input  logic [31:0] ReadData);
   
   logic 				ALUSrc, RegWrite, Jump, Zero;
   logic [1:0] 				ResultSrc;
   logic [2:0]        ImmSrc;
   logic [3:0] 				ALUControl;
   logic JalrControl;
   logic [1:0] ReginControl;
   
   controller c (Instr[6:0], Instr[14:12], Instr[30], Zero,v,Negative,Carry,
		 ResultSrc, MemWrite, PCSrc,
		 ALUSrc, RegWrite, Jump, JalrControl, loadcontrol, ReginControl,
		 ImmSrc, ALUControl,load);
   datapath dp (clk, reset, ResultSrc, PCSrc,
		ALUSrc, RegWrite,
		ImmSrc, ALUControl,
		Zero,v,Negative,Carry, PC, Instr,
		ALUResult, WriteData, ReadData, JalrControl, ReginControl,load);
   
endmodule // riscvsingle

module controller (input  logic [6:0] op,
		   input  logic [2:0] funct3,
		   input  logic       funct7b5,
		   input  logic       Zero,v,Negative,Carry,
		   output logic [1:0] ResultSrc,
		   output logic       MemWrite,
		   output logic       PCSrc, ALUSrc,
		   output logic       RegWrite, Jump, JalrControl,
       output logic [1:0]      loadcontrol,
        output logic [1:0] ReginControl,
		   output logic [2:0] ImmSrc,
		   output logic [3:0] ALUControl,
       output logic [2:0] load);
   
   logic [1:0] 			      ALUOp;
   logic 			      Branch;
   logic Branchout;

   maindec md (op, ResultSrc, MemWrite, Branch,
	       ALUSrc, RegWrite, Jump, JalrControl, ReginControl, ImmSrc, ALUOp);
   aludec ad (op[5], funct3, funct7b5, ALUOp, ALUControl);
   assign PCSrc = Branchout | Jump; //Branch & (Zero ^ funct3[0])
   always_comb
    case(funct3)
    3'b000: Branchout = Branch & Zero;                     // beg
    3'b001: Branchout = Branch & ~Zero;                    // bne
    3'b100: Branchout = Branch & (Negative != v);   // blt (signed)
    3'b101: Branchout = Branch & (Negative == v);   // bge (signed)
    3'b110: Branchout = Branch & ~Carry;                   // bltu (unsigned)
    3'b111: Branchout = Branch & Carry;                    // bgeu (unsigned)
    default: Branchout = 0;
  endcase
  always_comb 
    case (funct3)
        3'b000: loadcontrol = 2'b10; // SB (Store Byte)
        3'b001: loadcontrol = 2'b01; // SH (Store Halfword)
        3'b010: loadcontrol = 2'b00; // SW (Store Word)
        default: loadcontrol = 2'b00; // Default to SW
    endcase
    always_comb
     case (funct3)
    3'b000: load=3'b000;
    3'b001: load=3'b001;
    3'b010: load=3'b010;
    3'b100: load=3'b100;
    3'b101: load=3'b101;
    default: load=3'bx;

     endcase
endmodule // controller

module maindec (input  logic [6:0] op,
		output logic [1:0] ResultSrc,
		output logic 	   MemWrite,
		output logic 	   Branch, ALUSrc,
		output logic 	   RegWrite, Jump, JalrControl,
    output logic [1:0] ReginControl,
		output logic [2:0] ImmSrc,
		output logic [1:0] ALUOp);
   
   logic [14:0] 		   controls;
   
    assign {RegWrite, ReginControl, ImmSrc, ALUSrc, MemWrite,
            ResultSrc, Branch, ALUOp, Jump, JalrControl} = controls;

   
   always_comb
     case(op)
       // RegWrite_ReginControl_ImmSrc_ALUSrc_MemWrite_ResultSrc_Branch_ALUOp_Jump_JalrControl
       7'b0000011: controls = 15'b1_00_000_1_0_01_0_00_0_0; // lw
       7'b0100011: controls = 15'b0_00_001_1_1_00_0_00_0_0; // sw
       7'b0110011: controls = 15'b1_00_000_0_0_00_0_10_0_0; // R-type (corrected ImmSrc)
       7'b1100011: controls = 15'b0_00_010_0_0_00_1_01_0_0; // beq
       7'b0010011: controls = 15'b1_00_000_1_0_00_0_10_0_0; // I-type ALU
       7'b1101111: controls = 15'b1_00_011_0_0_10_0_00_1_0; // jal
       7'b0110111: controls = 15'b1_00_100_1_0_11_0_XX_0_0; // lui
       7'b0010111: controls = 15'b1_10_100_1_0_11_0_XX_0_0; // auipc
       //7'b1100111: controls = 15'b1_01_011_0_0_10_0_00_1_1; // jalr
       7'b1100111: controls = 15'b1_01_000_1_0_10_0_00_1_1; //jalr 
       default:    controls = 15'bx_xx_xxx_x_x_xx_x_xx_x_x; // default case
     endcase // case (op)
   
endmodule // maindec

module aludec (input  logic       opb5,
	       input  logic [2:0] funct3,
	       input  logic 	  funct7b5,
	       input  logic [1:0] ALUOp,
	       output logic [3:0] ALUControl);
   
   logic 			  RtypeSub;
   
   assign RtypeSub = funct7b5 & opb5; // TRUE for R–type subtract
   always_comb
     case(ALUOp)
       2'b00: ALUControl = 4'b0000; // addition
       2'b01: ALUControl = 4'b0001; // subtraction
       default: case(funct3) // R–type or I–type ALU
		  3'b000: if (RtypeSub)
		    ALUControl = 4'b0001; // sub
		  else
		    ALUControl = 4'b0000; // add, addi
		  3'b010: ALUControl = 4'b0101; // slt, slti
      3'b011: ALUControl = 4'b1001;   // sltu
		  3'b110: ALUControl = 4'b0011; // or, ori
		  3'b111: ALUControl = 4'b0010; // and, andi
      //Mariia - XOR Instruction
      3'b100: ALUControl = 4'b0100; //xor, xori
      3'b001: ALUControl = 4'b0110; // sll
      3'b101:
        if (funct7b5) ALUControl = 4'b1000; // sra
        else ALUControl = 4'b0111; // srl

		  default: ALUControl = 4'bxxx; // ???
		endcase // case (funct3)       
     endcase // case (ALUOp)
   
endmodule // aludec

module datapath (input  logic        clk, reset,
		 input  logic [1:0]  ResultSrc,
		 input  logic 	     PCSrc, ALUSrc,
		 input  logic 	     RegWrite,
		 input  logic [2:0]  ImmSrc,
		 input  logic [3:0]  ALUControl,
		 output logic 	     Zero,v,Negative,Carry,
		 output logic [31:0] PC,
		 input  logic [31:0] Instr,
		 output logic [31:0] ALUResult, WriteData,
		 input  logic [31:0] ReadData,
     input logic JalrControl,
     input logic [1:0] ReginControl,
     input logic [1:0] load);
   
   logic [31:0] 		     PCNext, PCPlus4, PCTarget, PCTargetNew;
   logic [31:0] 		     ImmExt;
   logic [31:0] 		     SrcA, SrcB;
   logic [31:0] 		     Result, ResultRF;
   logic [31:0]          LoadExtendOut;
   
   // next PC logic
   flopr #(32) pcreg (clk, reset, PCNext, PC);
   adder  pcadd4 (PC, 32'd4, PCPlus4);
   adder  pcaddbranch (PC, ImmExt, PCTarget);
   mux2 #(32)  pcmux (PCPlus4, PCTargetNew, PCSrc, PCNext);
   // register file logic
   regfile  rf (clk, RegWrite, Instr[19:15], Instr[24:20],
	       Instr[11:7], ResultRF, SrcA, WriteData);
   extend  ext (Instr[31:7], ImmSrc, ImmExt);
   // ALU logic
   mux2 #(32)  srcbmux (WriteData, ImmExt, ALUSrc, SrcB);
   alu  alu (SrcA, SrcB, ALUControl, ALUResult, Zero,v,Negative,Carry);
   mux4 #(32) resultmux (ALUResult, LoadExtendOut, PCPlus4,SrcB,ResultSrc, Result);
   mux3 #(32) Regwritesrc(Result,PCPlus4,PCTarget,ReginControl,ResultRF);
   mux2 #(32) PctargetJalr(PCTarget,ALUResult & ~32'h1,JalrControl,PCTargetNew);
   loadextend loader(ReadData,load,LoadExtendOut);

endmodule // datapath

module adder (input  logic [31:0] a, b,
	      output logic [31:0] y);
   
   assign y = a + b;
   
endmodule

module extend (input  logic [31:7] instr,
	       input  logic [2:0]  immsrc,
	       output logic [31:0] immext);
   
   always_comb
     case(immsrc)
       // I−type
       3'b000:  immext = {{20{instr[31]}}, instr[31:20]};
       // S−type (stores)
       3'b001:  immext = {{20{instr[31]}}, instr[31:25], instr[11:7]};
       // B−type (branches)
       3'b010:  immext = {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0};       
       // J−type (jal)
       3'b011:  immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};
       // U type (LUI)
       3'b100: immext= {instr[31:12], 12'b0000_0000_0000};

       default: immext = 32'bx; // undefinedRegWrite
     endcase // case (immsrc)
   
endmodule // extend
module loadextend(input logic[31:0] MemData, input logic [2:0] load,output logic [31:0] loadedMemory);
always_comb
case(load)
3'b000: loadedMemory={{26{Memdata[7]}},MemData[7:0]};
3'b001: loadedMemory={{16{Memdata[15]}},MemData[15:0]};
3'b010: loadedMemory=MemData;
3'b100: loadedMemory={{26{1'b0}},MemData[7:0]};
3'b101: loadedMemory={{16{1'b0}},MemData[15:0]};

default: loadedMemory=32'bx //undefined load
endcase//case load


endmodule
module flopr #(parameter WIDTH = 8)
   (input  logic             clk, reset,
    input logic [WIDTH-1:0]  d,
    output logic [WIDTH-1:0] q);
   
   always_ff @(posedge clk, posedge reset)
     if (reset) q <= 0;
     else  q <= d;
   
endmodule // flopr

module flopenr #(parameter WIDTH = 8)
   (input  logic             clk, reset, en,
    input logic [WIDTH-1:0]  d,
    output logic [WIDTH-1:0] q);
   
   always_ff @(posedge clk, posedge reset)
     if (reset)  q <= 0;
     else if (en) q <= d;
   
endmodule // flopenr

module mux2 #(parameter WIDTH = 8)
   (input  logic [WIDTH-1:0] d0, d1,
    input logic 	     s,
    output logic [WIDTH-1:0] y);
   
  assign y = s ? d1 : d0;
   
endmodule // mux2

module mux3 #(parameter WIDTH = 8)
   (input  logic [WIDTH-1:0] d0, d1, d2,
    input logic [1:0] 	     s,
    output logic [WIDTH-1:0] y);
   
  assign y = s[1] ? (d2) : (s[0] ? d1 : d0);
   
endmodule // mux3

module mux4 #(parameter WIDTH = 8)
   (input  logic [WIDTH-1:0] d0, d1, d2,d3,
    input logic [1:0] 	     s,
    output logic [WIDTH-1:0] y);
   
  assign y = s[1] ? (s[0] ? d3 : d2) : (s[0] ? d1 : d0);
   
endmodule // mux4

module top (input  logic        clk, reset,
	    output logic [31:0] WriteData, DataAdr,
	    output logic 	MemWrite);
   
   logic [31:0] 		PC, Instr, ReadData;
   logic [1:0]  loadcontrol;
   
   // instantiate processor and memories
   riscvsingle rv32single (clk, reset, PC, Instr, MemWrite, DataAdr,
			   WriteData, loadcontrol, ReadData);
   imem imem (PC, Instr);
   dmem dmem (clk, MemWrite, DataAdr, WriteData, loadcontrol,ReadData);
   
endmodule // top

module imem (input  logic [31:0] a,
	     output logic [31:0] rd);
   
   logic [31:0] 		 RAM[1500:0];
   
   assign rd = RAM[a[31:2]]; // word aligned
   
endmodule // imem

module dmem (input  logic        clk, we,
	     input  logic [31:0] a, wd,
       input logic [1:0] loadcontrol,
	     output logic [31:0] rd);
   
   logic [31:0] 		 RAM[255:0];
   
   assign rd = RAM[a[31:2]]; // word aligned
  //  always_ff @(posedge clk)
  //    if (we) RAM[a[31:2]] <= wd;
  always_ff @(posedge clk) begin
        if (we) begin
            case(loadcontrol)
                2'b00: RAM[a[31:2]] <= wd;                 // sw (store word)
                2'b01: // sh (store halfword)
                    if (a[1])                               // upper halfword
                        RAM[a[31:2]][31:16] <= wd[15:0];    // [31:16]
                    else                                    // lower halfword
                        RAM[a[31:2]][15:0] <= wd[15:0];     // [15:0]
                2'b10: RAM[a[31:2]][7:0] <= wd[7:0];        // sb (store byte)
                default: RAM[a[31:2]] <= wd;
            endcase
        end
    end
   
endmodule // dmem

module alu (input  logic [31:0] a, b,
            input  logic [3:0] 	alucontrol,
            output logic [31:0] result,
            output logic 	zero,v,Negative,Carry);

   logic [31:0] 	       condinvb, sum;
   logic 		       isAddSub;       // true when is add or subtract operation
    logic [32:0] Carryholder;

   assign condinvb = alucontrol[0] ? ~b : b;
   //assign sum = a + condinvb + alucontrol[0];
   assign sum = Carryholder[31:0];
   assign isAddSub = ~alucontrol[2] & ~alucontrol[1] |
                     ~alucontrol[1] & alucontrol[0]; 
   assign Carryholder = {1'b0, a} + {1'b0, condinvb} + alucontrol[0];   

   always_comb
     case (alucontrol)
       4'b0000:  result = sum;         // add
       4'b0001:  result = sum;         // subtract
       4'b0010:  result = a & b;       // and
       4'b0011:  result = a | b;       // or
       4'b0101:  result = sum[31] ^ v; // slt 
       4'b1001: result = (a < b) ? 32'd1 : 32'd0; //sltu
       4'b0100:  result = a ^ b;       // Mariia XOR 
       4'b0110:  result = a << b[4:0]; // sll /slli  
       4'b0111:  result = a >> b[4:0]; //srl/srli
       4'b1000: result = $signed(a) >>> b[4:0]; //sra/srai
       default: result = 32'bx;
     endcase

   assign zero = (result == 32'b0);
   assign v = ~(alucontrol[0] ^ a[31] ^ b[31]) & (a[31] ^ sum[31]) & isAddSub;
   assign Negative = (result[31]);
   assign Carry =  Carryholder[32];
   //assign Carry = (~alucontrol[1]& ((~a[31]&b[31]&~sum[31])|(a[31]&~b[31]&~sum[31])|(a[31]&b[31])) );
   
endmodule // alu

module regfile (input  logic        clk, 
		input  logic 	    we3, 
		input  logic [4:0]  a1, a2, a3, 
		input  logic [31:0] wd3, 
		output logic [31:0] rd1, rd2);

   logic [31:0] 		    rf[31:0];

   // three ported register file
   // read two ports combinationally (A1/RD1, A2/RD2)
   // write third port on rising edge of clock (A3/WD3/WE3)
   // register 0 hardwired to 0

   always_ff @(posedge clk)
     if (we3) rf[a3] <= wd3;	

   assign rd1 = (a1 != 0) ? rf[a1] : 0;
   assign rd2 = (a2 != 0) ? rf[a2] : 0;
   
endmodule // regfile
