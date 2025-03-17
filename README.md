# Lab 2 Design
This single-cycle RISC-V processor executes one instruction per clock cycle. It has two main parts: the controller and the datapath. The controller decodes instructions using opcode, funct3, and funct7 to generate control signals like RegWrite, ALUSrc, and Branch, which determine how data moves through the processor. The datapath takes care of updating the program counter (PC), accessing the register file, performing arithmetic or logic operations with the ALU, and generating immediate values.

It supports different types of instructions, including R-type, I-type, S-type, B-type, U-type, and J-type. Load and store operations work with bytes, halfwords, and words, using sign or zero extension as needed. Those instructions utilize the loadextend and store modules. 

Branching is handled using the ALU’s Zero, Carry, and overflow flags, while jump instructions update the PC and store return addresses. Memory accesses are word-aligned, with lw/sw moving data between registers and memory.
