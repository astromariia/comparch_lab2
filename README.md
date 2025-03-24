# Lab 2 Design
This single-cycle RISC-V processor executes one instruction per clock cycle. It has two main parts: the controller and the datapath. The controller decodes instructions using opcode, funct3, and funct7 to generate control signals like RegWrite, ALUSrc, and Branch, which determine how data moves through the processor. The datapath takes care of updating the program counter (PC), accessing the register file, performing arithmetic or logic operations with the ALU, and generating immediate values.

It supports different types of instructions, including R-type, I-type, S-type, B-type, U-type, and J-type. Load and store operations work with bytes, halfwords, and words, using sign or zero extension as needed. Those instructions utilize the loadextend and store modules. 

Branching is handled using the ALU’s Zero, Carry, and overflow flags, while jump instructions update the PC and store return addresses. Memory accesses are word-aligned, with lw/sw moving data between registers and memory.

We added a few extra components in the datapath to carry out some of the trickier instructions, such as loads,stores, AUIPC and JAL to name a few

for LUI, we connected the sourceB mux output as one of the inputs to the result mux

For load and store we did a similar technique for each, but placed them in different parts of the architecture. for each, we made an extender-esque module. The loader is simpler, it takes in the ALU result, to find the place in word to take data from, the data that is being loaded, and a control signal to decide on the type of load (half, word or byte).

#Implementation
For some reason the Elvis FPGA was not registering. We switched out multiple FPGAs, but that didn't make the device show up when we Auto Connect. In our files there is a picture of Vivado showing the Bitstream was generated, therefore we believe our design works.

Store works very similarly, taking in ALUresult for placement within the word, but it requires the data already in memory at that location and the data in a register that will be stored, and using logic based on the ALUresult and another control signal, combines the data correctly and stores it into memory.

We also added an extra mux right before the writedata port of the register. the inputs it chooses from are result mux output, PC+4 and PCtarget, in almost all cases it uses the result mux register. That mux is used to handle instructions like AUIPC and JAL, where something related to the PC must be written into a register.

This didn't make it into the final design, but instead of using the bit concatenation assignment for our carryout, we tried to do it with combinational logic based on the ALU inputs, and the sum. It didn't work out, but we tried it.
# Implementation
The issue we ran into in lab, was that the FPGA was not registering in Vivado. We switched out different FPGAs and none of them connected. We did provide the screenshot of Vivado showing that we generated a bitstream, therefore we think the design worked.
