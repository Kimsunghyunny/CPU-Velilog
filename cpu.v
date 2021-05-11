module testpc(
	clock,  // clock
	reset,  // reset
	pc,  // program counter
	instruction,  // command
	read_data1,  // first register data
	read_data2,  // second register data
	ext_imm_data,  // imm data
	alu_result,  // alu calculate value
	mem_data,  // data from memory
	reg_write_data,  // data for register
	imm_data, // set imm data
	mwrite_enable,
	mread_enable,
	read_addr1,
	read_addr2,
	write_addr
	);
	
	
	//input, output, reg, wire
	input clock, reset;
	
	output [15:0] pc, instruction, read_data1, read_data2, ext_imm_data, alu_result;
	output [15:0] reg_write_data, mem_data;
	output [6:0] imm_data;
	output mwrite_enable, mread_enable;
	output [2:0] read_addr1, read_addr2, write_addr;
	
	reg [15:0] pc, instruction, read_data1, read_data2, ext_imm_data, alu_result;
	reg [15:0] reg_write_data, mem_data;
	
	reg [15:0] jump_addr, branch_addr;
	reg [15:0] mwrite_addr, mread_addr;
	reg [6:0] imm_data;
	reg [2:0] read_addr1, read_addr2, write_addr;
	reg [1:0] result_sel;
	reg regwrite_enable, func_sel, imm_sel, mwrite_enable;
	reg mread_enable, memtoreg_sel, jump_enable, branch_enable;
	
	reg [15:0] reg_table[0:7];
	reg [15:0] c, temp;
	reg c1, c2, s1;
	
	wire [15:0] b1;

	//save address to pc
	always@(posedge clock)
	begin
		if(branch_enable == 1'b1)
		begin
			if(alu_result == 0)
				pc = pc + branch_addr;
			else
				pc = pc + 16'b0000000000000001;
		end
		else if(jump_enable == 1'b1)
			pc = 16'b0000000000000000 + jump_addr;
		else
			pc = pc + 16'b0000000000000001;
	end
							
												
	//change instruction value to the command corresponding to pc number
	reg [15:0] inst_memory[0:31];
	
	always@(posedge clock or negedge reset)
	begin
		if(reset == 1'b0)
		begin
			inst_memory[0] = 16'b0000000000000000;
			inst_memory[1] = 16'b011_001_001_0000001;  // addi $(001) = $(001) + 1
			inst_memory[2] = 16'b011_010_010_0000001;  // addi $(010) = $(010) + 1
			inst_memory[3] = 16'b001_001_010_011_0000;  // add $(011) = $(001) + $(010)
			inst_memory[4] = 16'b101_001_010_0000011;  // st mem($(001) + 3) = $(010)
			inst_memory[5] = 16'b011_011_100_0000010;  // addi $(100) = $(011) + 2
			inst_memory[6] = 16'b011_100_101_0000011;  // addi $(101) = $(100) + 3
			inst_memory[7] = 16'b100_001_011_0000011;  // ld $(011) = mem($(001) + 3)
			inst_memory[8] = 16'b110_010_011_0000011;  // beq $(010) == $(011) go pc+3
			inst_memory[9] = 16'b0000000000000000;
			inst_memory[10] = 16'b0000000000000000;
			inst_memory[11] = 16'b001_100_101_110_0001;  // and $(110) = $(100) & $(101)
			inst_memory[12] = 16'b001_001_000_111_0010;  // not $(111) = ~$(001) + $(000)
			inst_memory[13] = 16'b111_0000000000101;  // jump go 5
			inst_memory[14] = 16'b0000000000000000;
			inst_memory[15] = 16'b0000000000000000;
			inst_memory[16] = 16'b0000000000000000;
			inst_memory[17] = 16'b0000000000000000;
			inst_memory[18] = 16'b0000000000000000;
			inst_memory[19] = 16'b0000000000000000;
			inst_memory[20] = 16'b0000000000000000;
			inst_memory[21] = 16'b0000000000000000;
			inst_memory[22] = 16'b0000000000000000;
			inst_memory[23] = 16'b0000000000000000;
			inst_memory[24] = 16'b0000000000000000;
			inst_memory[25] = 16'b0000000000000000;
			inst_memory[26] = 16'b0000000000000000;
			inst_memory[27] = 16'b0000000000000000;
			inst_memory[28] = 16'b0000000000000000;
			inst_memory[29] = 16'b0000000000000000;
			inst_memory[30] = 16'b0000000000000000;
			inst_memory[31] = 16'b0000000000000000;
		end
	end
	
	always@(pc)
	begin
		instruction = inst_memory[pc];
	end

	// set output value corresponding to each instruction
	always@(instruction)
	begin
		if(reset == 1'b0)  // if reset value is 0, input address set 0
		begin
			read_addr1 = 3'b000;
			read_addr2 = 3'b000;
		end
		else// if reset value is not 0
		begin
			if(instruction[15:13] == 3'b001)  // R-Type instruction
			begin
				if(instruction[3:0] == 4'b0000)  // add instruction
				begin
					read_addr1 = instruction[12:10]; 
					read_addr2 = instruction[9:7];  
					write_addr = instruction[6:4];  
					imm_data = 7'b0000000;
					mwrite_addr = 16'b0000000000000000;
					mread_addr = 16'b0000000000000000;
					jump_addr = 16'b0000000000000000;
					branch_addr = 16'b0000000000000000;
					regwrite_enable = 1'b1;
					func_sel = 1'b0;
					result_sel = 2'b00;
					imm_sel = 1'b0;
					mwrite_enable = 1'b0;
					mread_enable = 1'b0;
					memtoreg_sel = 1'b0;
					jump_enable = 1'b0;
					branch_enable = 1'b0;
				end
				else if(instruction[3:0] == 4'b0001)  // and instruction
				begin
					read_addr1 = instruction[12:10];  
					read_addr2 = instruction[9:7];  
					write_addr = instruction[6:4];  
					imm_data = 7'b0000000;
					mwrite_addr = 16'b0000000000000000;
					mread_addr = 16'b0000000000000000;
					jump_addr = 16'b0000000000000000;
					branch_addr = 16'b0000000000000000;
					regwrite_enable = 1'b1;
					func_sel = 1'b0;
					result_sel = 2'b10;
					imm_sel = 1'b0;
					mwrite_enable = 1'b0;
					mread_enable = 1'b0;
					memtoreg_sel = 1'b0;
					jump_enable = 1'b0;
					branch_enable =	1'b0;		
				end
				else if(instruction[3:0] == 4'b0010)  // not instrction
				begin
					read_addr1 = instruction[12:10];  
					read_addr2 = instruction[9:7];  
					write_addr = instruction[6:4];  
					imm_data = 7'b0000000;
					mwrite_addr = 16'b0000000000000000;
					mread_addr = 16'b0000000000000000;
					jump_addr = 16'b0000000000000000;
					branch_addr = 16'b0000000000000000;
					regwrite_enable = 1'b1;
					func_sel = 1'b0;
					result_sel = 2'b11;
					imm_sel = 1'b0;
					mwrite_enable = 1'b0;
					mread_enable = 1'b0;
					memtoreg_sel = 1'b0;
					jump_enable = 1'b0;
					branch_enable =	1'b0;		
				end
			end
			else if(instruction[15:13] == 3'b011)  // addi instruction
			begin
				read_addr1 = instruction[12:10];  
				read_addr2 = 3'b000; 
				write_addr = instruction[9:7];  
				imm_data = instruction[6:0];  
				mwrite_addr = 16'b0000000000000000;
				mread_addr = 16'b0000000000000000;
				jump_addr = 16'b0000000000000000;
				branch_addr = 16'b0000000000000000;
				regwrite_enable = 1'b1;
				func_sel = 1'b0;
				result_sel = 2'b00;
				imm_sel = 1'b1;
				mwrite_enable = 1'b0;
				mread_enable = 1'b0;
				memtoreg_sel = 1'b0;
				jump_enable = 1'b0;
				branch_enable =	1'b0;	
			end
			else if(instruction[15:13] == 3'b100)  // load instruction
			begin
				read_addr1 = instruction[12:10]; 
				read_addr2 = 3'b000;  
				write_addr = instruction[9:7]; 
				imm_data = instruction[6:0];  
				mwrite_addr = 16'b0000000000000000;
				mread_addr = instruction[12:10];
				jump_addr = 16'b0000000000000000;
				branch_addr = 16'b0000000000000000;
				regwrite_enable = 1'b1;
				func_sel = 1'b0;
				result_sel = 2'b00;
				imm_sel = 1'b1;
				mwrite_enable = 1'b0;
				mread_enable = 1'b1;
				memtoreg_sel = 1'b1;
				jump_enable = 1'b0;
				branch_enable =	1'b0;	
			end
			else if(instruction[15:13] == 3'b101)  // store instruction
			begin
				read_addr1 = instruction[12:10]; 
				read_addr2 = instruction[9:7];
				write_addr = 3'b000;
				imm_data = instruction[6:0]; 
				mwrite_addr = instruction[9:7]; 
				mread_addr = 16'b0000000000000000;
				jump_addr = 16'b0000000000000000;
				branch_addr = 16'b0000000000000000;
				regwrite_enable = 1'b0;
				func_sel = 1'b0;
				result_sel = 2'b00;
				imm_sel = 1'b1;
				mwrite_enable = 1'b1;
				mread_enable = 1'b0;
				memtoreg_sel = 1'b0;
				jump_enable = 1'b0;
				branch_enable =	1'b0;	
			end
			else if(instruction[15:13] == 3'b110)  // beq instruction
			begin
				read_addr1 = instruction[12:10]; 
				read_addr2 = instruction[9:7]; 
				write_addr = 3'b000;
				imm_data = instruction[6:0]; 
				mwrite_addr = 16'b0000000000000000;
				mread_addr = 16'b0000000000000000;
				jump_addr = 16'b0000000000000000;
				branch_addr = instruction[6:0];
				regwrite_enable = 1'b0;
				func_sel = 1'b1;
				result_sel = 2'b01;
				imm_sel = 1'b1;
				mwrite_enable = 1'b0;
				mread_enable = 1'b0;
				memtoreg_sel = 1'b0;
				jump_enable = 1'b0;
				branch_enable =	1'b1;	
			end
			else if(instruction[15:13] == 3'b111)  // jump instruction
			begin
				read_addr1 = 3'b000;
				read_addr2 = 3'b000; 
				write_addr = 3'b000;
				imm_data = 7'b0000000;
				mwrite_addr = 16'b0000000000000000;
				mread_addr = 16'b0000000000000000;
				jump_addr = instruction[12:0];  // jump address
				branch_addr = 16'b0000000000000000;
				regwrite_enable = 1'b0;
				func_sel = 1'b0;
				result_sel = 2'b00;
				imm_sel = 1'b0;
				mwrite_enable = 1'b0;
				mread_enable = 1'b0;
				memtoreg_sel = 1'b0;
				jump_enable = 1'b1;
				branch_enable = 1'b0;	
			end
			else  // if instruction value is not applicable value
			begin
				read_addr1 = 3'b000;
				read_addr2 = 3'b000;
				write_addr = 3'b000;
				imm_data = 7'b0000000;
				mwrite_addr = 16'b0000000000000000;
				mread_addr = 16'b0000000000000000;
				jump_addr = 16'b0000000000000000;
				branch_addr = 16'b0000000000000000;
				regwrite_enable = 1'b0;
				func_sel = 1'b0;
				result_sel = 2'b00;
				imm_sel = 1'b0;
				mwrite_enable = 1'b0;
				mread_enable = 1'b0;
				memtoreg_sel = 1'b0;
				jump_enable = 1'b0;
				branch_enable =	1'b0;	
			end
		end
	end
	

	//set reg_write_data
	always@(alu_result, mem_data, memtoreg_sel)
	begin
		if(memtoreg_sel == 1'b1)
			reg_write_data = mem_data;
		else
			reg_write_data = alu_result;
	end

	
	always@(posedge clock or negedge reset)
	begin
		if(reset == 1'b0)  // clear
		begin
			reg_table[0] = 16'b0000000000000000;
			reg_table[1] = 16'b0000000000000000;
			reg_table[2] = 16'b0000000000000000;
			reg_table[3] = 16'b0000000000000000;
			reg_table[4] = 16'b0000000000000000;
			reg_table[5] = 16'b0000000000000000;
			reg_table[6] = 16'b0000000000000000;
			reg_table[7] = 16'b0000000000000000;
		end
		// if write_enable value is 1, change reg_table value		
		else if(regwrite_enable == 1'b1)
			reg_table[write_addr] = reg_write_data;
	end

	// set read_data value corresponding to regtable #
	always@(read_addr1 or read_addr2)
	begin
		read_data1 = reg_table[read_addr1];
		read_data2 = reg_table[read_addr2];
	end
	

	//alu // calculate command

	reg [15:0] mux_data;
	reg [15:0] adder_result;	
	
	//if imm is not 0, imm command
	always@(imm_data)
	begin
		if(imm_data[6] == 1'b1)
			ext_imm_data = 16'b1111111110000000 + imm_data;
		else
			ext_imm_data = 16'b0000000000000000 + imm_data;
	end
	
	always@(read_data2, ext_imm_data, imm_sel)
	begin
		if(imm_sel == 1'b0)
			mux_data = read_data2;
		else
			mux_data = ext_imm_data;
	end

		
	always@(mux_data, b1, func_sel)
	case(func_sel)
		1'b0 : temp = mux_data;
		1'b1 : temp = ~mux_data + 1;
	endcase
	
	assign b1 = temp;
	
	always
	begin


	c[0] = read_data1[0] & b1[0];	
	
	s1 = b1[1] ^ c[0];
	c1 = b1[1] & c[0];
	adder_result[1] = read_data1[1] ^ s1;
	c2 = read_data1[1] & s1;
	c[1] = c1 | c2;
	
	s1 = b1[2] ^ c[1];
	c1 = b1[2] & c[1];
	adder_result[2] = read_data1[2] ^ s1;
	c2 = read_data1[2] & s1;
	c[2] = c1 | c2;	

	s1 = b1[3] ^ c[2];
	c1 = b1[3] & c[2];
	adder_result[3] = read_data1[3] ^ s1;
	c2 = read_data1[3] & s1;
	c[3] = c1 | c2;

	s1 = b1[4] ^ c[3];
	c1 = b1[4] & c[3];
	adder_result[4] = read_data1[4] ^ s1;
	c2 = read_data1[4] & s1;
	c[4] = c1 | c2;

	s1 = b1[5] ^ c[4];
	c1 = b1[5] & c[4];
	adder_result[5] = read_data1[5] ^ s1;
	c2 = read_data1[5] & s1;
	c[5] = c1 | c2;

	s1 = b1[6] ^ c[5];
	c1 = b1[6] & c[5];
	adder_result[6] = read_data1[6] ^ s1;
	c2 = read_data1[6] & s1;
	c[6] = c1 | c2;

	s1 = b1[7] ^ c[6];
	c1 = b1[7] & c[6];
	adder_result[7] = read_data1[7] ^ s1;
	c2 = read_data1[7] & s1;
	c[7] = c1 | c2;

	s1 = b1[8] ^ c[7];
	c1 = b1[8] & c[7];
	adder_result[8] = read_data1[8] ^ s1;
	c2 = read_data1[8] & s1;
	c[8] = c1 | c2;

	s1 = b1[9] ^ c[8];
	c1 = b1[9] & c[8];
	adder_result[9] = read_data1[9] ^ s1;
	c2 = read_data1[9] & s1;
	c[9] = c1 | c2;

	s1 = b1[10] ^ c[9];
	c1 = b1[10] & c[9];
	adder_result[10] = read_data1[10] ^ s1;
	c2 = read_data1[10] & s1;
	c[10] = c1 | c2;

	s1 = b1[11] ^ c[10];
	c1 = b1[11] & c[10];
	adder_result[11] = read_data1[11] ^ s1;
	c2 = read_data1[11] & s1;
	c[11] = c1 | c2;

	s1 = b1[12] ^ c[11];
	c1 = b1[12] & c[11];
	adder_result[12] = read_data1[12] ^ s1;
	c2 = read_data1[12] & s1;
	c[12] = c1 | c2;

	s1 = b1[13] ^ c[12];
	c1 = b1[13] & c[12];
	adder_result[13] = read_data1[13] ^ s1;
	c2 = read_data1[13] & s1;
	c[13] = c1 | c2;

	s1 = b1[14] ^ c[13];
	c1 = b1[14] & c[13];
	adder_result[14] = read_data1[14] ^ s1;
	c2 = read_data1[14] & s1;
	c[14] = c1 | c2;
	
	s1 = b1[15] ^ c[14];
	c1 = b1[15] & c[14];
	adder_result[15] = read_data1[15] ^ s1;
	c2 = read_data1[15] & s1;
	c[15] = c1 | c2;
	end

	//and
	assign and_result = read_data1 & mux_data;
	
	//not
	assign not_result = ~read_data1 + mux_data;
	
	
	//set alu result to calculate value
	always@(adder_result, and_result, not_result, result_sel)
	case(result_sel)
		2'b00 : alu_result = adder_result;
		2'b01 : 
		begin
			if(adder_result >= 0)
				alu_result = 8'b00000000;
			else
				alu_result = 8'b00000001;
		end
		2'b10 : alu_result = and_result;
		2'b11 : alu_result = not_result;
	endcase
	
endmodule

