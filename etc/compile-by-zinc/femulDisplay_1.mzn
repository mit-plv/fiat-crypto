include "alldifferent.mzn";
include "cumulative.mzn";
%uint64_t x73 = x71 & 0x7ffffffffffff;
%uint128_t x74 = x72 + x66;
%uint64_t x75 = x74 >> 0x33;
%uint64_t x76 = x74 & 0x7ffffffffffff;
%uint128_t x77 = x75 + x68;
%uint64_t x78 = x77 >> 0x33;
%uint64_t x79 = x77 & 0x7ffffffffffff;
%uint128_t x80 = x78 + x44;
%uint64_t x81 = x80 >> 0x33;
%uint64_t x82 = x80 & 0x7ffffffffffff;
%uint64_t x83 = 0x13 * x81;
%uint64_t x84 = x70 + x83;
%uint64_t x85 = x84 >> 0x33;
%uint64_t x86 = x84 & 0x7ffffffffffff;
%uint64_t x87 = x85 + x73;
%uint64_t x88 = x87 >> 0x33;
%uint64_t x89 = x87 & 0x7ffffffffffff;
%uint64_t x90 = x88 + x76;
set of int: CORE = 1..3;
CORE: ADD_MUL = 1; CORE: MUL_CORE = 2; CORE: LEA_BW = 3; array[CORE] of string: CORE_NAMES = ["ADD_MUL", "MUL_CORE", "LEA_BW"];

set of int: INSTRUCTIONS = 1..18;
INSTRUCTIONS: x73 = 1; INSTRUCTIONS: x74 = 2; INSTRUCTIONS: x75 = 3; INSTRUCTIONS: x76 = 4; INSTRUCTIONS: x77 = 5; INSTRUCTIONS: x78 = 6; INSTRUCTIONS: x79 = 7; INSTRUCTIONS: x80 = 8; INSTRUCTIONS: x81 = 9; INSTRUCTIONS: x82 = 10; INSTRUCTIONS: x83 = 11; INSTRUCTIONS: x84 = 12; INSTRUCTIONS: x85 = 13; INSTRUCTIONS: x86 = 14; INSTRUCTIONS: x87 = 15; INSTRUCTIONS: x88 = 16; INSTRUCTIONS: x89 = 17; INSTRUCTIONS: x90 = 18; array[INSTRUCTIONS] of string: INSTRUCTIONS_NAMES = ["x73", "x74", "x75", "x76", "x77", "x78", "x79", "x80", "x81", "x82", "x83", "x84", "x85", "x86", "x87", "x88", "x89", "x90"];

set of int: OPS = 1..6;
OPS: SHL = 1; OPS: AND = 2; OPS: ADD = 3; OPS: MUL = 4; OPS: OR = 5; OPS: SHR = 6; array[OPS] of string: OPS_NAMES = ["SHL", "AND", "ADD", "MUL", "OR", "SHR"];

int: MAX_LOC = 78;

set of int: LOCATIONS = 1..MAX_LOC;
array[INSTRUCTIONS] of var LOCATIONS: output_locations;
array[INSTRUCTIONS] of var int: output_data_latency;
array[INSTRUCTIONS] of var int: output_core_latency;
array[INSTRUCTIONS] of var CORE: output_cores;
array[INSTRUCTIONS] of OPS: input_ops = [AND, ADD, SHL, AND, ADD, SHL, AND, ADD, SHL, AND, MUL, ADD, SHL, AND, ADD, SHL, AND, ADD];
array[INSTRUCTIONS] of var int: output_ADD_MUL_core_latency;
array[INSTRUCTIONS] of var 0..1: output_ADD_MUL_core_use;
constraint forall (i in INSTRUCTIONS) (0 <= output_ADD_MUL_core_latency[i]);
constraint forall (i in INSTRUCTIONS) (output_ADD_MUL_core_use[i] == 1 -> output_core_latency[i] == output_ADD_MUL_core_latency[i]);
array[INSTRUCTIONS] of var int: output_MUL_CORE_core_latency;
array[INSTRUCTIONS] of var 0..1: output_MUL_CORE_core_use;
constraint forall (i in INSTRUCTIONS) (0 <= output_MUL_CORE_core_latency[i]);
constraint forall (i in INSTRUCTIONS) (output_MUL_CORE_core_use[i] == 1 -> output_core_latency[i] == output_MUL_CORE_core_latency[i]);
array[INSTRUCTIONS] of var int: output_LEA_BW_core_latency;
array[INSTRUCTIONS] of var 0..1: output_LEA_BW_core_use;
constraint forall (i in INSTRUCTIONS) (0 <= output_LEA_BW_core_latency[i]);
constraint forall (i in INSTRUCTIONS) (output_LEA_BW_core_use[i] == 1 -> output_core_latency[i] == output_LEA_BW_core_latency[i]);
var LOCATIONS: RET_loc;


constraint alldifferent(output_locations);

constraint output_locations[x74] + output_data_latency[x74] <= output_locations[x75];
constraint output_locations[x74] + output_data_latency[x74] <= output_locations[x76];
constraint output_locations[x75] + output_data_latency[x75] <= output_locations[x77];
constraint output_locations[x77] + output_data_latency[x77] <= output_locations[x78];
constraint output_locations[x77] + output_data_latency[x77] <= output_locations[x79];
constraint output_locations[x78] + output_data_latency[x78] <= output_locations[x80];
constraint output_locations[x80] + output_data_latency[x80] <= output_locations[x81];
constraint output_locations[x80] + output_data_latency[x80] <= output_locations[x82];
constraint output_locations[x81] + output_data_latency[x81] <= output_locations[x83];
constraint output_locations[x83] + output_data_latency[x83] <= output_locations[x84];
constraint output_locations[x84] + output_data_latency[x84] <= output_locations[x85];
constraint output_locations[x84] + output_data_latency[x84] <= output_locations[x86];
constraint output_locations[x85] + output_data_latency[x85] <= output_locations[x87];
constraint output_locations[x73] + output_data_latency[x73] <= output_locations[x87];
constraint output_locations[x87] + output_data_latency[x87] <= output_locations[x88];
constraint output_locations[x87] + output_data_latency[x87] <= output_locations[x89];
constraint output_locations[x88] + output_data_latency[x88] <= output_locations[x90];
constraint output_locations[x76] + output_data_latency[x76] <= output_locations[x90];

constraint max([ output_locations[i] + output_data_latency[i] | i in INSTRUCTIONS ]) <= RET_loc;


constraint forall (i in INSTRUCTIONS) (input_ops[i] == SHL -> ((output_cores[i] == LEA_BW /\ output_LEA_BW_core_use[i] == 1 /\ output_LEA_BW_core_latency[i] == 4 /\ output_data_latency[i] == 4 /\ output_ADD_MUL_core_use[i] == 0 /\ output_ADD_MUL_core_latency[i] == 0 /\ output_MUL_CORE_core_use[i] == 0 /\ output_MUL_CORE_core_latency[i] == 0)));
constraint forall (i in INSTRUCTIONS) (input_ops[i] == AND -> ((output_cores[i] == LEA_BW /\ output_LEA_BW_core_use[i] == 1 /\ output_LEA_BW_core_latency[i] == 4 /\ output_data_latency[i] == 4 /\ output_ADD_MUL_core_use[i] == 0 /\ output_ADD_MUL_core_latency[i] == 0 /\ output_MUL_CORE_core_use[i] == 0 /\ output_MUL_CORE_core_latency[i] == 0)));
constraint forall (i in INSTRUCTIONS) (input_ops[i] == ADD -> ((output_cores[i] == ADD_MUL /\ output_ADD_MUL_core_use[i] == 1 /\ output_ADD_MUL_core_latency[i] == 4 /\ output_data_latency[i] == 4 /\ output_MUL_CORE_core_use[i] == 0 /\ output_MUL_CORE_core_latency[i] == 0 /\ output_LEA_BW_core_use[i] == 0 /\ output_LEA_BW_core_latency[i] == 0) \/ (output_cores[i] == LEA_BW /\ output_LEA_BW_core_use[i] == 1 /\ output_LEA_BW_core_latency[i] == 4 /\ output_data_latency[i] == 4 /\ output_ADD_MUL_core_use[i] == 0 /\ output_ADD_MUL_core_latency[i] == 0 /\ output_MUL_CORE_core_use[i] == 0 /\ output_MUL_CORE_core_latency[i] == 0)));
constraint forall (i in INSTRUCTIONS) (input_ops[i] == MUL -> ((output_cores[i] == ADD_MUL /\ output_ADD_MUL_core_use[i] == 1 /\ output_ADD_MUL_core_latency[i] == 4 /\ output_data_latency[i] == 12 /\ output_MUL_CORE_core_use[i] == 0 /\ output_MUL_CORE_core_latency[i] == 0 /\ output_LEA_BW_core_use[i] == 0 /\ output_LEA_BW_core_latency[i] == 0) \/ (output_cores[i] == MUL_CORE /\ output_MUL_CORE_core_use[i] == 1 /\ output_MUL_CORE_core_latency[i] == 4 /\ output_data_latency[i] == 12 /\ output_ADD_MUL_core_use[i] == 0 /\ output_ADD_MUL_core_latency[i] == 0 /\ output_LEA_BW_core_use[i] == 0 /\ output_LEA_BW_core_latency[i] == 0)));
constraint forall (i in INSTRUCTIONS) (input_ops[i] == OR -> ((output_cores[i] == LEA_BW /\ output_LEA_BW_core_use[i] == 1 /\ output_LEA_BW_core_latency[i] == 4 /\ output_data_latency[i] == 4 /\ output_ADD_MUL_core_use[i] == 0 /\ output_ADD_MUL_core_latency[i] == 0 /\ output_MUL_CORE_core_use[i] == 0 /\ output_MUL_CORE_core_latency[i] == 0)));
constraint forall (i in INSTRUCTIONS) (input_ops[i] == SHR -> ((output_cores[i] == LEA_BW /\ output_LEA_BW_core_use[i] == 1 /\ output_LEA_BW_core_latency[i] == 4 /\ output_data_latency[i] == 4 /\ output_ADD_MUL_core_use[i] == 0 /\ output_ADD_MUL_core_latency[i] == 0 /\ output_MUL_CORE_core_use[i] == 0 /\ output_MUL_CORE_core_latency[i] == 0)));

constraint cumulative(output_locations, output_ADD_MUL_core_latency, output_ADD_MUL_core_use, 2);
constraint cumulative(output_locations, output_MUL_CORE_core_latency, output_MUL_CORE_core_use, 1);
constraint cumulative(output_locations, output_LEA_BW_core_latency, output_LEA_BW_core_use, 2);

solve minimize RET_loc;

output [ "(" ++ show(INSTRUCTIONS_NAMES[i]) ++ ", " ++ show(CORE_NAMES[fix(output_cores[i])]) ++ ", " ++ show(output_locations[i]) ++ ", " ++ show(output_data_latency[i]) ++ ", " ++ show(output_core_latency[i]) ++ ") ,\n"
       | i in INSTRUCTIONS ];
output [ "RET_loc: " ++ show(RET_loc) ];
