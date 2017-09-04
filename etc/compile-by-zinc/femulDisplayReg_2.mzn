include "alldifferent.mzn";
include "cumulative.mzn";
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
set of int: INSTRUCTIONS = 1..21;
INSTRUCTIONS: x10 = 1; INSTRUCTIONS: x11 = 2; INSTRUCTIONS: x9 = 3; INSTRUCTIONS: x7 = 4; INSTRUCTIONS: x5 = 5; INSTRUCTIONS: x18 = 6; INSTRUCTIONS: x19 = 7; INSTRUCTIONS: x17 = 8; INSTRUCTIONS: x15 = 9; INSTRUCTIONS: x13 = 10; INSTRUCTIONS: x80 = 11; INSTRUCTIONS: x81 = 12; INSTRUCTIONS: x82 = 13; INSTRUCTIONS: x83 = 14; INSTRUCTIONS: x84 = 15; INSTRUCTIONS: x85 = 16; INSTRUCTIONS: x86 = 17; INSTRUCTIONS: x87 = 18; INSTRUCTIONS: x88 = 19; INSTRUCTIONS: x89 = 20; INSTRUCTIONS: x90 = 21; array[INSTRUCTIONS] of string: INSTRUCTIONS_NAMES = ["x10", "x11", "x9", "x7", "x5", "x18", "x19", "x17", "x15", "x13", "x80", "x81", "x82", "x83", "x84", "x85", "x86", "x87", "x88", "x89", "x90"];

int: MAX_LOC = 87;

set of int: LOCATIONS = 1..MAX_LOC;
array[INSTRUCTIONS] of var LOCATIONS: output_locations;
array[INSTRUCTIONS] of var LOCATIONS: live_duration;
array[INSTRUCTIONS] of int: output_register_count = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1];
var LOCATIONS: RET_loc;
constraint cumulative(output_locations, live_duration, output_register_count, 16);


constraint alldifferent(output_locations);

constraint output_locations[x83] + live_duration[x83] == max([output_locations[x84]]);
constraint output_locations[x81] + live_duration[x81] == max([output_locations[x83]]);
constraint output_locations[x44] + live_duration[x44] == max([output_locations[x80]]);
constraint output_locations[x87] + live_duration[x87] == max([output_locations[x88], output_locations[x89]]);
constraint output_locations[x85] + live_duration[x85] == max([output_locations[x87]]);
constraint output_locations[x78] + live_duration[x78] == max([output_locations[x80]]);
constraint output_locations[x84] + live_duration[x84] == max([output_locations[x85], output_locations[x86]]);
constraint output_locations[x76] + live_duration[x76] == max([output_locations[x90]]);
constraint output_locations[x88] + live_duration[x88] == max([output_locations[x90]]);
constraint output_locations[x73] + live_duration[x73] == max([output_locations[x87]]);
constraint output_locations[x70] + live_duration[x70] == max([output_locations[x84]]);
constraint output_locations[x80] + live_duration[x80] == max([output_locations[x81], output_locations[x82]]);


constraint output_locations[x78] + 1 <= output_locations[x80];
constraint output_locations[x44] + 1 <= output_locations[x80];
constraint output_locations[x80] + 1 <= output_locations[x81];
constraint output_locations[x80] + 1 <= output_locations[x82];
constraint output_locations[x81] + 1 <= output_locations[x83];
constraint output_locations[x70] + 1 <= output_locations[x84];
constraint output_locations[x83] + 1 <= output_locations[x84];
constraint output_locations[x84] + 1 <= output_locations[x85];
constraint output_locations[x84] + 1 <= output_locations[x86];
constraint output_locations[x85] + 1 <= output_locations[x87];
constraint output_locations[x73] + 1 <= output_locations[x87];
constraint output_locations[x87] + 1 <= output_locations[x88];
constraint output_locations[x87] + 1 <= output_locations[x89];
constraint output_locations[x88] + 1 <= output_locations[x90];
constraint output_locations[x76] + 1 <= output_locations[x90];

constraint max([ output_locations[i] + 1 | i in INSTRUCTIONS ]) <= RET_loc;


solve minimize RET_loc;

output [ "(" ++ show(INSTRUCTIONS_NAMES[i]) ++ ", " ++ show(output_locations[i]) ++ ", " ++ show(live_duration[i]) ++ ") ,\n"
       | i in INSTRUCTIONS ];
output [ "RET_loc: " ++ show(RET_loc) ];
