/* Autogenerated: src/ExtractionOCaml/unsaturated_solinas --lang Java --cmovznz-by-mul --widen-carry --widen-bytes --internal-static --only-signed Poly1305 32 '(auto)' '2^130 - 5' carry_mul carry_square carry add sub opp selectznz to_bytes from_bytes */
/* curve description: Poly1305 */
/* machine_wordsize = 32 (from "32") */
/* requested operations: carry_mul, carry_square, carry, add, sub, opp, selectznz, to_bytes, from_bytes */
/* n = 5 (from "(auto)") */
/* s-c = 2^130 - [(1, 5)] (from "2^130 - 5") */
/* tight_bounds_multiplier = 1.1 (from "") */
/*  */
/* Computed values: */
/* carry_chain = [0, 1, 2, 3, 4, 0, 1] */
/* eval z = z[0] + (z[1] << 26) + (z[2] << 52) + (z[3] << 78) + (z[4] << 104) */
/* bytes_eval z = z[0] + (z[1] << 8) + (z[2] << 16) + (z[3] << 24) + (z[4] << 32) + (z[5] << 40) + (z[6] << 48) + (z[7] << 56) + (z[8] << 64) + (z[9] << 72) + (z[10] << 80) + (z[11] << 88) + (z[12] << 96) + (z[13] << 104) + (z[14] << 112) + (z[15] << 120) + (z[16] << 128) */

package fiat_crypto;

public final class FiatPoly1305 {

static class Box<T> {
  private T value;
  public Box(T value) { this.value = value; }
  public void set(T value) { this.value = value; }
  public T get() { return this.value; }
}



/**
 * The function fiat_Poly1305_addcarryx_u26 is an addition with carry. <p>
 * Postconditions: <p>
 *   out1 = (arg1 + arg2 + arg3) mod 2^26 <p>
 *   out2 = ⌊(arg1 + arg2 + arg3) / 2^26⌋ <p>
 * <p>
 * Input Bounds: <p>
 *   arg1: [0x0 ~&gt; 0x1] <p>
 *   arg2: [0x0 ~&gt; 0x3ffffff] <p>
 *   arg3: [0x0 ~&gt; 0x3ffffff] <p>
 * Output Bounds: <p>
 *   out1: [0x0 ~&gt; 0x3ffffff] <p>
 *   out2: [0x0 ~&gt; 0x1] <p>
 */
static void fiat_Poly1305_addcarryx_u26(Box<Integer> out1, Box<Integer> out2, int arg1, int arg2, int arg3) {
  int x1 = ((arg1 + arg2) + arg3);
  int x2 = (x1 & 0x3ffffff);
  int x3 = (x1 >>> 26);
  out1.set(x2);
  out2.set(x3);
}

/**
 * The function fiat_Poly1305_subborrowx_u26 is a subtraction with borrow. <p>
 * Postconditions: <p>
 *   out1 = (-arg1 + arg2 + -arg3) mod 2^26 <p>
 *   out2 = -⌊(-arg1 + arg2 + -arg3) / 2^26⌋ <p>
 * <p>
 * Input Bounds: <p>
 *   arg1: [0x0 ~&gt; 0x1] <p>
 *   arg2: [0x0 ~&gt; 0x3ffffff] <p>
 *   arg3: [0x0 ~&gt; 0x3ffffff] <p>
 * Output Bounds: <p>
 *   out1: [0x0 ~&gt; 0x3ffffff] <p>
 *   out2: [0x0 ~&gt; 0x1] <p>
 */
static void fiat_Poly1305_subborrowx_u26(Box<Integer> out1, Box<Integer> out2, int arg1, int arg2, int arg3) {
  int x1 = ((arg2 - arg1) - arg3);
  int x2 = (x1 >>> 26);
  int x3 = (x1 & 0x3ffffff);
  out1.set(x3);
  out2.set((0x0 - x2));
}

/**
 * The function fiat_Poly1305_cmovznz_u64 is a single-word conditional move. <p>
 * Postconditions: <p>
 *   out1 = (if arg1 = 0 then arg2 else arg3) <p>
 * <p>
 * Input Bounds: <p>
 *   arg1: [0x0 ~&gt; 0x1] <p>
 *   arg2: [0x0 ~&gt; 0xffffffffffffffff] <p>
 *   arg3: [0x0 ~&gt; 0xffffffffffffffff] <p>
 * Output Bounds: <p>
 *   out1: [0x0 ~&gt; 0xffffffffffffffff] <p>
 */
static void fiat_Poly1305_cmovznz_u64(Box<Long> out1, int arg1, long arg2, long arg3) {
  long x1 = (Long.valueOf(arg1).longValue() * 0xffffffffffffffffL);
  long x2 = ((x1 & arg3) | ((~x1) & arg2));
  out1.set(x2);
}

/**
 * The function fiat_Poly1305_carry_mul multiplies two field elements and reduces the result. <p>
 * Postconditions: <p>
 *   eval out1 mod m = (eval arg1 * eval arg2) mod m <p>
 * <p>
 * Input Bounds: <p>
 *   arg1: [[0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332]] <p>
 *   arg2: [[0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332]] <p>
 * Output Bounds: <p>
 *   out1: [[0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666]] <p>
 */
public static void fiat_Poly1305_carry_mul(int[] out1, final int[] arg1, final int[] arg2) {
  long x1 = (Long.valueOf((arg1[4])).longValue() * Long.valueOf(((arg2[4]) * 0x5)).longValue());
  long x2 = (Long.valueOf((arg1[4])).longValue() * Long.valueOf(((arg2[3]) * 0x5)).longValue());
  long x3 = (Long.valueOf((arg1[4])).longValue() * Long.valueOf(((arg2[2]) * 0x5)).longValue());
  long x4 = (Long.valueOf((arg1[4])).longValue() * Long.valueOf(((arg2[1]) * 0x5)).longValue());
  long x5 = (Long.valueOf((arg1[3])).longValue() * Long.valueOf(((arg2[4]) * 0x5)).longValue());
  long x6 = (Long.valueOf((arg1[3])).longValue() * Long.valueOf(((arg2[3]) * 0x5)).longValue());
  long x7 = (Long.valueOf((arg1[3])).longValue() * Long.valueOf(((arg2[2]) * 0x5)).longValue());
  long x8 = (Long.valueOf((arg1[2])).longValue() * Long.valueOf(((arg2[4]) * 0x5)).longValue());
  long x9 = (Long.valueOf((arg1[2])).longValue() * Long.valueOf(((arg2[3]) * 0x5)).longValue());
  long x10 = (Long.valueOf((arg1[1])).longValue() * Long.valueOf(((arg2[4]) * 0x5)).longValue());
  long x11 = (Long.valueOf((arg1[4])).longValue() * Long.valueOf((arg2[0])).longValue());
  long x12 = (Long.valueOf((arg1[3])).longValue() * Long.valueOf((arg2[1])).longValue());
  long x13 = (Long.valueOf((arg1[3])).longValue() * Long.valueOf((arg2[0])).longValue());
  long x14 = (Long.valueOf((arg1[2])).longValue() * Long.valueOf((arg2[2])).longValue());
  long x15 = (Long.valueOf((arg1[2])).longValue() * Long.valueOf((arg2[1])).longValue());
  long x16 = (Long.valueOf((arg1[2])).longValue() * Long.valueOf((arg2[0])).longValue());
  long x17 = (Long.valueOf((arg1[1])).longValue() * Long.valueOf((arg2[3])).longValue());
  long x18 = (Long.valueOf((arg1[1])).longValue() * Long.valueOf((arg2[2])).longValue());
  long x19 = (Long.valueOf((arg1[1])).longValue() * Long.valueOf((arg2[1])).longValue());
  long x20 = (Long.valueOf((arg1[1])).longValue() * Long.valueOf((arg2[0])).longValue());
  long x21 = (Long.valueOf((arg1[0])).longValue() * Long.valueOf((arg2[4])).longValue());
  long x22 = (Long.valueOf((arg1[0])).longValue() * Long.valueOf((arg2[3])).longValue());
  long x23 = (Long.valueOf((arg1[0])).longValue() * Long.valueOf((arg2[2])).longValue());
  long x24 = (Long.valueOf((arg1[0])).longValue() * Long.valueOf((arg2[1])).longValue());
  long x25 = (Long.valueOf((arg1[0])).longValue() * Long.valueOf((arg2[0])).longValue());
  long x26 = (x25 + (x10 + (x9 + (x7 + x4))));
  long x27 = (x26 >>> 26);
  int x28 = (Long.valueOf(x26).intValue() & 0x3ffffff);
  long x29 = (x21 + (x17 + (x14 + (x12 + x11))));
  long x30 = (x22 + (x18 + (x15 + (x13 + x1))));
  long x31 = (x23 + (x19 + (x16 + (x5 + x2))));
  long x32 = (x24 + (x20 + (x8 + (x6 + x3))));
  long x33 = (x27 + x32);
  long x34 = (x33 >>> 26);
  int x35 = (Long.valueOf(x33).intValue() & 0x3ffffff);
  long x36 = (x34 + x31);
  long x37 = (x36 >>> 26);
  int x38 = (Long.valueOf(x36).intValue() & 0x3ffffff);
  long x39 = (x37 + x30);
  long x40 = (x39 >>> 26);
  int x41 = (Long.valueOf(x39).intValue() & 0x3ffffff);
  long x42 = (x40 + x29);
  long x43 = (x42 >>> 26);
  int x44 = (Long.valueOf(x42).intValue() & 0x3ffffff);
  long x45 = (x43 * Long.valueOf(0x5).longValue());
  long x46 = (Long.valueOf(x28).longValue() + x45);
  int x47 = Long.valueOf((x46 >>> 26)).intValue();
  int x48 = (Long.valueOf(x46).intValue() & 0x3ffffff);
  int x49 = (x47 + x35);
  int x50 = (x49 >>> 26);
  int x51 = (x49 & 0x3ffffff);
  int x52 = (x50 + x38);
  out1[0] = x48;
  out1[1] = x51;
  out1[2] = x52;
  out1[3] = x41;
  out1[4] = x44;
}

/**
 * The function fiat_Poly1305_carry_square squares a field element and reduces the result. <p>
 * Postconditions: <p>
 *   eval out1 mod m = (eval arg1 * eval arg1) mod m <p>
 * <p>
 * Input Bounds: <p>
 *   arg1: [[0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332]] <p>
 * Output Bounds: <p>
 *   out1: [[0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666]] <p>
 */
public static void fiat_Poly1305_carry_square(int[] out1, final int[] arg1) {
  int x1 = ((arg1[4]) * 0x5);
  long x2 = (Long.valueOf(x1).longValue() * Long.valueOf(0x2).longValue());
  int x3 = ((arg1[4]) * 0x2);
  int x4 = ((arg1[3]) * 0x5);
  long x5 = (Long.valueOf(x4).longValue() * Long.valueOf(0x2).longValue());
  int x6 = ((arg1[3]) * 0x2);
  int x7 = ((arg1[2]) * 0x2);
  int x8 = ((arg1[1]) * 0x2);
  long x9 = (Long.valueOf((arg1[4])).longValue() * Long.valueOf(x1).longValue());
  long x10 = (Long.valueOf((arg1[3])).longValue() * x2);
  long x11 = (Long.valueOf((arg1[3])).longValue() * Long.valueOf(x4).longValue());
  long x12 = (Long.valueOf((arg1[2])).longValue() * x2);
  long x13 = (Long.valueOf((arg1[2])).longValue() * x5);
  long x14 = (Long.valueOf((arg1[2])).longValue() * Long.valueOf((arg1[2])).longValue());
  long x15 = (Long.valueOf((arg1[1])).longValue() * x2);
  long x16 = (Long.valueOf((arg1[1])).longValue() * Long.valueOf(x6).longValue());
  long x17 = (Long.valueOf((arg1[1])).longValue() * Long.valueOf(x7).longValue());
  long x18 = (Long.valueOf((arg1[1])).longValue() * Long.valueOf((arg1[1])).longValue());
  long x19 = (Long.valueOf((arg1[0])).longValue() * Long.valueOf(x3).longValue());
  long x20 = (Long.valueOf((arg1[0])).longValue() * Long.valueOf(x6).longValue());
  long x21 = (Long.valueOf((arg1[0])).longValue() * Long.valueOf(x7).longValue());
  long x22 = (Long.valueOf((arg1[0])).longValue() * Long.valueOf(x8).longValue());
  long x23 = (Long.valueOf((arg1[0])).longValue() * Long.valueOf((arg1[0])).longValue());
  long x24 = (x23 + (x15 + x13));
  long x25 = (x24 >>> 26);
  int x26 = (Long.valueOf(x24).intValue() & 0x3ffffff);
  long x27 = (x19 + (x16 + x14));
  long x28 = (x20 + (x17 + x9));
  long x29 = (x21 + (x18 + x10));
  long x30 = (x22 + (x12 + x11));
  long x31 = (x25 + x30);
  long x32 = (x31 >>> 26);
  int x33 = (Long.valueOf(x31).intValue() & 0x3ffffff);
  long x34 = (x32 + x29);
  long x35 = (x34 >>> 26);
  int x36 = (Long.valueOf(x34).intValue() & 0x3ffffff);
  long x37 = (x35 + x28);
  long x38 = (x37 >>> 26);
  int x39 = (Long.valueOf(x37).intValue() & 0x3ffffff);
  long x40 = (x38 + x27);
  long x41 = (x40 >>> 26);
  int x42 = (Long.valueOf(x40).intValue() & 0x3ffffff);
  long x43 = (x41 * Long.valueOf(0x5).longValue());
  long x44 = (Long.valueOf(x26).longValue() + x43);
  int x45 = Long.valueOf((x44 >>> 26)).intValue();
  int x46 = (Long.valueOf(x44).intValue() & 0x3ffffff);
  int x47 = (x45 + x33);
  int x48 = (x47 >>> 26);
  int x49 = (x47 & 0x3ffffff);
  int x50 = (x48 + x36);
  out1[0] = x46;
  out1[1] = x49;
  out1[2] = x50;
  out1[3] = x39;
  out1[4] = x42;
}

/**
 * The function fiat_Poly1305_carry reduces a field element. <p>
 * Postconditions: <p>
 *   eval out1 mod m = eval arg1 mod m <p>
 * <p>
 * Input Bounds: <p>
 *   arg1: [[0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332]] <p>
 * Output Bounds: <p>
 *   out1: [[0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666]] <p>
 */
public static void fiat_Poly1305_carry(int[] out1, final int[] arg1) {
  int x1 = (arg1[0]);
  int x2 = ((x1 >>> 26) + (arg1[1]));
  int x3 = ((x2 >>> 26) + (arg1[2]));
  int x4 = ((x3 >>> 26) + (arg1[3]));
  int x5 = ((x4 >>> 26) + (arg1[4]));
  int x6 = ((x1 & 0x3ffffff) + ((x5 >>> 26) * 0x5));
  int x7 = ((x6 >>> 26) + (x2 & 0x3ffffff));
  int x8 = (x6 & 0x3ffffff);
  int x9 = (x7 & 0x3ffffff);
  int x10 = ((x7 >>> 26) + (x3 & 0x3ffffff));
  int x11 = (x4 & 0x3ffffff);
  int x12 = (x5 & 0x3ffffff);
  out1[0] = x8;
  out1[1] = x9;
  out1[2] = x10;
  out1[3] = x11;
  out1[4] = x12;
}

/**
 * The function fiat_Poly1305_add adds two field elements. <p>
 * Postconditions: <p>
 *   eval out1 mod m = (eval arg1 + eval arg2) mod m <p>
 * <p>
 * Input Bounds: <p>
 *   arg1: [[0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666]] <p>
 *   arg2: [[0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666]] <p>
 * Output Bounds: <p>
 *   out1: [[0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332]] <p>
 */
public static void fiat_Poly1305_add(int[] out1, final int[] arg1, final int[] arg2) {
  int x1 = ((arg1[0]) + (arg2[0]));
  int x2 = ((arg1[1]) + (arg2[1]));
  int x3 = ((arg1[2]) + (arg2[2]));
  int x4 = ((arg1[3]) + (arg2[3]));
  int x5 = ((arg1[4]) + (arg2[4]));
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
  out1[3] = x4;
  out1[4] = x5;
}

/**
 * The function fiat_Poly1305_sub subtracts two field elements. <p>
 * Postconditions: <p>
 *   eval out1 mod m = (eval arg1 - eval arg2) mod m <p>
 * <p>
 * Input Bounds: <p>
 *   arg1: [[0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666]] <p>
 *   arg2: [[0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666]] <p>
 * Output Bounds: <p>
 *   out1: [[0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332]] <p>
 */
public static void fiat_Poly1305_sub(int[] out1, final int[] arg1, final int[] arg2) {
  int x1 = ((0x7fffff6 + (arg1[0])) - (arg2[0]));
  int x2 = ((0x7fffffe + (arg1[1])) - (arg2[1]));
  int x3 = ((0x7fffffe + (arg1[2])) - (arg2[2]));
  int x4 = ((0x7fffffe + (arg1[3])) - (arg2[3]));
  int x5 = ((0x7fffffe + (arg1[4])) - (arg2[4]));
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
  out1[3] = x4;
  out1[4] = x5;
}

/**
 * The function fiat_Poly1305_opp negates a field element. <p>
 * Postconditions: <p>
 *   eval out1 mod m = -eval arg1 mod m <p>
 * <p>
 * Input Bounds: <p>
 *   arg1: [[0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666]] <p>
 * Output Bounds: <p>
 *   out1: [[0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332], [0x0 ~&gt; 0xd333332]] <p>
 */
public static void fiat_Poly1305_opp(int[] out1, final int[] arg1) {
  int x1 = (0x7fffff6 - (arg1[0]));
  int x2 = (0x7fffffe - (arg1[1]));
  int x3 = (0x7fffffe - (arg1[2]));
  int x4 = (0x7fffffe - (arg1[3]));
  int x5 = (0x7fffffe - (arg1[4]));
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
  out1[3] = x4;
  out1[4] = x5;
}

/**
 * The function fiat_Poly1305_selectznz is a multi-limb conditional select. <p>
 * Postconditions: <p>
 *   eval out1 = (if arg1 = 0 then eval arg2 else eval arg3) <p>
 * <p>
 * Input Bounds: <p>
 *   arg1: [0x0 ~&gt; 0x1] <p>
 *   arg2: [[0x0 ~&gt; 0xffffffff], [0x0 ~&gt; 0xffffffff], [0x0 ~&gt; 0xffffffff], [0x0 ~&gt; 0xffffffff], [0x0 ~&gt; 0xffffffff]] <p>
 *   arg3: [[0x0 ~&gt; 0xffffffff], [0x0 ~&gt; 0xffffffff], [0x0 ~&gt; 0xffffffff], [0x0 ~&gt; 0xffffffff], [0x0 ~&gt; 0xffffffff]] <p>
 * Output Bounds: <p>
 *   out1: [[0x0 ~&gt; 0xffffffff], [0x0 ~&gt; 0xffffffff], [0x0 ~&gt; 0xffffffff], [0x0 ~&gt; 0xffffffff], [0x0 ~&gt; 0xffffffff]] <p>
 */
public static void fiat_Poly1305_selectznz(long[] out1, int arg1, final long[] arg2, final long[] arg3) {
  Box<Long> x1 = new Box<Long>((long)0);
  fiat_Poly1305_cmovznz_u64(x1, arg1, (arg2[0]), (arg3[0]));
  Box<Long> x2 = new Box<Long>((long)0);
  fiat_Poly1305_cmovznz_u64(x2, arg1, (arg2[1]), (arg3[1]));
  Box<Long> x3 = new Box<Long>((long)0);
  fiat_Poly1305_cmovznz_u64(x3, arg1, (arg2[2]), (arg3[2]));
  Box<Long> x4 = new Box<Long>((long)0);
  fiat_Poly1305_cmovznz_u64(x4, arg1, (arg2[3]), (arg3[3]));
  Box<Long> x5 = new Box<Long>((long)0);
  fiat_Poly1305_cmovznz_u64(x5, arg1, (arg2[4]), (arg3[4]));
  out1[0] = (x1).get();
  out1[1] = (x2).get();
  out1[2] = (x3).get();
  out1[3] = (x4).get();
  out1[4] = (x5).get();
}

/**
 * The function fiat_Poly1305_to_bytes serializes a field element to bytes in little-endian order. <p>
 * Postconditions: <p>
 *   out1 = map (λ x, ⌊((eval arg1 mod m) mod 2^(8 * (x + 1))) / 2^(8 * x)⌋) [0..16] <p>
 * <p>
 * Input Bounds: <p>
 *   arg1: [[0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666]] <p>
 * Output Bounds: <p>
 *   out1: [[0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0x3]] <p>
 */
public static void fiat_Poly1305_to_bytes(int[] out1, final int[] arg1) {
  Box<Integer> x1 = new Box<Integer>((int)0);
  Box<Integer> x2 = new Box<Integer>((int)0);
  fiat_Poly1305_subborrowx_u26(x1, x2, 0x0, (arg1[0]), 0x3fffffb);
  Box<Integer> x3 = new Box<Integer>((int)0);
  Box<Integer> x4 = new Box<Integer>((int)0);
  fiat_Poly1305_subborrowx_u26(x3, x4, (x2).get(), (arg1[1]), 0x3ffffff);
  Box<Integer> x5 = new Box<Integer>((int)0);
  Box<Integer> x6 = new Box<Integer>((int)0);
  fiat_Poly1305_subborrowx_u26(x5, x6, (x4).get(), (arg1[2]), 0x3ffffff);
  Box<Integer> x7 = new Box<Integer>((int)0);
  Box<Integer> x8 = new Box<Integer>((int)0);
  fiat_Poly1305_subborrowx_u26(x7, x8, (x6).get(), (arg1[3]), 0x3ffffff);
  Box<Integer> x9 = new Box<Integer>((int)0);
  Box<Integer> x10 = new Box<Integer>((int)0);
  fiat_Poly1305_subborrowx_u26(x9, x10, (x8).get(), (arg1[4]), 0x3ffffff);
  Box<Long> x11 = new Box<Long>((long)0);
  fiat_Poly1305_cmovznz_u64(x11, (x10).get(), Long.valueOf(0x0).longValue(), 0xffffffff);
  Box<Integer> x12 = new Box<Integer>((int)0);
  Box<Integer> x13 = new Box<Integer>((int)0);
  fiat_Poly1305_addcarryx_u26(x12, x13, 0x0, Long.valueOf((x1).get()).intValue(), Long.valueOf((Long.valueOf((x11).get()).intValue() & 0x3fffffb)).intValue());
  Box<Integer> x14 = new Box<Integer>((int)0);
  Box<Integer> x15 = new Box<Integer>((int)0);
  fiat_Poly1305_addcarryx_u26(x14, x15, (x13).get(), (x3).get(), (Long.valueOf((x11).get()).intValue() & 0x3ffffff));
  Box<Integer> x16 = new Box<Integer>((int)0);
  Box<Integer> x17 = new Box<Integer>((int)0);
  fiat_Poly1305_addcarryx_u26(x16, x17, (x15).get(), (x5).get(), (Long.valueOf((x11).get()).intValue() & 0x3ffffff));
  Box<Integer> x18 = new Box<Integer>((int)0);
  Box<Integer> x19 = new Box<Integer>((int)0);
  fiat_Poly1305_addcarryx_u26(x18, x19, (x17).get(), (x7).get(), (Long.valueOf((x11).get()).intValue() & 0x3ffffff));
  Box<Integer> x20 = new Box<Integer>((int)0);
  Box<Integer> x21 = new Box<Integer>((int)0);
  fiat_Poly1305_addcarryx_u26(x20, x21, (x19).get(), (x9).get(), (Long.valueOf((x11).get()).intValue() & 0x3ffffff));
  long x22 = Long.valueOf((Long.valueOf((x18).get()).longValue() << 6)).longValue();
  int x23 = Long.valueOf((Long.valueOf((x16).get()).intValue() << 4)).intValue();
  int x24 = Long.valueOf((Long.valueOf((x14).get()).intValue() << 2)).intValue();
  int x25 = ((x12).get() >>> 8);
  int x26 = ((x12).get() & 0xff);
  int x27 = (x25 >>> 8);
  int x28 = (x25 & 0xff);
  int x29 = (x27 >>> 8);
  int x30 = (x27 & 0xff);
  int x31 = (x29 + x24);
  int x32 = (x31 >>> 8);
  int x33 = (x31 & 0xff);
  int x34 = (x32 >>> 8);
  int x35 = (x32 & 0xff);
  int x36 = (x34 >>> 8);
  int x37 = (x34 & 0xff);
  int x38 = (x36 + x23);
  int x39 = (x38 >>> 8);
  int x40 = (x38 & 0xff);
  int x41 = (x39 >>> 8);
  int x42 = (x39 & 0xff);
  int x43 = (x41 >>> 8);
  int x44 = (x41 & 0xff);
  long x45 = (Long.valueOf(x43).longValue() + x22);
  int x46 = Long.valueOf((x45 >>> 8)).intValue();
  int x47 = (Long.valueOf(x45).intValue() & 0xff);
  int x48 = (x46 >>> 8);
  int x49 = (x46 & 0xff);
  int x50 = (x48 >>> 8);
  int x51 = (x48 & 0xff);
  int x52 = (x50 & 0xff);
  int x53 = ((x20).get() >>> 8);
  int x54 = ((x20).get() & 0xff);
  int x55 = (x53 >>> 8);
  int x56 = (x53 & 0xff);
  int x57 = (x55 >>> 8);
  int x58 = (x55 & 0xff);
  out1[0] = x26;
  out1[1] = x28;
  out1[2] = x30;
  out1[3] = x33;
  out1[4] = x35;
  out1[5] = x37;
  out1[6] = x40;
  out1[7] = x42;
  out1[8] = x44;
  out1[9] = x47;
  out1[10] = x49;
  out1[11] = x51;
  out1[12] = x52;
  out1[13] = x54;
  out1[14] = x56;
  out1[15] = x58;
  out1[16] = x57;
}

/**
 * The function fiat_Poly1305_from_bytes deserializes a field element from bytes in little-endian order. <p>
 * Postconditions: <p>
 *   eval out1 mod m = bytes_eval arg1 mod m <p>
 * <p>
 * Input Bounds: <p>
 *   arg1: [[0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0xff], [0x0 ~&gt; 0x3]] <p>
 * Output Bounds: <p>
 *   out1: [[0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666], [0x0 ~&gt; 0x4666666]] <p>
 */
public static void fiat_Poly1305_from_bytes(int[] out1, final int[] arg1) {
  int x1 = Long.valueOf((Long.valueOf((arg1[16])).intValue() << 24)).intValue();
  int x2 = Long.valueOf((Long.valueOf((arg1[15])).intValue() << 16)).intValue();
  int x3 = Long.valueOf((Long.valueOf((arg1[14])).intValue() << 8)).intValue();
  int x4 = (arg1[13]);
  int x5 = Long.valueOf((Long.valueOf((arg1[12])).intValue() << 18)).intValue();
  int x6 = Long.valueOf((Long.valueOf((arg1[11])).intValue() << 10)).intValue();
  int x7 = Long.valueOf((Long.valueOf((arg1[10])).intValue() << 2)).intValue();
  int x8 = Long.valueOf((Long.valueOf((arg1[9])).intValue() << 20)).intValue();
  int x9 = Long.valueOf((Long.valueOf((arg1[8])).intValue() << 12)).intValue();
  int x10 = Long.valueOf((Long.valueOf((arg1[7])).intValue() << 4)).intValue();
  int x11 = Long.valueOf((Long.valueOf((arg1[6])).intValue() << 22)).intValue();
  int x12 = Long.valueOf((Long.valueOf((arg1[5])).intValue() << 14)).intValue();
  int x13 = Long.valueOf((Long.valueOf((arg1[4])).intValue() << 6)).intValue();
  long x14 = Long.valueOf((Long.valueOf((arg1[3])).longValue() << 24)).longValue();
  int x15 = Long.valueOf((Long.valueOf((arg1[2])).intValue() << 16)).intValue();
  int x16 = Long.valueOf((Long.valueOf((arg1[1])).intValue() << 8)).intValue();
  int x17 = (arg1[0]);
  long x18 = (Long.valueOf(x17).longValue() + (Long.valueOf(x16).longValue() + (Long.valueOf(x15).longValue() + x14)));
  int x19 = Long.valueOf((x18 >>> 26)).intValue();
  int x20 = (Long.valueOf(x18).intValue() & 0x3ffffff);
  int x21 = (x4 + (x3 + (x2 + x1)));
  int x22 = (x7 + (x6 + x5));
  int x23 = (x10 + (x9 + x8));
  int x24 = (x13 + (x12 + x11));
  int x25 = (x19 + x24);
  int x26 = (x25 >>> 26);
  int x27 = (x25 & 0x3ffffff);
  int x28 = (x26 + x23);
  int x29 = (x28 >>> 26);
  int x30 = (x28 & 0x3ffffff);
  int x31 = (x29 + x22);
  int x32 = (x31 & 0x3ffffff);
  out1[0] = x20;
  out1[1] = x27;
  out1[2] = x30;
  out1[3] = x32;
  out1[4] = x21;
}

}

