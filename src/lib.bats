(* arith -- freestanding arithmetic for ATS2 *)
(* g0/g1 arithmetic, comparisons, bitwise, type coercion *)

#include "share/atspre_staload.hats"

(* ========== g0 Arithmetic ========== *)

#pub fun add_int_int(a: int, b: int): int = "mac#atspre_g0int_add_int"

#pub fun sub_int_int(a: int, b: int): int = "mac#atspre_g0int_sub_int"

#pub fun mul_int_int(a: int, b: int): int = "mac#atspre_g0int_mul_int"

#pub fun div_int_int(a: int, b: int): int = "mac#atspre_g0int_div_int"

#pub fun mod_int_int(a: int, b: int): int = "mac#atspre_g0int_mod_int"

(* ========== g0 Comparison ========== *)

#pub fun eq_int_int(a: int, b: int): bool = "mac#atspre_g0int_eq_int"

#pub fun neq_int_int(a: int, b: int): bool = "mac#atspre_g0int_neq_int"

#pub fun gt_int_int(a: int, b: int): bool = "mac#atspre_g0int_gt_int"

#pub fun gte_int_int(a: int, b: int): bool = "mac#atspre_g0int_gte_int"

#pub fun lt_int_int(a: int, b: int): bool = "mac#atspre_g0int_lt_int"

#pub fun lte_int_int(a: int, b: int): bool = "mac#atspre_g0int_lte_int"

(* ========== g1 Dependent Comparison ========== *)

#pub fun gt1_int_int {a,b:int} (a: int a, b: int b): bool(a > b) = "mac#atspre_g0int_gt_int"

#pub fun lt1_int_int {a,b:int} (a: int a, b: int b): bool(a < b) = "mac#atspre_g0int_lt_int"

(* ========== Bitwise ========== *)

#pub fun bor_int_int(a: int, b: int): int = "mac#atspre_lor_int_int"

#pub fun bsl_int_int(a: int, n: int): int = "mac#atspre_g0int_asl_int"

#pub fun band_int_int(a: int, b: int): int = "mac#atspre_land_int_int"

#pub fun bsr_int_int(a: int, n: int): int = "mac#atspre_g0int_asr_int"

(* ========== g1 Dependent Arithmetic ========== *)

#pub fun add_g1 {a,b:int}(a: int(a), b: int(b)): int(a+b) = "mac#atspre_g0int_add_int"

#pub fun sub_g1 {a,b:int}(a: int(a), b: int(b)): int(a-b) = "mac#atspre_g0int_sub_int"

#pub fun mul_g1 {a,b:int}(a: int(a), b: int(b)): int(a*b) = "mac#atspre_g0int_mul_int"

(* ========== g1 Dependent Comparisons ========== *)

#pub fun lt_g1 {a,b:int}(a: int(a), b: int(b)): bool(a < b) = "mac#atspre_g0int_lt_int"

#pub fun gt_g1 {a,b:int}(a: int(a), b: int(b)): bool(a > b) = "mac#atspre_g0int_gt_int"

#pub fun eq_g1 {a,b:int}(a: int(a), b: int(b)): bool(a == b) = "mac#atspre_g0int_eq_int"

#pub fun lte_g1 {a,b:int}(a: int(a), b: int(b)): bool(a <= b) = "mac#atspre_g0int_lte_int"

#pub fun gte_g1 {a,b:int}(a: int(a), b: int(b)): bool(a >= b) = "mac#atspre_g0int_gte_int"

(* ========== g1 Dependent Bitwise ========== *)

#pub fun band_g1 {a,b:nat}(a: int(a), b: int(b)): [r:nat | r <= b] int(r) = "mac#atspre_land_int_int"

(* ========== Exclusive or, with its proof ========== *)

(* XOR(a, b, c): c is a xor b. The specification, bit by bit from the
   least significant: each case says what the bit makes of the number *)
#pub dataprop XOR(int, int, int) =
  | XOR_nil(0, 0, 0)
  | {a,b,c:nat | a + b > 0} XOR_00(2*a, 2*b, 2*c) of XOR(a, b, c)
  | {a,b,c:nat} XOR_01(2*a, 2*b + 1, 2*c + 1) of XOR(a, b, c)
  | {a,b,c:nat} XOR_10(2*a + 1, 2*b, 2*c + 1) of XOR(a, b, c)
  | {a,b,c:nat} XOR_11(2*a + 1, 2*b + 1, 2*c) of XOR(a, b, c)

(* a xor b, with the proof that it is. The C operator is trusted to be
   the one XOR describes (as band_g1 is trusted for its bound); that it
   is, is tested for every pair of 16-bit numbers (tests/dynamic/xor) *)
#pub fun xor_g1 {a,b:nat}(a: int(a), b: int(b)): [c:nat] (XOR(a, b, c) | int(c)) = "mac#atspre_lxor_int_int"

(* a xor b is one number *)
#pub prfun xor_functional {a,b,c1,c2:nat} (XOR(a, b, c1), XOR(a, b, c2)): [c1 == c2] void

prfun _xor_functional {a,b,c1,c2:nat} .<a+b>. (p: XOR(a, b, c1), q: XOR(a, b, c2)): [c1 == c2] void =
  case+ p of
  | XOR_nil() => (case+ q of XOR_nil() => ())
  | XOR_00(p1) => (case+ q of XOR_00(q1) => _xor_functional(p1, q1))
  | XOR_01(p1) => (case+ q of XOR_01(q1) => _xor_functional(p1, q1))
  | XOR_10(p1) => (case+ q of XOR_10(q1) => _xor_functional(p1, q1))
  | XOR_11(p1) => (case+ q of XOR_11(q1) => _xor_functional(p1, q1))

primplement xor_functional {a,b,c1,c2} (p, q) = _xor_functional(p, q)

(* POW2(k, p): p is 2 to the k *)
#pub dataprop POW2(int, int) =
  | POW2_zero(0, 1)
  | {k,p:nat} POW2_succ(k+1, 2*p) of POW2(k, p)

(* a xor b of numbers under 2 to the k is under 2 to the k *)
#pub prfun xor_bound {k,p,a,b,c:nat | a < p; b < p} (POW2(k, p), XOR(a, b, c)): [c < p] void

prfun _xor_bound {k,p,a,b,c:nat | a < p; b < p} .<k>. (w: POW2(k, p), x: XOR(a, b, c)): [c < p] void =
  case+ x of
  | XOR_nil() => ()
  | XOR_00(x1) => (case+ w of POW2_succ(w1) => _xor_bound(w1, x1))
  | XOR_01(x1) => (case+ w of POW2_succ(w1) => _xor_bound(w1, x1))
  | XOR_10(x1) => (case+ w of POW2_succ(w1) => _xor_bound(w1, x1))
  | XOR_11(x1) => (case+ w of POW2_succ(w1) => _xor_bound(w1, x1))

primplement xor_bound {k,p,a,b,c} (w, x) = _xor_bound(w, x)

(* ========== Bytes ========== *)

(* The low 8 bits of x as an int proven in [0, 256). Rebuilt from its
   bits: each term is a literal or 0, so the bound needs no cast. *)
#pub fn low_byte(x: int): [v:nat | v < 256] int v

implement low_byte(x) = let
  fn bit {w:nat | w < 256} (x: int, w: int w): [y:nat | y <= w] int y =
    if band_int_int(x, w) = 0 then 0 else w
in
  bit(x, 128) + bit(x, 64) + bit(x, 32) + bit(x, 16)
    + bit(x, 8) + bit(x, 4) + bit(x, 2) + bit(x, 1)
end

#pub fn byte_of_char(c: char): [v:nat | v < 256] int v

implement byte_of_char(c) = low_byte(char2int0(c))

