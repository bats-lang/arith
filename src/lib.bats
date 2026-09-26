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

