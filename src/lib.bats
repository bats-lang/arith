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

(* ========== Type Coercion ========== *)

#pub castfn g0_of_g1 {n:int} (x: int(n)): int

#pub castfn checked_pos(x: int): [n:pos] int n

#pub castfn checked_nat(x: int): [n:nat] int n

#pub castfn checked_byte(x: int): [v:nat | v < 256] int v

#pub castfn checked_arr_size(x: int): [n:pos | n <= 1048576] int n

#pub castfn checked_idx {n:pos} (x: int, len: int n): [i:nat | i < n] int i

(* ========== Safe Fuel ========== *)
(* Maximum safe recursion depth: 32768 stack frames.
   At ~128 bytes per frame, this uses ~4MB of stack, safely under the
   default 8MB stack limit. Any fuel value above this is capped.
   Use this instead of checked_nat for recursion fuel parameters. *)

stadef FUEL_MAX = 32768

#pub fn safe_fuel(x: int): [n:nat] int n

implement safe_fuel(x) =
  if x <= 0 then checked_nat(0)
  else if x > 32768 then checked_nat(32768)
  else checked_nat(x)
