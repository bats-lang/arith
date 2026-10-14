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

(* AND(a, b, c) and OR(a, b, c): c is a and b, a or b, by the same bit
   by bit specification *)
#pub dataprop AND(int, int, int) =
  | AND_nil(0, 0, 0)
  | {a,b,c:nat | a + b > 0} AND_00(2*a, 2*b, 2*c) of AND(a, b, c)
  | {a,b,c:nat} AND_01(2*a, 2*b + 1, 2*c) of AND(a, b, c)
  | {a,b,c:nat} AND_10(2*a + 1, 2*b, 2*c) of AND(a, b, c)
  | {a,b,c:nat} AND_11(2*a + 1, 2*b + 1, 2*c + 1) of AND(a, b, c)

#pub dataprop OR(int, int, int) =
  | OR_nil(0, 0, 0)
  | {a,b,c:nat | a + b > 0} OR_00(2*a, 2*b, 2*c) of OR(a, b, c)
  | {a,b,c:nat} OR_01(2*a, 2*b + 1, 2*c + 1) of OR(a, b, c)
  | {a,b,c:nat} OR_10(2*a + 1, 2*b, 2*c + 1) of OR(a, b, c)
  | {a,b,c:nat} OR_11(2*a + 1, 2*b + 1, 2*c + 1) of OR(a, b, c)

(* a and b, a or b, with the proofs that they are. The C operators are
   trusted to be the ones AND and OR describe (as band_g1 is trusted for
   its bound); that they are is tested for every pair of 16-bit numbers
   (tests/dynamic/xor, which checks the exclusive or made of them) *)
#pub fun and_proved {a,b:nat}(a: int(a), b: int(b)): [c:nat] (AND(a, b, c) | int(c)) = "mac#atspre_land_int_int"

#pub fun or_proved {a,b:nat}(a: int(a), b: int(b)): [c:nat] (OR(a, b, c) | int(c)) = "mac#atspre_lor_int_int"

(* a xor b is a or b less a and b: the bits both have are counted twice
   by the or, once too many *)
prfun _xor_or_and {a,b,o,n:nat} .<a+b>. (po: OR(a, b, o), pn: AND(a, b, n)): [n <= o] XOR(a, b, o - n) =
  case+ po of
  | OR_nil() => (case+ pn of AND_nil() => XOR_nil())
  | OR_00(po1) => (case+ pn of AND_00(pn1) => XOR_00(_xor_or_and(po1, pn1)))
  | OR_01(po1) => (case+ pn of AND_01(pn1) => XOR_01(_xor_or_and(po1, pn1)))
  | OR_10(po1) => (case+ pn of AND_10(pn1) => XOR_10(_xor_or_and(po1, pn1)))
  | OR_11(po1) => (case+ pn of AND_11(pn1) => XOR_11(_xor_or_and(po1, pn1)))

(* a xor b, with the proof that it is: the number is made of an and and an
   or, whose proofs make the one XOR describes. (The wasm runtime has no
   exclusive or of its own.) *)
#pub fun xor_g1 {a,b:nat}(a: int(a), b: int(b)): [c:nat] (XOR(a, b, c) | int(c))

implement xor_g1 (a, b) = let
  val (po | o) = or_proved(a, b)
  val (pn | n) = and_proved(a, b)
  prval px = _xor_or_and(po, pn)
in (px | sub_g1(o, n)) end

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

(* ========== The algebra of exclusive or ========== *)

(* What a table-driven checksum needs of XOR: it is commutative and
   associative, 0 is its identity, a number is its own inverse, and
   halving (dropping the low bit) goes through it. Each is proved from
   the bit by bit specification, so none is trusted. *)

(* 2a xor 2b is 2c where a xor b is c; XOR_00 alone needs a + b > 0, so
   this form is the one to build with *)
#pub prfun xor_double {a,b,c:nat} (XOR(a, b, c)): XOR(2*a, 2*b, 2*c)

primplement xor_double {a,b,c} (p) =
  case+ p of
  | XOR_nil() => XOR_nil()
  | XOR_00(p1) => XOR_00(xor_double(p1))
  | XOR_01(p1) => XOR_00(p)
  | XOR_10(p1) => XOR_00(p)
  | XOR_11(p1) => XOR_00(p)

(* a xor 0 and 0 xor a are a *)
#pub prfun xor_zero_right {a:nat} (): XOR(a, 0, a)

primplement xor_zero_right {a} () = let
  prfun go {a:nat} .<a>. (): XOR(a, 0, a) =
    sif a == 0 then XOR_nil()
    else sif a == 2*(a/2) then xor_double(go{a/2}())
    else XOR_10(go{a/2}())
in go{a}() end

#pub prfun xor_zero_left {a:nat} (): XOR(0, a, a)

primplement xor_zero_left {a} () = let
  prfun go {a:nat} .<a>. (): XOR(0, a, a) =
    sif a == 0 then XOR_nil()
    else sif a == 2*(a/2) then xor_double(go{a/2}())
    else XOR_01(go{a/2}())
in go{a}() end

(* a xor b is b xor a *)
#pub prfun xor_comm {a,b,c:nat} (XOR(a, b, c)): XOR(b, a, c)

primplement xor_comm {a,b,c} (p) =
  case+ p of
  | XOR_nil() => XOR_nil()
  | XOR_00(p1) => XOR_00(xor_comm(p1))
  | XOR_01(p1) => XOR_10(xor_comm(p1))
  | XOR_10(p1) => XOR_01(xor_comm(p1))
  | XOR_11(p1) => XOR_11(xor_comm(p1))

(* a xor a is 0 *)
#pub prfun xor_self {a:nat} (): XOR(a, a, 0)

primplement xor_self {a} () = let
  prfun go {a:nat} .<a>. (): XOR(a, a, 0) =
    sif a == 0 then XOR_nil()
    else sif a == 2*(a/2) then xor_double(go{a/2}())
    else XOR_11(go{a/2}())
in go{a}() end

(* Halving goes through xor: (a xor b) / 2 is a / 2 xor b / 2. (The low
   bit is in the constructors: matching on a XOR says it) *)
#pub prfun xor_half {a,b,c:nat} (XOR(a, b, c)): XOR(a/2, b/2, c/2)

primplement xor_half {a,b,c} (p) =
  case+ p of
  | XOR_nil() => XOR_nil()
  | XOR_00(p1) => p1
  | XOR_01(p1) => p1
  | XOR_10(p1) => p1
  | XOR_11(p1) => p1

(* a xor b is 0 only for a equal to b *)
#pub prfun xor_zero_equal {a,b:nat} (XOR(a, b, 0)): [a == b] void

primplement xor_zero_equal {a,b} (p) = let
  prfun go {a,b:nat} .<a+b>. (p: XOR(a, b, 0)): [a == b] void =
    case+ p of
    | XOR_nil() => ()
    | XOR_00(p1) => go(p1)
    | XOR_11(p1) => go(p1)
in go(p) end

(* (a xor b) xor c is a xor (b xor c). The cases where the second
   argument of one of the xors is 0 come first, as the XOR_00 of a
   zero has no recursion to carry the proof *)
#pub prfun xor_assoc {a,b,c,ab,bc,abc:nat}
  (XOR(a, b, ab), XOR(ab, c, abc), XOR(b, c, bc)): XOR(a, bc, abc)

prfn _assoc_rnil {a,ab,abc:nat} (p: XOR(a, 0, ab), q: XOR(ab, 0, abc)): XOR(a, 0, abc) = let
  prval () = xor_functional(p, xor_zero_right{a}())
  prval () = xor_functional(q, xor_zero_right{ab}())
in xor_zero_right{a}() end

prfn _assoc_qnil {a,b,bc:nat} (p: XOR(a, b, 0), r: XOR(b, 0, bc)): XOR(a, bc, 0) = let
  prval () = xor_zero_equal(p)
  prval () = xor_functional(r, xor_zero_right{b}())
in xor_self{a}() end

prfun _xor_assoc {a,b,c,ab,bc,abc:nat} .<a+b+c>.
  (p: XOR(a, b, ab), q: XOR(ab, c, abc), r: XOR(b, c, bc)): XOR(a, bc, abc) =
  case+ p of
  | XOR_nil() => let
      prval () = xor_functional(r, q)
    in xor_zero_left() end
  | XOR_00(p1) => (case+ r of
    | XOR_nil() => _assoc_rnil(p, q)
    | XOR_00(r1) => (case+ q of XOR_nil() => _assoc_qnil(p, r) | XOR_00(q1) => xor_double(_xor_assoc(p1, q1, r1)))
    | XOR_01(r1) => (case+ q of XOR_01(q1) => XOR_01(_xor_assoc(p1, q1, r1))))
  | XOR_01(p1) => (case+ r of
    | XOR_10(r1) => (case+ q of XOR_10(q1) => XOR_01(_xor_assoc(p1, q1, r1)))
    | XOR_11(r1) => (case+ q of XOR_11(q1) => xor_double(_xor_assoc(p1, q1, r1))))
  | XOR_10(p1) => (case+ r of
    | XOR_nil() => _assoc_rnil(p, q)
    | XOR_00(r1) => (case+ q of XOR_10(q1) => XOR_10(_xor_assoc(p1, q1, r1)))
    | XOR_01(r1) => (case+ q of XOR_11(q1) => XOR_11(_xor_assoc(p1, q1, r1))))
  | XOR_11(p1) => (case+ r of
    | XOR_10(r1) => (case+ q of XOR_nil() => _assoc_qnil(p, r) | XOR_00(q1) => XOR_11(_xor_assoc(p1, q1, r1)))
    | XOR_11(r1) => (case+ q of XOR_01(q1) => XOR_10(_xor_assoc(p1, q1, r1))))

primplement xor_assoc (p, q, r) = _xor_assoc(p, q, r)

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

