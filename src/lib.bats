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


(* ========== 32-bit words, as two 16-bit halves ========== *)

(* A word is its high and low halves, each a number under 65536. The
   halves, not the number, are what the specification is indexed by: the
   solver is 32-bit, a constant or a coefficient of 2 to the 30 or more
   in a hypothesis makes its context contradictory, so no proof here
   names 2 to the 32. The word is h * 65536 + l.

   The specifications are the standard's own definitions, one bit at a
   time: rotating right by n bits is n rotations by one bit, shifting
   right by n bits is n shifts by one bit, and an addition is modulo
   2 to the 32 by its carries (FIPS 180-4, sections 2.2.2, 3.2 and 4.1) *)

(* ROTR1(h, l, h2, l2): the word h:l rotated right by one bit is h2:l2.
   Each half is its upper bits and its lowest bit (h = 2a + s, l = 2b + t):
   the lowest bit of the word, t, becomes the highest, and the lowest bit
   of the high half, s, becomes the highest of the low half. *)
#pub dataprop ROTR1(int, int, int, int) =
  | {a,b:nat | a < 32768; b < 32768}{s,t:nat | s < 2; t < 2}
    ROTR1_mk(2*a + s, 2*b + t, a + 32768*t, b + 32768*s)

(* ROTR(n, h, l, h2, l2): h:l rotated right by n bits is h2:l2 *)
#pub dataprop ROTR(int, int, int, int, int) =
  | {h,l:nat} ROTR_zero(0, h, l, h, l)
  | {n:nat}{h,l,h1,l1,h2,l2:nat}
    ROTR_succ(n + 1, h, l, h2, l2) of (ROTR1(h, l, h1, l1), ROTR(n, h1, l1, h2, l2))

(* SHR1(h, l, h2, l2) and SHR(n, h, l, h2, l2): shifted right by one bit
   and by n bits; the bits shifted out are lost and zeros come in at the top *)
#pub dataprop SHR1(int, int, int, int) =
  | {a,b:nat | a < 32768; b < 32768}{s,t:nat | s < 2; t < 2}
    SHR1_mk(2*a + s, 2*b + t, a, b + 32768*s)

#pub dataprop SHR(int, int, int, int, int) =
  | {h,l:nat} SHR_zero(0, h, l, h, l)
  | {n:nat}{h,l,h1,l1,h2,l2:nat}
    SHR_succ(n + 1, h, l, h2, l2) of (SHR1(h, l, h1, l1), SHR(n, h1, l1, h2, l2))

(* ADD32(h1, l1, h2, l2, h3, l3): h1:l1 plus h2:l2 modulo 2 to the 32 is
   h3:l3. The low halves add to l3 and a carry c into the high halves,
   which add with it to h3 and a carry d that is dropped: the modulus *)
#pub dataprop ADD32(int, int, int, int, int, int) =
  | {h1,l1,h2,l2,h3,l3:nat | h1 < 65536; l1 < 65536; h2 < 65536; l2 < 65536; h3 < 65536; l3 < 65536}
    {c,d:nat | c < 2; d < 2; l1 + l2 == l3 + 65536*c; h1 + h2 + c == h3 + 65536*d}
    ADD32_mk(h1, l1, h2, l2, h3, l3)

(* NOT32(h, l, h2, l2): h2:l2 is h:l with every bit flipped *)
#pub dataprop NOT32(int, int, int, int) =
  | {h,l:nat | h < 65536; l < 65536} NOT32_mk(h, l, 65535 - h, 65535 - l)

(* x as 2a + s, a half and the bit that is left *)
fn half_split {x:nat | x < 65536} (x: int x): [a,s:nat | x == 2*a + s; a < 32768; s < 2] @(int a, int s) = let
  val a = x / 2
in @(a, sub_g1(x, mul_g1(2, a))) end

(* The word h:l rotated right by one bit, with the proof that it is *)
#pub fun rotr1 {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l)
  : [h2,l2:nat | h2 < 65536; l2 < 65536] (ROTR1(h, l, h2, l2) | @(int h2, int l2))

implement rotr1 {h,l} (h, l) = let
  val [a:int, s:int] @(a, s) = half_split(h)
  val [b:int, t:int] @(b, t) = half_split(l)
in (ROTR1_mk{a,b}{s,t}() | @(add_g1(a, mul_g1(32768, t)), add_g1(b, mul_g1(32768, s)))) end

(* The word shifted right by one bit, with the proof that it is *)
#pub fun shr1 {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l)
  : [h2,l2:nat | h2 < 65536; l2 < 65536] (SHR1(h, l, h2, l2) | @(int h2, int l2))

implement shr1 {h,l} (h, l) = let
  val [a:int, s:int] @(a, s) = half_split(h)
  val [b:int, t:int] @(b, t) = half_split(l)
in (SHR1_mk{a,b}{s,t}() | @(a, add_g1(b, mul_g1(32768, s)))) end

(* The word h:l rotated right by n bits, with the proof that it is: n
   rotations by one bit *)
#pub fun rotr {n,h,l:nat | h < 65536; l < 65536} (n: int n, h: int h, l: int l)
  : [h2,l2:nat | h2 < 65536; l2 < 65536] (ROTR(n, h, l, h2, l2) | @(int h2, int l2))

implement rotr {n,h,l} (n, h, l) = let
  fun loop {n,h,l:nat | h < 65536; l < 65536} .<n>. (n: int n, h: int h, l: int l)
    : [h2,l2:nat | h2 < 65536; l2 < 65536] (ROTR(n, h, l, h2, l2) | @(int h2, int l2)) =
    if n = 0 then (ROTR_zero() | @(h, l))
    else let
      val (once | @(h1, l1)) = rotr1(h, l)
      val (rest | @(h2, l2)) = loop(sub_g1(n, 1), h1, l1)
    in (ROTR_succ(once, rest) | @(h2, l2)) end
in loop(n, h, l) end

(* The word h:l shifted right by n bits, with the proof that it is *)
#pub fun shr {n,h,l:nat | h < 65536; l < 65536} (n: int n, h: int h, l: int l)
  : [h2,l2:nat | h2 < 65536; l2 < 65536] (SHR(n, h, l, h2, l2) | @(int h2, int l2))

implement shr {n,h,l} (n, h, l) = let
  fun loop {n,h,l:nat | h < 65536; l < 65536} .<n>. (n: int n, h: int h, l: int l)
    : [h2,l2:nat | h2 < 65536; l2 < 65536] (SHR(n, h, l, h2, l2) | @(int h2, int l2)) =
    if n = 0 then (SHR_zero() | @(h, l))
    else let
      val (once | @(h1, l1)) = shr1(h, l)
      val (rest | @(h2, l2)) = loop(sub_g1(n, 1), h1, l1)
    in (SHR_succ(once, rest) | @(h2, l2)) end
in loop(n, h, l) end

(* The sum modulo 2 to the 32 of two words, with the proof that it is *)
#pub fun add32 {h1,l1,h2,l2:nat | h1 < 65536; l1 < 65536; h2 < 65536; l2 < 65536}
  (h1: int h1, l1: int l1, h2: int h2, l2: int l2)
  : [h3,l3:nat | h3 < 65536; l3 < 65536] (ADD32(h1, l1, h2, l2, h3, l3) | @(int h3, int l3))

implement add32 {h1,l1,h2,l2} (h1, l1, h2, l2) = let
  val low = add_g1(l1, l2)
in
  if gte_g1(low, 65536) then let
    val l3 = sub_g1(low, 65536)
    val high = add_g1(add_g1(h1, h2), 1)
  in
    if gte_g1(high, 65536) then (ADD32_mk{h1,l1,h2,l2,h1+h2+1-65536,l1+l2-65536}{1,1}() | @(sub_g1(high, 65536), l3))
    else (ADD32_mk{h1,l1,h2,l2,h1+h2+1,l1+l2-65536}{1,0}() | @(high, l3))
  end
  else let
    val high = add_g1(h1, h2)
  in
    if gte_g1(high, 65536) then (ADD32_mk{h1,l1,h2,l2,h1+h2-65536,l1+l2}{0,1}() | @(sub_g1(high, 65536), low))
    else (ADD32_mk{h1,l1,h2,l2,h1+h2,l1+l2}{0,0}() | @(high, low))
  end
end

(* The word with every bit flipped, with the proof that it is *)
#pub fun not32 {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l)
  : (NOT32(h, l, 65535 - h, 65535 - l) | @(int(65535 - h), int(65535 - l)))

implement not32 {h,l} (h, l) = (NOT32_mk() | @(sub_g1(65535, h), sub_g1(65535, l)))

(* a and b, a or b of numbers under 2 to the k are under 2 to the k *)
#pub prfun and_bound {k,p,a,b,c:nat | a < p; b < p} (POW2(k, p), AND(a, b, c)): [c < p] void

prfun _and_bound {k,p,a,b,c:nat | a < p; b < p} .<k>. (w: POW2(k, p), x: AND(a, b, c)): [c < p] void =
  case+ x of
  | AND_nil() => (case+ w of POW2_zero() => () | POW2_succ(_) => ())
  | AND_00(x1) => (case+ w of POW2_succ(w1) => _and_bound(w1, x1))
  | AND_01(x1) => (case+ w of POW2_succ(w1) => _and_bound(w1, x1))
  | AND_10(x1) => (case+ w of POW2_succ(w1) => _and_bound(w1, x1))
  | AND_11(x1) => (case+ w of POW2_succ(w1) => _and_bound(w1, x1))

primplement and_bound {k,p,a,b,c} (w, x) = _and_bound(w, x)

#pub prfun or_bound {k,p,a,b,c:nat | a < p; b < p} (POW2(k, p), OR(a, b, c)): [c < p] void

prfun _or_bound {k,p,a,b,c:nat | a < p; b < p} .<k>. (w: POW2(k, p), x: OR(a, b, c)): [c < p] void =
  case+ x of
  | OR_nil() => (case+ w of POW2_zero() => () | POW2_succ(_) => ())
  | OR_00(x1) => (case+ w of POW2_succ(w1) => _or_bound(w1, x1))
  | OR_01(x1) => (case+ w of POW2_succ(w1) => _or_bound(w1, x1))
  | OR_10(x1) => (case+ w of POW2_succ(w1) => _or_bound(w1, x1))
  | OR_11(x1) => (case+ w of POW2_succ(w1) => _or_bound(w1, x1))

primplement or_bound {k,p,a,b,c} (w, x) = _or_bound(w, x)

(* 2 to the 16, the size of a half *)
#pub prfun pow2_half (): POW2(16, 65536)

primplement pow2_half () =
  POW2_succ(POW2_succ(POW2_succ(POW2_succ(POW2_succ(POW2_succ(POW2_succ(POW2_succ(
  POW2_succ(POW2_succ(POW2_succ(POW2_succ(POW2_succ(POW2_succ(POW2_succ(POW2_succ(
  POW2_zero()))))))))))))))))

(* The bitwise operations on words, each half by its own proof: the
   exclusive or, and and or of h1:l1 and h2:l2 are h3:l3 where the high
   halves and the low halves are each related by XOR, AND or OR *)
#pub fun xor32 {h1,l1,h2,l2:nat | h1 < 65536; l1 < 65536; h2 < 65536; l2 < 65536}
  (h1: int h1, l1: int l1, h2: int h2, l2: int l2)
  : [h3,l3:nat | h3 < 65536; l3 < 65536] (XOR(h1, h2, h3), XOR(l1, l2, l3) | @(int h3, int l3))

implement xor32 {h1,l1,h2,l2} (h1, l1, h2, l2) = let
  val (high | h3) = xor_g1(h1, h2)
  val (low | l3) = xor_g1(l1, l2)
  prval () = xor_bound(pow2_half(), high)
  prval () = xor_bound(pow2_half(), low)
in (high, low | @(h3, l3)) end

#pub fun and32 {h1,l1,h2,l2:nat | h1 < 65536; l1 < 65536; h2 < 65536; l2 < 65536}
  (h1: int h1, l1: int l1, h2: int h2, l2: int l2)
  : [h3,l3:nat | h3 < 65536; l3 < 65536] (AND(h1, h2, h3), AND(l1, l2, l3) | @(int h3, int l3))

implement and32 {h1,l1,h2,l2} (h1, l1, h2, l2) = let
  val (high | h3) = and_proved(h1, h2)
  val (low | l3) = and_proved(l1, l2)
  prval () = and_bound(pow2_half(), high)
  prval () = and_bound(pow2_half(), low)
in (high, low | @(h3, l3)) end

#pub fun or32 {h1,l1,h2,l2:nat | h1 < 65536; l1 < 65536; h2 < 65536; l2 < 65536}
  (h1: int h1, l1: int l1, h2: int h2, l2: int l2)
  : [h3,l3:nat | h3 < 65536; l3 < 65536] (OR(h1, h2, h3), OR(l1, l2, l3) | @(int h3, int l3))

implement or32 {h1,l1,h2,l2} (h1, l1, h2, l2) = let
  val (high | h3) = or_proved(h1, h2)
  val (low | l3) = or_proved(l1, l2)
  prval () = or_bound(pow2_half(), high)
  prval () = or_bound(pow2_half(), low)
in (high, low | @(h3, l3)) end

(* Each operation of a word gives one word *)
#pub prfun rotr1_functional {h,l,h2,l2,h3,l3:nat} (ROTR1(h, l, h2, l2), ROTR1(h, l, h3, l3)): [h2 == h3; l2 == l3] void

primplement rotr1_functional {h,l,h2,l2,h3,l3} (p, q) =
  case+ p of ROTR1_mk() => (case+ q of ROTR1_mk() => ())

#pub prfun rotr_functional {n,h,l,h2,l2,h3,l3:nat} (ROTR(n, h, l, h2, l2), ROTR(n, h, l, h3, l3)): [h2 == h3; l2 == l3] void

prfun _rotr_functional {n,h,l,h2,l2,h3,l3:nat} .<n>. (p: ROTR(n, h, l, h2, l2), q: ROTR(n, h, l, h3, l3)): [h2 == h3; l2 == l3] void =
  case+ p of
  | ROTR_zero() => (case+ q of ROTR_zero() => ())
  | ROTR_succ(p1, p2) => (case+ q of
    | ROTR_succ(q1, q2) => let
        prval () = rotr1_functional(p1, q1)
      in _rotr_functional(p2, q2) end)

primplement rotr_functional {n,h,l,h2,l2,h3,l3} (p, q) = _rotr_functional(p, q)

#pub prfun shr1_functional {h,l,h2,l2,h3,l3:nat} (SHR1(h, l, h2, l2), SHR1(h, l, h3, l3)): [h2 == h3; l2 == l3] void

primplement shr1_functional {h,l,h2,l2,h3,l3} (p, q) =
  case+ p of SHR1_mk() => (case+ q of SHR1_mk() => ())

#pub prfun shr_functional {n,h,l,h2,l2,h3,l3:nat} (SHR(n, h, l, h2, l2), SHR(n, h, l, h3, l3)): [h2 == h3; l2 == l3] void

prfun _shr_functional {n,h,l,h2,l2,h3,l3:nat} .<n>. (p: SHR(n, h, l, h2, l2), q: SHR(n, h, l, h3, l3)): [h2 == h3; l2 == l3] void =
  case+ p of
  | SHR_zero() => (case+ q of SHR_zero() => ())
  | SHR_succ(p1, p2) => (case+ q of
    | SHR_succ(q1, q2) => let
        prval () = shr1_functional(p1, q1)
      in _shr_functional(p2, q2) end)

primplement shr_functional {n,h,l,h2,l2,h3,l3} (p, q) = _shr_functional(p, q)

#pub prfun add32_functional {h1,l1,h2,l2,h3,l3,h4,l4:nat}
  (ADD32(h1, l1, h2, l2, h3, l3), ADD32(h1, l1, h2, l2, h4, l4)): [h3 == h4; l3 == l4] void

primplement add32_functional {h1,l1,h2,l2,h3,l3,h4,l4} (p, q) =
  case+ p of ADD32_mk() => (case+ q of ADD32_mk() => ())
