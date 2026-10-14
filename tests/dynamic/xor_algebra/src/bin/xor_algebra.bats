#include "share/atspre_staload.hats"
#use arith as AR

(* The laws of exclusive or (xor_comm, xor_assoc, xor_self, the zero
   identities, xor_half) are lemmas the compiler checks. Here they are
   applied to the proofs xor_g1 gives for numbers under 64 in every
   combination; the lemma's result is a proof of what the other operand
   order or grouping computes, and the program checks at run time that the
   C operator, which the proofs are about, agrees (so a lemma that
   is not true of the operator the specification stands for would be
   found). Exits 1 on any disagreement. *)
fn laws {a,b,c:nat}(a: int a, b: int b, c: int c): bool = let
  val (pab | ab) = $AR.xor_g1(a, b)
  val (pq | abc) = $AR.xor_g1(ab, c)
  val (pbc | bc) = $AR.xor_g1(b, c)
  prval pa = $AR.xor_assoc(pab, pq, pbc)
  val (pa2 | abc2) = $AR.xor_g1(a, bc)
  prval () = $AR.xor_functional(pa, pa2)
  val (pba | ba) = $AR.xor_g1(b, a)
  prval pc = $AR.xor_comm(pab)
  prval () = $AR.xor_functional(pc, pba)
  val (pself | zero) = $AR.xor_g1(a, a)
  prval () = $AR.xor_functional(pself, $AR.xor_self{a}())
  val (pz | z) = $AR.xor_g1(a, 0)
  prval () = $AR.xor_functional(pz, $AR.xor_zero_right{a}())
  val (pzl | zl) = $AR.xor_g1(0, a)
  prval () = $AR.xor_functional(pzl, $AR.xor_zero_left{a}())
  prval ph = $AR.xor_half(pab)
  val (ph2 | h) = $AR.xor_g1(a / 2, b / 2)
  prval () = $AR.xor_functional(ph, ph2)
in
  abc = abc2 andalso ab = ba andalso zero = 0 andalso z = a andalso zl = a
    andalso h = ab / 2
end

fun grid {a,b,c:nat | a <= 64; b <= 64; c <= 64} .<64 - a, 64 - b, 64 - c>.
  (a: int a, b: int b, c: int c, failed: int): int =
  if a >= 64 then failed
  else if b >= 64 then grid(a + 1, 0, 0, failed)
  else if c >= 64 then grid(a, b + 1, 0, failed)
  else grid(a, b, c + 1, (if laws(a, b, c) then failed else $AR.add_int_int(failed, 1)))

implement main0 () = let
  val failed = grid(0, 0, 0, 0)
in
  if failed = 0 then println! ("xor_algebra: all cases pass")
  else let val () = println! ("FAIL xor_algebra: ", failed, " cases differ") in exit_void(1) end
end
