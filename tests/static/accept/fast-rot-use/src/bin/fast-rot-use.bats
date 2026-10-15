#include "share/atspre_staload.hats"
#use arith as AR

(* A rotation by 13 in constant time, then by 7 more: the proofs add to a
   rotation by 20, which the slow specification agrees with *)
fn twice {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l): int = let
  val (first | @(h1, l1)) = $AR.rotr_fast(13, h, l)
  val (second | @(h2, l2)) = $AR.rotr_fast(7, h1, l1)
  prval together = $AR.rotr_add(first, second)
  val (spec | @(h3, l3)) = $AR.rotr(20, h, l)
  prval () = $AR.rotr_functional(together, spec)
in $AR.add_int_int(h2, h3) end

implement main0 () = println! (twice(1, 2))
