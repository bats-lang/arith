#include "share/atspre_staload.hats"
#use arith as AR

(* A word rotated by 3 and added to itself, each result with its proof;
   the proofs are what a caller reasons from *)
fn twice_rotated {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l): int = let
  val (rotated | @(rh, rl)) = $AR.rotr(3, h, l)
  val (summed | @(sh, sl)) = $AR.add32(rh, rl, rh, rl)
  prval () = $AR.rotr_functional(rotated, rotated)
  prval () = $AR.add32_functional(summed, summed)
in $AR.add_int_int(sh, sl) end

implement main0 () = println! (twice_rotated(1, 2))
