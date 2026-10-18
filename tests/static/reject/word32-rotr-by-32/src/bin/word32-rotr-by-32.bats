#include "share/atspre_staload.hats"
#use arith as AR

(* the amount is under 32 *)
fn claim (x: $AR.word32(0, 1)): int = let
  val (_ | r) = $AR.word32_rotr(x, 32)
in 0 end

implement main0 () = println! (claim($AR.word32_of_half(1)))
