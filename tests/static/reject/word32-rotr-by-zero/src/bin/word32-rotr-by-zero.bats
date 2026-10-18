#include "share/atspre_staload.hats"
#use arith as AR

(* a rotation by 0 would shift left by 32, which C leaves undefined: the amount is 1 to 31 *)
fn claim (x: $AR.word32(0, 1)): int = let
  val (_ | r) = $AR.word32_rotr(x, 0)
in 0 end

implement main0 () = println! (claim($AR.word32_of_half(1)))
