#include "share/atspre_staload.hats"
#use arith as AR

(* a byte is under 256 *)
fn claim (): int = let
  val w = $AR.word32_pack_inline(1, 2, 256, 4)
in 0 end

implement main0 () = println! (claim())
