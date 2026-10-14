#include "share/atspre_staload.hats"
#use arith as AR

(* the word 0:1 rotated right by one bit is 32768:0, the low bit coming
   round to the top: a proof that the result is 0:1 cannot be made *)
fn claim (): void = let
  prval pf = $AR.ROTR1_mk{0,0}{0,1}()
  prval _ = pf: $AR.ROTR1(0, 1, 0, 1)
in () end

implement main0 () = claim()
