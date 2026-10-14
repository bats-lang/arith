#include "share/atspre_staload.hats"
#use arith as AR

(* 0:65535 plus 0:1 is 1:0, the low half's carry going into the high
   half: 0:0 is not the sum, which modulo 2 to the 32 would need no carry *)
fn claim (): void = let
  prval _ = $AR.ADD32_mk{0,65535,0,1,0,0}{0,0}()
in () end

implement main0 () = claim()
