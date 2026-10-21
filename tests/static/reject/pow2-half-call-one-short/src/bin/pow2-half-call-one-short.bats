#include "share/atspre_staload.hats"
#use arith as AR

(* 2 to the 16 is the size of a half: the claim with 65535 is one short *)
prfn claim (): $AR.POW2(16, 65535) = $AR.pow2_half()

implement main0 () = ()
