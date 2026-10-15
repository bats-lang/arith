#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
prfun claim {a,b,h,l,h1,l1,h2,l2:nat} .<a>. (p: $AR.ROTR(a, h, l, h1, l1), q: $AR.ROTR(b, h1, l1, h2, l2)): $AR.ROTR(a + b + 1, h, l, h2, l2) =
  case+ p of
  | $AR.ROTR_zero() => q
  | $AR.ROTR_succ(once, rest) => $AR.ROTR_succ(once, claim(rest, q))

implement main0 () = ()
