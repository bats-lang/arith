#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
prfun claim {a,b,h,l,h1,l1,h2,l2:nat} .<a>. (p: $AR.SHR(a, h, l, h1, l1), q: $AR.SHR(b, h1, l1, h2, l2)): $AR.SHR(a + b + 1, h, l, h2, l2) =
  case+ p of
  | $AR.SHR_zero() => q
  | $AR.SHR_succ(once, rest) => $AR.SHR_succ(once, claim(rest, q))

implement main0 () = ()
