#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
prfun claim {n,h,l,h2,l2,h3,l3:nat} .<n>. (p: $AR.SHR(n, h, l, h2, l2), q: $AR.SHR(n, h, l, h3, l3)): [h2 == h3; l2 == l3 + 1] void =
  case+ p of
  | $AR.SHR_zero() => (case+ q of $AR.SHR_zero() => ())
  | $AR.SHR_succ(p1, p2) => (case+ q of
    | $AR.SHR_succ(q1, q2) => let
        prval () = $AR.shr1_functional(p1, q1)
      in claim(p2, q2) end)

implement main0 () = ()
