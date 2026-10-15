#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
prfun claim {n,h,l,h2,l2,h3,l3:nat} .<n>. (p: $AR.ROTR(n, h, l, h2, l2), q: $AR.ROTR(n, h, l, h3, l3)): [h2 == h3 + 1; l2 == l3] void =
  case+ p of
  | $AR.ROTR_zero() => (case+ q of $AR.ROTR_zero() => ())
  | $AR.ROTR_succ(p1, p2) => (case+ q of
    | $AR.ROTR_succ(q1, q2) => let
        prval () = $AR.rotr1_functional(p1, q1)
      in claim(p2, q2) end)

implement main0 () = ()
