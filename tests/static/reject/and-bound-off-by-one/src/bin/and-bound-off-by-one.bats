#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
prfun claim {k,p,a,b,c:nat | a < p; b < p} .<k>. (w: $AR.POW2(k, p), x: $AR.AND(a, b, c)): [c + 1 < p] void =
  case+ x of
  | $AR.AND_nil() => (case+ w of $AR.POW2_zero() => () | $AR.POW2_succ(_) => ())
  | $AR.AND_00(x1) => (case+ w of $AR.POW2_succ(w1) => claim(w1, x1))
  | $AR.AND_01(x1) => (case+ w of $AR.POW2_succ(w1) => claim(w1, x1))
  | $AR.AND_10(x1) => (case+ w of $AR.POW2_succ(w1) => claim(w1, x1))
  | $AR.AND_11(x1) => (case+ w of $AR.POW2_succ(w1) => claim(w1, x1))

implement main0 () = ()
