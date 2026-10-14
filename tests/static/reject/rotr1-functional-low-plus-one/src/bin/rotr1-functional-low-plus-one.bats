#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
prfn _digit2 {a,s,a2,s2:nat | s < 2; s2 < 2; 2*a + s == 2*a2 + s2} (): [a == a2; s == s2] void = ()

(* the statement claims l2 == l3 + 1 *)
prfn claim {h,l,h2,l2,h3,l3:nat} (p: $AR.ROTR1(h, l, h2, l2), q: $AR.ROTR1(h, l, h3, l3)): [h2 == h3; l2 == l3 + 1] void =
  case+ p of $AR.ROTR1_mk{a,b}{s,t}() => (case+ q of $AR.ROTR1_mk{a2,b2}{s2,t2}() => let
    prval () = _digit2{a,s,a2,s2}()
    prval () = _digit2{b,t,b2,t2}()
  in end)

implement main0 () = ()
