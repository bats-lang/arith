#include "share/atspre_staload.hats"
#use arith as AR

(* the control of tests/static/reject's call fixtures: each lemma called
   with the claim it gives, which the compiler must accept *)

prfn shr_call {n,h,l,h2,l2,h3,l3:nat} (p: $AR.SHR(n, h, l, h2, l2), q: $AR.SHR(n, h, l, h3, l3)): [h2 == h3; l2 == l3] void =
  $AR.shr_functional(p, q)

prfn shr1_call_low {h,l,h2,l2,h3,l3:nat} (p: $AR.SHR1(h, l, h2, l2), q: $AR.SHR1(h, l, h3, l3)): [h2 == h3; l2 == l3] void =
  $AR.shr1_functional(p, q)

prfn rotr1_call_high {h,l,h2,l2,h3,l3:nat} (p: $AR.ROTR1(h, l, h2, l2), q: $AR.ROTR1(h, l, h3, l3)): [h2 == h3; l2 == l3] void =
  $AR.rotr1_functional(p, q)

prfn add32_call_low {h1,l1,h2,l2,h3,l3,h4,l4:nat} (p: $AR.ADD32(h1, l1, h2, l2, h3, l3), q: $AR.ADD32(h1, l1, h2, l2, h4, l4)): [h3 == h4; l3 == l4] void =
  $AR.add32_functional(p, q)

fn step_1_call {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l)
  : [h2,l2:nat | h2 < 65536; l2 < 65536] ($AR.ROTR(1, h, l, h2, l2) | @(int h2, int l2)) =
  $AR.rotr_step_1(h, l)

fn step_2_call {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l)
  : [h2,l2:nat | h2 < 65536; l2 < 65536] ($AR.ROTR(2, h, l, h2, l2) | @(int h2, int l2)) =
  $AR.rotr_step_2(h, l)

fn step_4_call {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l)
  : [h2,l2:nat | h2 < 65536; l2 < 65536] ($AR.ROTR(4, h, l, h2, l2) | @(int h2, int l2)) =
  $AR.rotr_step_4(h, l)

fn step_8_call {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l)
  : [h2,l2:nat | h2 < 65536; l2 < 65536] ($AR.ROTR(8, h, l, h2, l2) | @(int h2, int l2)) =
  $AR.rotr_step_8(h, l)

fn step_16_call {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l)
  : ($AR.ROTR(16, h, l, l, h) | @(int l, int h)) =
  $AR.rotr_step_16(h, l)

prfn pow2_half_call (): $AR.POW2(16, 65536) = $AR.pow2_half()

prfn digits_1_call {a,b,r,t:nat | a < 32768; b < 32768; r < 2; t < 2} ()
  : $AR.ROTR(1, 2*a + r, 2*b + t, a + 32768*t, b + 32768*r) = $AR.rotr_digits_1{a,b,r,t}()

prfn digits_2_call {a,b,r,t:nat | a < 16384; b < 16384; r < 4; t < 4} ()
  : $AR.ROTR(2, 4*a + r, 4*b + t, a + 16384*t, b + 16384*r) = $AR.rotr_digits_2{a,b,r,t}()

prfn digits_8_call {a,b,r,t:nat | a < 256; b < 256; r < 256; t < 256} ()
  : $AR.ROTR(8, 256*a + r, 256*b + t, a + 256*t, b + 256*r) = $AR.rotr_digits_8{a,b,r,t}()

implement main0 () = ()
