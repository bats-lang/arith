#include "share/atspre_staload.hats"
#use arith as AR

(* A word's rotation runs on one machine word and its proof is the one the
   bit by bit specification gives: the rotation by 7 of the word is the
   rotation by 7 of its halves (ROTR is a function) *)
fn rotated {h,l:nat | h < 65536; l < 65536} (x: $AR.word32(h, l), h: int h, l: int l): int = let
  val (fast | r) = $AR.word32_rotr(x, 7)
  val (spec | @(rh, rl)) = $AR.rotr(7, h, l)
  prval () = $AR.rotr_functional(fast, spec)
in $AR.add_int_int(rh, rl) end

(* The first byte of a packed word is the first byte it was packed from:
   the byte's proof is a function of the word, and the digits of the high
   half of a packed word are its first two bytes *)
fn first {a,b,c,d:nat | a < 256; b < 256; c < 256; d < 256} (a: int a, b: int b, c: int c, d: int d): int(a) = let
  val w = $AR.word32_pack(a, b, c, d)
  val (got | x) = $AR.word32_byte(w, 0)
  prval want = $AR.WORD_BYTE_0{a,b,256*c + d}()
  prval () = $AR.word_byte_functional(got, want)
in x end

implement main0 () = println! (rotated($AR.word32_of_half(5), 0, 5), first(1, 2, 3, 4))
