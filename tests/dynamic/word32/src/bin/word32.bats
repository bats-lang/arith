#include "share/atspre_staload.hats"
#use arith as AR

(* The one-word operations (arith's word32) are C's own operators with the
   types of the proved halves-based ones. Here each is compared with the
   halves-based operation, which is proved against ROTR, SHR, ADD32 and the
   bit by bit relations, and with the standard's formulas on C's unsigned
   int (FIPS 180-4, sections 3.2 and 2.2.2), for edge words and a fixed
   pseudo-random sequence, every shift of 0 to 31. Exits 1 on any mismatch.
   This test is unsafe = true only to see through the abstract word32: a
   word is made from, and read as, a uint by $UNSAFE.cast. *)
fn whole (h: int, l: int): uint =
  (g0int2uint_int_uint(h) << 16) lor g0int2uint_int_uint(l)

fn bad(ok: bool): int = if ok then 0 else 1

fn plus(a: int, b: int): int = $AR.add_int_int(a, b)

(* the word h:l, made from the uint it is *)
fn mk {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l): $AR.word32(h, l) =
  $UNSAFE begin $UNSAFE.cast{$AR.word32(h, l)}(whole(h, l)) end

fn val_of {h,l:nat} (x: $AR.word32(h, l)): uint = $UNSAFE begin $UNSAFE.cast{uint}(x) end

fn same {a,b,h2,l2:nat | h2 < 65536; l2 < 65536} (x: $AR.word32(a, b), h2: int h2, l2: int l2, want: uint): bool =
  (val_of(x) = whole(h2, l2)) && (val_of(x) = want)

fn agrees {h,l,h0,l0:nat | h < 65536; l < 65536; h0 < 65536; l0 < 65536} (h: int h, l: int l, h0: int h0, l0: int l0): int = let
  val x = whole(h, l)
  val y = whole(h0, l0)
  val a = mk(h, l)
  val b = mk(h0, l0)
  fun shifts {n:nat | n <= 32} .<32 - n>. (n: int n, failed: int): int =
    if n >= 32 then failed
    else let
      val (_ | s) = $AR.word32_shr(a, n)
      val (_ | @(sh, sl)) = $AR.shr(n, h, l)
    in shifts(n + 1, plus(failed, bad(same(s, sh, sl, x >> n)))) end
  val (_ | sum) = $AR.word32_add(a, b)
  val (_ | @(ah, al)) = $AR.add32(h, l, h0, l0)
  val (_, _ | ex) = $AR.word32_xor(a, b)
  val (_, _ | @(xh, xl)) = $AR.xor32(h, l, h0, l0)
  val (_, _ | an) = $AR.word32_and(a, b)
  val (_, _ | @(dh, dl)) = $AR.and32(h, l, h0, l0)
  val (_, _ | orr) = $AR.word32_or(a, b)
  val (_, _ | @(oh, ol)) = $AR.or32(h, l, h0, l0)
  val (_ | nt) = $AR.word32_not(a)
  val (_ | @(nh, nl)) = $AR.not32(h, l)
  val halfword = $AR.word32_of_half(l)
  val back = $AR.word32_to_int(halfword)
  val extra = plus(plus(plus(bad(same(sum, ah, al, x + y)), bad(same(ex, xh, xl, x lxor y))),
    plus(bad(same(an, dh, dl, x land y)), bad(same(orr, oh, ol, x lor y)))),
    plus(bad(same(nt, nh, nl, lnot x)), bad(back = l)))
in shifts(0, extra) end

(* the next of a fixed pseudo-random sequence of halves *)
fn next (seed: int): [v:nat | v < 65536] int v =
  $AR.add_g1($AR.mul_g1($AR.low_byte($AR.div_int_int(seed, 7)), 256), $AR.low_byte($AR.div_int_int(seed, 3)))

fun walk {i:nat | i <= 3000} .<3000 - i>. (i: int i, failed: int): int =
  if i >= 3000 then failed
  else let
    val h = next(plus($AR.mul_int_int(i, 40503), 17))
    val l = next(plus($AR.mul_int_int(i, 9973), 5))
    val h0 = next(plus($AR.mul_int_int(i, 7919), 101))
    val l0 = next(plus($AR.mul_int_int(i, 31337), 7))
  in walk(i + 1, plus(failed, agrees(h, l, h0, l0))) end

implement main0 () = let
  val edges = plus(plus(plus(agrees(0, 0, 0, 0), agrees(65535, 65535, 65535, 65535)), plus(agrees(65535, 65535, 0, 1), agrees(32768, 0, 0, 1))),
    plus(plus(agrees(0, 1, 32768, 0), agrees(1, 0, 0, 65535)), agrees(43690, 21845, 21845, 43690)))
  val failed = plus(edges, walk(0, 0))
in
  if failed = 0 then println! ("word32: all cases pass")
  else let val () = println! ("FAIL word32: ", failed, " cases differ") in exit_void(1) end
end
