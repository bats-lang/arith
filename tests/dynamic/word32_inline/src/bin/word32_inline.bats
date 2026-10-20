#include "share/atspre_staload.hats"
#use arith as AR

(* The rotation, the packing of four bytes and the bytes of a word (arith's
   word32_rotr_inline, word32_pack_inline, word32_byte_inline: the templates
   the three trusted primitives of its one $UNSAFE block are, bats-lang/sha256#59) against references that do not share their
   code: the rotation against the bit by bit specification rotr (proved
   against ROTR, one bit at a time) and rotr_fast, and against the
   standard's formula on C's unsigned int; the packing and the bytes
   against the arithmetic on the halves (a word is h * 65536 + l, a byte a
   quotient or remainder by 256). Every rotation amount 1 to 31 on edge
   words and 3000 pseudo-random words from a fixed seed, every byte index,
   and every value 0 to 255 of every byte position over four backgrounds.
   Exits 1 on any mismatch. unsafe = true only to see through the abstract
   word32: a word is made from, and read as, a uint by $UNSAFE.cast. *)
fn whole (h: int, l: int): uint =
  (g0int2uint_int_uint(h) << 16) lor g0int2uint_int_uint(l)

fn bad(ok: bool): int = if ok then 0 else 1

fn plus(a: int, b: int): int = $AR.add_int_int(a, b)

fn mk {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l): $AR.word32(h, l) =
  $UNSAFE begin $UNSAFE.cast{$AR.word32(h, l)}(whole(h, l)) end

fn val_of {h,l:nat} (x: $AR.word32(h, l)): uint = $UNSAFE begin $UNSAFE.cast{uint}(x) end

(* every amount 1 to 31 of the rotation of the word h:l *)
fn rotations {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l): int = let
  val x = whole(h, l)
  val w = mk(h, l)
  fun go {n:nat | n <= 32} .<32 - n>. (n: int n, failed: int): int =
    if n >= 32 then failed
    else if n = 0 then go(n + 1, failed)
    else let
      val (pf | r) = $AR.word32_rotr_inline(w, n)
      val (spec | @(sh, sl)) = $AR.rotr(n, h, l)
      prval () = $AR.rotr_functional(pf, spec)
      val (_ | @(fh, fl)) = $AR.rotr_fast(n, h, l)
      val standard = (x >> n) lor (x << (32 - n))
      val ok = (val_of(r) = whole(sh, sl)) && (val_of(r) = whole(fh, fl)) && (val_of(r) = standard)
    in go(n + 1, plus(failed, bad(ok))) end
in go(0, 0) end

(* byte i of the word h:l is the quotient or the remainder by 256 of its half *)
fn bytes_of {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l): int = let
  val w = mk(h, l)
  val x = whole(h, l)
  fun go {i:nat | i <= 4} .<4 - i>. (i: int i, failed: int): int =
    if i >= 4 then failed
    else let
      val (_ | b) = $AR.word32_byte_inline(w, i)
      val want = (if i = 0 then $AR.div_int_int(h, 256) else if i = 1 then $AR.mod_int_int(h, 256)
                  else if i = 2 then $AR.div_int_int(l, 256) else $AR.mod_int_int(l, 256)): int
      val shifted = g0uint2int_uint_int((x >> (24 - 8 * i)) land 255u)
    in go(i + 1, plus(failed, bad((b = want) && (b = shifted)))) end
in go(0, 0) end

fn packed {a,b,c,d:nat | a < 256; b < 256; c < 256; d < 256} (a: int a, b: int b, c: int c, d: int d): int = let
  val w = $AR.word32_pack_inline(a, b, c, d)
  val h = plus($AR.mul_int_int(a, 256), b)
  val l = plus($AR.mul_int_int(c, 256), d)
  val (_ | b0) = $AR.word32_byte_inline(w, 0)
  val (_ | b1) = $AR.word32_byte_inline(w, 1)
  val (_ | b2) = $AR.word32_byte_inline(w, 2)
  val (_ | b3) = $AR.word32_byte_inline(w, 3)
in plus(bad(val_of(w) = whole(h, l)), bad((b0 = a) && (b1 = b) && (b2 = c) && (b3 = d))) end

(* every value of every position, over a background byte *)
fn positions {g:nat | g < 256} (g: int g): int = let
  fun go {p:nat | p <= 4}{v:nat | v <= 256} .<4 - p, 256 - v>. (p: int p, v: int v, failed: int): int =
    if p >= 4 then failed
    else if v >= 256 then go(p + 1, 0, failed)
    else let
      val vv = $AR.low_byte(v)
      val one = (if p = 0 then packed(vv, g, g, g) else if p = 1 then packed(g, vv, g, g)
                 else if p = 2 then packed(g, g, vv, g) else packed(g, g, g, vv)): int
    in go(p, v + 1, plus(failed, one)) end
in go(0, 0, 0) end

fn everything {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l): int =
  plus(rotations(h, l), bytes_of(h, l))

fn next (seed: int): [v:nat | v < 65536] int v =
  $AR.add_g1($AR.mul_g1($AR.low_byte($AR.div_int_int(seed, 7)), 256), $AR.low_byte($AR.div_int_int(seed, 3)))

fn next_byte (seed: int): [v:nat | v < 256] int v = $AR.low_byte($AR.div_int_int(seed, 5))

fun walk {i:nat | i <= 3000} .<3000 - i>. (i: int i, failed: int): int =
  if i >= 3000 then failed
  else let
    val h = next(plus($AR.mul_int_int(i, 40503), 17))
    val l = next(plus($AR.mul_int_int(i, 9973), 5))
    val a = next_byte(plus($AR.mul_int_int(i, 7919), 101))
    val b = next_byte(plus($AR.mul_int_int(i, 31337), 7))
    val c = next_byte(plus($AR.mul_int_int(i, 2749), 13))
    val d = next_byte(plus($AR.mul_int_int(i, 6571), 29))
  in walk(i + 1, plus(failed, plus(everything(h, l), packed(a, b, c, d)))) end

implement main0 () = let
  val edges = plus(plus(plus(everything(0, 0), everything(65535, 65535)), plus(everything(0, 1), everything(32768, 0))),
    plus(plus(everything(1, 0), everything(43690, 21845)), plus(everything(21845, 43690), everything(255, 65280))))
  val grounds = plus(plus(positions(0), positions(255)), plus(positions(165), positions(90)))
  val failed = plus(plus(edges, grounds), walk(0, 0))
in
  if failed = 0 then println! ("word32_inline: all cases pass")
  else let val () = println! ("FAIL word32_inline: ", failed, " cases differ") in exit_void(1) end
end
