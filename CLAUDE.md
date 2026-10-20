# arith

## CI is pinned

Every input to CI is pinned in the source (bats-lang/repository-prototype#269),
so a commit that passes keeps passing:

* The package has no dependencies, so it has no `bats.lock`.
* The compiler is the commit in `.github/bats-version`, read by every
  workflow that builds bats (and by the publish workflow).
* The package repository is fetched at the commit in
  `.github/repository-version`, so what the test packages under `tests/`
  lock (`bats lock --dev`) is pinned too.
* `publish.yml` and `relock-pins.yml` in bats-lang/repository-prototype are
  called by commit, never `@main`.

Pins move only through a reviewed pull request that runs the same CI. The
daily `relock.yml` (the shared `relock-pins.yml`) relocks against the
newest, moves the compiler and repository pins, pushes `relock/<date>`,
opens a pull request listing the old and new versions and dispatches
`check.yml` on it, so a breaking publish shows as a red relock pull
request and main stays green. GITHUB_TOKEN cannot change workflow files,
so without a `RELOCK_TOKEN` secret that pull request lists a workflow pin
that would move instead of moving it: move it in a pull request of its
own. A pull request that needs newer packages runs `bats lock
--repository <dir>` and commits `bats.lock` (and
`.github/repository-version`) with the change.

## Words are two halves (bats-lang/sha256#29)

A 32-bit word is its high and low halves, each proven under 65536
(`ROTR`, `SHR`, `ADD32`, `NOT32`, and `xor32`, `and32`, `or32` over the
`XOR`, `AND`, `OR` of each half). The solver is 32-bit: a constant or
coefficient of 2 to the 30 or more in a hypothesis makes its context
contradictory, so no proof here names 2 to the 32 and halves are what the
relations are indexed by. The specifications are the standard's own
definitions, one bit at a time (a rotation by n is n rotations by one
bit, an addition is modulo 2 to the 32 by its carries); `rotr` and `shr`
are loops of single bits, which is slow, so a caller that needs speed
adds a faster step with a proof against the same relations. What is
trusted is only the C operators under `and_proved`, `or_proved` and
`xor_g1`; `tests/dynamic/word` compares every operation with the
standard's formulas on C's unsigned int.

## Fast rotations (bats-lang/sha256#29, stage E)

`rotr` is the specification, n steps of one bit, and too slow to compute
with. `rotr_fast` rotates by n < 32 in at most five constant-time steps on
the halves (`rotr_step_16`, `_8`, `_4`, `_2`, `_1`, one for each set bit of
n), each returning the proof `ROTR(k, ...)` of the same relation. The
proofs: `rotr_add` (a rotation by a then by b is one by a + b, by
induction on a; `shr_add` the same for `SHR`), `rotr_digits_1` from
`ROTR1`, `rotr_digits_2/4/8` each from two steps of half the size (stated
on digits: h = p*a + r, l = p*b + t, the result (a + q*t):(b + q*r), p = 2
to the k, q = 2 to the 16 - k), and `rotr_by_16` from two of 8 (the halves
swap). Statements are on digits and the instantiations divide by a
constant of at most 16, because the nested closed forms (halves as
`h/256 + 256*(l mod 256)`, two deep) made the 32-bit solver's context
contradictory at 16 bits, which accepted a false claim: each lemma is
tried with a false variant for that reason (this is how it was found).
`tests/dynamic/fast_rot` compares every amount, step and the slow `rotr`
with C's unsigned int.

## Fast shifts (arith#36)

`shr_fast` shifts right by n < 32 in at most five constant-time steps
(`shr_step_16`, `_8`, `_4`, `_2`, `_1`), each returning the proof `SHR(k, ...)`
of the same relation as the single-bit `shr`, composed by `shr_add` as the
rotations are. The digit lemmas mirror `rotr_digits_*`: with h = p*a + r and
l = p*b + t, p = 2 to the k and q = 2 to the 16 - k, the result is a:(b + q*r)
(`shr_digits_1/2/4/8`, 2k from two of k, each with no nested division and
coefficients at most 2 to the 16), and `shr_by_16` is `SHR(16, h, l, 0, h)`
from two of 8. Checked by the gmp solver in under a second;
`tests/dynamic/fast_shr` compares every amount and step with C's `>>` and the
slow `shr`. Each lemma, step and the composition has a false variant in
`tests/static/reject` (`shr-*`, and `rotr-step-*`, `not32-*`, `xor32-*`,
`and32-*`, `or32-*`, `pow2-half-*` for the earlier ones that had none), and
quire's mutation check over `src/lib.bats` rejects all 154 mutants under gmp.

## Words as one machine word (bats-lang/sha256#40)

`word32(h, l)` is a C unsigned 32-bit integer whose value is h * 65536 + l,
indexed by its halves (so no type names 2 to the 32, as above). Each
operation (`word32_add`, `_xor`, `_and`, `_or`, `_not`, `_shr`) is ATS's own
prelude operation on unsigned int (`atspre_g0uint_*`: a macro or inline
function of the runtime, so a call is the C operator itself, in the caller's
own translation unit, and the proofs are erased) bound with a stronger type:
it returns the same relation (`ADD32`, `XOR`, `AND`, `OR`, `NOT32`, `SHR`) the
halves-based operation returns, so a proof built on those goes through with
either, and `shr_functional` and `xor_functional` equate them. Trusted: that
the C operator is the relation its type says, for any word, as `and_proved`
is; assumed of the platform: a 32-bit unsigned int and shifts by 0 to 31 (the
type allows no other). No C is written and no `$UNSAFE` is used in these (the rotation,
packing and bytes below are the package's one `$UNSAFE` block). `tests/dynamic/word32` (unsafe = true, only to see
through the abstract type) compares every operation with the halves-based
one and with the standard's formula, on edge words and 3000 pseudo-random
pairs, every shift; `tests/static/reject/word32-*` rejects a shift claimed to
be by another amount, the exclusive or's two proofs swapped and a complement
claimed one more. Rotation, packing and bytes are in the next section.

## The one unsafe block (bats-lang/sha256#40)

**Authorization.** The owner authorized, in the session that wrote this
(2026-10-18), `unsafe = true` in this package's `bats.toml` for exactly one
`$UNSAFE begin ... end` block holding three trusted primitives on `word32`:
rotate right, pack four bytes into a word, and take a byte of a word.
Nothing else in arith may become unsafe: a second `$UNSAFE` block, C code,
`praxi`, `assume`, `castfn` or `$extfcall` here needs a new ruling, and the
block does not grow past these three. Why: a proof-preserving fast SHA-256
(sha256#40): a word as one machine word, each operation returning the same
relation (`ROTR`, `ADD32`, ...) the halves-based specification does, so
sha256's proofs go through unchanged and the proved code runs on `uint`.

**What is in the block** (`word32_rotr`, `word32_pack`, `word32_byte`, at the
end of `src/lib.bats`), each an ordinary ATS expression on unsigned int whose
result is given the type of the relation it computes by one `$UNSAFE.cast`
(as array's cells are), with its assumption stated at its declaration:

* `word32_rotr {0 < n < 32} (word32(h, l), int n)` returns `ROTR(n, h, l, h2,
  l2)` and `word32(h2, l2)`: the very relation `rotr` and `rotr_fast` give, so
  `rotr_functional` equates them. `(x >> n) | (x << (32 - n))`; n is 1 to 31
  because a shift by 32 is undefined in C (a rotation by 0 is the identity
  and not needed).
* `word32_pack {a,b,c,d < 256}` returns `word32(256*a + b, 256*c + d)`, big
  endian (FIPS 180-4, section 3.1). The type states the halves, so there is
  no proof to fabricate, only the value.
* `word32_byte {i < 4} (word32(h, l), int i)` returns `WORD_BYTE(i, h, l, b)`
  and the byte `b`, counted from the most significant: byte 0 and 1 are the
  digits of the high half in base 256, 2 and 3 of the low half
  (`WORD_BYTE_0..3`, on digits so no division is in a type, which the
  solver does not like). `word_byte_functional` (proved here, no `praxi`)
  says a byte is one number.

Assumed of the platform, as for the operations above: unsigned int is 32 bits
(every bats target) and shifts are by 0 to 31 (the types allow no other).
Tested, not proved (`tests/dynamic/word32_rot_bytes`): every amount 1 to 31
against the bit by bit `rotr`, `rotr_fast` and the standard's formula, every
byte index against the quotient and remainder by 256 of the halves, every
value of every byte position over four backgrounds, edge words and 3000
words from a fixed seed; three one-line mutants (a rotation by one bit too
few, a byte packed twice, a byte mask of 127) were each caught. Rejected
(`tests/static/reject/word32-rotr-*`, `word32-byte-*`, `word32-pack-*`,
`word-byte-functional-plus-one`): an amount of 0 or 32, an index of 4, a
rotation claimed by the next amount, a byte claimed as the next index, a
byte of 256, halves swapped, a false lemma.

**Alternative considered and rejected.** Proving ROTR from `SHR`, a new `SHL`
and an or of disjoint halves, per amount (SHA-256 uses 2, 6, 7, 11, 13, 17,
18, 19, 22, 25), would keep the package safe, but it is a much larger job
(a `SHL` chain, a disjoint-or lemma, a closed-form digit lemma for each
amount whose coefficients the 32-bit solver can take) for no gain at run
time, since the C compiler turns the three operations into the rotate
anyway; likewise packing and bytes would need a `SHL` and the same lemma. The
precedent is array: `unsafe = true` with a small trusted core, tested in the
package.

## The same three primitives as templates (bats-lang/sha256#59)

`word32_rotr`, `word32_pack` and `word32_byte` are external symbols: a dependent
calls them, and the C compiler, which compiles each module alone, cannot inline
them. In the proved SHA-256 that was 106 of 394 instructions a byte (callgrind,
release, 1 MiB: `word32_pack` 43, `word32_rotr` 36, `word32_byte` 27). A template
with no template arguments is instantiated by the dependent, in its own
translation unit (a dependent loads this package's `lib.dats`), so the three are
also `word32_rotr_inline`, `word32_pack_inline` and `word32_byte_inline`
(`#pub fun{}`), with the very types of the three above, called as
`word32_rotr_inline(x, n)`.

Nothing is added to what is trusted: the bodies are the ones of the one
`$UNSAFE` block (it still holds three primitives, one `$UNSAFE.cast` each, no C);
the block's `implement word32_rotr` and the other two are now one call of the
template, so there is a single body of each. The old names stay (additive API).
`tests/dynamic/word32_inline` is `word32_rot_bytes` on the template names (every
amount against `rotr`, `rotr_fast` and the standard's formula, every byte index,
every value of every byte position, 3000 words from a fixed seed), and
`tests/static/reject/word32-inline-*` repeat the rejects of the three (an amount
of 0 or 32, a rotation claimed by the next amount, a byte of 256, halves
swapped, an index of 4, a byte claimed as the next index) with
`accept/word32-inline-use`.

**Override exposure (the review of arith#57, sha256#59).** A template body is
compiled into each translation unit that instantiates it, so a package in the
dependency graph that implements the same template (`implement{} $AR.word32_rotr_inline
...` in a dependent) replaces it at its own call sites, silently. The external
names are protected by the linker (a second `word32_rotr` is a link error); the
templates are not. A safe package that depends on an unsafe one carrying such an
override gets its body too. Writing such a body needs an unsafe package, since it
casts. The templates are not new trusted primitives (the owner's ruling). The
exposure is tracked by bats-lang/bats#421, which rejects an `implement` of a
template or function that another package declares.

## The proofs are checked by the infinite-precision solver (bats-lang/quire#594)

The int build of the constraint solver (`ATS2-Postiats-int-0.4.2`, C `int`
inside) proves false statements, even in small linear contexts (151 of 300
fuzzed ones), so a lemma that type-checks under it can be vacuous. The
statements here are checked with the gmp build (`gmpknd`, infinite
precision), which accepted none of those. Each lemma of the words and fast
rotations has a false variant in `tests/static/reject` (the lemma's own
body under a statement with one side shifted by one, the exact error and
its position in `expect`), and `tests/static/mutation_check.py` of quire
(`--ats-home` for the build) runs the same over every statement of
`src/lib.bats`: 130 mutants, all rejected by gmp.
Under int 129 of the 130 are rejected and the one it accepts is
`_add32_low`'s `c == c2 + 1`: the carry of a sum in two ways is one, which
int cannot see, so that helper is honest under gmp only (`add32_functional`
stays correct; the other half of the helper, `l3 == l4`, int rejects).
What was vacuous before, and is now restructured:

* `add32_functional` proved as one lemma, with two carries and eight
  halves in the context, did not terminate under gmp; it is two small
  lemmas, `_add32_low` and `_add32_high`.
* `rotr1_functional` and `shr1_functional` (a half is 2a + s in one way)
  accepted a false conclusion under int; the digit split `_digit2` is its
  own lemma, and the three of them are rejected when false under both.
* `rotr_by_16` is in digit form (the nested division form is true but
  gmp cannot prove it, and int accepted it only because its context was
  contradictory).
