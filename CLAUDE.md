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
