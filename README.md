# ChampernowneNormality

A Lean 4 / [Mathlib](https://github.com/leanprover-community/mathlib4)
formalization of **Champernowne's theorem** (1933): for every base `b ≥ 2`,
the sequence obtained by concatenating the base-`b` digits of `1, 2, 3, …`
is *normal* — every digit block of length `k` occurs with asymptotic
frequency `b⁻ᵏ`.

The classical instance is the base-10 sequence
`1 2 3 4 5 6 7 8 9 1 0 1 1 1 2 …`, the digit sequence of the Champernowne
constant `0.12345678910111213…`.

## The statement

The main theorem, in [`Champernowne/Main.lean`](Champernowne/Main.lean):

```lean
theorem champernowne_normal (b : ℕ) (hb : 2 ≤ b) :
    IsNormalSequence b (champDigit b)

/-- The classical base-10 statement. -/
theorem champernowne_normal_ten : IsNormalSequence 10 (champDigit 10)
```

All definitions involved are elementary and live in
[`Champernowne/Defs.lean`](Champernowne/Defs.lean):

```lean
/-- Big-endian digits of `n` in base `b`. -/
def bigDigits (b n : ℕ) : List ℕ := (Nat.digits b n).reverse

/-- First `N` blocks of the base-`b` Champernowne sequence: digits of 1..N. -/
def champBlocks (b N : ℕ) : List ℕ :=
  ((List.range N).map fun n => bigDigits b (n + 1)).flatten

/-- The `i`-th digit (0-indexed) of the base-`b` Champernowne sequence. -/
def champDigit (b i : ℕ) : ℕ := (champBlocks b (i + 1))[i]'_

/-- Number of (overlapping) occurrences of `w` as a contiguous block of `l`. -/
def countOccurrences (w l : List ℕ) : ℕ :=
  l.tails.countP (w.isPrefixOf ·)

/-- Normality of a digit sequence in base `b`: every block of length `k`
(entries `< b`, leading zeros allowed) has asymptotic frequency `b⁻ᵏ`. -/
def IsNormalSequence (b : ℕ) (s : ℕ → ℕ) : Prop :=
  ∀ w : List ℕ, w ≠ [] → (∀ d ∈ w, d < b) →
    Filter.Tendsto
      (fun n => (countOccurrences w ((List.range n).map s) : ℝ) / n)
      Filter.atTop (nhds ((b : ℝ) ^ w.length)⁻¹)
```

## Design

The development is **purely discrete**: neither the real number
`0.12345678910…` nor any digit expansion of a real is ever defined.
Normality is stated and proved as a property of the digit sequence itself.

- **Prefixes first.** The primary object is the finite list
  `champBlocks b N` (digits of `1..N` concatenated); the infinite sequence
  `champDigit b` is derived from it via prefix coherence, not defined by
  standalone index arithmetic.
- **Digits are `List ℕ`** produced by `Nat.digits`, with bounds carried as
  lemmas rather than types. Occurrences are counted with overlaps.
- **Combinatorics over `ℕ`, asymptotics over `ℝ`.** All counting lemmas are
  two-sided `ℕ` inequalities with explicit constants; casting to `ℝ` and
  Landau/filter reasoning (`Asymptotics.IsBigO`, `Filter.Tendsto` at
  `atTop`) happen only in the final layer.

## File guide

| File | Contents |
| --- | --- |
| [`Champernowne/Defs.lean`](Champernowne/Defs.lean) | Core definitions and prefix coherence |
| [`Champernowne/Count.lean`](Champernowne/Count.lean) | Occurrence counting under `++`, `flatten`, `take`/`drop` |
| [`Champernowne/DigitCount.lean`](Champernowne/DigitCount.lean) | Counting occurrences inside the digit strings of an interval of integers |
| [`Champernowne/Positions.lean`](Champernowne/Positions.lean) | Position arithmetic and prefix decomposition |
| [`Champernowne/Asymptotics.lean`](Champernowne/Asymptotics.lean) | The `ℝ` layer: length asymptotics and the limit |
| [`Champernowne/Main.lean`](Champernowne/Main.lean) | `champernowne_normal` |
| [`CountExtras.lean`](CountExtras.lean) | Extra occurrence-counting lemmas, not needed for the main theorem |
| [`Sandbox.lean`](Sandbox.lean) | `#eval`/`decide` sanity checks used during development |

## Building

```
lake exe cache get
lake build
```

The toolchain is pinned by [`lean-toolchain`](lean-toolchain) and the Mathlib
version by [`lake-manifest.json`](lake-manifest.json).

## License

Apache 2.0 — see [LICENSE](LICENSE).
