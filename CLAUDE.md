# Champernowne Normality — Project Instructions

## Project

Formalize, in Lean 4 with Mathlib, Champernowne's 1933 theorem: the base-10
Champernowne sequence (the concatenation of the big-endian decimal digits of
1, 2, 3, ...) is a normal sequence, i.e. every digit block `w` of length `k`
(digits `< 10`, leading zeros allowed) occurs with asymptotic frequency
`10⁻ᵏ`.

The development is **purely discrete**. We never define the real number
`0.123456789101112...` nor any digit expansion of a real. Normality is a
property of the digit sequence itself.

## Fixed design decisions (do not revisit without discussion)

1. **Digits are `List ℕ`, produced by `Nat.digits`.** We do NOT use
   `Fin (Nat.log b n + 1) → Fin b` or any function/`Fin`-indexed
   representation. Digit bounds (`d < 10`) are carried as lemmas
   (`Nat.digits_lt_base`), never as types.
2. **Endianness.** `Nat.digits` is little-endian. All Champernowne-facing
   code uses the big-endian wrapper
   `bigDigits b n := (Nat.digits b n).reverse`
   and a small API layer over it. Arithmetic lemmas (`ofDigits_append`,
   div/mod ↔ take/drop) are applied through `List.reverse` bridges.
3. **Prefixes-first architecture.** The primary object is
   `champBlocks N : List ℕ` (digits of `1..N` concatenated, via
   `List.flatten` of a `List.map` over `List.range N`). The infinite
   sequence `champDigit : ℕ → ℕ` is *derived* from it via a prefix-coherence
   lemma (`champBlocks N <+: champBlocks M` for `N ≤ M`; prefixes agree on
   shared indices). Never define `champDigit` by standalone index
   arithmetic; the arithmetic characterization is a lemma, not a definition.
4. **Block counting** uses overlapping occurrences via
   `countOccurrences w l := l.tails.countP (w.isPrefixOf ·)`.
   Mathlib has no such function; we own this mini-library
   (behavior under `++`, `flatten`, `take`/`drop`, seam error `≤ w.length`).
5. **Base is fixed at 10** until the `k = 1` vertical slice (PLAN.md Goal 1)
   is complete. After that, generalize to `b ≥ 2` (proofs must not use
   decimal-specific facts). Small bases give tractable `decide`/`#eval`
   test cases for the hard counting lemmas.
6. **Naming.** The normality predicate is `IsNormalSequence` (or similar).
   Never bare `Normal` — that name is taken by Galois theory in Mathlib.
7. **Numbers vs. reals boundary.** All combinatorial lemmas are stated over
   `ℕ` as two-sided inequalities with explicit constants (avoid equalities
   involving `ℕ` subtraction; prefer `a + c ≤ b` over `c ≤ b - a`). Cast to
   `ℝ` only in the asymptotics layer, using `push_cast`. Landau statements
   use `IsBigO`/`IsLittleO`/`IsTheta`/`IsEquivalent` over `ℕ → ℝ` at the
   filter `atTop`.
8. **`Nat.log` quarantine.** Sandwich `(Nat.log 10 n : ℝ)` against
   `Real.logb 10 n` once (via `Nat.pow_log_le_self`,
   `Nat.lt_pow_succ_log_self`), package as an `=Θ[atTop]` statement, and
   never let `Nat.log` appear in an analytic estimate afterwards.

## Workflow rules

- **Test before proving.** Every counting lemma gets `#eval` (and, where
  feasible in a small base, `decide`) sanity checks in `Sandbox.lean`
  BEFORE any proof attempt. Check boundary values (`n = 0`, `n = 1`,
  `n = 10^k`, `n = 10^k - 1`) explicitly. The dominant project risk is
  proving-resistant *false* statements from off-by-one errors, not hard
  proofs.
- **Sorry-first structure.** Keep the whole file tree compiling with
  `sorry` placeholders; fill leaves upward. Do not let the build break.
- **Record iteration notes.** `LESSONS.md` collects reusable gotchas
  (API renames, tactic quirks, `omega` atom traps, elaboration-order
  issues). Consult it before debugging a failing tactic; append a terse
  pattern → fix entry whenever a proof attempt fails for a reason that
  could recur.
- **Prefer `Nat.digits` API over unfolding.** Look for existing lemmas
  in `Mathlib.Data.Nat.Digits` (and `Mathlib.Data.Nat.Log`) before proving
  by induction. Useful search: `exact?`, `apply?`, Loogle, and
  leansearch.net.
- When a lemma needs a side condition like `n ≥ 1`, state it so the
  asymptotics layer can consume it via `Filter.Eventually` (`∀ᶠ n in atTop`).

## Build / toolchain

- `lake exe cache get` after any Mathlib bump; then `lake build`.
- Keep `Sandbox.lean` out of the root import graph so `#eval` noise never
  blocks the main build.
- Lint with `#lint` per file before considering a goal done.

## Key Mathlib entry points (cheat sheet)

- `Nat.digits`, `Nat.ofDigits`, `Nat.ofDigits_digits`, `Nat.digits_ofDigits`
- `Nat.ofDigits_append` — concatenation ↔ arithmetic
- `Nat.digits_len`, `Nat.digits_lt_base`, `Nat.digits_ne_nil_iff_ne_zero`
- `Nat.ofDigits_div_pow_eq_ofDigits_drop`, and `% p ^ i` ↔ `List.take`
- `List.IsPrefix` (`<+:`), `List.prefix_append`, `List.IsPrefix.getElem`
- `List.flatten`, `List.tails`, `List.countP`, `List.count`
- `Finset.geom_sum_eq`, `Finset.range` sum lemmas
- `Asymptotics.IsBigO/IsLittleO/IsTheta/IsEquivalent`,
  `isLittleO_one_iff`, `isLittleO_iff_tendsto`
- `Nat.pow_log_le_self`, `Nat.lt_pow_succ_log_self`

## Roadmap

See `PLAN.md`. Work goals strictly in order; Goal 1 (the `k = 1` vertical
slice) must be finished end-to-end before generalizing anything.
