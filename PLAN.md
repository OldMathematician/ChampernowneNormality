# PLAN — Champernowne's Constant is Normal (base 10)

**Status: theorem complete.** `champernowne_normal` (general base `b ≥ 2`)
and `champernowne_normal_ten` are fully proved in `Champernowne/Main.lean`,
zero `sorry`s anywhere in the codebase. Goals 0–5 below are all closed;
see "Post-theorem refactor" for the upper-from-lower simplification that
retired the upper counting chain and the `k = 1` slice, and "Stretch
(post-theorem)" for what's left to consider. Goal descriptions below are
kept as a historical record; where they name since-deleted lemmas, the
refactor section is authoritative.

Goals are ordered by **risk**, not logical dependency: attack whatever could
force a redesign while the codebase is small. Risk map: asymptotics layer =
low; definitions = low/medium; occurrence-counting list theory, the
interval ↔ digit-string transfer, and seam/partial-block accounting = high.
Cross-cutting risk: off-by-one errors (a wrong statement is discovered three
layers up as an unprovable goal).

---

## Goal 0 — Statement skeleton (make it compile) `[x]`

Everything defined, final theorem stated, all proofs `sorry`. Deliverables:

- [x] Lake project builds against current Mathlib (`lake exe cache get`).
- [x] File layout:
  - `Champernowne/Defs.lean` — all definitions below
  - `Champernowne/Count.lean` — occurrence-counting mini-library (Goal 2)
  - `Champernowne/DigitCount.lean` — interval ↔ string counting (Goals 1a, 3)
  - `Champernowne/Positions.lean` — length formulas, prefix decomposition (Goal 4)
  - `Champernowne/Asymptotics.lean` — ℝ layer and endgame (Goal 5)
  - `Champernowne/Main.lean` — final theorem
  - `Sandbox.lean` — `#eval`/`decide` checks (not imported by Main)
- [x] Skeleton (adjust names/universes as needed, keep the shapes):

```lean
import Mathlib

/-- Big-endian digits of `n` in base `b`. -/
def bigDigits (b n : ℕ) : List ℕ := (Nat.digits b n).reverse

/-- First `N` blocks of the Champernowne sequence: digits of 1..N. -/
def champBlocks (N : ℕ) : List ℕ :=
  ((List.range N).map fun n => bigDigits 10 (n + 1)).flatten

theorem champBlocks_prefix {N M : ℕ} (h : N ≤ M) :
    champBlocks N <+: champBlocks M := sorry

theorem le_length_champBlocks (N : ℕ) : N ≤ (champBlocks N).length := sorry

/-- The `i`-th Champernowne digit (0-indexed). -/
def champDigit (i : ℕ) : ℕ :=
  (champBlocks (i + 1))[i]'(lt_of_lt_of_le (Nat.lt_succ_self i)
    (le_length_champBlocks (i + 1)))

/-- Coherence: any sufficiently long prefix computes `champDigit`. -/
theorem champBlocks_getElem (N i : ℕ) (h : i < (champBlocks N).length) :
    (champBlocks N)[i] = champDigit i := sorry

/-- The first `n` digits of the Champernowne sequence. -/
def champPrefix (n : ℕ) : List ℕ := (champBlocks n).take n

theorem champPrefix_eq_map (n : ℕ) :
    champPrefix n = (List.range n).map champDigit := sorry

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

theorem champernowne_normal : IsNormalSequence 10 champDigit := sorry
```

- [x] Review checklist for the statement (the one unrecoverable error is
      proving the wrong theorem):
  - blocks with leading zeros ARE included (`w = [0,0]` must be counted);
  - occurrences overlap (sliding window), via `countOccurrences`;
  - `w : List ℕ` with `∀ d ∈ w, d < 10` — not `List (Fin 10)`;
  - decide the convention for windows at the very end of the prefix and
    document it next to `countOccurrences`.
- [x] `Sandbox.lean` first entries: `#eval champPrefix 15`
      (expect `[1,2,3,4,5,6,7,8,9,1,0,1,1,1,2]`),
      `#eval countOccurrences [1,1] (champPrefix 15)` and hand-checked
      friends; `decide` versions in base 2/3 once base is generalized.

---

## Goal 1 — Vertical slice: single-digit frequency (k = 1) `[x]`

Prove end-to-end: for every `d < 10`,
`(fun n => ((champPrefix n).count d : ℝ) / n) → 1/10`.
*(Done: `tendsto_count_champPrefix_div` in `Asymptotics.lean`. Since
retired in the post-theorem refactor: the `k = 1` statement is subsumed
by the general theorem at `w := [d]` via `countOccurrences_singleton`.
Its value was being first — that purpose was served.)*

Rationale: exercises every layer (prefix coherence, counting under
`flatten`, interval ↔ digit transfer, cumulative lengths, partial-block
error, ℕ→ℝ boundary, Landau endgame) using Mathlib's `List.count` instead
of homemade block counting. If the definitions are wrong, this finds out at
~20% of the cost. Do NOT attempt to obtain k = 1 later as a corollary of
the general case; its value is being first. Everything proved here for
`List.count` is the template for `countOccurrences`.

### Goal 1a — Interval ↔ digit-string equivalence (do this sub-goal FIRST) `[x]`

The mathematical heart; highest off-by-one density. Deliverable, as a
reusable bijection or at minimum its `Finset.card` consequences:

```lean
-- m-digit numbers ≃ length-m digit strings with nonzero head
def digitEquiv (m : ℕ) (hm : 0 < m) :
    Finset.Ico (10 ^ (m - 1)) (10 ^ m) ≃
    {l : List ℕ // l.length = m ∧ (∀ d ∈ l, d < 10) ∧ l.head? ≠ some 0}
```

Forward map `bigDigits 10`, inverse `Nat.ofDigits 10 ∘ List.reverse`;
round-trips from `Nat.ofDigits_digits`, `Nat.digits_ofDigits`,
`Nat.digits_len`, `Nat.digits_lt_base`. Then: the count of `m`-digit
numbers with digit `d` at position `j` (answers `10^(m-1)` / `9·10^(m-2)`
depending on `j` and `d`). **Prototype with `#eval` (base 10, m = 3) and
`decide` (base 2/3) before proving anything.**

### Remaining slice deliverables

- [x] Digit-`d` count in the full `m`-digit cohort (sum over positions).
- [x] Exact/bounded count in `champBlocks N`, then in `champPrefix n`
      (partial block error `O(log n)`). *(Complete. The ℕ layer compares
      `10·count` against `length`/`n` to stay subtraction- and
      division-free: per-cohort exact identities
      (`ten_mul_cohort_count(_zero)`), boundary and general-`N` sandwiches
      for `champBlocks` (error `10^(M+2)`), `champIndex` +
      the prefix chain `champBlocks (champIndex n) <+: champPrefix n <+:
      champBlocks (champIndex n + 1)` in `Positions.lean`, and the main
      transfer `|10·(champPrefix n).count d − n| ≤ 10^(M+3)` for
      `10^(M-1) ≤ champIndex n + 1 ≤ 10^M`.)*
- [x] Cast, package as `(count - n/10) =o[atTop] n`, bridge to `Tendsto`.
      *(Done in `Asymptotics.lean`: `champM` is the `Nat.log` quarantine;
      `count_champPrefix_sub_isLittleO` and
      `tendsto_count_champPrefix_div` close the slice.)*

---

## Goal 2 — Occurrence-counting mini-library `[x]`

Greenfield; entirely ours. All over `ℕ`, explicit constants, no asymptotics.

- [x] Convention decision for short tails / end-of-list windows, documented
      (at the definition in `Defs.lean`; lower bounds need `w ≠ []`).
- [x] `countOccurrences [d] l = l.count d` (sanity bridge to Goal 1).
- [x] Append sandwich (state as TWO inequalities, not an equality with a
      seam term):
      `countOccurrences w a + countOccurrences w b ≤ countOccurrences w (a ++ b)`
      and
      `countOccurrences w (a ++ b) ≤ countOccurrences w a + countOccurrences w b + w.length`
      *(proved by induction on `a` via `countOccurrences_cons`, not
      `tails_append`; the sharp seam constant `min w.length a.length` is
      `countOccurrences_append_le_min`).*
- [x] `flatten` corollary: deviation from `Σ` of per-block counts is
      `≤ L.length * w.length`.
- [x] `take`/`drop` monotonicity with error `≤ w.length`.
- [x] `#eval` test suite in `Sandbox.lean` BEFORE each proof (including an
      exhaustive check of the sandwich over small binary lists).

---

## Goal 3 — General position-counting lemma `[x]`

For `w.length = k ≤ m`, position `j ≤ m - k`: the number of `m`-digit
numbers with `w` at position `j` is
`b^(m-k)` if `j = 0 ∧ w.head? ≠ some 0`, `0` if `j = 0 ∧ w.head? = some 0`,
else `(b-1) * b^(m-k-1)`. Sum over `j` ⇒ internal occurrences in the full
`m`-digit cohort. Should be Goal 1a's proof with a longer constraint — if it
isn't, refactor Goal 1a NOW. Combined with Goal 2: two-sided bounds on
`countOccurrences w` over each cohort's concatenation.
*(Done: `block_eq_iff` (substring ↔ `n / b^(m-j-k) % b^k = value of w`,
via `self_div_pow_eq_ofDigits_drop` / `ofDigits_mod_pow_eq_ofDigits_take` /
`ofDigits_inj_of_len_eq`), the three cards `card_blockAt`,
`card_blockAt_head`, `card_blockAt_head_zero` — the interior card reuses
`card_Ico_filter_div_mod` with `q := b^k`, the head card reuses
`ofDigits_reverse_mem_Ico`, confirming the "Goal 1a with a longer
constraint" prediction — and the position characterization
`countOccurrences_eq_card_filter_range` in `Count.lean`.
Complete: `sum_countOccurrences_cohort(_zero)` give the exact cohort
occurrence counts `b^(m-k) + (m-k)·(b-1)·b^(m-k-1)` (resp. without the
head term) via `card_blockAt_past_end` and the position swap; the Goal 2
combination is the stream sandwich `sum_le_countOccurrences_champBlocks` /
`countOccurrences_champBlocks_le` (seam error `N·w.length`) in
`Count.lean`.)*

---

## Goal 4 — Position arithmetic & prefix decomposition `[x]`

- [x] Exact length of `champBlocks N` via digit-cohort sums
      (`Finset.geom_sum_eq`); sharp only where the dominant term needs it,
      inequalities elsewhere. *(`length_champBlocks` in `DigitCount.lean`,
      built during Goal 1.)*
- [x] Locate index `n` in the stream (cumulative-length function).
      *(`champIndex` + the prefix chain
      `champBlocks (champIndex n) <+: champPrefix n <+: champBlocks
      (champIndex n + 1)` in `Positions.lean`, built during Goal 1; this
      machinery is base/definition-general, not `List.count`-specific, so
      it is reused as-is below.)*
- [x] Decompose `champPrefix n` = complete cohorts ++ complete numbers of
      current cohort ++ partial number, with length bounds for the tail
      pieces (`O(cohort)` and `O(log n)`). *(Realized as the boundary
      induction + partial-cohort combination below, generalized from
      `List.count` to `countOccurrences`.)*
- [x] Truncated-subtraction hygiene throughout (see CLAUDE.md rule 7).
      *(All new error bounds stated as two-sided `≤` inequalities with
      explicit `+`, never `ℕ`-subtraction; every genuine subtraction
      site — `m - w.length`, `K + 1 - w.length`, etc. — resolved via
      `obtain ⟨j, hj⟩ : ∃ j, m = w.length + j` substitutions or `omega`,
      never left bare inside a `ring`/`nlinarith` call.)*
- [x] **General-`w` position arithmetic** (the actual remaining work: Goal
      1's `champIndex`/`champM` transfer was proved for `List.count`, which
      has no cross-number seam error since `List.count` distributes exactly
      over `flatten`; `countOccurrences` does not, so every step below is a
      genuine re-derivation, not a renaming of the `k = 1` proof).
      In `DigitCount.lean`:
  - [x] Partial-cohort block occurrence bounds: `card_blockAt_partial_le` /
        `le_card_blockAt_partial` (interior position, one sub-cohort range,
        reusing `card_Ico_filter_div_mod_le` with modulus `b^k` in place of
        digit-case's `b`), `card_blockAt_head_partial_le` (head position,
        by monotonicity from the exact full-cohort value — cheaper than
        the digit case's from-scratch interval argument), and the sandwich
        `sum_countOccurrences_partial_cohort_le` /
        `le_sum_countOccurrences_partial_cohort` (error budget
        `2·b^(K+1-k)`, geometric-series argument mirroring
        `sum_count_partial_cohort_le`). Validated against hand-computed
        cases in `Sandbox.lean` before proving (11 actual occurrences ≤ 20
        budget for a concrete `[100,150)` slice).
  - [x] Per-cohort `b^k·occurrences ≈ length` comparison — the general-`w`
        analogue of `base_mul_cohort_count` — split by nonzero/zero head
        as `sum_countOccurrences_cohort`/`_zero` already are:
        `base_pow_cohort_count_head_le`, `base_pow_cohort_count_zero_le`,
        `le_base_pow_cohort_count_head`, `le_base_pow_cohort_count_zero`.
        Error budget `(k+1)·b^m` (constant in `m`, since `k = w.length` is
        fixed for the whole theorem) — the shape needed for the boundary
        induction below to absorb error across cohort levels without it
        accumulating. *(Reworked once, post hoc: `card_blockAt` is exact
        **and independent of `w`** at interior positions, so
        `b^k · (interior card) = cohort size` on the nose — feeding that
        straight into `base_pow_cohort_count_head_eq`/`_zero_eq` (exact
        closed forms) and a small shared arithmetic lemma
        `cohort_coeff_bound` replaced four separate case-split/`ring`/
        `nlinarith` proofs with something ~35% shorter and easier to
        trust.)*
  - [x] Boundary induction across full cohorts `[1, b^K)`
        (`base_pow_count_boundary_le`/`le_base_pow_count_boundary`, the
        analogue of `base_mul_count_boundary_le`) plus the small helper
        `countOccurrences_eq_zero_of_length_lt` (→
        `sum_countOccurrences_cohort_short`) to zero out cohorts below
        `w.length`. Error `2(k+1)·b^K`: the extra factor of `2` over the
        `k = 1` case's plain `b^K` is because general `k` has no analogue
        of the lucky `w.length = 1` cancellation that made the `k=1`
        per-cohort error land exactly one power below its own cohort;
        with a fixed factor of `2` headroom the same `2·b^K ≤ b^(K+1)`
        absorption still closes the induction for any `b ≥ 2`. Then the
        partial-cohort analogue
        `base_pow_countOccurrences_partial_le`/`le_base_pow_countOccurrences_partial`
        (error `3(k+1)·b^(K+1)`, converting the existing
        `sum_countOccurrences_partial_cohort_le` count-vs-`t/b^k` bound
        into a count-vs-length one — needs `linear_le_const_mul_pow`,
        a small helper bounding the mod-rounding error) and the general-`N`
        combination
        `base_pow_countOccurrences_champBlocks_le`/`le_base_pow_countOccurrences_champBlocks`
        (error `6(k+1)·b^M`; `5` before the full-cohort path was folded into the partial one), the direct analogue of
        `base_mul_count_champBlocks_le`/`le_base_mul_count_champBlocks`.
        **Signature difference from the `k=1` case**: these last two need
        an extra hypothesis `w.length ≤ M` (the digit-count analogue got
        this for free from `d < b`); carries through as an eventual
        condition once instantiated at `M := champM b n` in
        `Asymptotics.lean`, since `champM b n → ∞`.
  - [x] `Positions.lean`: extended the `champIndex`-based straddle transfer
        (`base_mul_count_champPrefix_le` / `le_base_mul_count_champPrefix`)
        from `List.count` to `countOccurrences` as
        `base_pow_countOccurrences_champPrefix_le` /
        `le_base_pow_countOccurrences_champPrefix` (error
        `10(k+1)·b^k·b^M` / `6(k+1)·b^k·b^M`). Uses the Goal 2 stream
        sandwich (`countOccurrences_champBlocks_le` /
        `sum_le_countOccurrences_champBlocks`, seam error `N·k`) to bridge
        from "sum over individual numbers" to "occurrences in
        `champBlocks`", plus two small new lemmas
        (`le_countOccurrences_champPrefix` /
        `countOccurrences_champPrefix_le`) for the `champPrefix`-vs-
        `champBlocks (champIndex n)` seam itself. The `N·k` seam is `o(n)`
        because `N = o(n)` (`n ~ N·log_b N`), confirmed by re-deriving the
        error budget in terms of `n` before writing any of this section's
        proofs — it did not need to be sharpened further.

**Goal 4 complete.** All comparisons land in the shape Goal 5 needs:
`b^k · countOccurrences w (champPrefix b n)` vs `n`, error `O(k)·b^k·b^M`
in both directions, with `w.length ≤ M` as the one new side condition
(discharged as `∀ᶠ n in atTop` once `M := champM b n`, since
`champM b n → ∞`, mirroring `tendsto_champM_atTop`).

*(Post-theorem refactor: the entire upper half of this chain — every
`*_le` lemma named above except the straddle lemmas and
`le_card_blockAt_partial`'s mirror — was deleted; only the lower chain
survives, and the upper `champPrefix` transfer is derived from it by the
`allWords` complement/pigeonhole argument. See the refactor section.)*

---

## Goal 5 — Assembly (low risk) `[x]`

- [x] `Nat.log` ↔ `Real.log` Θ-bridge (once). *(Turned out unnecessary:
      `champM b n → ∞` (`tendsto_champM_atTop`, cast to ℝ) is all the
      squeeze arguments need — no analytic estimate ever requires
      `Real.logb`, so the bridge CLAUDE.md rule 8 anticipated was never
      built. `Nat.log` stays fully quarantined inside `champM`'s
      definition and the ℕ-layer lemmas that reference it directly.)*
- [x] Package Goals 2–4 into
      `(fun n => countOccurrences w (champPrefix b n) - n/b^k) =o[atTop] (n : ℝ)`.
      *(`countOccurrences_champPrefix_sub_isLittleO` in `Asymptotics.lean`,
      general-`w`; the `k = 1` case's `count_champPrefix_sub_isLittleO`
      was kept alongside it until the post-theorem refactor removed the
      whole `k = 1` slice.)*
- [x] Bridge to `Tendsto` via `isLittleO_iff_tendsto'`; discharge
      `champernowne_normal`. *(`tendsto_countOccurrences_champPrefix_div`
      → `champernowne_normal` in `Main.lean`, two lines via
      `champPrefix_eq_map` — note it needs `simp only`, not `rw`, since
      the rewrite target sits under a `fun n => …` binder that bare `rw`
      can't reach.)*
- [x] Only anticipated failure mode: a Goal 2–4 lemma with a wrong side
      condition — keep those `∀ᶠ`-friendly or unconditional. *(Realized:
      `w.length ≤ champM b n` isn't automatic the way `d < b` was for
      `k = 1`, so `base_pow_count_le`/`le_base_pow_count` are `∀ᶠ n in
      atTop` rather than unconditional — exactly the shape this bullet
      flagged in advance.)*

**Champernowne's theorem is fully proved. Zero `sorry`s in the codebase.**

---

## After Goal 1: generalize base `[x]`

Replace `10` by `b` with `2 ≤ b` hypothesis; definitions and proofs should
not use decimal-specific facts. Do this before Goal 3 so `decide` checks in
base 2/3 are available for the hard counting lemmas.
*(Done. All definitions take `b` (no hypothesis on definitions; `1 < b`
on lemmas). `champernowne_normal (b) (hb : 2 ≤ b)` is the final statement,
with `champernowne_normal_ten` as corollary. `ten_mul_*` lemmas renamed
`base_mul_*`; error budgets widened one power of `b` (base 2 is the tight
case): general-`N` `b^(M+3)`, transfer `b^(M+4)`. The k = 1 limit is now
`tendsto_count_champPrefix_div : d < b → count/n → 1/b` (since retired
with the `k = 1` slice). Base-2/3 `decide` checks live in `Sandbox.lean`.)*

## Post-theorem refactor — upper bounds from lower bounds `[x]`

*(July 2026.)* The upper occurrence-counting chain was never needed: a
window position in `champPrefix b n` matches **exactly one** length-`k`
word, so with `allWords b k` the enumeration of all `b^k` length-`k`
digit strings (leading zeros allowed),

```
Σ_{v ∈ allWords b k} countOccurrences v (champPrefix b n) ≤ n + 1
```

(`sum_countOccurrences_allWords_le` in `Count.lean` — distinct same-length
words have a unique prefix per window, so the position filters are
disjoint). Applying the LOWER transfer
`le_base_pow_countOccurrences_champPrefix` to each of the `b^k − 1` words
`v ≠ w` and subtracting from the pigeonhole yields the upper transfer

```
b^k · countOccurrences w (champPrefix b n) ≤ n + 6(k+1)·b^(2k)·b^M
```

(`base_pow_countOccurrences_champPrefix_le`, now ~50 lines), at the price
of one extra `b^k` factor in the error — harmless, since `k` is fixed in
the asymptotics. Validated in `Sandbox.lean` (exact constant, bases 2 and
10, words with leading zeros) before proving; the pigeonhole sum is
exactly `n + 1 − k` on `champPrefix`.

Deleted as a consequence (the entire upper chain plus the `k = 1`
vertical slice, whose statement is subsumed by `w := [d]` via
`countOccurrences_singleton`):

- `DigitCount.lean`: `base_pow_countOccurrences_champBlocks_le`,
  `base_pow_countOccurrences_partial_le`, `base_pow_count_boundary_le`,
  `sum_countOccurrences_partial_cohort_le`, `card_blockAt_partial_le`,
  `card_blockAt_head_partial_le`, `card_blockAt_past_end_partial`,
  `base_pow_cohort_count_head_le`, `base_pow_cohort_count_zero_le`, and
  the whole `k = 1` digit-count chain (`card_digitAt*`,
  `sum_count_bigDigits*`, `count_champBlocks*`, the partial-cohort digit
  sums, `base_mul_cohort_count*`, `base_mul_count_boundary*`,
  `base_mul_count_champBlocks*`, and the now-unused generic helpers
  `count_eq_card_filter_range`, `card_Ico_filter_div_mod_le`,
  `div_mul_le_div`).
- `Positions.lean`: `countOccurrences_champPrefix_le`,
  `countOccurrences_le_length_succ`, `le_count_champPrefix`,
  `count_champPrefix_le`, `base_mul_count_champPrefix_le`,
  `le_base_mul_count_champPrefix`.
- `Count.lean`: `countOccurrences_champBlocks_le`,
  `countOccurrences_flatten_le`.
- `Asymptotics.lean`: the `k = 1` packaging (`base_mul_count_le`,
  `le_base_mul_count`, `err_mul_le`, `err_mul_le'`, `tendsto_err_div`,
  `count_champPrefix_sub_isLittleO`, `tendsto_count_champPrefix_div`);
  the general-`w` error constant is now `6(k+1)·b^(2k)` (was
  `10(k+1)·b^k`).

Added: `allWords` + `mem_allWords` + `card_allWords` +
`sum_countOccurrences_allWords_le` (~110 lines in `Count.lean`). Net:
roughly 700 lines of the hardest counting arguments removed.

Code kept although not required for `champernowne_normal` (documented
Goal 2/1a/4 API, Mathlib upstream candidates) is segregated in
root-level `CountExtras.lean` — its own lake target, imported only by
`Sandbox.lean`, never by the `Champernowne` library, so the import
graph machine-checks the "needed for the theorem" boundary. It
collects the coherent Goal 2 remainder (append upper sandwich with the
sharp `min` seam, take/drop monotonicity, flatten lower bound,
`countOccurrences_singleton`), the exact Goal 1a/3 layer (`digitEquiv`
with its round-trips), and `champPrefix_prefix_champBlocks` (Goal 4);
each carries an individual "NOT required for `champernowne_normal`"
doc-comment.

## Stretch (post-theorem)

- Upstream candidates for Mathlib: `bigDigits` API, `countOccurrences`
  library, `IsNormalSequence`, `digitEquiv`.
- Champernowne constant as a real number and normality of the real — a
  separate project deliberately out of scope here.
