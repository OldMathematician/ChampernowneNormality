# LESSONS — iteration notes from proof sessions

Reusable gotchas discovered while building this project. Consult before
debugging a failing tactic; append a one-line entry (pattern → fix) when a
proof attempt fails for a reason that could recur. Keep entries terse.

## `omega`

- `omega` abstracts nonlinear subterms (`a * b`, `10 ^ M`, sums, `n / p`)
  as opaque **syntactic** atoms. It succeeds iff the goal is linear in
  those atoms — so supply every needed identity *between* atoms as a
  `have` first: distributions (`p*q*(x+1) = p*q*x + p*q` via `ring`),
  power steps (`10^(M+1) = 10*10^M` via `pow_succ'`), commutations
  (`t*(K+1) = (K+1)*t` via `Nat.mul_comm`).
- Atom traps — two spellings of the same value are *different* atoms:
  - `M.succ` vs `M + 1`: `Nat.le_succ M` and `Nat.succ_ne_zero` write
    `.succ` into goals/hypotheses; prefer `Nat.le_add_right M 1` and
    `(show _ + 1 ≠ 0 by omega)`.
  - beta-redexes: `filter_upwards`/`eventually_ge_atTop` can yield
    `hn : P ((fun n => …) n)`; normalize with a defeq
    `have hn' : P (…) := hn` before `omega`.
  - `10 ^ (M+1-1)` vs `10 ^ M`: rewrite with
    `show M + 1 - 1 = M from rfl` (defeq, but not syntactic).
- With a **variable base** `b`, products `b * X` are nonlinear atoms:
  every step that was free with literal `10` (scaling a hypothesis by the
  base, `2·b^K ≤ b^(K+1)`, distributing `b*(x+y)`) needs an explicit
  bridge — `Nat.mul_le_mul_left b h`, `Nat.mul_le_mul_left _ hb` +
  `Nat.mul_comm`, `rw [Nat.mul_add]`.
- **Division by a variable** (`t / b`) is poison for `omega`: it
  represents `↑(t/b)` and `↑t/↑b` as *different* atoms and loses the
  sign of the ℤ-division form (counterexamples with `t/b < 0`!). Fix:
  `generalize t / b = q at h₁ h₂ ⊢` (and `t % b = r`) right before
  `omega`, after deriving any needed bounds on `q` (e.g. `q ≤ b^K`)
  while it is still spelled `t / b`.
- ℕ-subtraction coefficients like `(b-1)` break `ring`; either bridge
  with `(b-1)*X + X = b*X` (via `b - 1 + 1 = b`) for omega, or
  `obtain ⟨c, rfl⟩ : ∃ c, b = c + 2` and rewrite `c + 2 - 1 = c + 1`
  by `rfl` so `ring` sees subtraction-free polynomials.
- Same for `Finset.card_erase_of_mem` (produces `card - 1`): convert
  immediately to the additive form `(s.erase a).card + 1 = s.card`
  (needs `0 < s.card`, from membership) and never let the `- 1` reach
  `ring`/`omega`.
- When the final `omega` needs relations between *products* of large
  expressions (e.g. `c*n` vs `P*n` given `c + 1 = P`), `set` the big
  expressions to short names FIRST, then state each bridge as a `have`
  whose statement is spelled exactly as the atoms appear
  (`have g : c * n + n = P * n := by rw [← hcard]; ring`). Stating the
  bridge explicitly keeps `ring` from normalizing into a spelling that
  no longer matches the hypotheses' atoms; `set` keeps the spellings
  short enough to get right. (Used to derive the upper champPrefix
  transfer from the lower one.)

## Decidability

- `Decidable` instances are **data**: after `simp only` rewrites inside an
  `if` condition, the two sides can be propositionally identical yet fail
  `rfl` because the embedded instances differ. Fix: full `simp` (its
  congruence repairs instances) or `if_congr Iff.rfl rfl rfl`.
- Term-level `decide (…)` fails instance synthesis for bounded-∀ over
  terms mentioning `Nat.digits` (both `Finset.Ico` and `List` forms); the
  **tactic** `by decide` handles all of them. Write decide-checks as
  `example : … := by decide`.
- `Finset.filter` synthesizes `DecidablePred` fine for digit predicates —
  the quirk above is specific to bounded-∀ `Decidable` synthesis.

## `#eval` / Sandbox

- `#eval` refuses terms whose *elaboration* depends on the `sorry` axiom
  (e.g. a `getElem` bound proof citing a sorried lemma). Use `#eval!` —
  safe, proofs are erased at runtime. Revert to `#eval` once proved.
- `lake env lean Sandbox.lean` elaborates against **existing oleans**; run
  `lake build` first after editing an imported module, or the identifiers
  added there are "unknown".
- PowerShell: piping `lake env lean … | Select-Object -First N` can close
  the pipe early and report a bogus nonzero exit code (255/-1) even though
  elaboration succeeded. Capture first (`$out = lake env lean … 2>&1`),
  check `$LASTEXITCODE`, then slice `$out`.
- Per-file `#lint` without polluting the build: temporarily append
  `#lint` to the file, `lake env lean <file>`, restore (try/finally) —
  no olean is written, imports resolve from cache.
- The IDE has the same staleness: after a dependency gains declarations,
  run "Lean 4: Restart File" on the importing file.

## Mathlib API (state as of 2026-07 master)

- `Nat.digits_len` is deprecated → `Nat.length_digits`. Better:
  `Nat.digits_length_le_iff` / `Nat.lt_digits_length_iff` characterize
  digit count directly against powers — avoids `Nat.log` entirely.
- `Nat.getD_digits : (digits b n).getD i 0 = n / b ^ i % b` — digit
  extraction; combine with `List.getElem?_reverse` for big-endian.
- `Nat.mul_add_mod` has the multiplier on the **left**:
  `(a * b + c) % a = c % a`.
- `Nat.add_mul_div_left (a c) (H : 0 < b) : (a + b * c) / b = a / b + c` —
  arrange the summand as `b * c`, not `c * b`.
- `div_le_div_iff` → `div_le_div_iff₀` (GroupWithZero refactor).
- `tendsto_atTop_add_const_right` needs an ordered **group**; for ℕ use
  `tendsto_atTop_mono` with a pointwise `≤`.
- `𝓝` notation requires `open Topology` (not just `Filter`).
- `List.getLast?_eq_head?_reverse` does the endianness work for
  head/last-digit arguments.
- `Finset.card_le_card_of_injOn` takes `Set.MapsTo f ↑s ↑t` (coe-side,
  like `Finset.card_nbij'`), NOT a Finset-level `∀ a ∈ s, f a ∈ t`: after
  `rintro`, memberships need `simp only [Finset.coe_product, Set.mem_prod,
  Finset.mem_coe, …]` / `[Finset.coe_filter, Set.mem_setOf_eq, …]`;
  `Finset.mem_product`/`mem_filter` alone make no progress.
- `Nat.findGreatest` API: `findGreatest_spec`, `le_findGreatest`,
  `findGreatest_is_greatest`; see elaboration note below.

## Elaboration order

- Lemmas whose conclusion mentions `P (findGreatest P n)` (or similar
  higher-order patterns) can't infer `P` from the goal through a project
  `def` — pass it explicitly: `Nat.findGreatest_spec (P := fun N => …)`.
- Same for `Finset.single_le_sum (f := fun m => …)` when the goal's sums
  are nested.
- A `(by tac)` argument inside an application may elaborate against
  unsolved metavariables and misbehave; hoist it to a named `have` first.

## `rw` / `calc`

- `rw` rewrites the **first** match: `Finset.sum_Ico_succ_top` aimed at
  the RHS may peel a sum on the LHS instead. Use
  `exact (lemma …).symm` or `conv_rhs`.
- In a `calc` step, `_` may be the entire LHS but not a subterm
  placeholder inside the step's RHS expression.
- `rw [defName]` works for simple non-recursive `def`s, but `show`
  (defeq) is more robust, e.g. for goals under binders.
- Plain `rw`/`rwa` cannot rewrite an occurrence sitting inside a
  `fun n => …` (or any binder) — it only rewrites at the top level of the
  goal/hypothesis. If the target term is under a lambda (e.g. rewriting
  `champPrefix b n = (List.range n).map (champDigit b)` inside a
  `Tendsto (fun n => f (champPrefix b n)) …` hypothesis), use
  `simp only [lemma] at h` (or `simpa only [lemma] using h`) instead —
  `simp`'s congruence closure reaches under binders where `rw` gives a
  silent "did not find occurrence" error that looks like a missing
  hypothesis rather than a binder problem.

## Statement design (project-level)

- Compare `10 * count` with `length`/`n` instead of `count` with
  `length / 10`: keeps the ℕ layer subtraction- and division-free, and
  the per-cohort identities become exact equalities.
- Parametrize error bounds by `M` with hypotheses
  `10^(M-1) ≤ … ≤ 10^M` in the ℕ layer; instantiate
  `M := Nat.log 10 (…) + 1` only in Asymptotics.lean (the `Nat.log`
  quarantine).
- Before reaching for a closed-form sum + `ring`/`nlinarith`/case-split
  proof of an `A ≈ B` comparison, check whether the underlying per-item
  fact is already *exact and independent of the free parameter* — e.g.
  `card_blockAt`'s value at an interior position doesn't depend on `w`
  at all, so `b^k * (interior card) = cohortSize` on the nose, with zero
  slack. Deriving the closed form first and only then comparing it to the
  target (what `base_pow_cohort_count_*` originally did) buries that
  exactness under `(m - w.length)`/`(m - w.length - 1)` subtraction
  bookkeeping; multiplying through *before* collapsing to the closed form
  keeps it visible and cuts the proof roughly in half. Worth a second pass
  once a family of lemmas is working, not just while first getting it to
  compile.
