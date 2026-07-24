/-
Copyright (c) 2026 Arthur Champernowne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Champernowne
-/
import Champernowne.Defs
import Champernowne.DigitCount
import Champernowne.Positions
import CountExtras

/-!
# Sandbox — `#eval` sanity checks (NOT imported by the main build)

Elaborate with `lake env lean Sandbox.lean`. Every counting lemma gets its
checks here BEFORE any proof attempt (CLAUDE.md: test before proving).
Expected values are hand-computed and noted next to each check.
-/

-- Champernowne prefix: 1 2 3 4 5 6 7 8 9 1 0 1 1 1 2 ...
#eval champPrefix 10 15   -- expect [1,2,3,4,5,6,7,8,9,1,0,1,1,1,2]

-- Boundary values
#eval champPrefix 10 0    -- expect []
#eval champPrefix 10 1    -- expect [1]
#eval champPrefix 10 9    -- expect [1,2,3,4,5,6,7,8,9]
#eval champPrefix 10 10   -- expect [1,2,3,4,5,6,7,8,9,1]

-- bigDigits basics
#eval bigDigits 10 0    -- expect []
#eval bigDigits 10 305  -- expect [3,0,5]

-- champBlocks boundaries
#eval champBlocks 10 0    -- expect []
#eval champBlocks 10 1    -- expect [1]
#eval champBlocks 10 10   -- expect [1,2,3,4,5,6,7,8,9,1,0]

-- champDigit plumbing must agree with champPrefix (champPrefix_eq_map).
-- `#eval!` because champDigit's getElem bound cites the (sorried)
-- le_length_champBlocks; the proof is erased at runtime, so this is safe.
#eval! (List.range 15).map (champDigit 10)  -- expect [1,2,3,4,5,6,7,8,9,1,0,1,1,1,2]

-- countOccurrences: overlapping occurrences
-- champPrefix 10 15 = [1,2,3,4,5,6,7,8,9,1,0,1,1,1,2]; [1,1] starts at 11,12
#eval countOccurrences [1,1] (champPrefix 10 15)  -- expect 2

-- leading-zero blocks are counted like any other
#eval countOccurrences [0] (champPrefix 10 15)    -- expect 1 (position 10)
#eval countOccurrences [0,0] (champPrefix 10 15)  -- expect 0
#eval countOccurrences [0,1] (champPrefix 10 15)  -- expect 1 (positions 10-11)

-- single-digit bridge to List.count (Goal 2 sanity)
#eval countOccurrences [1] (champPrefix 10 15)          -- expect 5
#eval (champPrefix 10 15).count 1                       -- expect 5

-- window convention: w longer than l counts nothing
#eval countOccurrences [1,2,3] [1,2]  -- expect 0

/-! ## Goal 1a prototyping — interval ↔ digit-string equivalence

`digitEquiv m : Finset.Ico (10^(m-1)) (10^m) ≃` {length-`m` strings, digits
`< 10`, nonzero head}. Forward map `bigDigits 10`, inverse
`Nat.ofDigits 10 ∘ List.reverse`. Prototyped at `m = 3` per PLAN.md,
with `m = 1, 2` boundaries. -/

/-- The `m`-digit cohort as a list: `[10^(m-1), …, 10^m - 1]`. -/
def cohort (m : ℕ) : List ℕ :=
  (List.range (10 ^ m - 10 ^ (m - 1))).map (· + 10 ^ (m - 1))

#eval (cohort 3).length    -- expect 900 (= 9 * 10^2, card of the LHS)
#eval (cohort 3).head?     -- expect some 100
#eval (cohort 3).getLast?  -- expect some 999

-- forward map lands in the RHS subtype: length m, digits < 10, head ≠ 0
#eval (cohort 3).all fun n =>
  (bigDigits 10 n).length == 3
    && (bigDigits 10 n).all (· < 10)
    && (bigDigits 10 n).head? != some 0
-- expect true

-- round-trip 1: ofDigits ∘ reverse ∘ bigDigits = id on the interval
#eval (cohort 3).all fun n => Nat.ofDigits 10 (bigDigits 10 n).reverse == n
-- expect true

/-- All length-3 digit strings with nonzero head (RHS of `digitEquiv 3`). -/
def threeDigitStrings : List (List ℕ) :=
  (List.range 9).flatMap fun a =>
    (List.range 10).flatMap fun b =>
      (List.range 10).map fun c => [a + 1, b, c]

#eval threeDigitStrings.length  -- expect 900 (cards match)

-- inverse map lands in the interval
#eval threeDigitStrings.all fun l =>
  100 ≤ Nat.ofDigits 10 l.reverse && Nat.ofDigits 10 l.reverse < 1000
-- expect true

-- round-trip 2: bigDigits ∘ ofDigits ∘ reverse = id on strings
#eval threeDigitStrings.all fun l =>
  bigDigits 10 (Nat.ofDigits 10 l.reverse) == l
-- expect true

/-- Count of `m`-digit numbers with digit `d` at (big-endian) position `j`.
Expected: `j = 0`: `10^(m-1)` if `d ≠ 0` else `0`; `0 < j < m`: `9·10^(m-2)`. -/
def countDigitAt (m j d : ℕ) : ℕ :=
  (cohort m).countP fun n => (bigDigits 10 n)[j]? == some d

#eval (List.range 10).map (countDigitAt 3 0 ·)
-- expect [0, 100, 100, 100, 100, 100, 100, 100, 100, 100]
#eval (List.range 10).map (countDigitAt 3 1 ·)  -- expect ten 90s
#eval (List.range 10).map (countDigitAt 3 2 ·)  -- expect ten 90s

-- boundaries: m = 1 (cohort 1..9), m = 2 (cohort 10..99)
#eval (List.range 10).map (countDigitAt 1 0 ·)  -- expect [0, 1, 1, ..., 1]
#eval (List.range 10).map (countDigitAt 2 0 ·)  -- expect [0, 10, 10, ..., 10]
#eval (List.range 10).map (countDigitAt 2 1 ·)  -- expect ten 9s

-- digit-d total over the concatenated cohort (Goal 1 deliverable):
-- d ≠ 0: 10^(m-1) + (m-1)·9·10^(m-2); d = 0: (m-1)·9·10^(m-2)
-- (consistency: sums of the per-position counts above)
#eval ((cohort 3).map (bigDigits 10)).flatten.count 5  -- expect 280
#eval ((cohort 3).map (bigDigits 10)).flatten.count 0  -- expect 180

-- decide works on the bounded statements (bigDigits is already
-- base-general, so base-2 decide checks are available pre-generalization).
-- NB: must be the TACTIC `by decide` — term-level `decide (...)` fails
-- Decidable synthesis when `Nat.digits` appears under the binder.
example : ∀ n ∈ Finset.Ico 4 8,
    (bigDigits 2 n).length = 3 ∧ (bigDigits 2 n).head? ≠ some 0 := by decide
example : ∀ n ∈ Finset.Ico 4 8,
    Nat.ofDigits 2 (bigDigits 2 n).reverse = n := by decide

/-! ### card_Ico_filter_div_mod prototyping (for the position-count cards)

Claim: for `d < q`, `p*q ∣ A`, `p*q ∣ B`:
`#{n ∈ [A,B) | n/p % q = d} = (B/(p*q) - A/(p*q)) * p`. -/

#eval ((Finset.Ico 100 1000).filter (fun n => n / 10 % 10 = 7)).card  -- expect 90
#eval (1000 / 100 - 100 / 100) * 10                                   -- expect 90
#eval ((Finset.Ico 40 160).filter (fun n => n / 2 % 4 = 3)).card      -- expect 30
#eval (160 / 8 - 40 / 8) * 2                                          -- expect 30
#eval ((Finset.Ico 0 1000).filter (fun n => n / 100 % 10 = 0)).card   -- expect 100
#eval ((Finset.Ico 30 90).filter (fun n => n / 3 % 2 = 1)).card       -- expect 30
#eval (90 / 6 - 30 / 6) * 3                                           -- expect 30

/-! ### Cohort digit-count sums (Goal 1)

Claim: over all `m`-digit numbers, digit `d ≠ 0` occurs
`10^(m-1) + (m-1)·9·10^(m-2)` times; digit `0` occurs `(m-1)·9·10^(m-2)`. -/

#eval (Finset.Ico 100 1000).sum fun n => (bigDigits 10 n).count 5  -- expect 280
#eval (Finset.Ico 100 1000).sum fun n => (bigDigits 10 n).count 0  -- expect 180
#eval (Finset.Ico 10 100).sum fun n => (bigDigits 10 n).count 5    -- expect 19
#eval (Finset.Ico 10 100).sum fun n => (bigDigits 10 n).count 0    -- expect 9
#eval (Finset.Ico 1 10).sum fun n => (bigDigits 10 n).count 5      -- expect 1
#eval (Finset.Ico 1 10).sum fun n => (bigDigits 10 n).count 0      -- expect 0

/-! ### champBlocks digit counts at cohort boundaries (Goal 1)

Claim: `(champBlocks 10 10 (10^M - 1)).count d` = sum of the cohort formulas. -/

#eval (champBlocks 10 99).count 5    -- expect 20  (= 1 + 19)
#eval (champBlocks 10 99).count 0    -- expect 9   (= 0 + 9)
#eval (champBlocks 10 999).count 5   -- expect 300 (= 1 + 19 + 280)
#eval (champBlocks 10 999).count 0   -- expect 189 (= 0 + 9 + 180)
#eval ∑ m ∈ Finset.Icc 1 3, (10 ^ (m-1) + (m-1) * (9 * 10 ^ (m-2)))  -- expect 300
#eval ∑ m ∈ Finset.Icc 1 3, (m-1) * (9 * 10 ^ (m-2))                 -- expect 189
-- general-N sanity for the Finset-sum form of the count
#eval (champBlocks 10 47).count 3
#eval (Finset.Ico 1 48).sum fun n => (bigDigits 10 n).count 3  -- expect: same

/-! ### Partial-cohort bounds prototyping (Goal 1)

Claim A: for `p*q ∣ A`, any `t`:
  `t/(p*q)*p ≤ #{n ∈ [A,A+t) | n/p % q = d} ≤ t/(p*q)*p + p`.
Claim B: for `10^(M-1) + t ≤ 10^M`, `d < 10`:
  `M*(t/10) ≤ (∑ n ∈ [10^(M-1), 10^(M-1)+t), count d) + 10^M` and
  `∑ ... ≤ M*(t/10) + 10^M`. -/

-- Claim A, interior position (M = 3, j = 1: p = 10, q = 10, A = 100)
#eval (List.range 901).all fun t =>
  let c := ((Finset.Ico 100 (100 + t)).filter (fun n => n / 10 % 10 = 7)).card
  t / 100 * 10 ≤ c && c ≤ t / 100 * 10 + 10
-- expect true

-- Claim A, last position (p = 1, q = 10, A = 10, M = 2)
#eval (List.range 91).all fun t =>
  let c := ((Finset.Ico 10 (10 + t)).filter (fun n => n / 1 % 10 = 5)).card
  t / 10 * 1 ≤ c && c ≤ t / 10 * 1 + 1
-- expect true

-- Claim B (M = 3, d = 5 and d = 0)
#eval (List.range 901).all fun t =>
  let S := (Finset.Ico 100 (100 + t)).sum fun n => (bigDigits 10 n).count 5
  3 * (t / 10) ≤ S + 1000 && S ≤ 3 * (t / 10) + 1000
-- expect true
#eval (List.range 901).all fun t =>
  let S := (Finset.Ico 100 (100 + t)).sum fun n => (bigDigits 10 n).count 0
  3 * (t / 10) ≤ S + 1000 && S ≤ 3 * (t / 10) + 1000
-- expect true

/-! ### 10·count vs length comparison (Goal 1, general N)

Per-cohort identities: `d ≠ 0`: `10·count = length + 10^(m-1)`;
`d = 0`: `10·count + 9·10^(m-1) = length`.
General N (`10^(M-1) ≤ N+1 ≤ 10^M`):
`|10·(champBlocks 10 N).count d − (champBlocks 10 N).length| ≤ 10^(M+2)`. -/

#eval (10 * ((Finset.Ico 100 1000).sum fun n => (bigDigits 10 n).count 5),
       ((Finset.Ico 100 1000).sum fun n => (bigDigits 10 n).length) + 100)
-- expect equal pair (identity, d ≠ 0, m = 3)
#eval (10 * ((Finset.Ico 100 1000).sum fun n => (bigDigits 10 n).count 0) + 900,
       (Finset.Ico 100 1000).sum fun n => (bigDigits 10 n).length)
-- expect equal pair (identity, d = 0, m = 3)
#eval (List.range 400).all fun N =>
  let M := (Nat.digits 10 (N + 1)).length
  let L := (champBlocks 10 N).length
  let c3 := 10 * (champBlocks 10 N).count 3
  let c0 := 10 * (champBlocks 10 N).count 0
  c3 ≤ L + 10 ^ (M + 2) && L ≤ c3 + 10 ^ (M + 2)
    && c0 ≤ L + 10 ^ (M + 2) && L ≤ c0 + 10 ^ (M + 2)
-- expect true

/-! ### champIndex and the champPrefix transfer (Goal 1) -/

#eval (List.range 20).map (champIndex 10)
-- expect [0,1,2,3,4,5,6,7,8,9,9,10,10,11,11,12,12,13,13,14]
#eval (List.range 60).all fun n =>
  (champBlocks 10 (champIndex 10 n)).length ≤ n
    && n < (champBlocks 10 (champIndex 10 n + 1)).length
-- expect true (defining sandwich of champIndex)
#eval (List.range 200).all fun n =>
  let N := champIndex 10 n
  let M := (Nat.digits 10 (N + 1)).length
  let c := 10 * (champPrefix 10 n).count 1
  c ≤ n + 10 ^ (M + 3) && n ≤ c + 10 ^ (M + 3)
-- expect true (main transfer bounds, d = 1)

/-! ### Asymptotics-layer ℕ facts (Goal 1 endgame)

`M := log 10 (champIndex 10 n + 1) + 1`; claims:
(D) `9·10^(M-2)·(M-1) ≤ n`; (F) `10^(M+3)·9(M-1) ≤ 10^5·n`. -/

#eval (List.range 300).all fun n =>
  let M := Nat.log 10 (champIndex 10 n + 1) + 1
  9 * 10 ^ (M - 2) * (M - 1) ≤ n
    && 10 ^ (M + 3) * (9 * (M - 1)) ≤ 10 ^ 5 * n
-- expect true

-- digitEquiv computes (fully proved, plain #eval)
#eval (digitEquiv (b := 10) (by norm_num) 3 (by norm_num) ⟨305, by decide⟩).1
-- expect [3, 0, 5]
set_option maxRecDepth 4096 in
#eval ((digitEquiv (b := 10) (by norm_num) 3 (by norm_num)).symm
  ⟨[3, 0, 5], by decide⟩ : ℕ)
-- expect 305

/-! ### countOccurrences mini-library (Goal 2)

Append sandwich (`w ≠ []`):
`occ a + occ b ≤ occ (a++b) ≤ occ a + occ b + min |w| |a|`;
flatten deviation ≤ `|L|·|w|`; take/drop monotone. -/

-- append sandwich instances
#eval (countOccurrences [1,2] [1,2,1], countOccurrences [1,2] [2,1,2],
       countOccurrences [1,2] ([1,2,1] ++ [2,1,2]))
-- expect (1, 1, 3): 1+1 ≤ 3 ≤ 1+1+min 2 3 ✓
#eval (countOccurrences [0,0] [0], countOccurrences [0,0] [0],
       countOccurrences [0,0] ([0] ++ [0]))
-- expect (0, 0, 1): 0+0 ≤ 1 ≤ 0+0+min 2 1 ✓ (straddle, min is sharp)
-- exhaustive check over binary lists (lengths ≤ 4) and w of length ≤ 2
#eval (do
  let mut ok := true
  let lists : List (List ℕ) :=
    (List.range 32).map fun k =>
      (List.range 5).filterMap fun i =>
        if k / 2 ^ i % 2 = 1 ∨ i < k % 5 then some (k / 2 ^ i % 2) else none
  for w in [[0], [1], [0,0], [0,1], [1,0], [1,1]] do
    for a in lists do
      for b in lists do
        let s := countOccurrences w (a ++ b)
        let lo := countOccurrences w a + countOccurrences w b
        ok := ok && lo ≤ s && s ≤ lo + min w.length a.length
  return ok : Id Bool)
-- expect true

-- flatten deviation
#eval (countOccurrences [2,1] [[1,2],[1,2]].flatten,
       ([[1,2],[1,2]].map (countOccurrences [2,1])).sum)
-- expect (1, 0): 0 ≤ 1 ≤ 0 + 2*2 ✓

-- take/drop monotone + error
#eval ((List.range 16).all fun n =>
  countOccurrences [1,1] ((champPrefix 10 15).take n)
      ≤ countOccurrences [1,1] (champPrefix 10 15)
    && countOccurrences [1,1] ((champPrefix 10 15).drop n)
      ≤ countOccurrences [1,1] (champPrefix 10 15)
    && countOccurrences [1,1] (champPrefix 10 15)
      ≤ countOccurrences [1,1] ((champPrefix 10 15).take n)
        + countOccurrences [1,1] ((champPrefix 10 15).drop n) + 2)
-- expect true

-- singleton bridge
#eval ((List.range 10).all fun d =>
  countOccurrences [d] (champPrefix 10 50) == (champPrefix 10 50).count d)
-- expect true

/-! ### Goal 3 prototyping — general position counting

Claim: among `m`-digit numbers, block `w` (length `k`, digits `< b`) at
position `j`: `j = 0`: `b^(m-k)` if `w.head? ≠ some 0` else `0`;
`0 < j ≤ m-k`: `(b-1)·b^(m-k-1)`. Bridge: `w` at `j` ⟺
`n / b^(m-j-k) % b^k = ofDigits b w.reverse`. -/

-- bridge instance: 305 has block [0,5] at position 1
#eval (((bigDigits 10 305).drop 1).take 2 == [0, 5],
       305 / 10 ^ 0 % 10 ^ 2 == Nat.ofDigits 10 [5, 0])
-- expect (true, true)

-- base 10, m = 3: interior j = 1, w = [1,2] → 9; head w = [1,2] → 10;
-- head-zero w = [0,1] → 0; interior j = 1, w = [0,1] → 9
#eval ((Finset.Ico 100 1000).filter
  (fun n => ((bigDigits 10 n).drop 1).take 2 = [1, 2])).card  -- expect 9
#eval ((Finset.Ico 100 1000).filter
  (fun n => ((bigDigits 10 n).drop 0).take 2 = [1, 2])).card  -- expect 10
#eval ((Finset.Ico 100 1000).filter
  (fun n => ((bigDigits 10 n).drop 0).take 2 = [0, 1])).card  -- expect 0
#eval ((Finset.Ico 100 1000).filter
  (fun n => ((bigDigits 10 n).drop 1).take 2 = [0, 1])).card  -- expect 9

-- decide versions in bases 2 and 3
example : ((Finset.Ico 4 8).filter
    (fun n => ((bigDigits 2 n).drop 0).take 2 = [1, 0])).card = 2 ^ (3 - 2) := by
  decide
example : ((Finset.Ico 4 8).filter
    (fun n => ((bigDigits 2 n).drop 1).take 1 = [0])).card
    = (2 - 1) * 2 ^ (3 - 1 - 1) := by decide
example : ((Finset.Ico 3 9).filter
    (fun n => ((bigDigits 3 n).drop 1).take 1 = [2])).card
    = (3 - 1) * 3 ^ (2 - 1 - 1) := by decide

-- cohort occurrence sums: b^(m-k) + (m-k)·(b-1)·b^(m-k-1) for head ≠ 0;
-- (m-k)·(b-1)·b^(m-k-1) for head = 0
#eval (Finset.Ico 100 1000).sum fun n =>
  countOccurrences [1, 2] (bigDigits 10 n)  -- expect 10 + 9 = 19
#eval (Finset.Ico 100 1000).sum fun n =>
  countOccurrences [0, 1] (bigDigits 10 n)  -- expect 9
#eval (Finset.Ico 100 1000).sum fun n =>
  countOccurrences [1] (bigDigits 10 n)     -- expect 100 + 180 = 280
example : (Finset.Ico 4 8).sum
    (fun n => countOccurrences [1, 0] (bigDigits 2 n))
    = 2 ^ (3 - 2) + (3 - 2) * ((2 - 1) * 2 ^ (3 - 2 - 1)) := by decide
example : (Finset.Ico 4 8).sum
    (fun n => countOccurrences [0, 0] (bigDigits 2 n))
    = (3 - 2) * ((2 - 1) * 2 ^ (3 - 2 - 1)) := by decide

-- champBlocks occurrence sandwich (Goal 2 + Goal 3 combination)
#eval
  let s := (Finset.Ico 1 100).sum fun n =>
    countOccurrences [1, 2] (bigDigits 10 n)
  let c := countOccurrences [1, 2] (champBlocks 10 99)
  (s ≤ c && c ≤ s + 99 * 2, s, c)
-- expect (true, _, _)

-- countOccurrences as a count of window positions
#eval (countOccurrences [1, 1] (champPrefix 10 15),
  ((Finset.range 16).filter
    (fun j => [1, 1].isPrefixOf ((champPrefix 10 15).drop j))).card)
-- expect (2, 2)

/-! ### Base-general checks (post-generalization)

`decide` in small bases is now available for exact counting facts. -/

#eval champPrefix 2 15
-- expect [1,1,0,1,1,1,0,0,1,0,1,1,1,0,1] (1,10,11,100,101,110,…)
example : (champBlocks 2 3).count 1 = 4 := by decide
example : (champBlocks 2 3).count 0 = 1 := by decide
example : (champBlocks 3 8).count 0 = 2 := by decide
-- cohort formula in base 2, M = 2: Σ = (1+0) + (2+1·1·1) = 4
example : (champBlocks 2 (2 ^ 2 - 1)).count 1
    = ∑ m ∈ Finset.Icc 1 2, (2 ^ (m-1) + (m-1) * (1 * 2 ^ (m-2))) := by decide

/-! ### Goal 4 prototyping — partial-cohort block occurrence sums

`K = 2`, 3-digit numbers `[100, 1000)`, partial range `[100, 150)` (`t = 50`).
`w = [1, 2]`: head block "12" at `n ∈ [120,130)` (10 numbers); interior
block "12" at position 1 (`n ≡ 12 mod 100`) hits only `n = 112` (1 number).
Total 11, budget `(K+1-k)*(t/b^k) + 2*b^(K+1-k) = 1*0 + 20 = 20`. -/
#eval (Finset.Ico 100 150).sum fun n => countOccurrences [1, 2] (bigDigits 10 n)
-- expect 11
#eval (2 - 1) * (50 / 10 ^ 2) + 2 * 10 ^ (2 + 1 - 2)  -- expect budget 20

-- w = [0, 1]: head impossible (leading zero); interior "01" at position 1
-- means n ≡ 1 mod 100: only n = 101. Total 1.
#eval (Finset.Ico 100 150).sum fun n => countOccurrences [0, 1] (bigDigits 10 n)
-- expect 1

-- Sharper check: t spanning almost the whole cohort, k = 1 (single digit,
-- should match List.count exactly via the countOccurrences_singleton bridge).
#eval (Finset.Ico 100 150).sum fun n => countOccurrences [5] (bigDigits 10 n)
#eval (Finset.Ico 100 150).sum fun n => (bigDigits 10 n).count 5
-- expect equal

/-! ### Upper-from-lower refactor prototyping (allWords + window pigeonhole)

Plan: replace the entire upper chain by the complement argument
`b^k·occ w = b^k·(#windows) − Σ_{v ≠ w} b^k·occ v`, using the existing
lower bound on each `v ≠ w`. Needs (a) the enumeration `allWords b k` of
all length-`k` digit strings (leading zeros allowed), `card = b^k`;
(b) pigeonhole: distinct same-length words occupy disjoint windows, so
`Σ_{v ∈ allWords b k} countOccurrences v l ≤ l.length + 1`. -/

/-- List prototype of `allWords` (the real one is a `Finset`). -/
def allWordsL (b : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (List.range b).flatMap fun d => (allWordsL b k).map (d :: ·)

#eval (allWordsL 10 2).length  -- expect 100 (= b^k)
#eval (allWordsL 2 3).length   -- expect 8
#eval allWordsL 2 2            -- expect [[0,0],[0,1],[1,0],[1,1]] (some order)
#eval (allWordsL 2 3).all fun v => v.length == 3 && v.all (· < 2)  -- expect true
#eval ((allWordsL 3 3).eraseDups).length  -- expect 27 (no duplicates)
#eval (allWordsL 2 0)          -- expect [[]] (k = 0 boundary)

-- Pigeonhole: Σ_v occ v ≤ len + 1. On champPrefix every window is a valid
-- digit string, so for n ≥ k the sum is EXACTLY n + 1 - k (all windows hit);
-- the ≤ (n+1) form is what gets proved (subtraction-free).
#eval (List.range 40).all fun n =>
  ((allWordsL 10 2).map fun v => countOccurrences v (champPrefix 10 n)).sum ≤ n + 1
-- expect true
#eval (List.range 40).all fun n =>
  ((allWordsL 2 3).map fun v => countOccurrences v (champPrefix 2 n)).sum
    == if n ≥ 3 then n + 1 - 3 else 0
-- expect true (exactness on champPrefix, base 2, k = 3)
#eval (((allWordsL 2 1).map fun v => countOccurrences v (champPrefix 2 7)).sum,
       ((allWordsL 10 1).map fun v => countOccurrences v (champPrefix 10 9)).sum)
-- expect (7, 9) (k = 1 boundary: n + 1 - 1 = n)

-- The new derived upper bound with the exact proposed constant:
-- b^k · occ w (champPrefix b n) ≤ n + 7·(k+1)·b^(2k)·b^M
-- where b^(M-1) ≤ champIndex b n + 1 ≤ b^M (M from the digit length).
-- Exhaustive small-base check over several w including leading zeros.
#eval (List.range 260).all fun n =>
  let M := (Nat.digits 2 (champIndex 2 n + 1)).length
  [[1], [0], [1,1], [0,0], [0,1], [1,0,1], [0,0,1]].all fun w =>
    2 ^ w.length * countOccurrences w (champPrefix 2 n)
      ≤ n + 7 * (w.length + 1) * 2 ^ (2 * w.length) * 2 ^ M
-- expect true
#eval (List.range 200).all fun n =>
  let M := (Nat.digits 10 (champIndex 10 n + 1)).length
  [[1], [0], [1,2], [0,0]].all fun w =>
    10 ^ w.length * countOccurrences w (champPrefix 10 n)
      ≤ n + 7 * (w.length + 1) * 10 ^ (2 * w.length) * 10 ^ M
-- expect true

-- Core additive combination step (before absorbing into the constant):
-- b^k·occ w + (b^k − 1)·n ≤ b^k·(n+1) + (b^k − 1)·E with E the lower-bound
-- error 7·(k+1)·b^k·b^M; sanity that b^k ≤ E (absorption b^k + (b^k−1)E ≤ b^k·E).
#eval (List.range 260).all fun n =>
  let M := (Nat.digits 2 (champIndex 2 n + 1)).length
  [[1,1], [0,1]].all fun w =>
    let k := w.length
    let E := 7 * (k + 1) * 2 ^ k * 2 ^ M
    2 ^ k ≤ E
      && 2 ^ k * countOccurrences w (champPrefix 2 n) + (2 ^ k - 1) * n
          ≤ 2 ^ k * (n + 1) + (2 ^ k - 1) * E
-- expect true
