/-
Copyright (c) 2026 Arthur Champernowne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Champernowne
-/
import Mathlib

/-!
# Champernowne sequence — core definitions

All definitions for the project (PLAN.md Goal 0), generalized over the
base `b` (post-Goal-1 generalization; hypotheses `1 < b` appear only on
lemmas that need them, never on definitions). Digits are `List ℕ`
produced by `Nat.digits`; all Champernowne-facing code is big-endian via
`bigDigits`. The primary object is the finite prefix `champBlocks b N`;
the infinite sequence `champDigit b` is derived from it (prefixes-first
architecture, CLAUDE.md rule 3).
-/

/-- Big-endian digits of `n` in base `b`. -/
def bigDigits (b n : ℕ) : List ℕ := (Nat.digits b n).reverse

/-- First `N` blocks of the base-`b` Champernowne sequence: digits of 1..N. -/
def champBlocks (b N : ℕ) : List ℕ :=
  ((List.range N).map fun n => bigDigits b (n + 1)).flatten

theorem champBlocks_prefix {b N M : ℕ} (h : N ≤ M) :
    champBlocks b N <+: champBlocks b M := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [champBlocks, List.range_add, List.map_append, List.flatten_append]
  exact List.prefix_append _ _

theorem champBlocks_succ (b N : ℕ) :
    champBlocks b (N + 1) = champBlocks b N ++ bigDigits b (N + 1) := by
  simp [champBlocks, List.range_succ]

theorem le_length_champBlocks (b N : ℕ) : N ≤ (champBlocks b N).length := by
  induction N with
  | zero => simp [champBlocks]
  | succ n ih =>
    rw [champBlocks_succ, List.length_append]
    have hpos : 0 < (bigDigits b (n + 1)).length := by
      rw [bigDigits, List.length_reverse]
      exact List.length_pos_of_ne_nil
        (Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.succ_ne_zero n))
    omega

/-- The `i`-th digit (0-indexed) of the base-`b` Champernowne sequence. -/
def champDigit (b i : ℕ) : ℕ :=
  (champBlocks b (i + 1))[i]'(lt_of_lt_of_le (Nat.lt_succ_self i)
    (le_length_champBlocks b (i + 1)))

/-- Coherence: any sufficiently long prefix computes `champDigit`. -/
theorem champBlocks_getElem (b N i : ℕ) (h : i < (champBlocks b N).length) :
    (champBlocks b N)[i] = champDigit b i := by
  simp only [champDigit]
  rcases le_total N (i + 1) with hN | hN
  · exact (champBlocks_prefix hN).getElem h
  · exact ((champBlocks_prefix hN).getElem (lt_of_lt_of_le (Nat.lt_succ_self i)
      (le_length_champBlocks b (i + 1)))).symm

/-- The first `n` digits of the base-`b` Champernowne sequence. -/
def champPrefix (b n : ℕ) : List ℕ := (champBlocks b n).take n

theorem length_champPrefix (b n : ℕ) : (champPrefix b n).length = n := by
  rw [champPrefix, List.length_take]
  exact Nat.min_eq_left (le_length_champBlocks b n)

theorem champPrefix_eq_map (b n : ℕ) :
    champPrefix b n = (List.range n).map (champDigit b) := by
  have hlen := length_champPrefix b n
  apply List.ext_getElem
  · rw [hlen, List.length_map, List.length_range]
  · intro i h1 h2
    have hi : i < (champBlocks b n).length := by
      rw [hlen] at h1
      exact lt_of_lt_of_le h1 (le_length_champBlocks b n)
    simp only [champPrefix, List.getElem_take, List.getElem_map, List.getElem_range]
    exact champBlocks_getElem b n i hi

/-- Number of (overlapping) occurrences of `w` as a contiguous block of `l`.

Window convention: `l.tails` yields the suffixes starting at positions
`0, 1, …, l.length` (the last being `[]`). A tail shorter than `w` can never
satisfy `w.isPrefixOf`, so the windows that can count are exactly the start
positions `0 … l.length - w.length`; there are no partial windows at the end
of the list. In particular `countOccurrences w l = 0` whenever
`w.length > l.length`, and `countOccurrences [] l = l.length + 1`
(the empty word is a prefix of every tail) — callers always pass `w ≠ []`. -/
def countOccurrences (w l : List ℕ) : ℕ :=
  l.tails.countP (w.isPrefixOf ·)

/-- Normality of a digit sequence in base `b`: every block of length `k`
(entries `< b`, leading zeros allowed) has asymptotic frequency `b⁻ᵏ`. -/
def IsNormalSequence (b : ℕ) (s : ℕ → ℕ) : Prop :=
  ∀ w : List ℕ, w ≠ [] → (∀ d ∈ w, d < b) →
    Filter.Tendsto
      (fun n => (countOccurrences w ((List.range n).map s) : ℝ) / n)
      Filter.atTop (nhds ((b : ℝ) ^ w.length)⁻¹)
