/-
Copyright (c) 2026 Arthur Champernowne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Champernowne
-/
import Champernowne.Defs

/-!
# Comparator challenge: Champernowne's theorem (1933)

States the base-`b` Champernowne sequence normality theorem against the
project's core definitions (`Champernowne/Defs.lean`), left unproved.
Paired with `Solution.lean` for independent verification via
`leanprover/comparator` (see `comparator_config.json` at the repo root).

Not part of the published proof — the real proof lives in `Main.lean`
and is unaffected by this file. `Solution.lean` shares this file's import
of `Defs.lean` but does not import `Challenge.lean` itself, so the two
`champernowne_normal` declarations live in separate module environments
for comparator to compare rather than colliding as duplicate names.
-/

theorem champernowne_normal (b : ℕ) (hb : 2 ≤ b) :
    IsNormalSequence b (champDigit b) := sorry
