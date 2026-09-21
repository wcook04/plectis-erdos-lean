/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249ag

Every non-theorem declaration of `PalomarCorpus/E249ag/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter

namespace PalomarCorpus.E249.PaperStatementsAG
open Filter
/-- Lacunary spike ranks `2^(k+3)`, beginning at `8`. Local copy of Erdos249257.TotientParityCoboundaryCountermodel.IsLargePowerTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsLargePowerTwo (n : ℕ) : Prop :=
  ∃ k : ℕ, n = 2 ^ (k + 3)
/-- The zero-one indicator of the lacunary spike ranks. Local copy of Erdos249257.TotientParityCoboundaryCountermodel.largePowerTwoBit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def largePowerTwoBit (n : ℕ) : ℕ := by
  classical
  exact if IsLargePowerTwo n then 1 else 0
/-- Rational base coefficients before adding zero-valued sparse carries. Local copy of Erdos249257.TotientParityCoboundaryCountermodel.parityBaseWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def parityBaseWeight : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | _ => 4
/-- The parity countermodel. Natural subtraction is exact because every negative spike lands on a base coefficient `4`. Local copy of Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def parityCoboundaryWeight (n : ℕ) : ℕ :=
  parityBaseWeight n + 2 * largePowerTwoBit n -
    4 * largePowerTwoBit (n - 1)
end PalomarCorpus.E249.PaperStatementsAG
