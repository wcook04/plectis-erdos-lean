/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E68c

Every non-theorem declaration of `PalomarCorpus/E68c/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E68.PaperStatementsC
open scoped BigOperators
/-- One summand of the universal factorial-gap tail beyond `D`. Local copy of Erdos68.factorialGapTailTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapTailTerm (D d : ℕ) : ℝ :=
  if D < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)
  else 0
/-- The universal factorial-gap tail beyond `D`. Local copy of Erdos68.factorialGapTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapTail (D : ℕ) : ℝ :=
  ∑' d : ℕ, factorialGapTailTerm D d
/-- The original Erdős #68 series, expressed through the universal factorial-gap tail beginning after `1`. Local copy of Erdos68.factorialGapSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapSeries : ℝ :=
  factorialGapTail 1
/-- Integral weight of index `i` in the divisor channel `d`. Local copy of ErdosProblems.Erdos68.channelWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def channelWeight (i d : ℕ) : ℕ :=
  i.factorial / (d.factorial ^ (i / d))
/-- Finite-support integer numerator in channel `d`. Local copy of ErdosProblems.Erdos68.channelNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def channelNumerator (lam : ℕ →₀ ℤ) (d : ℕ) : ℤ :=
  lam.sum fun i z => z * (channelWeight i d : ℤ)
/-- The factorial moment of a finite-support coefficient vector. Local copy of ErdosProblems.Erdos68.factorialMoment, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialMoment (lam : ℕ →₀ ℤ) : ℤ :=
  lam.sum fun i z => z * (i.factorial : ℤ)
/-- The shifted companion term `1/(n!(n!+t))`, anchored at `n ≥ 2`. Local copy of ErdosProblems.Erdos68.shiftCompanionTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftCompanionTerm (t : ℤ) (n : ℕ) : ℝ :=
  if 2 ≤ n then 1 / ((n.factorial : ℝ) * ((n.factorial : ℝ) + (t : ℝ))) else 0
/-- The shifted companion constant `C_t = ∑_{n≥2} 1/(n!(n!+t))`. Local copy of ErdosProblems.Erdos68.shiftCompanionConstant, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftCompanionConstant (t : ℤ) : ℝ :=
  ∑' n : ℕ, shiftCompanionTerm t n
/-- The shifted factorial-gap term `1/(n!+t)`, anchored at `n ≥ 2`. Local copy of ErdosProblems.Erdos68.shiftGapTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftGapTerm (t : ℤ) (n : ℕ) : ℝ :=
  if 2 ≤ n then 1 / ((n.factorial : ℝ) + (t : ℝ)) else 0
/-- Erdős's shifted series `S_t = ∑_{n≥2} 1/(n!+t)`. Local copy of ErdosProblems.Erdos68.shiftGapSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftGapSeries (t : ℤ) : ℝ :=
  ∑' n : ℕ, shiftGapTerm t n
end PalomarCorpus.E68.PaperStatementsC
