/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #68, band c

Erdős problem #68 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E68` under the Challenge size ceiling; it does not replace it.
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
/-- States long68:res:bandbreakpoint, res:bandbreakpoint from the long record and the short record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.supported_breakpoint_escape in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem supported_breakpoint_escape (f : ℕ →₀ ℤ) (d : ℕ)
    (hlo : ∀ n ∈ f.support, d ≤ n)
    (hz : channelNumerator f d = 0) (hm : factorialMoment f ≠ 0) :
    ∃ n ∈ f.support, 2 * d ≤ n := by
  sorry
/-- States long68:res:bandbreakpoint, res:bandbreakpoint from the long record and the short record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.supported_first_band_cancellation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem supported_first_band_cancellation (f : ℕ →₀ ℤ) (d : ℕ)
    (hlo : ∀ n ∈ f.support, d ≤ n)
    (hhi : ∀ n ∈ f.support, n < 2 * d)
    (hz : channelNumerator f d = 0) : factorialMoment f = 0 := by
  sorry
/-- States long68:res:normalform from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.supported_integral_normal_form in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem supported_integral_normal_form (f : ℕ →₀ ℤ) {d : ℕ} (hd : 2 ≤ d) :
    ∃ k : ℤ, channelNumerator f d = factorialMoment f + ((d.factorial : ℤ) - 1) * k := by
  sorry
/-- States long68:res:bandbreakpoint, res:bandbreakpoint from the long record and the short record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.supported_quotient_band in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem supported_quotient_band (f : ℕ →₀ ℤ) (d k : ℕ)
    (hlo : ∀ n ∈ f.support, k * d ≤ n)
    (hhi : ∀ n ∈ f.support, n < (k + 1) * d) :
    factorialMoment f = (d.factorial : ℤ) ^ k * channelNumerator f d := by
  sorry
/-- States long68:res:shift-family from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.uniform_family_boundary in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem uniform_family_boundary {t : ℤ} (ht : -1 ≤ t) :
    (¬ Irrational (shiftGapSeries t) ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        (m : ℤ) ∣ ⌈(t : ℝ) * (m.factorial : ℝ) * shiftCompanionConstant t⌉ - 2) ∧
    (Irrational (shiftGapSeries t) ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬ (m : ℤ) ∣ ⌈(t : ℝ) * (m.factorial : ℝ) * shiftCompanionConstant t⌉ - 2) := by
  sorry
/-- States long68:res:shift-family from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.uniform_family_members in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem uniform_family_members :
    shiftGapSeries (-1) = factorialGapSeries ∧
    shiftGapSeries 0 = Real.exp 1 - 2 ∧
    (∀ m : ℕ, ⌈(0 : ℝ) * (m.factorial : ℝ) * shiftCompanionConstant 0⌉ = 0) ∧
    (∀ m : ℕ, 3 ≤ m → ¬ (m : ℤ) ∣ (0 : ℤ) - 2) ∧
    Irrational (Real.exp 1) := by
  sorry
end PalomarCorpus.E68.PaperStatementsC
