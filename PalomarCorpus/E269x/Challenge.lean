/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #269, band x

Erdős problem #269 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E269` under the Challenge size ceiling; it does not replace it.
-/

open Polynomial
open scoped BigOperators

namespace PalomarCorpus.E269.PaperStatementsX
open Polynomial
open scoped BigOperators
/-- The Hecke--Mahler series `F_θ(β,α) = ∑_{n≥1} ∑_{k=1}^{⌊nθ⌋} β^n α^k`. The outer index runs over all `n ≥ 0`; the inner sum is empty at `n = 0`. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.heckeMahlerSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def heckeMahlerSeries (θ β α : ℝ) : ℝ :=
  ∑' n : ℕ, ∑ k ∈ Finset.Icc 1 ⌊(n : ℝ) * θ⌋₊, β ^ n * α ^ k
/-- Bugeaud and Laurent, Theorem 1.1, in the case `ρ = 0` due to Loxton and van der Poorten, Theorem 8, p. 40: the Hecke--Mahler series takes transcendental values at nonzero algebraic arguments inside the stated region. This is the one external input of the two-prime theorem. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.BugeaudLaurentTranscendence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def BugeaudLaurentTranscendence : Prop :=
  ∀ θ β α : ℝ, Irrational θ → 0 < θ → θ < 1 →
    IsAlgebraic ℚ β → IsAlgebraic ℚ α → β ≠ 0 → α ≠ 0 →
    |β| < 1 → |β| * |α| ^ θ < 1 →
    Transcendental ℚ (heckeMahlerSeries θ β α)
/-- The positive `{p,q}`-smooth integers. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.SmoothSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SmoothSet (p q : ℕ) : Set ℕ := {n : ℕ | 0 < n ∧ ∃ i j : ℕ, n = p ^ i * q ^ j}
/-- The exponent pairs of the actual `{p,q}`-smooth prefix up to `x`. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.smoothPrefixPairs, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def smoothPrefixPairs (p q x : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.range (Nat.log p x + 1)) ×ˢ (Finset.range (Nat.log q x + 1))).filter
    fun e => p ^ e.1 * q ^ e.2 ≤ x)
/-- The literal running least common multiple of the `{p,q}`-smooth numbers `≤ x`. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.runningLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def runningLcm (p q x : ℕ) : ℕ :=
  (smoothPrefixPairs p q x).lcm fun e => p ^ e.1 * q ^ e.2
/-- The distinct values taken by the running LCM on the positive smooth integers. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.runningLcmValues, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def runningLcmValues (p q : ℕ) : Set ℕ := (runningLcm p q) '' SmoothSet p q
/-- `D_{p,q}`: each distinct running LCM counted once. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.distinctSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def distinctSum (p q : ℕ) : ℝ :=
  ∑' H : runningLcmValues p q, (((H : ℕ) : ℝ))⁻¹
/-- `R_{p,q}`: the reciprocal running LCM summed at every positive `{p,q}`-smooth integer. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.repeatedSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def repeatedSum (p q : ℕ) : ℝ :=
  ∑' n : SmoothSet p q, ((runningLcm p q (n : ℕ) : ℝ))⁻¹
/-- States long269:res:lead-two-prime, res:two-prime-transcendence from the long record and the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR21.two_prime_sums_transcendental in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_prime_sums_transcendental (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Transcendental ℚ (distinctSum p q) ∧ Transcendental ℚ (repeatedSum p q) := by
  sorry
/-- States long269:res:lead-two-prime from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR21.two_prime_transcendence in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_prime_transcendence (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Transcendental ℚ (repeatedSum p q) ∧ Transcendental ℚ (distinctSum p q) := by
  sorry
end PalomarCorpus.E269.PaperStatementsX
