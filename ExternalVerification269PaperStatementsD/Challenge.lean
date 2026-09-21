/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #269

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos269.PaperCompleteR20.RealCutoffs`,
`ErdosProblems.Erdos269.RealCutoffR10`, `ErdosProblems.Erdos269.ThreePrimeRunningLcm`.
-/

open Finset
open scoped BigOperators

namespace Erdos249257.ExternalVerification269PaperStatementsD

noncomputable def SameThreePrimeRealLogCell (p q r : ℕ) (x y : ℝ) : Prop :=
  ⌊Real.logb p x⌋₊ = ⌊Real.logb p y⌋₊ ∧
    ⌊Real.logb q x⌋₊ = ⌊Real.logb q y⌋₊ ∧
      ⌊Real.logb r x⌋₊ = ⌊Real.logb r y⌋₊

noncomputable def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k

noncomputable def realSmoothExponentShell
    (p q r : ℕ) (lo hi : ℝ) (hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (hp + 1)).product
      ((range (hq + 1)).product (range (hr + 1)))).filter
    fun e => lo ≤ (smooth3Val p q r e.1 e.2.1 e.2.2 : ℝ) ∧
      (smooth3Val p q r e.1 e.2.1 e.2.2 : ℝ) < hi

noncomputable def realPrefixExponents (p q r : ℕ) (x : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (⌊Real.logb p x⌋₊ + 1)).product
    ((Finset.range (⌊Real.logb q x⌋₊ + 1)).product
      (Finset.range (⌊Real.logb r x⌋₊ + 1)))).filter
        (fun e => (smooth3Val p q r e.1 e.2.1 e.2.2 : ℝ) ≤ x)

noncomputable def realPrefixLcm (p q r : ℕ) (x : ℝ) : ℕ :=
  (realPrefixExponents p q r x).lcm
    (fun e => smooth3Val p q r e.1 e.2.1 e.2.2)

noncomputable def realThreePrimeHeight (p q r : ℕ) (x : ℝ) : ℕ :=
  p ^ ⌊Real.logb p x⌋₊ * q ^ ⌊Real.logb q x⌋₊ * r ^ ⌊Real.logb r x⌋₊

noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x

noncomputable def threePrimeKernelQ (p q r i j k : ℕ) : ℚ :=
  (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹

/-- States long269:res:cell, res:cell from the long record and the short record for Erdős
problem #269. Transported from
ErdosProblems.Erdos269.PaperCompleteR20.realPrefixLcm_eq_of_sameLogCell in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem realPrefixLcm_eq_of_sameLogCell
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hcell : SameThreePrimeRealLogCell p q r x y) :
    realPrefixLcm p q r x = realPrefixLcm p q r y := by
  sorry

/-- States long269:res:cell, res:cell from the long record and the short record for Erdős
problem #269. Transported from
ErdosProblems.Erdos269.PaperCompleteR20.realPrefixLcm_jump_first in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem realPrefixLcm_jump_first
    {p q r : ℕ} (pPrime : p.Prime) (qPrime : q.Prime) (rPrime : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : ⌊Real.logb p y⌋₊ = ⌊Real.logb p x⌋₊ + 1)
    (hq : ⌊Real.logb q y⌋₊ = ⌊Real.logb q x⌋₊)
    (hr : ⌊Real.logb r y⌋₊ = ⌊Real.logb r x⌋₊) :
    realPrefixLcm p q r y = p * realPrefixLcm p q r x := by
  sorry

/-- States long269:res:cell, res:cell from the long record and the short record for Erdős
problem #269. Transported from
ErdosProblems.Erdos269.PaperCompleteR20.realPrefixLcm_jump_second in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem realPrefixLcm_jump_second
    {p q r : ℕ} (pPrime : p.Prime) (qPrime : q.Prime) (rPrime : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : ⌊Real.logb p y⌋₊ = ⌊Real.logb p x⌋₊)
    (hq : ⌊Real.logb q y⌋₊ = ⌊Real.logb q x⌋₊ + 1)
    (hr : ⌊Real.logb r y⌋₊ = ⌊Real.logb r x⌋₊) :
    realPrefixLcm p q r y = q * realPrefixLcm p q r x := by
  sorry

/-- States long269:res:cell, res:cell from the long record and the short record for Erdős
problem #269. Transported from
ErdosProblems.Erdos269.PaperCompleteR20.realPrefixLcm_jump_third in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem realPrefixLcm_jump_third
    {p q r : ℕ} (pPrime : p.Prime) (qPrime : q.Prime) (rPrime : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : ⌊Real.logb p y⌋₊ = ⌊Real.logb p x⌋₊)
    (hq : ⌊Real.logb q y⌋₊ = ⌊Real.logb q x⌋₊)
    (hr : ⌊Real.logb r y⌋₊ = ⌊Real.logb r x⌋₊ + 1) :
    realPrefixLcm p q r y = r * realPrefixLcm p q r x := by
  sorry

/-- States long269:res:drop, long269:res:shell from the long record for Erdős problem #269.
Transported from ErdosProblems.Erdos269.PaperCompleteR20.realSmoothExponentShell_bounds in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem realSmoothExponentShell_bounds
    {p q r hp hq hr j : ℕ} {lo hi : ℝ}
    (hpPos : 0 < p) (hrPos : 0 < r) :
    (hi ≤ (r : ℝ) * lo →
      (realSmoothExponentShell p q r lo hi hp hq hr).card ≤
        (hp + 1) * (hq + 1)) ∧
    (hi ≤ (p : ℝ) * lo →
      (realSmoothExponentShell p q r lo hi hp hq hr).card ≤
        (hq + 1) * (hr + 1)) ∧
    (hi ≤ (r : ℝ) * lo → hp ≤ hq → hq ≤ hr → hp + hq + hr = j →
      9 * (realSmoothExponentShell p q r lo hi hp hq hr).card ≤
        (j + 3) ^ 2) := by
  sorry

/-- States long269:res:lcm, res:lcm from the long record and the short record for Erdős problem
#269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.running_lcm_real_cutoff_exact
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem running_lcm_real_cutoff_exact {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x : ℝ} (hx : 1 ≤ x) :
    realPrefixLcm p q r x = realThreePrimeHeight p q r x := by
  sorry

/-- States long269:res:cell from the long record for Erdős problem #269. Transported from
ErdosProblems.Erdos269.PaperCompleteR20.threePrimeKernelQ_eq_of_sameRealLogCell in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem threePrimeKernelQ_eq_of_sameRealLogCell
    {p q r i j k i' j' k' : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hcell : SameThreePrimeRealLogCell p q r
      (smooth3Val p q r i j k : ℝ) (smooth3Val p q r i' j' k' : ℝ)) :
    threePrimeKernelQ p q r i j k =
      threePrimeKernelQ p q r i' j' k' := by
  sorry

end Erdos249257.ExternalVerification269PaperStatementsD
