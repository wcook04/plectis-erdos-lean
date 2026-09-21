/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1049, band b

Erdős problem #1049 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1049` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators

namespace PalomarCorpus.E1049.PaperStatementsB
open scoped BigOperators
/-- Local copy of ErdosProblems.Erdos1049.AllRow.S, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev S := PowerSeries ℤ
/-- Equality of all coefficients strictly below `D`. Local copy of ErdosProblems.Erdos1049.AllRow.Agree, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Agree (D : ℕ) (f g : S) : Prop :=
  ∀ d, d < D → PowerSeries.coeff d f = PowerSeries.coeff d g
/-- A finite ratio with constant term one in the state variable. Local copy of ErdosProblems.Erdos1049.AllRow.finiteRatio, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def finiteRatio (a : ℕ → S) (K n : ℕ) : S :=
  1 + ∑ s ∈ Finset.range K,
    a (s + 1) * PowerSeries.X ^ ((n + 1) * (s + 1))
/-- Row exponent in a form compatible with the canonical row proposition. Local copy of ErdosProblems.Erdos1049.AllRow.rowExponent, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rowExponent (j l : ℕ) : ℕ := j * (j + 1) / 2 + j * l
/-- The finite arithmetic core of a coordinatewise rational-base corridor. `digit` abstracts the final divisor coefficient that is individually cleared. Local copy of ErdosProblems.Erdos1049.CoordinatewiseCorridor, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CoordinatewiseCorridor
    (a b N K Q digit : ℕ) : Prop :=
  0 < a ∧ 0 < Q ∧ 0 < digit ∧ digit ≤ N + K ∧
    a ^ K ∣ Q * digit ∧
    Q * b ^ (N + K + 1) < a ^ (K + 1)
/-- `H(q^{n+1}) = 1 + ∑_{s ≥ 1} a_s(q) q^{(n+1)s}`, the untruncated ratio. Each coefficient is the corresponding coefficient of a long enough truncation, which is exactly what the infinite sum means: the term of index `s` has order at least `s + 1`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.paperRatio, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperRatio (a : ℕ → S) (n : ℕ) : S :=
  PowerSeries.mk fun d => PowerSeries.coeff d (finiteRatio a (d + 1) n)
/-- `H̄ = H mod q`, an ordinary power series in `X` over `ℤ`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.paperReducedSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperReducedSeries (a : ℕ → S) : PowerSeries ℤ :=
  PowerSeries.mk fun s => if s = 0 then 1 else PowerSeries.constantCoeff (a s)
/-- `h_r = [X^r] H̄(X)^{-1}`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.paperReciprocal, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperReciprocal (a : ℕ → S) (r : ℕ) : ℤ :=
  PowerSeries.coeff r (PowerSeries.invOfUnit (paperReducedSeries a) 1)
/-- States long1049:res:allrowinitial from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.paperE_eq_rowExponent in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperE_eq_rowExponent (m j : ℕ) (hjm : j ≤ m) :
    m * j - j * (j - 1) / 2 = rowExponent j (m - j) := by
  sorry
/-- States long1049:res:allrowinitial from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.paperRatio_agree in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperRatio_agree (a : ℕ → S) (n D K : ℕ) (hDK : D ≤ K) :
    Agree D (paperRatio a n) (finiteRatio a K n) := by
  sorry
/-- States long1049:res:allrowinitial from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.paperReciprocal_rec in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperReciprocal_rec (a : ℕ → S) (i : ℕ) :
    paperReciprocal a (i + 1) =
      -(∑ s ∈ Finset.range (i + 1),
          PowerSeries.constantCoeff (a (s + 1)) * paperReciprocal a (i - s)) := by
  sorry
/-- States long1049:res:allrowinitial from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.paperReciprocal_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperReciprocal_zero (a : ℕ → S) : paperReciprocal a 0 = 1 := by
  sorry
/-- States long1049:res:corridorbound from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.coordinatewiseCorridor_implies_pow_lt_linear in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem coordinatewiseCorridor_implies_pow_lt_linear
    {a b N K Q digit : ℕ}
    (h : CoordinatewiseCorridor a b N K Q digit) :
    b ^ (N + K + 1) < a * (N + K) := by
  sorry
/-- States long1049:res:sevenhalves, res:sevenhalves from the long record and the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.sevenHalves_archimedean_height_condition in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sevenHalves_archimedean_height_condition :
    Real.log 7 / Real.log ((7 : ℝ) / 2) <
      ((1 : ℝ) / 2 + 1 / Real.pi ^ 2)⁻¹ := by
  sorry
/-- States long1049:res:exp from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.three_mul_lt_two_pow_succ in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem three_mul_lt_two_pow_succ {x : ℕ} (hx : 2 ≤ x) :
    3 * x < 2 ^ (x + 1) := by
  sorry
end PalomarCorpus.E1049.PaperStatementsB
