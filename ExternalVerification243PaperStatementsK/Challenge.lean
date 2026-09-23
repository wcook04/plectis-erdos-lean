/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #243

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos243.FiniteHorizonResidue`,
`ErdosProblems.Erdos243.PaperCompleteR21.ForcedOrbitResidueHorizon`,
`ErdosProblems.Erdos243.PaperCompleteR21.ProtectedEpochBarrierCount`,
`ErdosProblems.Erdos243.PrimitiveRecordBarrier`.
-/

namespace Erdos249257.ExternalVerification243PaperStatementsK

noncomputable def forcedNumerator (n : ℕ) (a : ℤ) : ℤ :=
  (n + 1 : ℤ) * a ^ 2 - (n + 2 : ℤ) * a + (n + 3 : ℤ)

noncomputable def ForcedSurvives : ℕ → ℕ → ℤ → Prop
  | 0, _, _ => True
  | remaining + 1, index, a =>
      let d : ℤ := index + 2
      d ∣ forcedNumerator index a ∧
        ForcedSurvives remaining (index + 1)
          (forcedNumerator index a / d)

noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

/-- States long243:res:epochenergy from the long record for Erdős problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR21.epoch_energy_named_crossing_set in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem epoch_energy_named_crossing_set
    (a u v w hc : ℕ → ℕ) (p l s τ : ℕ) (J : Finset ℕ)
    (hp : p.Prime)
    (hp3 : 3 ≤ p)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hcentre : ∀ n, s ≤ n → 2 * ((u n : ℤ) - (w n : ℤ)).natAbs < u n)
    (hprot : p ^ l ∣ v s)
    (hQ : 16 ≤ p ^ l)
    (hRs : 4 * runningMax u s < p * p ^ l)
    (hsτ : s < τ)
    (hτ : p * p ^ l ≤ 2 * u τ)
    (hτfirst : ∀ n, s < n → n < τ → 2 * u n < p * p ^ l)
    (hJ : ∀ n, n ∈ J ↔ (s ≤ n ∧ n < τ ∧ ∃ b : ℕ, Odd b ∧ p ∣ b ∧
      p * p ^ l < 4 * b ∧ 2 * b ≤ p * p ^ l ∧
      b ≤ u (n + 1) ∧ ∀ j, s ≤ j → j < n → u (j + 1) < b)) :
    (∀ n ∈ J, runningMax u n < u (n + 1) ∧ hc n = 1 ∧ u n + 3 ≤ u (n + 1)) ∧
      p * p ^ l ≤ (8 * p + 8) * J.card
        + 4 * ∑ n ∈ J, (u (n + 1) - u n - 2) + 8 * p := by
  sorry

/-- States long243:res:residue from the long record for Erdős problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR21.forcedOrbit_survives_iff_of_factorial_modEq in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem forcedOrbit_survives_iff_of_factorial_modEq
    (h : ℕ) (a b : ℤ)
    (hab : a ≡ b [ZMOD ((h + 1).factorial : ℤ)]) :
    ForcedSurvives h 0 a ↔ ForcedSurvives h 0 b := by
  sorry

/-- States long243:res:residue, res:residue from the long record and the short record for Erdős
problem #243. Transported from ErdosProblems.Erdos243.forcedSurvives_iff_of_modEq_factorial
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem forcedSurvives_iff_of_modEq_factorial
    {h : ℕ} {a b : ℤ}
    (hab : a ≡ b [ZMOD ((h + 1).factorial : ℤ)]) :
    ForcedSurvives h 0 a ↔ ForcedSurvives h 0 b := by
  sorry

end Erdos249257.ExternalVerification243PaperStatementsK
