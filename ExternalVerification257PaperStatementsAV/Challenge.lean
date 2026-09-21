/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.AllBaseReciprocalSupportIrrationality`, `Erdos249257.CertificateKernel`,
`Erdos249257.GenericTailOrbitRigidity`, `Erdos249257.RationalSupportCarrySkeleton`.
-/

open ArithmeticFunction
open Filter
open Set
open Topology

namespace Erdos249257.ExternalVerification257PaperStatementsAV

noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

noncomputable def reciprocalSupportTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a

noncomputable def reciprocalMass (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, reciprocalSupportTerm A a

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

/-- States record:257rig-i2 from the long record for Erdős problem #257. Transported from
Erdos249257.dyadic_support_fraction_reciprocalMass_diverges_or_gt_one in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadic_support_fraction_reciprocalMass_diverges_or_gt_one
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c : ℕ)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ)) :
    ¬ Summable (reciprocalSupportTerm A) ∨ 1 < reciprocalMass A := by
  sorry

/-- States record:257rig-i3 from the long record for Erdős problem #257. Transported from
Erdos249257.exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    ∃ u : ℕ → ℕ,
      (∀ n : ℕ, (u n : ℝ) =
        (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + n)) ∧
      (∀ n : ℕ, 0 < u n) ∧
      (∀ n : ℕ, u (n + 1) +
        v * supportCoeff A (c + n + 1) = 2 * u n) ∧
      (∀ n : ℕ, u n ≡ p.toNat * 2 ^ n [MOD v]) ∧
      (∀ B : ℕ, ∃ n : ℕ, B < u n) := by
  sorry

/-- States res:reciprocal-support from the short record for Erdős problem #257. Transported from
Erdos249257.irrational_erdosSupportSeries_of_summable_reciprocal in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_erdosSupportSeries_of_summable_reciprocal
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hsum : Summable (reciprocalSupportTerm A)) :
    Irrational (erdosSupportSeries b A) := by
  sorry

/-- States record:257rig-i3 from the long record for Erdős problem #257. Transported from
Erdos249257.one_add_mul_card_le_two_mul_shifted_state in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem one_add_mul_card_le_two_mul_shifted_state
    (A : Set ℕ) (F : Finset ℕ) (c v L : ℕ) (u : ℕ → ℕ)
    (hcL : c < L) (hpos : ∀ n : ℕ, 0 < u n)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n)
    (hFA : ∀ a ∈ F, a ∈ A) (hFdvd : ∀ a ∈ F, a ∣ L) :
    1 + v * F.card ≤ 2 * u (L - c - 1) := by
  sorry

/-- States record:257rig-i2 from the long record for Erdős problem #257. Transported from
Erdos249257.one_lt_reciprocalMass_of_dyadic_support_fraction_of_two_pos_mem in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem one_lt_reciprocalMass_of_dyadic_support_fraction_of_two_pos_mem
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A))
    (p : ℤ) (c : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (haA : a ∈ A) (hbA : b ∈ A)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ)) :
    1 < reciprocalMass A := by
  sorry

/-- States record:257rig-i3 from the long record for Erdős problem #257. Transported from
Erdos249257.shifted_state_unbounded_of_infinite_support in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem shifted_state_unbounded_of_infinite_support
    (A : Set ℕ) (hAinf : A.Infinite) (c v : ℕ) (hv : 0 < v)
    (u : ℕ → ℕ) (hpos : ∀ n : ℕ, 0 < u n)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n) :
    ∀ B : ℕ, ∃ n : ℕ, B < u n := by
  sorry

end Erdos249257.ExternalVerification257PaperStatementsAV
