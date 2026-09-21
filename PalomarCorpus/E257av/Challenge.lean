/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band v

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open ArithmeticFunction
open Filter
open Set
open Topology

namespace PalomarCorpus.E257.PaperStatementsAV
open ArithmeticFunction
open Filter
open Set
open Topology
/-- The scaled tail `T_c(N) = ∑_{j≥1} c(N+j)/2^j`. Local copy of Erdos249257.binaryCoeffTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)
/-- **The Erdős #257 support series** `∑_{a ∈ A} 1/(b^a - 1)`, as an indicator series over ℕ. The `a = 0` term is `1/(1-1) = 0` under real division-by-zero conventions, so supports containing `0` contribute nothing spurious. Local copy of Erdos249257.erdosSupportSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- The reciprocal summand of a support, with exponent zero harmlessly normalized to zero by real division. Local copy of Erdos249257.reciprocalSupportTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def reciprocalSupportTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a
/-- The reciprocal mass `ρ(A) = ∑_{a∈A} 1/a`. Local copy of Erdos249257.reciprocalMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def reciprocalMass (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, reciprocalSupportTerm A a
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}` — the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- States record:257rig-i2 from the long record for Erdős problem #257. Transported from Erdos249257.dyadic_support_fraction_reciprocalMass_diverges_or_gt_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadic_support_fraction_reciprocalMass_diverges_or_gt_one
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c : ℕ)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ)) :
    ¬ Summable (reciprocalSupportTerm A) ∨ 1 < reciprocalMass A := by
  sorry
/-- States record:257rig-i3 from the long record for Erdős problem #257. Transported from Erdos249257.exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
/-- States res:reciprocal-support from the short record for Erdős problem #257. Transported from Erdos249257.irrational_erdosSupportSeries_of_summable_reciprocal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_erdosSupportSeries_of_summable_reciprocal
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hsum : Summable (reciprocalSupportTerm A)) :
    Irrational (erdosSupportSeries b A) := by
  sorry
/-- States record:257rig-i3 from the long record for Erdős problem #257. Transported from Erdos249257.one_add_mul_card_le_two_mul_shifted_state in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem one_add_mul_card_le_two_mul_shifted_state
    (A : Set ℕ) (F : Finset ℕ) (c v L : ℕ) (u : ℕ → ℕ)
    (hcL : c < L) (hpos : ∀ n : ℕ, 0 < u n)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n)
    (hFA : ∀ a ∈ F, a ∈ A) (hFdvd : ∀ a ∈ F, a ∣ L) :
    1 + v * F.card ≤ 2 * u (L - c - 1) := by
  sorry
/-- States record:257rig-i2 from the long record for Erdős problem #257. Transported from Erdos249257.one_lt_reciprocalMass_of_dyadic_support_fraction_of_two_pos_mem in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem one_lt_reciprocalMass_of_dyadic_support_fraction_of_two_pos_mem
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A))
    (p : ℤ) (c : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (haA : a ∈ A) (hbA : b ∈ A)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ)) :
    1 < reciprocalMass A := by
  sorry
/-- States record:257rig-i3 from the long record for Erdős problem #257. Transported from Erdos249257.shifted_state_unbounded_of_infinite_support in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem shifted_state_unbounded_of_infinite_support
    (A : Set ℕ) (hAinf : A.Infinite) (c v : ℕ) (hv : 0 < v)
    (u : ℕ → ℕ) (hpos : ∀ n : ℕ, 0 < u n)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n) :
    ∀ B : ℕ, ∃ n : ℕ, B < u n := by
  sorry
end PalomarCorpus.E257.PaperStatementsAV
