/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.BooleanMobiusCarry
import Erdos249257.CertificateKernel
import Erdos249257.GenericTailOrbitRigidity

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.BooleanMobiusCarry`, `Erdos249257.CertificateKernel`,
`Erdos249257.GenericTailOrbitRigidity`.
-/

open ArithmeticFunction
open Filter
open Set
open scoped ArithmeticFunction.Moebius
open Topology

namespace Erdos249257.ExternalVerification257PaperStatementsAU

noncomputable def HasRationalValue (x : ℝ) : Prop :=
  ∃ p : ℤ, ∃ v : ℕ, 0 < v ∧ x = (p : ℝ) / (v : ℝ)

noncomputable def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)

noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)

noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

noncomputable def positiveSupportBit (A : Set ℕ) (n : ℕ) : ℤ :=
  letI := Classical.propDecidable (0 < n ∧ n ∈ A)
  if 0 < n ∧ n ∈ A then 1 else 0

noncomputable def positiveSupportBitAF (A : Set ℕ) : ArithmeticFunction ℤ :=
  ⟨positiveSupportBit A, by simp [positiveSupportBit]⟩

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

noncomputable def supportCoeffAF (A : Set ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n ↦ (supportCoeff A n : ℤ), by simp [supportCoeff]⟩

theorem binaryCoeffTail_supportCoeff_le_two_sqrt_add_four
    (A : Set ℕ) (N : ℕ) :
    binaryCoeffTail (supportCoeff A) N ≤
      2 * Real.sqrt (N : ℝ) + 4 := @Erdos249257.binaryCoeffTail_supportCoeff_le_two_sqrt_add_four A N

theorem erdosSupportSeries_rational_iff_exists_temperedCarry (A : Set ℕ) :
    HasRationalValue (erdosSupportSeries 2 A) ↔
      ∃ q : ℕ, 0 < q ∧ ∃ U : ℕ → ℤ,
        IsTemperedBinaryOrbit (supportCoeff A) q U := @Erdos249257.erdosSupportSeries_rational_iff_exists_temperedCarry A

theorem erdosSupportSeries_two_eq_binaryCoeffSeries (A : Set ℕ) :
    erdosSupportSeries 2 A = binaryCoeffSeries (supportCoeff A) := @Erdos249257.erdosSupportSeries_two_eq_binaryCoeffSeries A

theorem mobius_supportCoeff_boolean (A : Set ℕ) (n : ℕ) :
    (ArithmeticFunction.moebius * supportCoeffAF A) n = 0 ∨
      (ArithmeticFunction.moebius * supportCoeffAF A) n = 1 := @Erdos249257.mobius_supportCoeff_boolean A n

theorem mobius_supportCoeff_eq_one_iff (A : Set ℕ) {n : ℕ} (hn : 0 < n) :
    (ArithmeticFunction.moebius * supportCoeffAF A) n = 1 ↔ n ∈ A := @Erdos249257.mobius_supportCoeff_eq_one_iff A n hn

theorem moebius_mul_supportCoeffAF (A : Set ℕ) :
    ArithmeticFunction.moebius * supportCoeffAF A = positiveSupportBitAF A := @Erdos249257.moebius_mul_supportCoeffAF A

end Erdos249257.ExternalVerification257PaperStatementsAU
