/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.DiagonalFreshLossBridge
import Erdos249257.FullTargetPrimeAdjunctionNoGo
import Erdos249257.GcdMomentCalculus
import Erdos249257.MersenneShadowCyclotomicNoncollapse
import Erdos249257.RadicalMobiusShadow
import Erdos249257.ResidualGaugeObstruction
import ErdosProblems.Erdos249.PaperCompleteR20.MobiusSquareReduction
import ErdosProblems.Erdos249.PaperCompleteR21.PrimeJumpWitnessAndMersenneChannels
import ErdosProblems.Erdos249.PaperCompleteR21.ScalarLocalisationAndInversePhaseGauge
import ErdosProblems.Erdos249.PaperCompleteR21.SternBrocotStoppingRecursion
import ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeStaircaseConditions
import Solutions.PalomarCorpus.E249_08.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsAY
export PalomarCorpus.E249_08.Shared (cylinderMass)

noncomputable def actualCenteredLift (A M : ℤ) : ℤ :=
  let r := A % M
  if r ≤ M / 2 then r else r - M

noncomputable def totientSeries : ℝ :=
  ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n

noncomputable def lcmHeight (t : ℕ) : ℕ :=
  (Finset.Icc 1 t).lcm (fun n ↦ n)

noncomputable def upperHalfPrimes (t : ℕ) : Finset ℕ :=
  (Finset.Ioc (t / 2) t).filter Nat.Prime

noncomputable def mersenne (n : ℕ) : ℕ := 2 ^ n - 1

noncomputable def mobiusNumerator (r : ℕ) : ℤ :=
  ∑ s ∈ r.primeFactors.powerset,
    (-1 : ℤ) ^ s.card *
      ((r / s.prod id : ℕ) : ℤ) *
        (((mersenne r) / (mersenne (s.prod id)) : ℕ) : ℤ)

noncomputable def baseMobiusShadow (r : ℕ) : ℚ :=
  Rat.divInt (mobiusNumerator r) (mersenne r : ℤ)

noncomputable def squarefreeKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

noncomputable def numericMobiusShadow (H : ℕ) : ℚ :=
  baseMobiusShadow (squarefreeKernel H) / (squarefreeKernel H : ℚ)

noncomputable def phasePowerMatrix
    {d : ℕ} (e : Fin d → ℕ) (z : Fin d → ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j ↦ z j ^ e i

theorem irrational_totient_iff_mobius_square :
    Irrational totientSeries ↔
      Irrational (∑' d : ℕ+, (ArithmeticFunction.moebius (d : ℕ) : ℝ) /
        ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2) := @ErdosProblems.Erdos249.PaperCompleteR20.irrational_totient_iff_mobius_square

theorem mobius_square_reduction :
    totientSeries = (1 : ℝ) / 2 +
      ∑' d : ℕ+, (ArithmeticFunction.moebius (d : ℕ) : ℝ) /
        ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2 := @ErdosProblems.Erdos249.PaperCompleteR20.mobius_square_reduction

theorem centeredLift_range {A M : ℤ} (hM : 0 < M) :
    -M < 2 * actualCenteredLift A M ∧ 2 * actualCenteredLift A M ≤ M := @ErdosProblems.Erdos249.PaperCompleteR21.centeredLift_range A M hM

theorem cylinderMass_eq_divisibility_mass_mul (a b : ℕ+) :
    cylinderMass a b
      = (∑' k : ℕ, if 0 < k ∧ (a : ℕ) ∣ k then ((1 : ℝ) / 2) ^ k else 0)
        * (∑' k : ℕ, if 0 < k ∧ (b : ℕ) ∣ k then ((1 : ℝ) / 2) ^ k else 0) := @ErdosProblems.Erdos249.PaperCompleteR21.cylinderMass_eq_divisibility_mass_mul a b

theorem cylinder_mediant_split (a b : ℕ+) :
    cylinderMass a b
      = 1 / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
        + cylinderMass (a + b) b + cylinderMass a (a + b) := @ErdosProblems.Erdos249.PaperCompleteR21.cylinder_mediant_split a b

theorem cylinder_root_values :
    cylinderMass 1 1 = 1 ∧
      1 / ((2 : ℝ) ^ (((1 : ℕ+) : ℕ) + ((1 : ℕ+) : ℕ)) - 1) = 1 / 3 ∧
      cylinderMass (1 + 1) 1 = 1 / 3 ∧ cylinderMass 1 (1 + 1) = 1 / 3 := @ErdosProblems.Erdos249.PaperCompleteR21.cylinder_root_values

theorem exists_upperHalf_channel_paper {t : ℕ} (ht : 5 ≤ t) :
    ∃ p ∈ upperHalfPrimes t,
      2 ^ (t / 2) ≤ mersenne p ∧
      mersenne p < 2 ^ t ∧
      mersenne p ∣
        ((lcmHeight t : ℚ) *
          numericMobiusShadow (lcmHeight t)).den := @ErdosProblems.Erdos249.PaperCompleteR21.exists_upperHalf_channel_paper t ht

theorem inversePhaseGauge_locks_row_and_preserves_minor
    {d : ℕ} (_hd : 1 ≤ d) (e : Fin d → ℕ) (z : Fin d → ℂ)
    (hz : ∀ j, z j ≠ 0) (i₀ : Fin d) (hi₀ : e i₀ = 1) :
    (∀ j, (phasePowerMatrix e z * Matrix.diagonal (fun j => (z j)⁻¹)) i₀ j = 1) ∧
      Matrix.det (phasePowerMatrix e z * Matrix.diagonal (fun j => (z j)⁻¹))
          = Matrix.det (phasePowerMatrix e z) * ∏ j, (z j)⁻¹ ∧
      (Matrix.det (phasePowerMatrix e z) ≠ 0 →
        Matrix.det (phasePowerMatrix e z * Matrix.diagonal (fun j => (z j)⁻¹)) ≠ 0) ∧
      ((∀ j, ‖z j‖ = 1) →
        ‖Matrix.det (phasePowerMatrix e z * Matrix.diagonal (fun j => (z j)⁻¹))‖
          = ‖Matrix.det (phasePowerMatrix e z)‖) := by
  apply ErdosProblems.Erdos249.PaperCompleteR21.inversePhaseGauge_locks_row_and_preserves_minor <;> assumption

theorem normalised_split_probabilities (a b : ℕ+) :
    (1 / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)) / cylinderMass a b
        = ((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1)
          / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
      ∧ cylinderMass (a + b) b / cylinderMass a b
        = ((2 : ℝ) ^ (a : ℕ) - 1) / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
      ∧ cylinderMass a (a + b) / cylinderMass a b
        = ((2 : ℝ) ^ (b : ℕ) - 1) / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1) := @ErdosProblems.Erdos249.PaperCompleteR21.normalised_split_probabilities a b

theorem upperHalfMersenneProduct_between_bounds {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤ ∏ p ∈ upperHalfPrimes t, mersenne p ∧
      (∏ p ∈ upperHalfPrimes t, mersenne p) ≤
        ((lcmHeight t : ℚ) *
          numericMobiusShadow (lcmHeight t)).den := @ErdosProblems.Erdos249.PaperCompleteR21.upperHalfMersenneProduct_between_bounds t ht

theorem upperHalfPrimes_member_bounds {t p : ℕ} (hp : p ∈ upperHalfPrimes t) :
    t / 2 ≤ p - 1 ∧ p ≤ t := @ErdosProblems.Erdos249.PaperCompleteR21.upperHalfPrimes_member_bounds t p hp

theorem upperHalfPrimes_nonempty_paper {t : ℕ} (ht : 2 ≤ t) :
    (upperHalfPrimes t).Nonempty := @ErdosProblems.Erdos249.PaperCompleteR21.upperHalfPrimes_nonempty_paper t ht

theorem upperHalfPrimes_spec (t : ℕ) :
    upperHalfPrimes t = (Finset.Ioc (t / 2) t).filter Nat.Prime := @ErdosProblems.Erdos249.PaperCompleteR21.upperHalfPrimes_spec t

end PalomarCorpus.E249.PaperStatementsAY
