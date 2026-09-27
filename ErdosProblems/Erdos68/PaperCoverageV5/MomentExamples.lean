import ErdosProblems.Erdos68.PaperCompleteMomentIdeal
import Mathlib.Tactic

/-!
# Exact depth-four moment ideal and a supported attaining vector

The finite calculations below rewrite the actual isolated-unit recurrence;
they do not assume a table for an unrelated sequence. Complete bodies, UNRUN.
The quadratic horizon (D,p,H)=(4,3,20) proves the infinite tail conclusion.
-/
namespace ErdosProblems.Erdos68.PaperCoverageV5
open ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp

theorem scalar_3 : channelScalar 3 = 0 := by
  exact channelScalar_odd (by decide) (by decide)

theorem scalar_4 : channelScalar 4 = -12 := by
  rw [channelScalar_recurrence (by decide : 2 < 4)]
  rw [show Finset.Ico 2 4 = ({2, 3} : Finset ℕ) from by decide]
  norm_num [channelWeight, channelScalar_two, scalar_3]

theorem scalar_5 : channelScalar 5 = 0 := by
  exact channelScalar_odd (by decide) (by decide)

theorem scalar_6 : channelScalar 6 = -180 := by
  rw [channelScalar_recurrence (by decide : 2 < 6)]
  rw [show Finset.Ico 2 6 = ({2, 3, 4, 5} : Finset ℕ) from by decide]
  norm_num [channelWeight, channelScalar_two, scalar_3, scalar_4, scalar_5]

theorem scalar_7 : channelScalar 7 = 0 := by
  exact channelScalar_odd (by decide) (by decide)

theorem scalar_8 : channelScalar 8 = -4200 := by
  rw [channelScalar_recurrence (by decide : 2 < 8)]
  rw [show Finset.Ico 2 8 = ({2, 3, 4, 5, 6, 7} : Finset ℕ) from by decide]
  norm_num [channelWeight, channelScalar_two, scalar_3, scalar_4, scalar_5, scalar_6, scalar_7]

theorem scalar_9 : channelScalar 9 = 0 := by
  exact channelScalar_odd (by decide) (by decide)

theorem scalar_10 : channelScalar 10 = -226800 := by
  rw [channelScalar_recurrence (by decide : 2 < 10)]
  rw [show Finset.Ico 2 10 = ({2, 3, 4, 5, 6, 7, 8, 9} : Finset ℕ) from by decide]
  norm_num [channelWeight, channelScalar_two, scalar_3, scalar_4, scalar_5, scalar_6, scalar_7, scalar_8, scalar_9]

theorem scalar_11 : channelScalar 11 = 0 := by
  exact channelScalar_odd (by decide) (by decide)

theorem scalar_12 : channelScalar 12 = -14386680 := by
  rw [channelScalar_recurrence (by decide : 2 < 12)]
  rw [show Finset.Ico 2 12 = ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11} : Finset ℕ) from by decide]
  norm_num [channelWeight, channelScalar_two, scalar_3, scalar_4, scalar_5, scalar_6, scalar_7, scalar_8, scalar_9, scalar_10, scalar_11]

theorem scalar_13 : channelScalar 13 = 0 := by
  exact channelScalar_odd (by decide) (by decide)

theorem scalar_14 : channelScalar 14 = -1362160800 := by
  rw [channelScalar_recurrence (by decide : 2 < 14)]
  rw [show Finset.Ico 2 14 = ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} : Finset ℕ) from by decide]
  norm_num [channelWeight, channelScalar_two, scalar_3, scalar_4, scalar_5, scalar_6, scalar_7, scalar_8, scalar_9, scalar_10, scalar_11, scalar_12, scalar_13]

theorem scalar_15 : channelScalar 15 = 0 := by
  exact channelScalar_odd (by decide) (by decide)

theorem scalar_16 : channelScalar 16 = -162648486000 := by
  rw [channelScalar_recurrence (by decide : 2 < 16)]
  rw [show Finset.Ico 2 16 = ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15} : Finset ℕ) from by decide]
  norm_num [channelWeight, channelScalar_two, scalar_3, scalar_4, scalar_5, scalar_6, scalar_7, scalar_8, scalar_9, scalar_10, scalar_11, scalar_12, scalar_13, scalar_14, scalar_15]

theorem scalar_17 : channelScalar 17 = 0 := by
  exact channelScalar_odd (by decide) (by decide)

theorem scalar_18 : channelScalar 18 = -25006184723520 := by
  rw [channelScalar_recurrence (by decide : 2 < 18)]
  rw [show Finset.Ico 2 18 = ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17} : Finset ℕ) from by decide]
  norm_num [channelWeight, channelScalar_two, scalar_3, scalar_4, scalar_5, scalar_6, scalar_7, scalar_8, scalar_9, scalar_10, scalar_11, scalar_12, scalar_13, scalar_14, scalar_15, scalar_16, scalar_17]

theorem scalar_19 : channelScalar 19 = 0 := by
  exact channelScalar_odd (by decide) (by decide)

theorem scalar_20 : channelScalar 20 = -4748053349239200 := by
  rw [channelScalar_recurrence (by decide : 2 < 20)]
  rw [show Finset.Ico 2 20 = ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19} : Finset ℕ) from by decide]
  norm_num [channelWeight, channelScalar_two, scalar_3, scalar_4, scalar_5, scalar_6, scalar_7, scalar_8, scalar_9, scalar_10, scalar_11, scalar_12, scalar_13, scalar_14, scalar_15, scalar_16, scalar_17, scalar_18, scalar_19]

theorem finite_scalar_gcd_four : finiteScalarGcd 4 20 = 60 := by
  unfold finiteScalarGcd
  rw [show Finset.Icc (4 + 1) 20 = ({5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20} : Finset ℕ) from by decide]
  norm_num [scalar_5, scalar_6, scalar_7, scalar_8, scalar_9, scalar_10, scalar_11, scalar_12, scalar_13, scalar_14, scalar_15, scalar_16, scalar_17, scalar_18, scalar_19, scalar_20]

/-- This is an infinite-tail statement, via the already authored all-depth
finite horizon theorem, not via extrapolation from the table. -/
theorem scalar_tail_gcd_four : IsScalarTailGcd 4 60 := by
  have h := finite_channel_moment_certificate (D := 4) (p := 3)
    (by decide) (by decide) (by decide) (by decide)
  simpa only [show 4 * (2 * 3 - 1) = 20 by decide, finite_scalar_gcd_four] using h.2.1

theorem kernelOne_scalar_formula (D : ℕ) :
    kernelOne D = (channelLCM D : ℤ) - ∑ d ∈ Finset.Icc 2 D,
      ((channelLCM D : ℤ) / ((d.factorial : ℤ) - 1)) * channelScalar d := by
  classical
  unfold kernelOne
  rw [canonicalKernel_expansion, Finsupp.sub_apply, Finsupp.finset_sum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_eq_same, mul_one]
  rfl

theorem lcm_four_value : channelLCM 4 = 115 := by decide +kernel

theorem kernelOne_four : kernelOne 4 = -55 := by
  rw [kernelOne_scalar_formula]
  rw [show Finset.Icc 2 4 = ({2, 3, 4} : Finset ℕ) from by decide]
  norm_num [lcm_four_value, channelScalar_two, scalar_3, scalar_4]

theorem minimumMoment_four : minimumMoment 4 3 = 1380 := by
  norm_num [minimumMoment, finite_scalar_gcd_four, kernelOne_four, lcm_four_value]

/-- Every possible support, not merely support at most eight, is covered. -/
theorem exact_depth_four_ideal (m : ℤ) : AttainsMoment 4 m ↔ (1380 : ℤ) ∣ m := by
  simpa only [minimumMoment_four] using
    attainable_moment_ideal (D := 4) (p := 3)
      (by decide) (by decide) (by decide) (by decide) m

noncomputable def depthFourVector : ℕ →₀ ℤ :=
  12 • canonicalKernel 4 + 253 • isolatedChannelUnit 6 - 11 • isolatedChannelUnit 8

theorem depthFourVector_admissible : Admissible depthFourVector := by
  apply (admissible_iff _).mpr
  constructor
  · simp [depthFourVector, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply,
      canonicalKernel_at_zero, isolated_unit_outside 6 0 (Or.inl rfl),
      isolated_unit_outside 8 0 (Or.inl rfl)]
  · change 12 * kernelOne 4 + 253 * channelScalar 6 - 11 * channelScalar 8 = 0
    norm_num [kernelOne_four, scalar_6, scalar_8]

theorem depthFourVector_channels : LowChannels 4 depthFourVector := by
  intro d hd
  have hd2 := (Finset.mem_Icc.mp hd).1
  have hd4 := (Finset.mem_Icc.mp hd).2
  simp [depthFourVector, channelNumerator_add, channelNumerator_sub,
    channelNumerator_smul, canonicalKernel_channel hd2, hd4,
    channelNumerator_isolatedChannelUnit (by decide : 2 ≤ 6) hd2,
    channelNumerator_isolatedChannelUnit (by decide : 2 ≤ 8) hd2,
    show d ≠ 6 by omega, show d ≠ 8 by omega,
    show 6 ≠ d by omega, show 8 ≠ d by omega]

theorem depthFourVector_moment : factorialMoment depthFourVector = 1380 := by
  simp [depthFourVector, factorialMoment_add, factorialMoment_sub,
    factorialMoment_smul, canonicalKernel_moment, lcm_four_value,
    factorialMoment_isolatedChannelUnit (by decide : 2 ≤ 6),
    factorialMoment_isolatedChannelUnit (by decide : 2 ≤ 8)]

theorem depth_four_minimum : AttainsMoment 4 1380 ∧
    ∀ m : ℤ, AttainsMoment 4 m → 0 < m → 1380 ≤ m := by
  constructor
  · exact ⟨depthFourVector, depthFourVector_admissible,
      depthFourVector_channels, depthFourVector_moment⟩
  · intro m hm hpos
    simpa only [minimumMoment_four] using minimum_positive_moment
      (D := 4) (p := 3) (by decide) (by decide) (by decide) (by decide) hm hpos

/-- The explicit attaining vector, not merely some existential witness, has
coefficient content one because any nontrivial scaling lowers its moment. -/
theorem depthFourVector_content_one : coefficientContent depthFourVector = 1 := by
  have hne : depthFourVector ≠ 0 := by
    intro h
    have hm := depthFourVector_moment
    rw [h] at hm
    simpa [factorialMoment] using hm
  apply (primitive_iff_content_one hne).mp
  apply minimum_moment_vector_primitive (D := 4) (p := 3)
    (by decide) (by decide) (by decide) (by decide)
    depthFourVector_admissible depthFourVector_channels
  rw [depthFourVector_moment, minimumMoment_four]

end ErdosProblems.Erdos68.PaperCoverageV5
