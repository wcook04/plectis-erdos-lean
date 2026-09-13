/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.AdelicHeightBridge
import Solutions.PalomarCorpus.E1049.Statement

open Polynomial

namespace PalomarCorpus.E1049.AdelicHeightBridge
export PalomarCorpus.E1049.Shared (hpCyclotomicSaving hpDecay hpHeight hpThreshold)

theorem zudilin_firstTransformedRow_initialMonomial (l : ℕ) :
    PowerSeries.order (zudilinFirstTransformedRow l) = l + 1 ∧
      PowerSeries.coeff (l + 1) (zudilinFirstTransformedRow l) = -6 := by
  have hmoment (n : ℕ) :
      zudilinNormalizedMoment n =
        ErdosProblems.Erdos1049.zudilinNormalizedMoment n := by
    rfl
  have hrow :
      ErdosProblems.Erdos1049.zudilinTransformedNormalizedMoment 1 l =
        ErdosProblems.Erdos1049.zudilinNormalizedMoment (l + 1) -
          ErdosProblems.Erdos1049.zudilinNormalizedMoment l := by
    simpa using
      (ErdosProblems.Erdos1049.zudilinTransformedNormalizedMoment_succ 0 l)
  rw [zudilinFirstTransformedRow, hmoment, hmoment, ← hrow]
  exact
    ErdosProblems.Erdos1049.zudilinTransformedNormalizedMoment_one_initialMonomial l

theorem zudilinSharpHankelOrderAndCoeff_algebraicAssembly (N : ℕ) :
    6 * zudilinSharpHankelQOrder N =
        (N : ℤ) * ((N : ℤ) - 1) * (2 * (N : ℤ) - 1) ∧
      2 ^ N * (∏ j ∈ Finset.range N, zudilinTransformedRowCoeff j) =
        (N.factorial) ^ 2 * (N + 1).factorial := by
  have horder :
      zudilinSharpHankelQOrder =
        ErdosProblems.Erdos1049.zudilinSharpHankelQOrder := rfl
  have hcoeff :
      zudilinTransformedRowCoeff =
        ErdosProblems.Erdos1049.zudilinTransformedRowCoeff := rfl
  rw [horder, hcoeff]
  exact
    ErdosProblems.Erdos1049.zudilinSharpHankelOrderAndCoeff_algebraicAssembly N

theorem threePow_fortyOne_lt_twoPow_sixtyFive : 3 ^ 41 < 2 ^ 65 := by
  exact ErdosProblems.Erdos1049.threePow_fortyOne_lt_twoPow_sixtyFive

theorem twoPow_sixtyFour_lt_threePow_fortyOne : 2 ^ 64 < 3 ^ 41 := by
  exact ErdosProblems.Erdos1049.twoPow_sixtyFour_lt_threePow_fortyOne

theorem threeHalves_rectangular_hp_gap_gt_threeThirteenths (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - hpThreshold rho sigma := by
  simpa [hpThreshold, hpDecay, hpHeight, hpCyclotomicSaving,
    ErdosProblems.Erdos1049.hpThreshold, ErdosProblems.Erdos1049.hpDecay,
    ErdosProblems.Erdos1049.hpHeight,
    ErdosProblems.Erdos1049.hpCyclotomicSaving] using
    ErdosProblems.Erdos1049.threeHalves_rectangular_hp_gap_gt_threeThirteenths
      rho sigma hrho hsigma

theorem threeHalves_hankelChargeThreshold_lt_eightFortyOne :
    (Real.log 3 / Real.log 2 - 1) / 3 < (8 : ℝ) / 41 := by
  exact ErdosProblems.Erdos1049.threeHalves_hankelChargeThreshold_lt_eightFortyOne

theorem zudilinScalarContent_cannot_meet_required_charge
    (N extractedDegree : ℤ) (hN : 0 < N)
    (hextracted : extractedDegree ≤ N ^ 3 - N) :
    41 * extractedDegree < 39 * (4 * N ^ 3 - 3 * N ^ 2) := by
  exact ErdosProblems.Erdos1049.zudilinScalarContent_cannot_meet_required_charge
    N extractedDegree hN hextracted

theorem zudilinScalarPlusBorder_cannot_meet_required_charge
    (N extractedDegree : ℤ) (hN : 2 ≤ N)
    (hextracted : extractedDegree ≤ 2 * N ^ 3 - N) :
    41 * extractedDegree < 39 * (4 * N ^ 3 - 3 * N ^ 2) := by
  exact ErdosProblems.Erdos1049.zudilinScalarPlusBorder_cannot_meet_required_charge
    N extractedDegree hN hextracted

theorem three_two_scalar_margin_lt_explicit {C0 C1 : ℝ}
    (hC0 : 0 < C0) (hsource : 2 * C0 ≤ C1) :
    C0 * Real.log 3 - C1 * Real.log 2 <
      -((17 : ℝ) / 41) * C0 * Real.log 2 := by
  exact ErdosProblems.Erdos1049.three_two_scalar_margin_lt_explicit hC0 hsource

theorem exists_distinct_binary_selectors_same_fourJet_of_power_certificate
    {n p q T S W : ℕ}
    (forms : Fin n → Polynomial ℤ × Polynomial ℤ)
    (hpq : (3 : ℕ) ^ p < (2 : ℕ) ^ q) (hT : 0 < T)
    (hrank : 2 * q * T + 2 * S ≤ n) :
    ∃ ε η : Fin n → Bool, ε ≠ η ∧
      selectedFourJetSum (p * T) S W forms ε =
        selectedFourJetSum (p * T) S W forms η := by
  simpa [selectedFourJetSum, fourJetSignature, bottomJet3, topJet2,
    homEvalThreeTwo, ErdosProblems.Erdos1049.selectedFourJetSum,
    ErdosProblems.Erdos1049.fourJetSignature,
    ErdosProblems.Erdos1049.bottomJet3, ErdosProblems.Erdos1049.topJet2,
    ErdosProblems.Erdos1049.homEvalThreeTwo] using
    ErdosProblems.Erdos1049.exists_distinct_binary_selectors_same_fourJet_of_power_certificate
      forms hpq hT hrank

theorem exists_distinct_binary_selectors_same_fourJet_of_rank_41
    {n T S W : ℕ}
    (forms : Fin n → Polynomial ℤ × Polynomial ℤ) (hT : 0 < T)
    (hrank : 130 * T + 2 * S ≤ n) :
    ∃ ε η : Fin n → Bool, ε ≠ η ∧
      selectedFourJetSum (41 * T) S W forms ε =
        selectedFourJetSum (41 * T) S W forms η := by
  simpa [selectedFourJetSum, fourJetSignature, bottomJet3, topJet2,
    homEvalThreeTwo, ErdosProblems.Erdos1049.selectedFourJetSum,
    ErdosProblems.Erdos1049.fourJetSignature,
    ErdosProblems.Erdos1049.bottomJet3, ErdosProblems.Erdos1049.topJet2,
    ErdosProblems.Erdos1049.homEvalThreeTwo] using
    ErdosProblems.Erdos1049.exists_distinct_binary_selectors_same_fourJet_of_rank_41
      forms hT hrank

theorem fourJet_card_gt_two_pow_of_rank_41 (S : ℕ) :
    2 ^ (129 + 2 * S) < Fintype.card (FourJetSignature 41 S) := by
  exact ErdosProblems.Erdos1049.fourJet_card_gt_two_pow_of_rank_41 S

theorem exists_ne_map_eq_map_ne_of_card_mul_lt {α β γ : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : α → γ) (k : ℕ)
    (hg : ∀ x : α, (Finset.univ.filter fun y => g y = g x).card ≤ k)
    (hcard : Fintype.card β * k < Fintype.card α) :
    ∃ x y : α, x ≠ y ∧ f x = f y ∧ g x ≠ g y := by
  exact ErdosProblems.Erdos1049.exists_ne_map_eq_map_ne_of_card_mul_lt
    f g k hg hcard

end PalomarCorpus.E1049.AdelicHeightBridge
