/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos1049.AdelicHeightBridge
import ErdosProblems.Erdos1049.PaperNoDecayR9
import Mathlib
import ErdosProblems.Erdos1049.BezoutPluckerJets
import ErdosProblems.Erdos1049.HermitePadeNoGo
import ErdosProblems.Erdos1049.QAperyTailDenominator
import ErdosProblems.Erdos1049.TwoSelectorRemainderEscape
import ErdosProblems.Erdos1049.ZudilinHeightRegion
import ErdosProblems.Erdos1049.RationalBaseLambert

open Polynomial
open Filter Asymptotics
open scoped Topology
open scoped BigOperators
open Filter

namespace PalomarCorpus.E1049.Shared
noncomputable def hpCyclotomicSaving (sigma : ℝ) : ℝ :=
  3 * sigma ^ 2 / Real.pi ^ 2

noncomputable def hpDecay (rho sigma : ℝ) : ℝ :=
  (1 + rho ^ 2) / 2 + sigma

noncomputable def hpHeight (rho sigma : ℝ) : ℝ :=
  (1 + rho) ^ 2 / 2 + sigma * (1 + rho)

noncomputable def hpThreshold (rho sigma : ℝ) : ℝ :=
  (hpDecay rho sigma - hpCyclotomicSaving sigma) /
    (hpHeight rho sigma + hpDecay rho sigma)

end PalomarCorpus.E1049.Shared
namespace PalomarCorpus.E1049.AdelicHeightBridge
export PalomarCorpus.E1049.Shared (hpCyclotomicSaving hpDecay hpHeight hpThreshold)

open Polynomial

noncomputable def homEvalThreeTwo (W : ℕ) (P : Polynomial ℤ) : ℤ :=
  ∑ i ∈ Finset.range (W + 1), P.coeff i * 3 ^ i * 2 ^ (W - i)
noncomputable def bottomJet3 (R W : ℕ) (P : Polynomial ℤ) : ZMod (3 ^ R) :=
  homEvalThreeTwo W P
noncomputable def topJet2 (S W : ℕ) (P : Polynomial ℤ) : ZMod (2 ^ S) :=
  homEvalThreeTwo W P
noncomputable abbrev FourJetSignature (R S : ℕ) :=
  (ZMod (3 ^ R) × ZMod (3 ^ R)) ×
    (ZMod (2 ^ S) × ZMod (2 ^ S))
noncomputable def fourJetSignature (R S W : ℕ) (U V : Polynomial ℤ) :
    FourJetSignature R S :=
  ((bottomJet3 R W U, bottomJet3 R W V),
    (topJet2 S W U, topJet2 S W V))
noncomputable def selectedFourJetSum {n : ℕ} (R S W : ℕ)
    (forms : Fin n → Polynomial ℤ × Polynomial ℤ)
    (ε : Fin n → Bool) : FourJetSignature R S :=
  ∑ i, if ε i then
    fourJetSignature R S W (forms i).1 (forms i).2
  else 0
noncomputable def zudilinPochhammerPS (start len : ℕ) : PowerSeries ℤ :=
  ∏ r ∈ Finset.range len,
    (1 - PowerSeries.X ^ (start + r) : PowerSeries ℤ)

noncomputable def zudilinNormalizedTailUnit (n t : ℕ) : PowerSeries ℤ :=
  zudilinPochhammerPS 1 n ^ 3 * zudilinPochhammerPS (t + 1) n *
    PowerSeries.invOfUnit (zudilinPochhammerPS (n + 1 + t) (n + 1)) 1

noncomputable def zudilinNormalizedTail (n t : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ ((n + 1) * t) * zudilinNormalizedTailUnit n t

noncomputable def zudilinNormalizedMoment (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d =>
    ∑ t ∈ Finset.range (d / (n + 1) + 1),
      PowerSeries.coeff d (zudilinNormalizedTail n t)

noncomputable def zudilinFirstTransformedRow (l : ℕ) : PowerSeries ℤ :=
  zudilinNormalizedMoment (l + 1) - zudilinNormalizedMoment l

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

noncomputable def zudilinSharpHankelQOrder (N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range N, (j : ℤ) ^ 2
noncomputable def zudilinTransformedRowCoeff (j : ℕ) : ℕ :=
  ((j + 1) ^ 2 * (j + 2)) / 2
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

namespace PalomarCorpus.E1049.ArchimedeanCap
open Filter Asymptotics
open scoped Topology

noncomputable def width (U V : ℕ → Polynomial ℤ) (n : ℕ) : ℕ := max (U n).natDegree (V n).natDegree
noncomputable def height (P : Polynomial ℤ) : ℝ := ∑ i ∈ P.support, |(P.coeff i : ℝ)|
noncomputable def remainder (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  (U n).eval₂ (Int.castRingHom ℝ) x * F x - (V n).eval₂ (Int.castRingHom ℝ) x

theorem archimedean_cap (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ) (σ δ h : ℝ)
    (hσ : 0 < σ) (hδ : 0 < δ) (hh : 0 ≤ h)
    (hdeg : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, (width U V n : ℝ) ≤ (δ + ε) * (n : ℝ)^2)
    (hheight : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log (max (height (U n)) (height (V n))) ≤ (h + ε) * (n : ℝ)^2)
    (hne : ∀ x : ℝ, 1 < x → ∀ᶠ n in atTop, remainder U V F x n ≠ 0)
    (hrate : ∀ x : ℝ, 1 < x →
      (fun n => Real.log |remainder U V F x n| - (-σ * Real.log x) * (n : ℝ)^2)
        =o[atTop] (fun n : ℕ => (n : ℝ)^2)) :
    σ / (σ + δ) ≤ (1 : ℝ) / 2 ∧
    ∀ a b : ℕ, 1 ≤ b → b < a →
      Real.log b / Real.log a < σ / (σ + δ) →
      Tendsto (fun n => (b : ℝ) ^ width U V n * remainder U V F ((a : ℝ) / b) n)
        atTop (𝓝 0) := by
  exact ErdosProblems.Erdos1049.PaperR9.short_note_archimedean_cap U V F σ δ h
    ⟨hσ, hδ, hh, hdeg, hheight, hne, hrate⟩

noncomputable def maxCoefficient (P : Polynomial ℤ) : ℕ :=
  P.support.sup (fun i => (P.coeff i).natAbs)
/-- Exact all-base hypotheses; no limit of the normalized degree is assumed. -/
theorem cleared_below_square_not_tendsto_zero
    (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ) (σ δ h : ℝ)
    (hσ : 0 < σ) (hδ : 0 < δ) (hh : 0 ≤ h)
    (hdeg : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (width U V n : ℝ) ≤ (δ + ε) * (n : ℝ)^2)
    (hheight : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log ((max (maxCoefficient (U n)) (maxCoefficient (V n)) : ℕ) : ℝ)
        ≤ (h + ε) * (n : ℝ)^2)
    (hne : ∀ x : ℝ, 1 < x → ∀ᶠ n in atTop, remainder U V F x n ≠ 0)
    (hrate : ∀ x : ℝ, 1 < x →
      (fun n => Real.log |remainder U V F x n| - (-σ * Real.log x) * (n : ℝ)^2)
        =o[atTop] (fun n : ℕ => (n : ℝ)^2))
    (a b : ℕ) (hb : 1 ≤ b) (hab : b < a) (hsquare : a < b * b) :
    ¬ Tendsto (fun n => (b : ℝ) ^ width U V n *
      remainder U V F ((a : ℝ) / b) n) atTop (𝓝 0) := by
  exact ErdosProblems.Erdos1049.PaperR9.cleared_below_square_not_tendsto_zero
    U V F σ δ h ⟨hσ, hδ, hh, hdeg, hheight, hne, hrate⟩ a b hb hab hsquare

end PalomarCorpus.E1049.ArchimedeanCap

namespace PalomarCorpus.E1049.BezoutPluckerJets

open scoped BigOperators

theorem anchor_det_zero_forces_all_det_zero {R : Type*} [CommRing R]
    {ι : Type*} (w : ι → R × R) {a b : R}
    (hab : IsCoprime a b) (hdet : ∀ i, a * (w i).2 - b * (w i).1 = 0) :
    ∀ i j, (w i).1 * (w j).2 - (w i).2 * (w j).1 = 0 := by
  exact ErdosProblems.Erdos1049.BezoutPluckerJets.anchor_det_zero_forces_all_det_zero
    w hab hdet

theorem binary_row_collision_of_anchor_det_zero
    {R ι : Type*} [CommRing R] [Fintype R] [Fintype ι]
    (w : ι → R × R) {a b : R}
    (hab : IsCoprime a b) (hdet : ∀ i, a * (w i).2 - b * (w i).1 = 0)
    (hcard : Fintype.card R < 2 ^ Fintype.card ι) :
    ∃ s t : ι → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by
  exact ErdosProblems.Erdos1049.BezoutPluckerJets.binary_row_collision_of_anchor_det_zero
    w hab hdet hcard

theorem adjacent_det_zero_forces_all_det_zero {R : Type*} [CommRing R]
    (w : ℕ → R × R) (hunit : ∀ n, IsUnit (w n).2)
    (hadj : ∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0) :
    ∀ i j, (w i).1 * (w j).2 - (w i).2 * (w j).1 = 0 := by
  exact ErdosProblems.Erdos1049.BezoutPluckerJets.adjacent_det_zero_forces_all_det_zero
    w hunit hadj

theorem zmod_binary_tail_collision_of_two_three_depth {R S k : ℕ}
    [NeZero (2 ^ S * 3 ^ R)]
    (w : ℕ → ZMod (2 ^ S * 3 ^ R) × ZMod (2 ^ S * 3 ^ R))
    (hunit : ∀ n, IsUnit (w n).2)
    (hadj : ∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0)
    (hR : 0 < R) (hrank : S + 2 * R ≤ k) :
    ∃ s t : Fin k → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by
  exact ErdosProblems.Erdos1049.BezoutPluckerJets.zmod_binary_tail_collision_of_two_three_depth
    w hunit hadj hR hrank

end PalomarCorpus.E1049.BezoutPluckerJets

namespace PalomarCorpus.E1049.HermitePadeNoGo
export PalomarCorpus.E1049.Shared (hpCyclotomicSaving hpDecay hpHeight hpThreshold)

noncomputable abbrev hpClearedGap := ErdosProblems.Erdos1049.hpClearedGap

theorem hpClearedGap_expansion (rho u : ℝ) :
    hpClearedGap rho (1 + rho + u) =
      -Real.pi ^ 2 * rho ^ 2 - Real.pi ^ 2 * rho * u -
        2 * Real.pi ^ 2 * rho - 2 * rho ^ 2 - 10 * rho * u -
        4 * rho - 6 * u ^ 2 - 8 * u :=
  ErdosProblems.Erdos1049.hpClearedGap_expansion rho u

theorem hpClearedGap_nonpos (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpClearedGap rho sigma ≤ 0 :=
  ErdosProblems.Erdos1049.hpClearedGap_nonpos rho sigma hrho hsigma

theorem hpClearedGap_eq_zero_iff (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpClearedGap rho sigma = 0 ↔ rho = 0 ∧ sigma = 1 :=
  ErdosProblems.Erdos1049.hpClearedGap_eq_zero_iff rho sigma hrho hsigma

theorem rectangular_hp_threshold_le_classical (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpThreshold rho sigma ≤ 1 / 2 - 1 / Real.pi ^ 2 :=
  ErdosProblems.Erdos1049.rectangular_hp_threshold_le_classical
    rho sigma hrho hsigma

theorem rectangular_hp_threshold_eq_classical_iff (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpThreshold rho sigma = 1 / 2 - 1 / Real.pi ^ 2 ↔
      rho = 0 ∧ sigma = 1 :=
  ErdosProblems.Erdos1049.rectangular_hp_threshold_eq_classical_iff
    rho sigma hrho hsigma

end PalomarCorpus.E1049.HermitePadeNoGo

namespace PalomarCorpus.E1049.PrimeSupportSelectors

open Filter

theorem twoSelector_rationalGap
    (a q A₁ B₁ A₂ B₂ : ℤ) (hq : 0 < q)
    (hdet : A₁ * B₂ - A₂ * B₁ ≠ 0) :
    (1 : ℝ) / q ≤
        |(B₁ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ : ℝ)| ∨
      (1 : ℝ) / q ≤
        |(B₂ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ : ℝ)| :=
  ErdosProblems.Erdos1049.rational_twoSelector_remainder_gap
    a q A₁ B₁ A₂ B₂ hq hdet

theorem integerLinearForm_rationalGap
    (a q A B : ℤ) (hq : 0 < q)
    (hne : (B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ) ≠ 0) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| :=
  ErdosProblems.Erdos1049.rational_integerLinearForm_gap a q A B hq hne

theorem rationalTwoSelector_notBothTendstoZero
    (a q : ℤ) (hq : 0 < q)
    (A₁ B₁ A₂ B₂ : ℕ → ℤ)
    (hdet : ∀ n, A₁ n * B₂ n - A₂ n * B₁ n ≠ 0) :
    ¬(Tendsto
        (fun n ↦ (B₁ n : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ n : ℝ))
        atTop (nhds 0) ∧
      Tendsto
        (fun n ↦ (B₂ n : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ n : ℝ))
        atTop (nhds 0)) :=
  ErdosProblems.Erdos1049.rational_twoSelector_not_both_tendsto_zero
    a q hq A₁ B₁ A₂ B₂ hdet

theorem twoSelector_detHeightDecay_tradeoff
    (A₁ B₁ A₂ B₂ F ε : ℝ)
    (h₁ : |B₁ * F - A₁| ≤ ε) (h₂ : |B₂ * F - A₂| ≤ ε) :
    |A₁ * B₂ - A₂ * B₁| ≤ ε * (|B₁| + |B₂|) :=
  ErdosProblems.Erdos1049.twoSelector_det_height_decay_tradeoff
    A₁ B₁ A₂ B₂ F ε h₁ h₂

theorem twoSelector_unimodularHeightDecay_tradeoff
    (A₁ B₁ A₂ B₂ u v w z F H ε : ℝ)
    (hunimod : |u * z - v * w| = 1)
    (hε : 0 ≤ ε)
    (hu : |u| ≤ H) (hv : |v| ≤ H) (hw : |w| ≤ H) (hz : |z| ≤ H)
    (h₁ : |(u * B₁ + v * B₂) * F - (u * A₁ + v * A₂)| ≤ ε)
    (h₂ : |(w * B₁ + z * B₂) * F - (w * A₁ + z * A₂)| ≤ ε) :
    |A₁ * B₂ - A₂ * B₁| ≤
      2 * H * ε * (|B₁| + |B₂|) :=
  ErdosProblems.Erdos1049.twoSelector_unimodular_height_decay_tradeoff
    A₁ B₁ A₂ B₂ u v w z F H ε hunimod hε hu hv hw hz h₁ h₂

theorem primeSupportedTwoSelector_rationalGap
    {ell : ℕ} (hell : ell.Prime)
    (a q A₁ B₁ A₂ B₂ : ℤ) (hq : 0 < q)
    (hellq : ¬ (ell : ℤ) ∣ q)
    (hellB₁ : (ell : ℤ) ∣ B₁)
    (hellB₂ : (ell : ℤ) ∣ B₂)
    (hdet : ¬ (ell : ℤ) ^ 2 ∣ A₁ * B₂ - A₂ * B₁) :
    (1 : ℝ) / q ≤
        |(B₁ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ : ℝ)| ∨
      (1 : ℝ) / q ≤
        |(B₂ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ : ℝ)| :=
  ErdosProblems.Erdos1049.rational_twoSelector_gap_of_prime_tail_support
    hell a q A₁ B₁ A₂ B₂ hq hellq hellB₁ hellB₂ hdet

theorem primeSupportedOneRow_rationalGap
    {ell : ℕ} (hell : ell.Prime)
    (a q A B : ℤ) (hq : 0 < q)
    (hellB : (ell : ℤ) ∣ B)
    (hellA : ¬ (ell : ℤ) ∣ A)
    (hellq : ¬ (ell : ℤ) ∣ q) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| :=
  ErdosProblems.Erdos1049.rational_integerLinearForm_gap_of_prime_support
    hell a q A B hq hellB hellA hellq

theorem primePowerSupportedOneRow_rationalGap
    {ell r : ℕ} (hell : ell.Prime) (hr : r ≠ 0)
    (a q A B : ℤ) (hq : 0 < q)
    (hellPowB : (ell : ℤ) ^ r ∣ B)
    (hellA : ¬ (ell : ℤ) ∣ A)
    (hellq : ¬ (ell : ℤ) ∣ q) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| :=
  ErdosProblems.Erdos1049.rational_integerLinearForm_gap_of_prime_power_support
    hell hr a q A B hq hellPowB hellA hellq

theorem zeroDenominatorCoordinates_binaryCollision
    {N k : ℕ} [NeZero N]
    (w : Fin k → ZMod N × ZMod N)
    (hzero : ∀ i, (w i).2 = 0)
    (hcard : N < 2 ^ k) :
    ∃ s t : Fin k → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 :=
  ErdosProblems.Erdos1049.zmod_binary_collision_of_zero_denominator_coordinates
    w hzero hcard

end PalomarCorpus.E1049.PrimeSupportSelectors

namespace PalomarCorpus.E1049.PublishedHeightRegions

noncomputable def BundschuhVaananenHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < 1 / 2 - 1 / Real.pi ^ 2
noncomputable def ZudilinHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < (81 : ℝ) / 200
theorem threeHalves_zudilin_power_obstruction :
    3 ^ 81 < 2 ^ 200 :=
  ErdosProblems.Erdos1049.threeHalves_zudilin_power_obstruction

theorem eightyOneTwoHundredths_lt_threeHalves_log_ratio :
    (81 : ℝ) / 200 < Real.log 2 / Real.log 3 :=
  ErdosProblems.Erdos1049.eightyOneTwoHundredths_lt_threeHalves_log_ratio

theorem threeHalves_outside_zudilinHeightRegion :
    ¬ ZudilinHeightRegion 3 2 := by
  simpa [ZudilinHeightRegion, ErdosProblems.Erdos1049.ZudilinHeightRegion] using
    ErdosProblems.Erdos1049.threeHalves_outside_zudilinHeightRegion

theorem threeHalves_outside_bundschuhVaananenHeightRegion :
    ¬ BundschuhVaananenHeightRegion 3 2 := by
  simpa [BundschuhVaananenHeightRegion,
    ErdosProblems.Erdos1049.BundschuhVaananenHeightRegion] using
    ErdosProblems.Erdos1049.threeHalves_outside_bundschuhVaananenHeightRegion

end PalomarCorpus.E1049.PublishedHeightRegions

namespace PalomarCorpus.E1049.RationalBaseBarrier

open scoped BigOperators

noncomputable def CoordinatewiseCorridor
    (a b N K Q digit : ℕ) : Prop :=
  0 < a ∧ 0 < Q ∧ 0 < digit ∧ digit ≤ N + K ∧
    a ^ K ∣ Q * digit ∧
    Q * b ^ (N + K + 1) < a ^ (K + 1)
noncomputable def rationalBasePrefixQ
    (r s : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ m ∈ Finset.range N,
    coeff (m + 1) * s ^ (m + 1) / r ^ (m + 1)
noncomputable def rationalBaseClearedTailQ
    (r s B F : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  B * r ^ N * (F - rationalBasePrefixQ r s coeff N)
noncomputable def rationalBaseForcingNat
    (s B : ℕ) (coeff : ℕ → ℕ) (N : ℕ) : ℕ :=
  B * coeff (N + 1) * s ^ (N + 1)
theorem rationalBaseClearedTailQ_succ
    {r s B F : ℚ} {coeff : ℕ → ℚ} (hr : r ≠ 0) (N : ℕ) :
    rationalBaseClearedTailQ r s B F coeff (N + 1) =
      r * rationalBaseClearedTailQ r s B F coeff N -
        B * coeff (N + 1) * s ^ (N + 1) := by
  simpa [rationalBaseClearedTailQ, rationalBasePrefixQ,
    ErdosProblems.Erdos1049.rationalBaseClearedTailQ,
    ErdosProblems.Erdos1049.rationalBasePrefixQ] using
    ErdosProblems.Erdos1049.rationalBaseClearedTailQ_succ hr N

theorem twoPow_le_rationalBaseForcingNat
    {s B : ℕ} {coeff : ℕ → ℕ} {N : ℕ}
    (hs : 2 ≤ s) (hB : 1 ≤ B) (hc : 1 ≤ coeff (N + 1)) :
    2 ^ (N + 1) ≤ rationalBaseForcingNat s B coeff N := by
  simpa [rationalBaseForcingNat,
    ErdosProblems.Erdos1049.rationalBaseForcingNat] using
    ErdosProblems.Erdos1049.twoPow_le_rationalBaseForcingNat hs hB hc

theorem threeHalves_no_coordinatewiseCorridor
    {N K Q digit : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K) :
    ¬ CoordinatewiseCorridor 3 2 N K Q digit := by
  simpa [CoordinatewiseCorridor,
    ErdosProblems.Erdos1049.CoordinatewiseCorridor] using
    ErdosProblems.Erdos1049.threeHalves_no_coordinatewiseCorridor
      (Q := Q) (digit := digit) hN hK

end PalomarCorpus.E1049.RationalBaseBarrier
