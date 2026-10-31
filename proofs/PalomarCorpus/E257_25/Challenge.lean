/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257, record section 6.2: exact identities and reductions (part 5 of 6)

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open Matrix
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
open scoped BigOperators

namespace PalomarCorpus.E257_25.Shared
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The Mersenne tail beyond rank n, namely the sum over k at least 0 of the Mersenne weight at n+k+1. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- The positive gap between one Mersenne weight and the tail after it. Local copy of Erdos249257.mersenneGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneGap (n : ℕ) : ℝ :=
  mersenneWeight n - mersenneTail n
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
end PalomarCorpus.E257_25.Shared

namespace PalomarCorpus.E257.PaperStatementsAA
/-- States lem:linear-channel-nogo from the long record for Erdős problem #257. Transported from Erdos249257.AdelicHeightObstruction.linearDescender_eq_smul_eval in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem linearDescender_eq_smul_eval
    {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (ev : V →ₗ[ℚ] ℚ) (Λ : V →ₗ[ℚ] W)
    (hker : LinearMap.ker ev ≤ LinearMap.ker Λ)
    (he : ∃ e : V, ev e = 1) :
    ∃ w₀ : W, ∀ v : V, Λ v = ev v • w₀ := by
  sorry
/-- States lem:reverse-carry-word from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_reverse_carry_word in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_reverse_carry_word :
    (∀ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) →
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) →
      ∀ k L : ℕ, a₁ k = a₂ k → b₁ k - b₂ k = 1 →
        (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) →
        (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) →
        u₁ (k + L + 1) - u₂ (k + L + 1) = 2 ^ L * (2 * (u₁ k - u₂ k) + 1) ∧
          Odd (2 * (u₁ k - u₂ k) + 1)) ∧
    (∀ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) →
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) →
      ∀ (k L : ℕ) (B₁ B₂ : ℝ), a₁ k = a₂ k → b₁ k - b₂ k = 1 →
        (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) →
        (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) →
        |((u₁ (k + L + 1) : ℤ) : ℝ)| ≤ B₁ →
        |((u₂ (k + L + 1) : ℤ) : ℝ)| ≤ B₂ →
        (2 : ℝ) ^ L ≤ B₁ + B₂) ∧
    (∀ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) →
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) →
      ∀ (k L : ℕ) (B : ℝ), a₁ k = a₂ k → b₁ k - b₂ k = 1 →
        (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) →
        (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) →
        |((u₁ (k + L + 1) : ℤ) : ℝ)| ≤ B →
        |((u₂ (k + L + 1) : ℤ) : ℝ)| ≤ B →
        (2 : ℝ) ^ L ≤ 2 * B) := by
  sorry
/-- States thm:two-thirds-band from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_two_thirds_band in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_two_thirds_band :
    (∀ (R : ℚ) (k : ℕ), 0 < R → (1 / R ≤ 1 / 2 ^ k ↔ (2 : ℚ) ^ k ≤ R)) ∧
    (∀ R q : ℚ, 0 < R → R < q → 1 / (1 / R - 1 / q) = R * q / (q - R)) ∧
    (∀ R q m : ℚ, 0 < R → R < q → 1 ≤ m →
        ((m - 1 < R * q / (q - R) ∧ R * q / (q - R) < m) ↔
          (q * (m - 1) / (q + m - 1) < R ∧ R < q * m / (q + m)))) ∧
    (∀ q m : ℚ, 0 < q → 1 ≤ m →
        q * m / (q + m) - q * (m - 1) / (q + m - 1)
          = q ^ 2 / ((q + m) * (q + m - 1))) ∧
    (∀ b : ℕ, (2 : ℚ) ^ (b + 1) = 2 * ((2 : ℚ) ^ b - 1) + 2) ∧
    (∀ q : ℚ, 0 < q →
        2 * q * (q + 1) / (3 * q + 2) - q * (2 * q + 1) / (3 * q + 1)
            = q ^ 2 / ((3 * q + 1) * (3 * q + 2)) ∧
          q ^ 2 / ((3 * q + 1) * (3 * q + 2)) < 1 / 9) ∧
    (∀ R q : ℚ, 0 < q →
        (q * (2 * q + 1) / (3 * q + 1) < R ∧ R < 2 * q * (q + 1) / (3 * q + 2)) →
        2 * q < 3 * R ∧ 3 * R < 2 * q + 2 / 3) ∧
    (∀ (R q : ℚ) (mm n : ℤ), 0 < q → R = (mm : ℚ) → q = (n : ℚ) →
        ¬ (q * (2 * q + 1) / (3 * q + 1) < R ∧
          R < 2 * q * (q + 1) / (3 * q + 2))) ∧
    (∀ p D q : ℤ, 0 < p → 0 < D → 0 < q → Odd p → Odd D → Odd q →
        (q * (2 * q + 1) * p < 2 * D * (3 * q + 1) ∧
          2 * D * (3 * q + 2) < 2 * p * q * (q + 1)) →
        (4 : ℤ) ∣ (6 * D - 2 * p * q) ∧ 7 ≤ p) ∧
    (Odd (17 : ℤ) ∧ Odd (41 : ℤ) ∧ Odd (7 : ℤ) ∧ (∃ x y : ℤ, x * 17 + y * 41 = 1) ∧
      (2 : ℚ) ^ 3 - 1 = 7 ∧
      ((7 : ℚ) * (2 * 7 + 1) / (3 * 7 + 1) < (2 * 41 : ℚ) / 17 ∧
        (2 * 41 : ℚ) / 17 < 2 * 7 * (7 + 1) / (3 * 7 + 2))) := by
  sorry
/-- States lem:reverse-carry-word from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.reverse_carry_word_common_bound_sharp in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem reverse_carry_word_common_bound_sharp :
    ∃ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ) (k L : ℕ) (B : ℝ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) ∧
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) ∧
      a₁ k = a₂ k ∧ b₁ k - b₂ k = 1 ∧
      (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) ∧
      (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) ∧
      |((u₁ (k + L + 1) : ℤ) : ℝ)| ≤ B ∧ |((u₂ (k + L + 1) : ℤ) : ℝ)| ≤ B ∧
      ¬ ((2 : ℝ) ^ L ≤ B) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAA

namespace PalomarCorpus.E257.PaperStatementsAB
open Matrix
/-- States lem:linear-channel-nogo from the long record for Erdős problem #257. Transported from Erdos249257.HalfTrappingReturnCarry.relationInvariantLinearChannels_det_eq_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem relationInvariantLinearChannels_det_eq_zero
    {V ι : Type*} [AddCommGroup V] [Module ℚ V]
    [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (ev : V →ₗ[ℚ] ℚ) (channel : ι → V →ₗ[ℚ] ℚ)
    (hker : ∀ j : ι, LinearMap.ker ev ≤ LinearMap.ker (channel j))
    (he : ∃ e : V, ev e = 1) (row : ι → V) :
    Matrix.det (fun i j : ι ↦ channel j (row i)) = 0 := by
  sorry
end PalomarCorpus.E257.PaperStatementsAB

namespace PalomarCorpus.E257.PaperStatementsAM
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_25.Shared (mersenneGap mersenneTail mersenneWeight)
/-- States lem:gap-mass-summability, record:257hg-i2 from the long record for Erdős problem #257. Transported from Erdos249257.mersenneGap_tail_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneGap_tail_le (N : ℕ) :
    ∑' k : ℕ, mersenneGap (N + k + 1)
      ≤ (2 / 9 : ℝ) * ((1 : ℝ) / 4) ^ N + (3 / 7 : ℝ) * ((1 : ℝ) / 8) ^ N := by
  sorry
/-- States lem:gap-mass-summability from the long record for Erdős problem #257. Transported from Erdos249257.summable_mersenneGap_succ in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem summable_mersenneGap_succ : Summable (fun k : ℕ => mersenneGap (k + 1)) := by
  sorry
/-- States lem:gap-mass-summability, record:257hg-i2 from the long record for Erdős problem #257. Transported from Erdos249257.tendsto_mersenneGap_tail_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tendsto_mersenneGap_tail_zero :
    Tendsto (fun N : ℕ => ∑' k : ℕ, mersenneGap (N + k + 1)) atTop (nhds 0) := by
  sorry
/-- States thm:sharp-fatal-gap from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_fatal_gap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_sharp_fatal_gap :
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < L → 2 ^ k * u + a = 2 * L + u →
        (0 < a ↔ (u : ℝ) / (2 * L) < mersenneWeight k)) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < L → 2 ^ k * u + a = 2 * L + u →
        (0 < a ↔ ¬ (mersenneWeight k ≤ (u : ℝ) / (2 * L)))) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < L → 2 ^ k * u + a = 2 * L + u →
        ((u : ℝ) / (2 * L) ≤ 1 / 2 ^ k ↔ u ≤ a)) ∧
    (∀ k : ℕ, (1 : ℝ) / 2 ^ k + 1 / (3 * 4 ^ k) + 1 / (7 * 8 ^ k) < mersenneTail k) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < a → 2 ^ k * u + a = 2 * L + u →
        2 * u ≤ 3 * a → (u : ℝ) / (2 * L) < mersenneTail k) ∧
    (∀ u a : ℕ, u ≤ a → 2 * u ≤ 3 * a) ∧
    ((2 : ℕ) ^ 2 * 7 + 5 = 2 * 13 + 7 ∧ 2 * 7 ≤ 3 * 5 ∧ ¬ (7 ≤ 5) ∧
      (1 : ℝ) / 2 ^ 2 < (7 : ℝ) / (2 * 13) ∧ (7 : ℝ) / (2 * 13) < mersenneTail 2) ∧
    (∀ k L : ℕ, 1 ≤ k → 2 ^ k * 3 + 2 ≠ 2 * L + 3) ∧
    (∀ k L a : ℕ, 1 ≤ k → 0 < a → 2 ^ k * 1 + a = 2 * L + 1 →
        (1 : ℝ) / (2 * L) < mersenneTail k) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < a → 2 ^ k * u + a = 2 * L + u →
        mersenneTail k < (u : ℝ) / (2 * L) →
        3 * a < 2 * u ∧ 2 ≤ u ∧ (Odd u → 3 ≤ u)) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAM

namespace PalomarCorpus.E257.PaperStatementsAH
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_25.Shared (mersenneGap mersenneTail mersenneWeight)
/-- States lem:gap-mass-summability from the long record for Erdős problem #257. Transported from Erdos249257.mersenneGap_pos in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneGap_pos {n : ℕ} (hn : 0 < n) :
    0 < mersenneGap n := by
  sorry
end PalomarCorpus.E257.PaperStatementsAH

namespace PalomarCorpus.E257.PaperStatementsAL
open Filter
open Set
open Topology
export PalomarCorpus.E257_25.Shared (supportCoeff)
/-- A Boolean support word through exponent `N`. Index zero is retained so restriction is literal; admissibility forces exponents zero and one off. Local copy of Erdos249257.HalfCarryReachability.HalfWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev HalfWord (N : ℕ) := Fin (N + 1) → Bool
/-- The set represented by a finite Boolean word. Local copy of Erdos249257.HalfCarryReachability.wordSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def wordSupport {N : ℕ} (a : HalfWord N) : Set ℕ :=
  {n | ∃ h : n < N + 1, a ⟨n, h⟩ = true}
/-- Append one Boolean bit to a finite half word. Local copy of Erdos249257.HalfCarrySelectedWindow.extendHalfWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def extendHalfWord {N : ℕ} (a : HalfWord N) (β : Bool) : HalfWord (N + 1) :=
  Fin.lastCases β a
/-- States lem:half-divisor-unit-drop, record:257bm-i17 from the long record for Erdős problem #257. Transported from Erdos249257.HalfDivisorUnitDrop.supportCoeff_extend_true_eq_false_add_one_at_double in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem supportCoeff_extend_true_eq_false_add_one_at_double
    {N : ℕ} (a : HalfWord N) :
    supportCoeff (wordSupport (extendHalfWord a true)) (2 * (N + 1)) =
      supportCoeff (wordSupport (extendHalfWord a false)) (2 * (N + 1)) + 1 := by
  sorry
end PalomarCorpus.E257.PaperStatementsAL

namespace PalomarCorpus.E257.PaperStatementsAN
open scoped BigOperators
open Filter
open Topology
export PalomarCorpus.E257_25.Shared (supportCoeff)
/-- States lem:half-divisor-unit-drop from the long record for Erdős problem #257. Transported from Erdos249257.HalfCylinderIntegerGreedy.supportCoeff_insert_eq_add_indicator in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem supportCoeff_insert_eq_add_indicator
    (A : Set ℕ) {d n : ℕ} (hdA : d ∉ A) :
    supportCoeff (insert d A) n =
      supportCoeff A n + if d ∈ n.divisors then 1 else 0 := by
  sorry
end PalomarCorpus.E257.PaperStatementsAN

namespace PalomarCorpus.E257.PaperStatementsAE
open Filter
open Set
/-- A real number represented by an integer numerator and a positive natural denominator. This is the explicit positive-denominator form of membership in `ℚ`; it keeps the carry multiplier visible in theorem statements. Local copy of Erdos249257.HasRationalValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HasRationalValue (x : ℝ) : Prop :=
  ∃ p : ℤ, ∃ v : ℕ, 0 < v ∧ x = (p : ℝ) / (v : ℝ)
/-- The exact integer recurrence together with the subexponential boundary `u(N) = o(2^N)`, expressed as convergence of the quotient. Local copy of Erdos249257.IsTemperedBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)
/-- The binary coefficient series `X_c = ∑_{n≥1} c(n)/2^n`. Local copy of Erdos249257.binaryCoeffSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)
/-- The scaled tail `T_c(N) = ∑_{j≥1} c(N+j)/2^j`. Local copy of Erdos249257.binaryCoeffTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)
/-- States thm:tempered-orbit-rigidity from the long record for Erdős problem #257. Transported from Erdos249257.binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    HasRationalValue (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u := by
  sorry
/-- States thm:tempered-orbit-rigidity from the long record for Erdős problem #257. Transported from Erdos249257.temperedBinaryOrbit_eq_scaledTail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem temperedBinaryOrbit_eq_scaledTail
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n)
    {v : ℕ} {u : ℕ → ℤ} (horbit : IsTemperedBinaryOrbit c v u) :
    ∀ N : ℕ, (u N : ℝ) = (v : ℝ) * binaryCoeffTail c N := by
  sorry
end PalomarCorpus.E257.PaperStatementsAE

namespace PalomarCorpus.E257.PaperStatementsAG
open Filter
open Topology
/-- **The Erdős #257 support series** `∑_{a ∈ A} 1/(b^a - 1)`, as an indicator series over ℕ. The `a = 0` term is `1/(1-1) = 0` under real division-by-zero conventions, so supports containing `0` contribute nothing spurious. Local copy of Erdos249257.erdosSupportSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- States lem:tail-transfer from the long record for Erdős problem #257. Transported from Erdos249257.irrational_erdosSupportSeries_of_tail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_erdosSupportSeries_of_tail (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b)
    (B : ℕ) (h : Irrational (erdosSupportSeries b {n : ℕ | n ∈ A ∧ B < n})) :
    Irrational (erdosSupportSeries b A) := by
  sorry
/-- States lem:tail-transfer from the long record for Erdős problem #257. Transported from Erdos249257.irrational_erdosSupportSeries_tail_of_irrational in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_erdosSupportSeries_tail_of_irrational (b : ℕ) (A : Set ℕ)
    (hb : 2 ≤ b) (B : ℕ) (h : Irrational (erdosSupportSeries b A)) :
    Irrational (erdosSupportSeries b {n : ℕ | n ∈ A ∧ B < n}) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAG

namespace PalomarCorpus.E257.PaperStatementsAF
open Set
/-- For a displayed residual `p / (2L)`, the integer numerator of its excess above the next dyadic point `2^-(n+1)`. Indeed, `p/(2L) - 2^-(n+1) = E/(2^(n+1)L)`. Keeping `E` integral makes the unresolved skipped-branch comparison an exact Diophantine inequality rather than a real-valued phase estimate. Local copy of Erdos249257.nextDyadicExcessIntNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def nextDyadicExcessIntNumerator (p : ℤ) (n L : ℕ) : ℤ :=
  ((2 ^ n : ℕ) : ℤ) * p - (L : ℤ)
/-- States lem:dyadic-excess-reformulation from the long record for Erdős problem #257. Transported from Erdos249257.divInt_le_nextDyadic_iff_excess_nonpos in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem divInt_le_nextDyadic_iff_excess_nonpos
    (p : ℤ) (n L : ℕ) (hL : 0 < L) :
    Rat.divInt p ((2 * L : ℕ) : ℤ) ≤ 1 / (2 : ℚ) ^ (n + 1) ↔
      nextDyadicExcessIntNumerator p n L ≤ 0 := by
  sorry
end PalomarCorpus.E257.PaperStatementsAF
