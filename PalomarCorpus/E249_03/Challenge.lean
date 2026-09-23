/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record section 2.3: limits of specific reductions and estimates

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open Finset
open Filter
open Set

namespace PalomarCorpus.E249.PaperStatementsAK
/-- States prop:b4 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.twoAdic_pulse_defining_congruence in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem twoAdic_pulse_defining_congruence (H K B : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, B < p ∧ H + K < p ∧ p.Prime ∧
      p ≡ 1 + 2 ^ (K - 1) [MOD 2 ^ K] ∧ 1 + 2 ^ (K - 1) ≤ p := by
  sorry
/-- States prop:b4 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.twoAdic_pulse_error_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem twoAdic_pulse_error_bound (H K p : ℕ) (hKp : K ≤ p)
    (hp : 2 ^ (K - 1) < p) :
    (p - K) + H + K + 2 = p + H + 2 ∧ 2 ^ (K - 1) < p + H + 2 := by
  sorry
/-- States prop:b2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.two_point_sample_numerical_requirement in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_point_sample_numerical_requirement :
    2 * ((2 : ℝ)) ^ 2 / 5 = 8 / 5 ∧ (8 : ℝ) / 5 ≤ 2 * (9 / 10) ^ 2 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAK

namespace PalomarCorpus.E249.PaperStatementsAU
open Finset
/-- The window discrepancy `A_{h,N,L} = ∑_{j=0}^{L-1} (φ(N+h+1+j) - φ(N+1+j))·2^{L-1-j}`: the depth-`L` truncation of `2^L·(R_{N+h} - R_N)`. Local copy of Erdos249257.TotientTailPeriodKiller.windowDiscrepancy, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- Predicate for a real quantity to be an integer. Local copy of Erdos249257.DiagonalPincerDecomposition.IsIntegralValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsIntegralValue (x : ℝ) : Prop := x ∈ Set.range ((↑) : ℤ → ℝ)
/-- The residue angle used by the first additive character. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstAngle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi *
    (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
      ((2 ^ L : ℤ) : ℝ))
/-- The complex first additive character of the endpoint discrepancy. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstExp, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((windowFirstAngle h N L : ℂ) * Complex.I)
/-- Fixed-shift fibre-free counted window-phase anti-concentration. The sample `T` may be any nonempty subset of a cofinal dyadic block. Local copy of Erdos249257.TotientTailPeriodKiller.DTWWindowSeparatedPairsAt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DTWWindowSeparatedPairsAt (h : ℕ) : Prop :=
  ∀ X₀ : ℕ, ∃ X L : ℕ, ∃ T : Finset ℕ,
      ∃ P : Finset (ℕ × ℕ), ∃ δ : ℝ,
      max X₀ 1 ≤ X ∧
      T.Nonempty ∧
      T ⊆ Finset.Ico X (2 * X) ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      P ⊆ T.product T ∧
      0 ≤ δ ∧
      (∀ p ∈ P,
        δ ≤ ‖windowFirstExp h p.1 L - windowFirstExp h p.2 L‖) ∧
      2 * (T.card : ℝ) ^ 2 / 5 ≤ (P.card : ℝ) * δ ^ 2
/-- Fibre-free counted window-phase anti-concentration at every positive shift; neither primality nor a pivot factorization is part of the statement. Local copy of Erdos249257.TotientTailPeriodKiller.DTWWindowSeparatedPairs, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DTWWindowSeparatedPairs : Prop :=
  ∀ h : ℕ, 0 < h → DTWWindowSeparatedPairsAt h
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
/-- **The supply normal form.** For every ray `d ≥ 1` and every basepoint threshold `c`, some multiple period `t·d` admits a certified kill at some `N ≥ c`. The odd part of a hypothetical denominator selects the ray; the kill contradicts the tail-period law on it. Local copy of ErdosProblems.Erdos249.PeriodMultipleEscape.PeriodMultipleKillSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PeriodMultipleKillSupply : Prop :=
  ∀ d : ℕ, 0 < d → ∀ c : ℕ,
    ∃ t N L : ℕ, 0 < t ∧ c ≤ N ∧ certifiedKill (t * d) N L
/-- States prop:b2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.three_particular_equivalences in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem three_particular_equivalences :
    (PeriodMultipleKillSupply ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
      ∧ (DTWWindowSeparatedPairs ↔
          Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
      ∧ (∀ H p q : ℕ, 0 < p → 0 < q →
          ((IsIntegralValue (totientTail (2 * H) - totientTail H)
              ∧ IsIntegralValue (totientTail (2 * (p * H)) - totientTail (p * H))
              ∧ IsIntegralValue (totientTail (2 * (q * H)) - totientTail (q * H))
              ∧ IsIntegralValue
                  (totientTail (2 * (p * q * H)) - totientTail (p * q * H)))
            ↔ IsIntegralValue (totientTail (2 * H) - totientTail H))) := by
  sorry
/-- States prop:b4 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.twoAdic_pulse_construction_never_certifies in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem twoAdic_pulse_construction_never_certifies
    (H K : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, p.Prime ∧ H + K < p ∧ 2 ^ (K - 1) < p ∧
      windowDiscrepancy H (p - K) K ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      ¬ certifiedKill H (p - K) K := by
  sorry
end PalomarCorpus.E249.PaperStatementsAU

namespace PalomarCorpus.E249.PaperStatementsAZ
open Filter
open Set
/-- The radius of the balanced-pulse family at location `m`. Local copy of Erdos249257.balancedPulseRadius, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def balancedPulseRadius (m : ℕ) : ℕ := (m + 1) / 2
/-- A two-site pulse whose mass can be moved from position `m` to `m+1` without changing its binary-series value. Local copy of Erdos249257.balancedPulseCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def balancedPulseCoeff (m r : ℕ) : ℕ → ℕ := fun n ↦
  if n = m then balancedPulseRadius m - r
  else if n = m + 1 then 2 * r
  else 0
/-- The binary coefficient series `X_c = ∑_{n≥1} c(n)/2^n`. Local copy of Erdos249257.binaryCoeffSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)
/-- The scaled tail `T_c(N) = ∑_{j≥1} c(N+j)/2^j`. Local copy of Erdos249257.binaryCoeffTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)
/-- States prop:b5 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_common_history in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem balancedPulse_common_history (m : ℕ) (hm : 2 ≤ m) (r : ℕ)
    (hr : r ≤ balancedPulseRadius m) :
    (∀ n : ℕ, n ≠ m → n ≠ m + 1 → balancedPulseCoeff m r n = 0)
      ∧ balancedPulseCoeff m r m = balancedPulseRadius m - r
      ∧ balancedPulseCoeff m r (m + 1) = 2 * r
      ∧ (∀ n : ℕ, balancedPulseCoeff m r n ≤ n)
      ∧ binaryCoeffSeries (balancedPulseCoeff m r)
          = (balancedPulseRadius m : ℝ) / 2 ^ m
      ∧ (∀ N : ℕ, N < m → binaryCoeffTail (balancedPulseCoeff m r) N
          = (balancedPulseRadius m : ℝ) / 2 ^ (m - N))
      ∧ binaryCoeffTail (balancedPulseCoeff m r) m = (r : ℝ) := by
  sorry
/-- States prop:b5 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_label_lower_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem balancedPulse_label_lower_bound {m : ℕ} {Λ : Type*} [Fintype Λ]
    (label : Fin (balancedPulseRadius m + 1) → Λ) (decode : Λ → ℕ)
    (hdecode : ∀ r, decode (label r) = r) :
    balancedPulseRadius m + 1 ≤ Fintype.card Λ := by
  sorry
/-- States prop:b5 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_no_decoder_from_common_state in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem balancedPulse_no_decoder_from_common_state
    {State : Type*} (m : ℕ) (hm : 2 ≤ m)
    (state : Fin (balancedPulseRadius m + 1) → State)
    (hstate : ∀ r, state r = state ⟨0, by simp⟩) :
    ¬ ∃ decode : State → ℕ, ∀ r, decode (state r) = r := by
  sorry
/-- States prop:b5 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_series in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem balancedPulse_series (m : ℕ) (hm : 2 ≤ m) (r : ℕ)
    (hr : r ≤ balancedPulseRadius m) :
    binaryCoeffSeries (balancedPulseCoeff m r)
      = (balancedPulseRadius m : ℝ) / 2 ^ m := by
  sorry
/-- States prop:b5 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_tail_at in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem balancedPulse_tail_at (m r : ℕ) (hm : 2 ≤ m)
    (hr : r ≤ balancedPulseRadius m) :
    binaryCoeffTail (balancedPulseCoeff m r) m = (r : ℝ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAZ

namespace PalomarCorpus.E249.PaperStatementsD
open Filter
open Set
/-- The exact binary affine orbit driven by the fresh coefficient word `a`. Local copy of Erdos249257.affineBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)
/-- States prop:b5 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.affineBinaryOrbit_difference_and_reset in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem affineBinaryOrbit_difference_and_reset (a : ℕ → ℤ) (u0 v0 : ℤ) (L : ℕ) :
    affineBinaryOrbit a u0 L - affineBinaryOrbit a v0 L = (2 : ℤ) ^ L * (u0 - v0)
      ∧ affineBinaryOrbit a u0 L ≡ affineBinaryOrbit a v0 L [ZMOD (2 : ℤ) ^ L] := by
  sorry
end PalomarCorpus.E249.PaperStatementsD

namespace PalomarCorpus.E249.PaperStatementsG
/-- The crude two-tail cost attached to an inverse/adjugate row. Recovering `φ(x)` as `2 R_(x-1) - R_x` and applying `R_M ≤ M+2` termwise gives the factor `2(x+1) + (x+2)`. Local copy of Erdos249257.totientAdjugateTailCost, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientAdjugateTailCost
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (x : ι → ℕ) : ℚ :=
  ∑ i, |w i| * (2 * ((x i : ℚ) + 1) + ((x i : ℚ) + 2))
/-- States prop:b6 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.b6_adjugate_tail_cost_floor in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem b6_adjugate_tail_cost_floor
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (x : ι → ℕ)
    (hisolate : ∑ i, w i * (Nat.totient (x i) : ℚ) = 1) :
    (1 : ℚ) ≤ ∑ i, |w i| * (Nat.totient (x i) : ℚ)
      ∧ (∑ i, |w i| * (Nat.totient (x i) : ℚ)) ≤ ∑ i, |w i| * (x i : ℚ)
      ∧ totientAdjugateTailCost w x = ∑ i, |w i| * (3 * (x i : ℚ) + 4)
      ∧ (3 : ℚ) ≤ totientAdjugateTailCost w x
      ∧ ¬ totientAdjugateTailCost w x < 1 := by
  sorry
/-- States prop:b6 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.b6_compressed_adjoint_identity_impossible in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem b6_compressed_adjoint_identity_impossible
    {Q v : ℕ} (hQ : 0 < Q) (hv : 0 < v) {A b : ℤ}
    (hA : A ≠ 0) (hid : (Q : ℤ) * (v : ℤ) * A = b) :
    ¬ |b| < (Q : ℤ) * (v : ℤ) := by
  sorry
/-- States prop:b6 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.b6_rankOneSubrankQuotient_sub_totientSeries_offset_gt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem b6_rankOneSubrankQuotient_sub_totientSeries_offset_gt
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (1 : ℝ) / 480 <
      (∑ d ∈ Finset.Icc 1 Y,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1) ^ (e + 2)) ^ 2 /
        (∑ d ∈ Finset.Icc 1 Y,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1) ^ (2 * e + 2)) -
        ((∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2) := by
  sorry
end PalomarCorpus.E249.PaperStatementsG

namespace PalomarCorpus.E249.PaperStatementsI
open Finset
/-- The window step `a_n = φ(n+h) - φ(n)` driving the carry recurrence. Local copy of Erdos249257.TotientTailPeriodKiller.deltaTotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
/-- The depth-`L` cleared binary prefix, accumulated from left to right. Equivalently this is `∑ j < L, a (n+j) * 2^(L-1-j)`. Local copy of Erdos249257.TotientTailPeriodKiller.dyadicClearedPrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicClearedPrefix (a : ℕ → ℤ) (n : ℕ) : ℕ → ℤ
  | 0 => 0
  | L + 1 => 2 * dyadicClearedPrefix a n L + a (n + L)
/-- `periodLcm t = lcm(1, …, t)`: the universal period at scale `t`. Every primitive period `h₀ ≤ t` divides it. Local copy of Erdos249257.TotientTailPeriodKiller.periodLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
/-- State anchors corresponding to the exact whole-ray letters at `q * periodLcm t`, for `2 ≤ q < t`. Local copy of Erdos249257.TotientTailPeriodKiller.lcmAnchorStates, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmAnchorStates (t : ℕ) : Finset ℕ :=
  (Finset.Ico 2 t).image (fun q => (q - 1) * periodLcm t)
/-- A state which is `-A` on a finite anchor set and zero elsewhere. Local copy of Erdos249257.TotientTailPeriodKiller.sparsePulseState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sparsePulseState (A : ℤ) (S : Finset ℕ) (k : ℕ) : ℤ :=
  if k ∈ S then -A else 0
/-- The zero-based forcing letter determined by `c_{i+1} = 2c_i - a_i`. Local copy of Erdos249257.TotientTailPeriodKiller.sparsePulseLetter, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sparsePulseLetter (A : ℤ) (S : Finset ℕ) (i : ℕ) : ℤ :=
  2 * sparsePulseState A S i - sparsePulseState A S (i + 1)
/-- The LCM pulse forcing word. Local copy of Erdos249257.TotientTailPeriodKiller.lcmAnchorPulseLetter, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmAnchorPulseLetter (t i : ℕ) : ℤ :=
  sparsePulseLetter (Nat.totient (periodLcm t) : ℤ) (lcmAnchorStates t) i
/-- The LCM pulse state with amplitude `φ(periodLcm t)`. Local copy of Erdos249257.TotientTailPeriodKiller.lcmAnchorPulseState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmAnchorPulseState (t k : ℕ) : ℤ :=
  sparsePulseState (Nat.totient (periodLcm t) : ℤ) (lcmAnchorStates t) k
/-- Evaluation of a finite integer shift polynomial on a sequence. A term `(h, q)` contributes `q * f(n+h)`. Local copy of Erdos249257.TotientTailPeriodKiller.shiftLinearCombination, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftLinearCombination : List (ℕ × ℤ) → (ℕ → ℤ) → (ℕ → ℤ)
  | [], _ => fun _ => 0
  | (h, q) :: terms, f => fun n =>
      q * f (n + h) + shiftLinearCombination terms f n
/-- Pulse letters transformed by the same shift polynomial. Local copy of Erdos249257.TotientTailPeriodKiller.lcmAnchorShiftPolynomialLetter, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmAnchorShiftPolynomialLetter
    (t : ℕ) (terms : List (ℕ × ℤ)) : ℕ → ℤ :=
  shiftLinearCombination terms (lcmAnchorPulseLetter t)
/-- Pulse state transformed by an arbitrary finite integer shift polynomial. Local copy of Erdos249257.TotientTailPeriodKiller.lcmAnchorShiftPolynomialState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmAnchorShiftPolynomialState
    (t : ℕ) (terms : List (ℕ × ℤ)) : ℕ → ℤ :=
  shiftLinearCombination terms (lcmAnchorPulseState t)
/-- The `ℓ1` weight of a finite shift polynomial. Local copy of Erdos249257.TotientTailPeriodKiller.shiftLinearWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftLinearWeight : List (ℕ × ℤ) → ℤ
  | [] => 0
  | (_, q) :: terms => |q| + shiftLinearWeight terms
/-- States prop:b6 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.b6_synthetic_sequence_prescribed_differences in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem b6_synthetic_sequence_prescribed_differences {t : ℕ} (ht : 3 ≤ t) :
    (∀ k : ℕ, k ∈ lcmAnchorStates t →
        lcmAnchorPulseState t k = -(Nat.totient (periodLcm t) : ℤ))
      ∧ (∀ k : ℕ, k ∉ lcmAnchorStates t → lcmAnchorPulseState t k = 0)
      ∧ (∀ q : ℕ, 2 ≤ q → q < t →
          (q - 1) * periodLcm t ∈ lcmAnchorStates t)
      ∧ (∀ i : ℕ, lcmAnchorPulseLetter t i =
          2 * lcmAnchorPulseState t i - lcmAnchorPulseState t (i + 1))
      ∧ ∀ q : ℕ, 2 ≤ q → q < t →
          lcmAnchorPulseLetter t ((q - 1) * periodLcm t - 1)
              = (Nat.totient (periodLcm t) : ℤ)
            ∧ lcmAnchorPulseLetter t ((q - 1) * periodLcm t - 1)
              = deltaTotient (periodLcm t) (q * periodLcm t) := by
  sorry
/-- States prop:b6 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.b6_synthetic_shift_combinations_same_form in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem b6_synthetic_shift_combinations_same_form
    (t : ℕ) (terms : List (ℕ × ℤ)) :
    (∀ i : ℕ,
        lcmAnchorShiftPolynomialState t terms i =
          shiftLinearCombination terms (lcmAnchorPulseState t) i)
      ∧ (∀ i : ℕ,
          lcmAnchorShiftPolynomialLetter t terms i =
            shiftLinearCombination terms (lcmAnchorPulseLetter t) i)
      ∧ (∀ i : ℕ,
          lcmAnchorShiftPolynomialLetter t terms i =
            2 * lcmAnchorShiftPolynomialState t terms i -
              lcmAnchorShiftPolynomialState t terms (i + 1))
      ∧ (∀ n L : ℕ,
          dyadicClearedPrefix (lcmAnchorShiftPolynomialLetter t terms) n L =
            (2 : ℤ) ^ L * lcmAnchorShiftPolynomialState t terms n -
              lcmAnchorShiftPolynomialState t terms (n + L))
      ∧ (∀ i : ℕ, |lcmAnchorShiftPolynomialState t terms i| ≤
          shiftLinearWeight terms * (Nat.totient (periodLcm t) : ℤ))
      ∧ (∀ i : ℕ, |lcmAnchorShiftPolynomialLetter t terms i| ≤
          shiftLinearWeight terms * (2 * (Nat.totient (periodLcm t) : ℤ))) := by
  sorry
end PalomarCorpus.E249.PaperStatementsI
