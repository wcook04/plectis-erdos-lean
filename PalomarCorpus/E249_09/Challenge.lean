/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record sections 6.2.1 to 6.2.2: initial implications; equivalent quantified certificate conditions

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open Filter
open Topology
open ArithmeticFunction
open Finset
open scoped BigOperators

namespace PalomarCorpus.E249_09.Shared
/-- The universal period `lcm(1, 2, ..., t)`, given recursively by `periodLcm 0 = 1` and `periodLcm (t + 1) = lcm (periodLcm t) (t + 1)`. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
/-- The binary totient tail `R_N = ∑_{j ≥ 1} φ(N + j) / 2 ^ j`, a real number satisfying `2 ^ N S = Φ_N + R_N`, where `S = ∑_{n ≥ 1} φ(n) / 2 ^ n` and `Φ_N = ∑_{n ≤ N} φ(n) 2 ^ (N - n)` is an integer. It obeys `0 < R_N ≤ N + 1` for `N ≥ 1`. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- The signed binary discrepancy `D_{h,N,L} = ∑_{j < L} (φ(N + h + 1 + j) - φ(N + 1 + j)) 2 ^ (L - 1 - j)` between two length-`L` totient windows separated by the shift `h`, an integer satisfying `|2 ^ L (R_{N + h} - R_N) - D_{h,N,L}| ≤ N + h + L + 2`. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
end PalomarCorpus.E249_09.Shared

namespace PalomarCorpus.E249.PaperStatementsBD
open Filter
open Topology
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_divisor_count_prime_support in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem composite_dilation_divisor_count_prime_support (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (hx1 : 1 ≤ x) (hAprime : ∀ d ∈ A, d.Prime) :
    supportCoeff A (a * x) = supportCoeff A x + (if a ∣ x then 0 else 1) := by
  sorry
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.lambert_support_series in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lambert_support_series (A : Set ℕ) :
    (∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((2 : ℝ) ^ a - 1)) a) =
      ∑' m : ℕ, (supportCoeff A (m + 1) : ℝ) / (2 : ℝ) ^ (m + 1) := by
  sorry
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.lambert_support_series_restricted in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lambert_support_series_restricted (A : Set ℕ) :
    (∑' a : ℕ, Set.indicator {a ∈ A | 1 ≤ a} (fun a => (1 : ℝ) / ((2 : ℝ) ^ a - 1)) a) =
      ∑' m : ℕ, (supportCoeff A (m + 1) : ℝ) / (2 : ℝ) ^ (m + 1) := by
  sorry
end PalomarCorpus.E249.PaperStatementsBD

namespace PalomarCorpus.E249.PaperStatementsBN
open ArithmeticFunction
/-- The Euler totient as an integer-valued arithmetic function. Local copy of MersenneLambertLadder.totientZ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientZ : ArithmeticFunction ℤ :=
  ⟨fun n => (Nat.totient n : ℤ), by simp⟩
/-- **The primitive-conductor weight** `A = φ * μ` (Dirichlet convolution). `A(n)` counts the primitive Dirichlet characters of conductor `n` (OEIS A007431); it is multiplicative, nonnegative, vanishes exactly on `n ≡ 2 (mod 4)`, and satisfies `A(p) = p - 2`, `A(p^e) = (p-1)²·p^(e-2)`. Local copy of MersenneLambertLadder.primWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primWeight : ArithmeticFunction ℤ := totientZ * moebius
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_mul_zeta in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_convolution_weight_mul_zeta (n : ℕ) :
    ∑ e ∈ n.divisors, primWeight e = (Nat.totient n : ℤ) := by
  sorry
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_not_periodic in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_convolution_weight_not_periodic :
    ¬ ∃ p : ℕ, 0 < p ∧
      ∀ n : ℕ, primWeight (n + p) =
        primWeight n := by
  sorry
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_prime in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_convolution_weight_prime {p : ℕ} (hp : p.Prime) :
    primWeight p = (p : ℤ) - 2 := by
  sorry
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_unbounded in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_convolution_weight_unbounded :
    ¬ ∃ B : ℕ, ∀ n : ℕ, primWeight n ≤ (B : ℤ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsBN

namespace PalomarCorpus.E249.PaperStatementsAU
open Finset
export PalomarCorpus.E249_09.Shared (certifiedKill totientTail windowDiscrepancy)
/-- Second-difference window discrepancy `A₂ = A(h, N+h, L) - A(h, N, L)`: the depth-`L` truncation of `2^L·((R_{N+2h} - R_{N+h}) - (R_{N+h} - R_N))`. Local copy of Erdos249257.TotientTailPeriodKiller.windowDiscrepancy2, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowDiscrepancy2 (h N L : ℕ) : ℤ :=
  windowDiscrepancy h (N + h) L - windowDiscrepancy h N L
/-- The decidable rank-2 certificate: the residue of `A₂` modulo `2^L` avoids the radius-`2(N+2h+L+2)` neighbourhood of `0`. The doubled radius pays for two window truncations; in exchange the second difference cancels the whole `H·C` clean shadow on the lcm cone. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedRank2Kill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedRank2Kill (h N L : ℕ) : Prop :=
  (2 * ((N : ℤ) + 2 * h + L + 2)) < windowDiscrepancy2 h N L % 2 ^ L ∧
    windowDiscrepancy2 h N L % 2 ^ L < 2 ^ L - 2 * ((N : ℤ) + 2 * h + L + 2)
/-- States catalogue:cert:b2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_period_multiple_certificate_supply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_period_multiple_certificate_supply
    (hsupply : ∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
      ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill (m * h₀) N L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States catalogue:cert:b2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.period_multiple_certificate_at_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem period_multiple_certificate_at_one {h₀ N L : ℕ}
    (hcert : certifiedKill h₀ N L) : certifiedKill (1 * h₀) N L := by
  sorry
/-- States catalogue:cert:b2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.period_multiple_certificate_supply_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem period_multiple_certificate_supply_iff :
    (∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
        ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill (m * h₀) N L) ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States catalogue:cert:b2 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.rational_forces_period_multiple_integrality in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_forces_period_multiple_integrality
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ, ∀ m N : ℕ, N₀ ≤ N →
      totientTail (N + m * h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States catalogue:cert:b9a from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.second_difference_cell_one_eight in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem second_difference_cell_one_eight :
    certifiedKill 1 8 8 ∧
      (∀ L : ℕ, L ≤ 8 → ¬ certifiedRank2Kill 1 8 L) ∧
      certifiedRank2Kill 1 8 9 := by
  sorry
/-- States catalogue:cert:b9a from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.second_difference_certificate_sound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem second_difference_certificate_sound {h N L : ℕ}
    (hlow : 2 * ((N : ℤ) + 2 * h + L + 2) <
      (windowDiscrepancy h (N + h) L - windowDiscrepancy h N L) % 2 ^ L)
    (hhigh : (windowDiscrepancy h (N + h) L - windowDiscrepancy h N L) % 2 ^ L <
      2 ^ L - 2 * ((N : ℤ) + 2 * h + L + 2)) :
    totientTail (N + 2 * h) - 2 * totientTail (N + h) + totientTail N ∉
      Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States catalogue:cert:b9a from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.second_difference_error_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem second_difference_error_bound (h N L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (N + 2 * h) - 2 * totientTail (N + h) + totientTail N) -
        ((windowDiscrepancy h (N + h) L - windowDiscrepancy h N L : ℤ) : ℝ)| ≤
      2 * ((N : ℝ) + 2 * h + L + 2) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAU

namespace PalomarCorpus.E249.PaperStatementsA
open Finset
export PalomarCorpus.E249_09.Shared (certifiedKill periodLcm totientTail windowDiscrepancy)
/-- States catalogue:cert:b4 from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.eq_prime_pow_of_not_dvd_periodLcm in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem eq_prime_pow_of_not_dvd_periodLcm {t j : ℕ} (hj : 0 < j) (hlt : j < 2 * t)
    (hnd : ¬ j ∣ periodLcm t) :
    ∃ p k : ℕ, Nat.Prime p ∧ j = p ^ k ∧ t < j := by
  sorry
/-- States catalogue:cert:b8 from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_cone_nonintegrality_supply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totient_series_of_lcm_cone_nonintegrality_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m : ℕ, 0 < q ∧
      totientTail (q * periodLcm t + m * periodLcm t) - totientTail (q * periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States catalogue:cert:b8 from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_diagonal_nonintegrality_supply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totient_series_of_lcm_diagonal_nonintegrality_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧
      totientTail (periodLcm t + periodLcm t) - totientTail (periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States catalogue:cert:b8 from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.periodLcm_diagonal_kill_iff_tail_diff_notMem_int in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem periodLcm_diagonal_kill_iff_tail_diff_notMem_int (t : ℕ) :
    (∃ L, certifiedKill (periodLcm t) (periodLcm t) L) ↔
      totientTail (periodLcm t + periodLcm t) - totientTail (periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsA

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
export PalomarCorpus.E249_09.Shared (certifiedKill periodLcm totientTail windowDiscrepancy)
/-- The window step `a_n = φ(n+h) - φ(n)` driving the carry recurrence. Local copy of Erdos249257.TotientTailPeriodKiller.deltaTotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
/-- The integer carry orbit launched from candidate `d` at position `N`: `orbit 0 = d`, `orbit (i+1) = 2·orbit i - a_{N+i+1}`. If `D_h(N)` is the integer `d`, this orbit equals `D_h(N+i)` forever. Local copy of Erdos249257.TotientTailPeriodKiller.carryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryOrbit (h N : ℕ) (d : ℤ) : ℕ → ℤ
  | 0 => d
  | i + 1 => 2 * carryOrbit h N d i - deltaTotient h (N + i + 1)
/-- States catalogue:cert:b6, prop:B6-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.certificate_denominator_exclusion in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certificate_denominator_exclusion (r : ℚ) (h N L : ℕ)
    (hcert : certifiedKill h N L) (hden : r.den ∣ 2 ^ N * (2 ^ h - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) := by
  sorry
/-- States catalogue:cert:b5 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.clean_lcm_ray_factorisation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem clean_lcm_ray_factorisation (t j q : ℕ) (hdvd : j ∣ periodLcm t)
    (hclean : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ (periodLcm t / j)) :
    q * periodLcm t + j = j * (q * (periodLcm t / j) + 1) ∧
    Nat.Coprime j (q * (periodLcm t / j) + 1) ∧
    Nat.totient (q * periodLcm t + j) = Nat.totient j * Nat.totient (q * (periodLcm t / j) + 1) := by
  sorry
/-- States catalogue:cert:b12, prop:B12cons from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_test_sound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_carry_test_sound (h N K : ℕ)
    (htest : ∀ z : ℤ, |z| ≤ (N + h + 1 : ℤ) →
      ∃ i : ℕ, i ≤ K ∧ (N + i + h + 2 : ℤ) ≤ |carryOrbit h N z i|) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States catalogue:cert:b6, prop:B6-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_flatness in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lcm_grid_flatness
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ q m : ℕ, 0 < q →
      totientTail ((q + m) * periodLcm t) - totientTail (q * periodLcm t)
        ∈ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States catalogue:cert:b6 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_fractional_parts in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lcm_grid_fractional_parts
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ q m : ℕ, 0 < q →
      Int.fract (totientTail ((q + m) * periodLcm t)) =
        Int.fract (totientTail (q * periodLcm t)) := by
  sorry
/-- States catalogue:cert:b7 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_multiplier_positive in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lcm_grid_multiplier_positive (t q m L : ℕ)
    (hc : certifiedKill (m * periodLcm t) (q * periodLcm t) L) : 0 < m := by
  sorry
/-- States catalogue:cert:b6, catalogue:cert:b7, prop:B6-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_supply_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lcm_grid_supply_iff :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m L : ℕ, 0 < q ∧
        certifiedKill (m * periodLcm t) (q * periodLcm t) L := by
  sorry
/-- States catalogue:cert:b5 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.unclean_lcm_ray_counterexample in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem unclean_lcm_ray_counterexample :
    2 ∣ periodLcm 2 ∧ Nat.totient (periodLcm 2 + 2) = 2 ∧
    Nat.totient 2 * Nat.totient (periodLcm 2 / 2 + 1) = 1 ∧
    ¬ (∀ p : ℕ, Nat.Prime p → p ∣ 2 → p ∣ (periodLcm 2 / 2)) := by
  sorry
/-- States catalogue:cert:b9a from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.abs_tail_diff_scaled_sub_window_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem abs_tail_diff_scaled_sub_window_le (h N L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (N + h) - totientTail N) -
        ((windowDiscrepancy h N L : ℤ) : ℝ)| ≤ (N : ℝ) + h + L + 2 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAT

namespace PalomarCorpus.E249.PaperStatementsAD
open Finset
export PalomarCorpus.E249_09.Shared (totientTail)
/-- States catalogue:cert:b8 from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_all_tail_diffs_nonintegral in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totient_series_iff_all_tail_diffs_nonintegral :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N : ℕ,
        totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAD

namespace PalomarCorpus.E249.PaperStatementsAX
open scoped BigOperators
open Finset
export PalomarCorpus.E249_09.Shared (periodLcm totientTail)
/-- The depth-`L` window numerator `P_L(M) = Σ_{j<L} φ(M+1+j)·2^{L-1-j}`: the integer layer of `2^L·R_M`, exact up to the one-sided deep tail `0 ≤ 2^L·R_M - P_L(M) ≤ M+L+2`. Local copy of Erdos249257.TotientTailPeriodKiller.windowNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowNumerator (M L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range L, Nat.totient (M + 1 + j) * 2 ^ (L - 1 - j)
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.paperGridNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperGridNumerator (H L q : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 L, Nat.totient (q * H + j) * 2 ^ (L - j)
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.paperGridCertificate, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperGridCertificate (H L : ℕ) (Q : Finset ℕ) : Prop :=
  ∀ qi ∈ Q, ∃ qj ∈ Q,
    (qj * H + L + 2 : ℤ) <
      ((paperGridNumerator H L qi : ℤ) - paperGridNumerator H L qj) % 2 ^ L
/-- States catalogue:cert:b10a, prop:B10 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_nonintegral_pair in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_grid_nonintegral_pair (H L : ℕ) (Q : Finset ℕ) (hQ : Q.Nonempty)
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : paperGridCertificate H L Q) :
    ∃ qi ∈ Q, ∃ qj ∈ Q,
      totientTail (qj * H) - totientTail (qi * H) ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States catalogue:cert:b10b, prop:B10 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_supply_irrational in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_grid_supply_irrational
    (hs : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ, ∃ Q : Finset ℕ,
      Q.Nonempty ∧ (∀ q ∈ Q, 0 < q) ∧
      (∀ q ∈ Q, (q * periodLcm t + L + 2 : ℤ) < 2 ^ L) ∧
      paperGridCertificate (periodLcm t) L Q) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States catalogue:cert:b10a, catalogue:cert:b10b, prop:B10 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.paperGridNumerator_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperGridNumerator_eq (H L q : ℕ) :
    paperGridNumerator H L q = windowNumerator (q * H) L := by
  sorry
end PalomarCorpus.E249.PaperStatementsAX

namespace PalomarCorpus.E249.PaperStatementsAJ
/-- States catalogue:cert:b12, prop:B12cons from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_candidate_count in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_carry_candidate_count (h N : ℕ) :
    (Finset.Icc (-(N + h + 1 : ℤ)) (N + h + 1)).card = 2 * (N + h + 1) + 1 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAJ
