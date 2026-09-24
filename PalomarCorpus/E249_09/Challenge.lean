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

open scoped BigOperators
open Finset
open scoped ArithmeticFunction.Moebius
open Filter
open Topology
open ArithmeticFunction

namespace PalomarCorpus.E249_09.Shared
/-- Support divisors created by multiplication by `a`, excluding the distinguished divisor `a` itself. Local copy of Erdos249257.CompositeDilationDefect.compositeDilationDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def compositeDilationDefect (A : Set ℕ) (a x : ℕ) : ℕ :=
  by
    classical
    exact ((a * x).divisors.filter fun d =>
      d ∈ A ∧ ¬ d ∣ x ∧ d ≠ a).card
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

namespace PalomarCorpus.E249.PaperStatementsAX
open scoped BigOperators
open Finset
export PalomarCorpus.E249_09.Shared (totientTail windowDiscrepancy)
/-- The integer window obtained from the three cone differences based at `H`. Local copy of Erdos249257.JointExponentTransport.joint35ConeWindow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def joint35ConeWindow (H L : ℕ) : ℤ :=
  windowDiscrepancy (14 * H) H L -
    3 * windowDiscrepancy (2 * H) H L -
    2 * windowDiscrepancy (4 * H) H L
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.joint35ConeWindow_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem joint35ConeWindow_eq (H L : ℕ) :
    joint35ConeWindow H L
      = ∑ j ∈ Finset.range L,
          ((Nat.totient (15 * H + (j + 1)) : ℤ)
            - 3 * (Nat.totient (3 * H + (j + 1)) : ℤ)
            - 2 * (Nat.totient (5 * H + (j + 1)) : ℤ)
            + 4 * (Nat.totient (H + (j + 1)) : ℤ)) * 2 ^ (L - (j + 1)) := by
  sorry
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.joint35_nonintegral_of_separated_window in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem joint35_nonintegral_of_separated_window {H L : ℕ} (hH : 1 ≤ H)
    (hlow : ((19 * H + 5 * L + 5 : ℕ) : ℤ) < joint35ConeWindow H L % 2 ^ L)
    (hhigh : joint35ConeWindow H L % 2 ^ L
      < 2 ^ L - ((19 * H + 5 * L + 5 : ℕ) : ℤ)) :
    (totientTail (15 * H) - 3 * totientTail (3 * H)
      - 2 * totientTail (5 * H) + 4 * totientTail H) ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.joint35_truncation_error in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem joint35_truncation_error (H L : ℕ) (hH : 1 ≤ H) :
    (2 : ℝ) ^ L * (totientTail (15 * H) - 3 * totientTail (3 * H)
        - 2 * totientTail (5 * H) + 4 * totientTail H)
        - (joint35ConeWindow H L : ℝ)
      = (totientTail (15 * H + L) + 4 * totientTail (H + L))
        - (3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L))
    ∧ |(2 : ℝ) ^ L * (totientTail (15 * H) - 3 * totientTail (3 * H)
        - 2 * totientTail (5 * H) + 4 * totientTail H)
        - (joint35ConeWindow H L : ℝ)|
      ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ)
    ∧ (0 ≤ totientTail (15 * H + L) + 4 * totientTail (H + L)
        ∧ totientTail (15 * H + L) + 4 * totientTail (H + L)
          ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ))
    ∧ (0 ≤ 3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L)
        ∧ 3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L)
          ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ)) := by
  sorry
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientTail_enclosure in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totientTail_enclosure (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ totientTail n ∧ totientTail n ≤ (n : ℝ) + 1 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAX

namespace PalomarCorpus.E249.PaperStatementsBE
open scoped BigOperators
open scoped ArithmeticFunction.Moebius
/-- Least positive shift sending `N` to a multiple of `d`. Local copy of Erdos249257.ExponentOnlyTransport.transportResidueOffset, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def transportResidueOffset (d N : ℕ) : ℕ := d - N % d
/-- Exact Möbius residue kernel, stated locally so this disjoint transport owner can be validated independently of adjacent projection files. Local copy of Erdos249257.ExponentOnlyTransport.transportResidueKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def transportResidueKernel (d N : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    (2 : ℝ) ^ (d - transportResidueOffset d N) *
      (((N + transportResidueOffset d N : ℕ) : ℝ) /
          ((d : ℝ) * ((2 : ℝ) ^ d - 1)) +
        1 / (((2 : ℝ) ^ d - 1) ^ 2))
/-- The manuscript's `K_d(N) = N/(d(2ᵈ-1)) + 2ᵈ/(2ᵈ-1)²`, the `d`th term of the Möbius expansion of `R_N` with its sign `μ(d)` removed. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.mobiusTermKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusTermKernel (d N : ℕ) : ℝ :=
  (N : ℝ) / ((d : ℝ) * ((2 : ℝ) ^ d - 1)) + (2 : ℝ) ^ d / (((2 : ℝ) ^ d - 1) ^ 2)
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.transportResidueKernel_eq_mobiusTermKernel in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem transportResidueKernel_eq_mobiusTermKernel {d N : ℕ}
    (hd : 0 < d) (hdN : d ∣ N) :
    transportResidueKernel d N
      = ((ArithmeticFunction.moebius d : ℤ) : ℝ) * mobiusTermKernel d N := by
  sorry
end PalomarCorpus.E249.PaperStatementsBE

namespace PalomarCorpus.E249.PaperStatementsAJ
export PalomarCorpus.E249_09.Shared (compositeDilationDefect)
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_defect_eq_zero_of_prime_support in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem composite_dilation_defect_eq_zero_of_prime_support (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (hAprime : ∀ d ∈ A, d.Prime) :
    compositeDilationDefect A a x = 0 := by
  sorry
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_defect_univ_six_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem composite_dilation_defect_univ_six_one :
    ((6 * 1 : ℕ).divisors.filter
        fun d => (d ∈ (Set.univ : Set ℕ) ∧ ¬ d ∣ 1 ∧ d ≠ 6)) = ({2, 3} : Finset ℕ) := by
  sorry
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_defect_univ_six_one_card in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem composite_dilation_defect_univ_six_one_card :
    compositeDilationDefect (Set.univ : Set ℕ) 6 1 = 2 := by
  sorry
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.sum_divisors_totient_ne_totient in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sum_divisors_totient_ne_totient :
    (∀ n : ℕ, ∑ d ∈ n.divisors, Nat.totient d = n) ∧
      (∑ d ∈ (2 : ℕ).divisors, Nat.totient d) = 2 ∧ Nat.totient 2 = 1 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsBD
open Filter
open Topology
export PalomarCorpus.E249_09.Shared (compositeDilationDefect)
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_divisor_count in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem composite_dilation_divisor_count (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (ha1 : 1 ≤ a) (hx1 : 1 ≤ x) :
    supportCoeff A (a * x) =
      supportCoeff A x + (if a ∣ x then 0 else 1) +
        compositeDilationDefect A a x := by
  sorry
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
end PalomarCorpus.E249.PaperStatementsAU

namespace PalomarCorpus.E249.PaperStatementsA
open Finset
export PalomarCorpus.E249_09.Shared (periodLcm totientTail)
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
end PalomarCorpus.E249.PaperStatementsA

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
export PalomarCorpus.E249_09.Shared (certifiedKill periodLcm totientTail windowDiscrepancy)
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
end PalomarCorpus.E249.PaperStatementsAT
