/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CertificateKernel
import Solutions.PalomarCorpus.E257_21.Statement

open Filter
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAG

noncomputable def finiteErdosSum (F : Finset Nat) (b : Nat) : Rat :=
  ∑ n ∈ F, 1 / ((b : Rat) ^ n - 1)

noncomputable def intWeightedCoeff (w : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, w d

noncomputable def intWeightedErdosSeries (b : ℕ) (w : ℕ → ℤ) : ℝ :=
  ∑' a : ℕ, ((w a : ℤ) : ℝ) / ((b : ℝ) ^ a - 1)

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

theorem coprime_base_den_finiteErdosSum
    (F : Finset Nat) (b : Nat) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    Nat.Coprime b (finiteErdosSum F b).den := @Erdos249257.coprime_base_den_finiteErdosSum F b h0 hb

theorem erdosSupportSeries_multiples_eq_pow_base_full_support
    (b d : ℕ) (hb : 2 ≤ b) (hd : 1 ≤ d) :
    erdosSupportSeries b {n : ℕ | d ∣ n}
      = ∑' k : ℕ, (1 : ℝ) / (((b : ℝ) ^ d) ^ (k + 1) - 1) := @Erdos249257.erdosSupportSeries_multiples_eq_pow_base_full_support b d hb hd

theorem irrational_coeff_series_of_weighted_coeff_block_certificates
    (b : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b) (hgrowth : ∀ m : ℕ, c m ≤ m)
    (hcert : ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
        (∀ r ∈ Finset.Icc 1 K, b ^ r ∣ c (N + r)) ∧
        (∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) ≤ C) ∧
        (∃ t : ℕ, 0 < c (N + L + 1 + t)) ∧
        q * (C + (N + L + 2)) < b ^ L) :
    Irrational (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1)) := @Erdos249257.irrational_coeff_series_of_weighted_coeff_block_certificates b c hb hgrowth hcert

theorem irrational_erdosSum_factorial_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (Nat.factorial (k + 1)) - 1)) := @Erdos249257.irrational_erdosSum_factorial_support b hb

theorem irrational_erdosSum_full_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)) := @Erdos249257.irrational_erdosSum_full_support b hb

theorem irrational_erdosSum_of_lcm_gap
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (hgap : Tendsto (fun k => a k - ((Finset.range k).image a).lcm id)
      atTop atTop) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (a k) - 1)) := @Erdos249257.irrational_erdosSum_of_lcm_gap b hb a ha ha0 hgap

theorem irrational_erdosSum_two_pow_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (2 ^ k) - 1)) := @Erdos249257.irrational_erdosSum_two_pow_support b hb

theorem irrational_erdosSupportSeries_eventuallyPeriodic
    (b m N₀ : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, N₀ ≤ n → (n + m ∈ A ↔ n ∈ A))
    (hinf : A.Infinite) :
    Irrational (erdosSupportSeries b A) := by
  apply Erdos249257.irrational_erdosSupportSeries_eventuallyPeriodic <;> assumption

theorem irrational_erdosSupportSeries_multiples (b d : ℕ) (hb : 2 ≤ b) (hd : 1 ≤ d) :
    Irrational (erdosSupportSeries b {n : ℕ | d ∣ n}) := @Erdos249257.irrational_erdosSupportSeries_multiples b d hb hd

theorem irrational_erdosSupportSeries_odd (b : ℕ) (hb : 2 ≤ b) :
    Irrational (erdosSupportSeries b {n : ℕ | Odd n}) := @Erdos249257.irrational_erdosSupportSeries_odd b hb

theorem irrational_erdosSupportSeries_of_tail (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b)
    (B : ℕ) (h : Irrational (erdosSupportSeries b {n : ℕ | n ∈ A ∧ B < n})) :
    Irrational (erdosSupportSeries b A) := @Erdos249257.irrational_erdosSupportSeries_of_tail b A hb B h

theorem irrational_erdosSupportSeries_pairwise_coprime (b : ℕ) (A : Set ℕ)
    (hb : 2 ≤ b) (hA : A.Infinite) (hpair : A.Pairwise Nat.Coprime)
    (hsum : Summable (Set.indicator A fun a : ℕ => (1 : ℝ) / a)) :
    Irrational (erdosSupportSeries b A) := @Erdos249257.irrational_erdosSupportSeries_pairwise_coprime b A hb hA hpair hsum

theorem irrational_erdosSupportSeries_periodic
    (b m : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, n + m ∈ A ↔ n ∈ A)
    (hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A) :
    Irrational (erdosSupportSeries b A) := @Erdos249257.irrational_erdosSupportSeries_periodic b m A hb hm hper hpos

theorem irrational_erdosSupportSeries_residueClass
    (b m c : ℕ) (hb : 2 ≤ b) (hm : 0 < m) :
    Irrational (erdosSupportSeries b {n : ℕ | n % m = c % m}) := @Erdos249257.irrational_erdosSupportSeries_residueClass b m c hb hm

theorem irrational_erdosSupportSeries_tail_of_irrational (b : ℕ) (A : Set ℕ)
    (hb : 2 ≤ b) (B : ℕ) (h : Irrational (erdosSupportSeries b A)) :
    Irrational (erdosSupportSeries b {n : ℕ | n ∈ A ∧ B < n}) := @Erdos249257.irrational_erdosSupportSeries_tail_of_irrational b A hb B h

theorem irrational_intWeightedErdosSeries_periodic_of_coeff_nonneg_of_frequently_ne_zero
    (b m : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n)
    (hc0 : ∀ n : ℕ, 0 < n → 0 ≤ intWeightedCoeff w n)
    (hne : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ intWeightedCoeff w n ≠ 0) :
    Irrational (intWeightedErdosSeries b w) := @Erdos249257.irrational_intWeightedErdosSeries_periodic_of_coeff_nonneg_of_frequently_ne_zero b m w hb hm hper hc0 hne

theorem irrational_intWeightedErdosSeries_periodic_of_coeff_nonpos_of_frequently_ne_zero
    (b m : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n)
    (hc0 : ∀ n : ℕ, 0 < n → intWeightedCoeff w n ≤ 0)
    (hne : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ intWeightedCoeff w n ≠ 0) :
    Irrational (intWeightedErdosSeries b w) := @Erdos249257.irrational_intWeightedErdosSeries_periodic_of_coeff_nonpos_of_frequently_ne_zero b m w hb hm hper hc0 hne

theorem irrational_or_bpow_mul_eq_intCast_intWeightedErdosSeries_periodic
    (b m : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n) :
    Irrational (intWeightedErdosSeries b w)
      ∨ ∃ (k : ℕ) (z : ℤ), (b : ℝ) ^ k * intWeightedErdosSeries b w = (z : ℝ) := @Erdos249257.irrational_or_bpow_mul_eq_intCast_intWeightedErdosSeries_periodic b m w hb hm hper

theorem lcm_lt_den_finiteErdosSum
    (F : Finset Nat) (b : Nat)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (h2 : 2 ≤ F.lcm id) :
    F.lcm id < (finiteErdosSum F b).den := @Erdos249257.lcm_lt_den_finiteErdosSum F b hF h0 hb h2

theorem supportCoeff_le_card_divisors (A : Set ℕ) (n : ℕ) :
    supportCoeff A n ≤ n.divisors.card := @Erdos249257.supportCoeff_le_card_divisors A n

theorem supportCoeff_le_self (A : Set ℕ) (n : ℕ) : supportCoeff A n ≤ n := @Erdos249257.supportCoeff_le_self A n

end PalomarCorpus.E257.PaperStatementsAG
