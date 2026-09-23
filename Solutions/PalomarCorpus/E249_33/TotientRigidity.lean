/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos249.PrefixValuationAndControlRigidity
import Solutions.PalomarCorpus.E249_33.Statement

namespace PalomarCorpus.E249.TotientRigidity

theorem totient_prime_mul_of_dvd {p n : ℕ} (hp : p.Prime) (h : p ∣ n) :
    (Nat.totient (p * n) : ℤ) = (p : ℤ) * (Nat.totient n : ℤ) :=
  ErdosProblems.Erdos249.totient_prime_mul_of_dvd hp h

theorem totient_prime_mul_of_not_dvd {p n : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) :
    (Nat.totient (p * n) : ℤ) = ((p : ℤ) - 1) * (Nat.totient n : ℤ) :=
  ErdosProblems.Erdos249.totient_prime_mul_of_not_dvd hp h

theorem totient_two_mul_of_odd {m : ℕ} (hm : Odd m) :
    Nat.totient (2 * m) = Nat.totient m :=
  ErdosProblems.Erdos249.totient_two_mul_of_odd hm

theorem totient_two_mul_of_even {m : ℕ} (hm : Even m) :
    Nat.totient (2 * m) = 2 * Nat.totient m :=
  ErdosProblems.Erdos249.totient_two_mul_of_even hm

theorem one_prime_law_and_little_o_forces_totient
    {p : ℕ} (hp : p.Prime) {g : ℕ → ℤ}
    (hlaw_not_dvd : ∀ n : ℕ, 1 ≤ n → ¬ p ∣ n → g (p * n) = ((p : ℤ) - 1) * g n)
    (hlaw_dvd : ∀ n : ℕ, 1 ≤ n → p ∣ n → g (p * n) = (p : ℤ) * g n)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |(g n : ℝ) - (Nat.totient n : ℝ)| ≤ ε * (n : ℝ))
    {n : ℕ} (hn : 1 ≤ n) :
    g n = (Nat.totient n : ℤ) :=
  ErdosProblems.Erdos249.one_prime_law_and_little_o_forces_totient
    hp hlaw_not_dvd hlaw_dvd hsmall hn

theorem even_law_and_eventual_congruence_forces_totient
    {g : ℕ → ℤ}
    (hodd : ∀ m : ℕ, Odd m → 1 ≤ m → g (2 * m) = g m)
    (heven : ∀ m : ℕ, Even m → 2 ≤ m → g (2 * m) = 2 * g m)
    (hcong : ∀ q : ℕ, 1 ≤ q → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (q : ℤ) ∣ totientDefect g n)
    {n : ℕ} (hn : 1 ≤ n) :
    g n = (Nat.totient n : ℤ) := by
  simpa [totientDefect, ErdosProblems.Erdos249.totientDefect] using
    ErdosProblems.Erdos249.even_law_and_eventual_congruence_forces_totient
      hodd heven hcong hn

end PalomarCorpus.E249.TotientRigidity
