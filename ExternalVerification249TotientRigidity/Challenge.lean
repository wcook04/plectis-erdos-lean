/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for totient rigidity in Erdős #249

One exact prime law plus an `o(n)` error forces `g = φ`. The exact even
doubling laws plus eventual congruence modulo every integer also force
`g = φ`. These are rigidity no-gos for weaker rational controls, not a
solution of Erdős #249.
-/

namespace Erdos249257.ExternalVerification249TotientRigidity

/-- The defect of a candidate integer coefficient sequence against `φ`. -/
def totientDefect (g : ℕ → ℤ) (n : ℕ) : ℤ := g n - (Nat.totient n : ℤ)

/-- `φ(pn) = p φ(n)` when `p` is prime and `p ∣ n`. -/
theorem totient_prime_mul_of_dvd {p n : ℕ} (hp : p.Prime) (h : p ∣ n) :
    (Nat.totient (p * n) : ℤ) = (p : ℤ) * (Nat.totient n : ℤ) := by
  sorry

/-- `φ(pn) = (p-1) φ(n)` when `p` is prime and `p ∤ n`. -/
theorem totient_prime_mul_of_not_dvd {p n : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) :
    (Nat.totient (p * n) : ℤ) = ((p : ℤ) - 1) * (Nat.totient n : ℤ) := by
  sorry

/-- `φ(2m) = φ(m)` for odd `m`. -/
theorem totient_two_mul_of_odd {m : ℕ} (hm : Odd m) :
    Nat.totient (2 * m) = Nat.totient m := by
  sorry

/-- `φ(2m) = 2 φ(m)` for even `m`. -/
theorem totient_two_mul_of_even {m : ℕ} (hm : Even m) :
    Nat.totient (2 * m) = 2 * Nat.totient m := by
  sorry

/-- One prime law plus an `o(n)` error forces `g = φ` on `n ≥ 1`. -/
theorem one_prime_law_and_little_o_forces_totient
    {p : ℕ} (hp : p.Prime) {g : ℕ → ℤ}
    (hlaw_not_dvd : ∀ n : ℕ, 1 ≤ n → ¬ p ∣ n → g (p * n) = ((p : ℤ) - 1) * g n)
    (hlaw_dvd : ∀ n : ℕ, 1 ≤ n → p ∣ n → g (p * n) = (p : ℤ) * g n)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |(g n : ℝ) - (Nat.totient n : ℝ)| ≤ ε * (n : ℝ))
    {n : ℕ} (hn : 1 ≤ n) :
    g n = (Nat.totient n : ℤ) := by
  sorry

/-- Exact doubling identities plus eventual congruence modulo every integer
force `g = φ` on `n ≥ 1`. -/
theorem even_law_and_eventual_congruence_forces_totient
    {g : ℕ → ℤ}
    (hodd : ∀ m : ℕ, Odd m → 1 ≤ m → g (2 * m) = g m)
    (heven : ∀ m : ℕ, Even m → 2 ≤ m → g (2 * m) = 2 * g m)
    (hcong : ∀ q : ℕ, 1 ≤ q → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (q : ℤ) ∣ totientDefect g n)
    {n : ℕ} (hn : 1 ≤ n) :
    g n = (Nat.totient n : ℤ) := by
  sorry

end Erdos249257.ExternalVerification249TotientRigidity
