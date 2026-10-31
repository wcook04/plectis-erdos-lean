/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos251.ShiftedCountingSourceR11

noncomputable section
open Finset

namespace Erdos249257.ExternalVerification251ShiftedFourPrimeCounting

def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n
def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n

def shiftedMatches (h N : ℕ) (r : ℤ) : Finset ℕ := by
  classical
  exact (range N).filter (fun n => (primeGap0 (n + h) : ℤ) - primeGap0 n = r)

def quadCandidates (N H : ℕ) (r : ℤ) : Finset ((ℕ × ℕ) × ℕ) := by
  classical
  exact (((range (prime0 N)).product (range (H + 1))).product (range (H + 1))).filter
    (fun z => 0 < z.1.2 ∧ z.1.2 < z.2 ∧ 0 < (z.1.2 : ℤ) + r ∧
      Nat.Prime z.1.1 ∧ Nat.Prime (z.1.1 + z.1.2) ∧ Nat.Prime (z.1.1 + z.2) ∧
      Nat.Prime (((z.1.1 : ℤ) + z.2 + z.1.2 + r).toNat))

def ZeroDensity (s : Set ℕ) : Prop := by
  classical
  exact ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    (((range N).filter (fun n => n ∈ s)).card : ℝ) < ε * N

def SeparatedQuadSieve_target (h : ℕ) (r : ℤ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ H : ℕ,
    ((h + 1 : ℕ) : ℝ) * prime0 (N + (h + 1)) +
      (H + 1 : ℕ) * ((quadCandidates N H r).card : ℝ) < ε * N * (H + 1 : ℕ)

theorem shifted_count_bound (h N H : ℕ) (hh : 2 ≤ h) (r : ℤ) :
    (H + 1) * (shiftedMatches h N r).card ≤
      (h + 1) * prime0 (N + (h + 1)) + (H + 1) * (quadCandidates N H r).card := by
  exact ErdosProblems.Erdos251.PaperR11.PrimeSource.shifted_count_bound h N H hh r

theorem separated_zeroDensity_of_quad_sieve (h : ℕ) (hh : 2 ≤ h) (r : ℤ)
    (hsieve : SeparatedQuadSieve_target h r) :
    ZeroDensity {n | (primeGap0 (n + h) : ℤ) - primeGap0 n = r} := by
  exact ErdosProblems.Erdos251.PaperR11.PrimeSource.separated_zeroDensity_of_quad_sieve h hh r hsieve

end Erdos249257.ExternalVerification251ShiftedFourPrimeCounting
