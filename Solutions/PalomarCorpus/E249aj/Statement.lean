/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249aj

Every non-theorem declaration of `PalomarCorpus/E249aj/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

namespace PalomarCorpus.E249.PaperStatementsAJ
/-- Support divisors created by multiplication by `a`, excluding the distinguished divisor `a` itself. Local copy of Erdos249257.CompositeDilationDefect.compositeDilationDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def compositeDilationDefect (A : Set ℕ) (a x : ℕ) : ℕ :=
  by
    classical
    exact ((a * x).divisors.filter fun d =>
      d ∈ A ∧ ¬ d ∣ x ∧ d ≠ a).card
/-- Exact direct tail radius for the four-vertex commutator. Local copy of Erdos249257.PrimeJumpWindow.primeJumpSharpRadius, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeJumpSharpRadius (H p L : ℕ) : ℤ :=
  3 * p * H + (p + 1) * (L + 2)
/-- The exact ordering socket for the fixed-rank curvature: the rank-two totient is strictly below both outer ranks or strictly above both of them. This is the local conclusion supplied by any factor-separated ordering of the three nonproportional linear forms. The unresolved arithmetic step for Erdős #249 is to force this socket on cofinally many prescribed LCM heights, not merely on a positive-density set of unrestricted heights. Local copy of Erdos249257.TotientFixedRankLcmAsymptotic.MiddleRankTotientExtremal, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def MiddleRankTotientExtremal (H j : ℕ) : Prop :=
  (Nat.totient (2 * H + j) < Nat.totient (H + j) ∧
      Nat.totient (2 * H + j) < Nat.totient (3 * H + j)) ∨
    (Nat.totient (H + j) < Nat.totient (2 * H + j) ∧
      Nat.totient (3 * H + j) < Nat.totient (2 * H + j))
/-- The two scale-`b` guard bits of a `(b+2)`-bit residue are mixed. The intervals are exactly the binary cylinders `01` and `10`; every lower bit is left unrestricted. Local copy of Erdos249257.TotientTailPeriodKiller.DyadicMixedGuard, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicMixedGuard (A : ℤ) (b : ℕ) : Prop :=
  let P : ℤ := (2 : ℤ) ^ b
  let r : ℤ := A % (2 : ℤ) ^ (b + 2)
  (P ≤ r ∧ r < 2 * P) ∨ (2 * P ≤ r ∧ r < 3 * P)
/-- The unsigned binary cyclotomic layer `|Φ_n(2)|`. Local copy of ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCyclotomicLayer (n : ℕ) : ℕ :=
  ((Polynomial.cyclotomic n ℤ).eval (2 : ℤ)).natAbs
/-- The first `H` totient-tail letters at `N`, cleared by `2^H`. Local copy of ErdosProblems.Erdos249.CyclotomicAnchoredKill.totientBlock, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientBlock (H N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range H,
    (Nat.totient (N + 1 + j) : ℤ) * 2 ^ (H - 1 - j)
/-- The wave-17 gap certificate at window `(N, K)` for the denominator `q`: the committed totient residue avoids the thin band of width `q(N+K+2)`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.GapCertificate, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def GapCertificate (N K q : ℕ) : Prop :=
  (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K))
      % 2 ^ K + q * (N + K + 2) < 2 ^ K
/-- `sup_K (b+d)(K) = ∞`: the proved Farey-gap denominator-exclusion bounds on the `N = 1` window family are arbitrarily large, that is, every finite denominator range `[1, Q]` is excluded by some single window `K`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.FareyGapExclusionUnbounded, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FareyGapExclusionUnbounded : Prop :=
  ∀ Q : ℕ, ∃ K : ℕ, ∀ q : ℕ, 0 < q → q ≤ Q → GapCertificate 1 K q
/-- The four asserted coefficient properties of a sequence `c : ℕ → ℕ`: uniform boundedness, `c(n) ≤ n`, parity agreement with `φ` at every index, and the separated-carry form of aperiodicity together with genuine non-eventual-periodicity. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.ParityComparisonProperties, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ParityComparisonProperties (c : ℕ → ℕ) : Prop :=
  (∀ n, c n ≤ 6) ∧ (∀ n, c n ≤ n) ∧ (∀ n, c n % 2 = Nat.totient n % 2) ∧
    (∀ N G K : ℕ, ∃ k : ℕ, N < 2 ^ (k + 3) ∧
      ∀ i : ℕ, i < K →
        2 ^ (k + i + 3) + G < 2 ^ (k + i + 4) ∧
        c (2 ^ (k + i + 3)) = 6 ∧ c (2 ^ (k + i + 3) + 1) = 0) ∧
    (¬ ∃ p N : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → c (n + p) = c n)
/-- Every rational prime divisor of a layer supplies an exact-order witness in extension degree at most `d`. Local copy of ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.BoundedDegreeOrderConsumer, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def BoundedDegreeOrderConsumer
    (C : ℕ → ℕ) (m d : ℕ) : Prop :=
  ∀ q p : ℕ,
    q.Prime → p.Prime → p ∣ C (m * q) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ m * q ∣ p ^ k - 1
/-- Bounded-degree order witnesses beyond a prime-index cutoff. Unlike `BoundedDegreeOrderConsumer`, this permits the finitely many characteristic primes that occur naturally in cyclotomic layers. Local copy of ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.EventualBoundedDegreeOrderConsumer, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def EventualBoundedDegreeOrderConsumer
    (C : ℕ → ℕ) (m d : ℕ) : Prop :=
  ∃ Q₀ : ℕ, ∀ q p : ℕ,
    q.Prime → Q₀ ≤ q → p.Prime → p ∣ C (m * q) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ m * q ∣ p ^ k - 1
/-- Large prime-ray layers escape every prescribed finite prime support. Local copy of ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.FinitePrimeSupportEscape, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FinitePrimeSupportEscape (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ S : Finset ℕ, ∃ Q₀ : ℕ, ∀ q : ℕ,
    q.Prime → Q₀ ≤ q →
      ∀ p ∈ S, p.Prime → ¬ p ∣ C (m * q)
/-- Eventual nontrivial, clean cyclotomic layers on the prime ray `m*q`. Local copy of ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.PrimeRayLayerSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PrimeRayLayerSupply (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∃ Q₀ : ℕ, ∀ q : ℕ,
    q.Prime → Q₀ ≤ q →
      1 < C (m * q) ∧ Nat.Coprime (C (m * q)) (m * q)
/-- The prime divisors appearing on the ray `m*q` are unbounded, even after imposing an arbitrary lower bound on the prime index `q`. Local copy of ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.UnboundedPrimeDivisorSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def UnboundedPrimeDivisorSupply (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ B N₀ : ℕ, ∃ q p : ℕ,
    q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (m * q) ∧ B < p
/-- `qstar` is the exact first displayed denominator at which a gap certificate fails. This is the small checker-facing contract emitted by the untrusted Stern--Brocot producer: all smaller positive denominators pass, while `qstar` itself fails. Local copy of GapFareyBound.IsFirstGapFailure, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsFirstGapFailure (V K H qstar : ℕ) : Prop :=
  (∀ q : ℕ, 0 < q → q < qstar → (q * V) % 2 ^ K + q * H < 2 ^ K) ∧
    ¬ ((qstar * V) % 2 ^ K + qstar * H < 2 ^ K)
end PalomarCorpus.E249.PaperStatementsAJ
