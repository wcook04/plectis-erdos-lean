/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257aa

Every non-theorem declaration of `PalomarCorpus/E257aa/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

namespace PalomarCorpus.E257.PaperStatementsAA
/-- The three-channel Lambert lower bound for the Mersenne tail `T (k + 1)`. `T (k + 1) = ∑_{v ≥ 1} 2 ^ (-k * v) / (2 ^ v - 1)`; truncating that expansion after `v = 3` gives this rational function of `t = 2 ^ k`, namely `1/t + 1/(3 * t ^ 2) + 1/(7 * t ^ 3)` (equivalently `1 / 2 ^ k + 1 / (3 * 4 ^ k) + 1 / (7 * 8 ^ k)`). Local copy of Erdos249257.HalfGreedyFatalGap.mersenneTailLB3, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneTailLB3 (k : ℕ) : ℝ :=
  1 / 2 ^ k + 1 / (3 * (2 ^ k) ^ 2) + 1 / (7 * (2 ^ k) ^ 3)
/-- The signed coefficient layer between exact `p`-adic levels `e-1` and `e`. Local copy of Erdos249257.MaximalOmegaLayer.primePowerLayer, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primePowerLayer (p e : ℕ) (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  g (p ^ e * n) - g (p ^ (e - 1) * n)
/-- A one-point predicate satisfying the same endpoint transition shape as `exactLocalMersenneHalfRow_double_or_recycle`. It is the smallest explicit falsifier for any attempt to infer cofinal exact rows from that dichotomy alone: at endpoint six the recycling arm may return to endpoint six through `c = 4` forever. Local copy of Erdos249257.boundedDoubleOrRecycleModel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def boundedDoubleOrRecycleModel (n : ℕ) : Prop := n = 6
/-- `Ψ_{L,D}(x) = ∑_{d=2}^{D} ∑_{i=1}^{L} 2^{-i} 1_{d ∣ x+i}`, the finite-cutoff residue form (paper line 7966). Local copy of ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.Psi, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Psi (L D x : ℕ) : ℚ :=
  ∑ d ∈ Finset.Icc 2 D, ∑ i ∈ (Finset.Icc 1 L).filter (fun i => d ∣ x + i), (1 / 2 : ℚ) ^ i
/-- Definition `defn:theta` (line 7850): the short-window divisor phase `Θ_L(M) = ∑_{i=1}^{L} (τ(M+i) − 1) 2^{-i}`, where `τ` is the number-of-divisors function. For `M ≥ 1` and `1 ≤ i` the truncated subtraction is the honest `τ(M+i) − 1` because `M + i ≥ 1`; see `card_divisors_sub_one` for the paper's own gloss `τ(n) − 1 = #{d ≥ 2 : d ∣ n}`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.Theta, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Theta (L M : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 L, (((M + i).divisors.card - 1 : ℕ) : ℚ) * (1 / 2 : ℚ) ^ i
/-- `i_d(M)`: the least `i ≥ 1` with `d ∣ M + i`. Equal to `d − (M mod d)`, with value `d` when the remainder is zero, and manifestly a function of `M mod d`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.iLeast, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def iLeast (d M : ℕ) : ℕ := d - M % d
/-- `m_d = #{1 ≤ i ≤ L : d ∣ M + i}`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.mCount, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mCount (d M L : ℕ) : ℕ := ((Finset.Icc 1 L).filter (fun i => d ∣ M + i)).card
/-- The manuscript's misalignment mass `μ_J(M) = ∑_{q=2}^{J} 2^{M mod q}/(2^q-1)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.misalignMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def misalignMass (J M : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 2 J, (2 : ℝ) ^ (M % q) / (2 ^ q - 1)
/-- The manuscript's `B(r) = 2^⌊(r+4)/2⌋ + 2r + 3`: a division-free integer envelope for a reset which can feed a right branch at the two-thirds crossing of its largest false rank. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.resetCrossingBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def resetCrossingBound (r : ℕ) : ℕ :=
  2 ^ ((r + 4) / 2) + 2 * r + 3
/-- The paper's row-weight functional `W_s(E) = ∑_{e ∈ E} ⌊4^s/(2^e − 1)⌋`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rowWeightSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rowWeightSum (s : ℕ) (E : Finset ℕ) : ℤ :=
  ∑ e ∈ E, ⌊(4 : ℝ) ^ s / ((2 : ℝ) ^ e - 1)⌋
/-- The finite Mersenne sum associated with a skip set. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.skipSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def skipSum (S : Finset ℕ) : ℚ := ∑ d ∈ S, 1 / ((2 : ℚ) ^ d - 1)
/-- The manuscript's `L_J = lcm(2,3,…,J)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.truncLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def truncLcm (J : ℕ) : ℕ := (Finset.Icc 2 J).lcm id
/-- The manuscript's `T_{n+1}^{(J)} = ∑_{q=1}^{J} 2^{-qn}/(2^q-1)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.truncTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def truncTail (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / (2 ^ (q * n) * (2 ^ q - 1))
/-- The manuscript's `w_n^{(J)} = ∑_{q=1}^{J} 2^{-qn}`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.truncWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def truncWeight (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / 2 ^ (q * n)
end PalomarCorpus.E257.PaperStatementsAA
