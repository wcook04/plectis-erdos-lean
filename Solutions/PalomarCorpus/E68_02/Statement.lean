/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E68_02

Every non-theorem declaration of `PalomarCorpus/E68_02/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open Finsupp

namespace PalomarCorpus.E68_02.Shared
/-- The channel weight `W d i = i! / (d!)^(i / d)`, computed with natural division and an exact integer because `(d!)^(i / d)` divides `i!`; the value is `i!` whenever `d ≤ 1` or `d > i`. -/
noncomputable def channelWeight (i d : ℕ) : ℕ :=
  i.factorial / (d.factorial ^ (i / d))
/-- The `d`-th divisor channel numerator `V d (lam)`, the finite sum of `lam i * channelWeight i d` over the support of `lam`; because `d!` is congruent to `1` modulo `d! - 1`, this integer agrees with the factorial moment of `lam` modulo `d! - 1`. -/
noncomputable def channelNumerator (lam : ℕ →₀ ℤ) (d : ℕ) : ℤ :=
  lam.sum fun i z => z * (channelWeight i d : ℤ)
/-- One summand of the universal factorial-gap tail beyond `D`. Local copy of Erdos68.factorialGapTailTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapTailTerm (D d : ℕ) : ℝ :=
  if D < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)
  else 0
/-- The universal factorial-gap tail beyond `D`. Local copy of Erdos68.factorialGapTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapTail (D : ℕ) : ℝ :=
  ∑' d : ℕ, factorialGapTailTerm D d
/-- The original Erdős #68 series, expressed through the universal factorial-gap tail beginning after `1`. Local copy of Erdos68.factorialGapSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapSeries : ℝ :=
  factorialGapTail 1
/-- The factorial moment `M (lam) = ∑ lam i * i!` of a finitely supported integer vector. -/
noncomputable def factorialMoment (lam : ℕ →₀ ℤ) : ℤ :=
  lam.sum fun i z => z * (i.factorial : ℤ)
end PalomarCorpus.E68_02.Shared

namespace PalomarCorpus.E68.PaperStatementsC
open scoped BigOperators
export PalomarCorpus.E68_02.Shared (channelNumerator channelWeight factorialGapSeries factorialGapTail factorialGapTailTerm factorialMoment)
/-- The shifted companion term `1/(n!(n!+t))`, anchored at `n ≥ 2`. Local copy of ErdosProblems.Erdos68.shiftCompanionTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftCompanionTerm (t : ℤ) (n : ℕ) : ℝ :=
  if 2 ≤ n then 1 / ((n.factorial : ℝ) * ((n.factorial : ℝ) + (t : ℝ))) else 0
/-- The shifted companion constant `C_t = ∑_{n≥2} 1/(n!(n!+t))`. Local copy of ErdosProblems.Erdos68.shiftCompanionConstant, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftCompanionConstant (t : ℤ) : ℝ :=
  ∑' n : ℕ, shiftCompanionTerm t n
/-- The shifted factorial-gap term `1/(n!+t)`, anchored at `n ≥ 2`. Local copy of ErdosProblems.Erdos68.shiftGapTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftGapTerm (t : ℤ) (n : ℕ) : ℝ :=
  if 2 ≤ n then 1 / ((n.factorial : ℝ) + (t : ℝ)) else 0
/-- Erdős's shifted series `S_t = ∑_{n≥2} 1/(n!+t)`. Local copy of ErdosProblems.Erdos68.shiftGapSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftGapSeries (t : ℤ) : ℝ :=
  ∑' n : ℕ, shiftGapTerm t n
end PalomarCorpus.E68.PaperStatementsC

namespace PalomarCorpus.E68.PaperStatementsA
open scoped BigOperators
open Finsupp
export PalomarCorpus.E68_02.Shared (factorialGapSeries factorialGapTail factorialGapTailTerm)
/-- Lcm of all off-diagonal pairwise gcds in a finite denominator family. Each index is omitted from its own inner lcm, so diagonal terms do not erase the private support. Local copy of ErdosProblems.Erdos68.pairwiseCollisionCore, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def pairwiseCollisionCore
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (d : ι → ℕ) : ℕ :=
  s.lcm fun i =>
    (s.erase i).lcm fun j => Nat.gcd (d i) (d j)
/-- The collision core used by the endpoint decomposition also contains a distinguished base denominator. Local copy of ErdosProblems.Erdos68.collisionCore, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def collisionCore
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  Nat.lcm base (pairwiseCollisionCore s d)
/-- Canonical projection of a weighted support numerator modulo `Q`. Local copy of ErdosProblems.Erdos68.projectedResidue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def projectedResidue (T Q : ℕ) : ℕ :=
  T % Q
/-- Canonical projection of the additive inverse of a natural numerator. The outer remainder sends the zero residue to zero rather than to `Q`. Local copy of ErdosProblems.Erdos68.complementaryProjectedResidue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def complementaryProjectedResidue (T Q : ℕ) : ℕ :=
  projectedResidue (Q - projectedResidue T Q) Q
/-- Common denominator for the distinguished base and the finite denominator family. Local copy of ErdosProblems.Erdos68.endpointDenominatorLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def endpointDenominatorLcm
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  Nat.lcm base (s.lcm d)
/-- Numerator of the reciprocal tail after placing every denominator over the common endpoint lcm. Local copy of ErdosProblems.Erdos68.endpointTailNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def endpointTailNumerator
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  s.sum fun i => endpointDenominatorLcm base s d / d i
/-- Distinguished predecessor-factorial denominator in the prime block. Local copy of ErdosProblems.Erdos68.factorialBlockBase, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialBlockBase (p : ℕ) : ℕ :=
  (p - 1).factorial
/-- Exact budget numerator `2p+1` in the endpoint upper bound. Local copy of ErdosProblems.Erdos68.factorialBlockBudget, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialBlockBudget (p : ℕ) : ℕ :=
  2 * p + 1
/-- Literal Erdős #68 reciprocal denominator. Local copy of ErdosProblems.Erdos68.factorialGapDenominator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapDenominator (n : ℕ) : ℕ :=
  n.factorial - 1
/-- Reciprocal-denominator index block for the factorial endpoint: `2, …, 2p-1`. Local copy of ErdosProblems.Erdos68.factorialBlockIndices, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialBlockIndices (p : ℕ) : Finset ℕ :=
  Finset.Icc 2 (2 * p - 1)
/-- Full literal common denominator `L_p`. Local copy of ErdosProblems.Erdos68.factorialBlockEndpointLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialBlockEndpointLcm (p : ℕ) : ℕ :=
  endpointDenominatorLcm
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator
/-- Private quotient owned by one denominator after deleting all support visible in the collision core. Local copy of ErdosProblems.Erdos68.privateQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def privateQuotient
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) (i : ι) : ℕ :=
  d i / Nat.gcd (d i) (collisionCore base s d)
/-- Product of all finite-family private quotients. Local copy of ErdosProblems.Erdos68.privateModulus, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def privateModulus
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  s.prod (privateQuotient base s d)
/-- Literal private modulus `R_p = L_p / C_p`. Local copy of ErdosProblems.Erdos68.factorialBlockPrivateModulus, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialBlockPrivateModulus (p : ℕ) : ℕ :=
  privateModulus
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator
/-- Exact scale `2p²(2p-1)!` in the endpoint comparison. Local copy of ErdosProblems.Erdos68.factorialBlockScale, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialBlockScale (p : ℕ) : ℕ :=
  2 * p ^ 2 * (2 * p - 1).factorial
/-- Common-denominator reciprocal-tail numerator `T_p`. Local copy of ErdosProblems.Erdos68.factorialBlockTailNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialBlockTailNumerator (p : ℕ) : ℕ :=
  endpointTailNumerator
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator
end PalomarCorpus.E68.PaperStatementsA

namespace PalomarCorpus.E68.MomentIdeal
open scoped BigOperators
open Finsupp
export PalomarCorpus.E68_02.Shared (channelNumerator channelWeight factorialMoment)
/-- The common denominator `L D = lcm (d! - 1)` taken over the channel indices `2 ≤ d ≤ D`, the least common multiple of the denominators of the partial sum through `D`; the index set is empty and the value is `1` when `D < 2`. -/
noncomputable def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)
/-- The adjacent factorial difference `T n = n * e (n - 1) - e n`, the finitely supported integer vector with coefficient `n` at index `n - 1` and coefficient `-1` at index `n`, the subtraction `n - 1` taken in the natural numbers; for `n ≥ 1` its factorial moment vanishes because `n * (n - 1)! = n!`. -/
noncomputable def adjacentDifference (n : ℕ) : ℕ →₀ ℤ :=
  single (n - 1) (n : ℤ) - single n 1
/-- The isolated channel unit `U n`, defined by strong recursion as `T n` minus the sum of `channelWeight n d * U d` over the divisors `d` of `n` with `2 ≤ d < n`, and as the zero vector for `n ≤ 1`; the recursion cancels every proper divisor channel, so `U n` has zero factorial moment and acts only on the channel at `n`. -/
noncomputable def isolatedChannelUnit (n : ℕ) : ℕ →₀ ℤ :=
  n.strongRecOn' fun n rec =>
    if n ≤ 1 then 0
    else
      adjacentDifference n -
        ∑ d ∈ (Finset.Ico 2 n).attach,
          if d.1 ∣ n then
            (channelWeight n d.1 : ℤ) • rec d.1 (Finset.mem_Ico.mp d.2).2
          else 0
/-- The auxiliary coordinate `u n = (U n) 1` of the isolated channel unit, the integer weight that `U n` places on index `1`. -/
noncomputable def channelScalar (n : ℕ) : ℤ := isolatedChannelUnit n 1
/-- The greatest common divisor of the absolute values `|u n|` over the finite range `D + 1 ≤ n ≤ N`, as a natural number; the empty range gives `0`. -/
noncomputable def finiteScalarGcd (D N : ℕ) : ℕ :=
  (Finset.Icc (D + 1) N).gcd (fun n => (channelScalar n).natAbs)
/-- The `j`-th column of the divisor channel basis: the unit vector at index `1` when `j = 0`, and the isolated channel unit `U (j + 1)` when `j ≥ 1`. -/
noncomputable def channelBasisColumn (j : ℕ) : ℕ →₀ ℤ :=
  if j = 0 then single 1 1 else isolatedChannelUnit (j + 1)
/-- The finitely supported integer vector assembled from coordinates `a` in the divisor channel basis, namely the finite sum of `a j` scaled copies of `channelBasisColumn j`. -/
noncomputable def channelSynthesis (a : ℕ →₀ ℤ) : ℕ →₀ ℤ :=
  a.sum (fun j z => z • channelBasisColumn j)
/-- The divisor channel coordinates of the canonical low channel kernel at depth `D`: the value `L D` in coordinate `0`, which carries the unit vector at index `1`, and the value `-(L D / (d! - 1))` in coordinate `d - 1`, which carries `U d`, for each `d` with `2 ≤ d ≤ D`. -/
noncomputable def kernelCoordinates (D : ℕ) : ℕ →₀ ℤ :=
  single 0 (channelLCM D : ℤ) -
    ∑ d ∈ Finset.Icc 2 D,
      single (d - 1) ((channelLCM D : ℤ) / ((d.factorial : ℤ) - 1))
/-- The canonical low channel kernel `K D = L D * e 1 - ∑_{2 ≤ d ≤ D} (L D / (d! - 1)) * U d`, the vector of factorial moment `L D` whose channel numerators vanish at every `d` with `2 ≤ d ≤ D`. -/
noncomputable def canonicalKernel (D : ℕ) : ℕ →₀ ℤ :=
  channelSynthesis (kernelCoordinates D)
/-- The auxiliary coordinate `a D = (K D) 1` of the canonical low channel kernel at depth `D`. -/
noncomputable def kernelOne (D : ℕ) : ℤ := canonicalKernel D 1
/-- The support restriction of the problem: every index in the support of `f` is at least `2`, so `f` has no coefficient at index `0` and none at the auxiliary index `1`. -/
noncomputable def Admissible (f : ℕ →₀ ℤ) : Prop :=
  ∀ n ∈ f.support, 2 ≤ n
/-- The low channel condition at depth `D`: the channel numerator of `f` vanishes at every channel `d` with `2 ≤ d ≤ D`. -/
noncomputable def LowChannels (D : ℕ) (f : ℕ →₀ ℤ) : Prop :=
  ∀ d ∈ Finset.Icc 2 D, channelNumerator f d = 0
/-- The property that the integer `m` is the factorial moment of some admissible finitely supported integer vector whose channel numerators vanish at every `d` with `2 ≤ d ≤ D`. -/
noncomputable def AttainsMoment (D : ℕ) (m : ℤ) : Prop :=
  ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧ factorialMoment f = m
/-- The candidate generator `L D * (G / gcd (G, a D))` of the attainable moments at depth `D`, where `G` is the greatest common divisor of the auxiliary coordinates `u n` over the finite horizon `D + 1 ≤ n ≤ D * (2 * p - 1)` cut at the parameter `p`, on which this definition imposes no primality, and the outer division is exact integer division. -/
noncomputable def minimumMoment (D p : ℕ) : ℤ :=
  let G : ℤ := finiteScalarGcd D (D * (2 * p - 1))
  (channelLCM D : ℤ) * (G / (Int.gcd G (kernelOne D) : ℤ))
/-- The primitivity condition on `f`: for no natural `k ≥ 2` is `f` equal to `k` times another finitely supported integer vector. -/
noncomputable def PrimitiveVector (f : ℕ →₀ ℤ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → ¬ ∃ g : ℕ →₀ ℤ, f = (k : ℤ) • g
end PalomarCorpus.E68.MomentIdeal
