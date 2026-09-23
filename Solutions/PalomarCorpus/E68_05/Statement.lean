/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E68_05

Every non-theorem declaration of `PalomarCorpus/E68_05/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open Finsupp

namespace PalomarCorpus.E68.PaperStatementsA
open scoped BigOperators
open Finsupp
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
/-- Adjacent difference `T_n = n e_{n-1} - e_n`. Local copy of ErdosProblems.Erdos68.adjacentDifference, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def adjacentDifference (n : ℕ) : ℕ →₀ ℤ :=
  single (n - 1) (n : ℤ) - single n 1
/-- Integral weight of index `i` in the divisor channel `d`. Local copy of ErdosProblems.Erdos68.channelWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def channelWeight (i d : ℕ) : ℕ :=
  i.factorial / (d.factorial ^ (i / d))
/-- Isolated one-channel basis vector, `U_n = T_n - ∑_{d | n, 2 ≤ d < n} W_{d,n} U_d`. Local copy of ErdosProblems.Erdos68.isolatedChannelUnit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def isolatedChannelUnit (n : ℕ) : ℕ →₀ ℤ :=
  n.strongRecOn' fun n rec =>
    if n ≤ 1 then 0
    else
      adjacentDifference n -
        ∑ d ∈ (Finset.Ico 2 n).attach,
          if d.1 ∣ n then
            (channelWeight n d.1 : ℤ) • rec d.1 (Finset.mem_Ico.mp d.2).2
          else 0
/-- Local copy of ErdosProblems.Erdos68.PaperComplete.channelScalar, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def channelScalar (n : ℕ) : ℤ := isolatedChannelUnit n 1
/-- The universal property that uniquely specifies the positive tail gcd. Local copy of ErdosProblems.Erdos68.PaperComplete.IsScalarTailGcd, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsScalarTailGcd (D G : ℕ) : Prop :=
  ∀ b : ℕ, b ∣ G ↔ ∀ n : ℕ, D < n → (b : ℤ) ∣ channelScalar n
/-- b_0=e_1 and b_j=U_(j+1) for j>0. Local copy of ErdosProblems.Erdos68.PaperComplete.channelBasisColumn, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def channelBasisColumn (j : ℕ) : ℕ →₀ ℤ :=
  if j = 0 then single 1 1 else isolatedChannelUnit (j + 1)
/-- Local copy of ErdosProblems.Erdos68.PaperComplete.channelSynthesis, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def channelSynthesis (a : ℕ →₀ ℤ) : ℕ →₀ ℤ :=
  a.sum (fun j z => z • channelBasisColumn j)
/-- Local copy of ErdosProblems.Erdos68.PaperComplete.finiteScalarGcd, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def finiteScalarGcd (D N : ℕ) : ℕ :=
  (Finset.Icc (D + 1) N).gcd (fun n => (channelScalar n).natAbs)
/-- Floor of the `m!`-scaled real number. Local copy of ErdosProblems.Erdos68.facFloor, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def facFloor (x : ℝ) (m : ℕ) : ℤ :=
  ⌊(m.factorial : ℝ) * x⌋
/-- Finite-support integer numerator in channel `d`. Local copy of ErdosProblems.Erdos68.channelNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def channelNumerator (lam : ℕ →₀ ℤ) (d : ℕ) : ℤ :=
  lam.sum fun i z => z * (channelWeight i d : ℤ)
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
/-- Companion-constant term, anchored at `n ≥ 2`. Local copy of ErdosProblems.Erdos68.compConstTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def compConstTerm (n : ℕ) : ℝ :=
  if 2 ≤ n then
    (1 : ℝ) /
      ((((n.factorial : ℕ) : ℝ)) *
        ((((n.factorial : ℤ) - 1 : ℤ) : ℝ)))
  else 0
/-- The fixed companion constant whose factorial orbit controls the carry congruence. Local copy of ErdosProblems.Erdos68.companionConstant, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def companionConstant : ℝ :=
  ∑' n : ℕ, compConstTerm n
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
/-- The exact rational prefix of the Erdős #68 series through index `n`. Local copy of ErdosProblems.Erdos68.factorialGapPrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)
/-- Strict successor of the factorially scaled prefix. Local copy of ErdosProblems.Erdos68.strictFacTop, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def strictFacTop (x : ℝ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℝ) * x⌋ + 1
/-- Distance from the strict factorial successor of the preceding actual prefix to that scaled prefix. Unlike an ordinary fractional-part complement, this takes the value one when the scaled prefix is integral. Local copy of ErdosProblems.Erdos68.factorialGapPredecessorGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapPredecessorGap (m : ℕ) : ℝ :=
  (strictFacTop
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ) (m - 1) : ℝ) -
    ((m - 1).factorial : ℝ) *
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ)
/-- The exact rounding carry in the strict-successor recurrence for the Erdős #68 prefixes. Local copy of ErdosProblems.Erdos68.factorialGapStepCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapStepCarry (m : ℕ) : ℤ :=
  -⌊1 + 1 / ((m.factorial : ℝ) - 1) -
      (m : ℝ) * factorialGapPredecessorGap m⌋
/-- The factorial moment of a finite-support coefficient vector. Local copy of ErdosProblems.Erdos68.factorialMoment, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialMoment (lam : ℕ →₀ ℤ) : ℤ :=
  lam.sum fun i z => z * (i.factorial : ℤ)
/-- Computable rational form of `strictFacTop`, used for exact finite certificates while retaining the real-valued statement needed for the series. Local copy of ErdosProblems.Erdos68.strictFacTopRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℚ) * x⌋ + 1
end PalomarCorpus.E68.PaperStatementsA
