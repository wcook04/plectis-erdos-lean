/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_29

Every non-theorem declaration of `PalomarCorpus/E249_29/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter Topology
open scoped BigOperators
open Module
open ArithmeticFunction

namespace PalomarCorpus.E249.CompleteKernelBases
open Filter Topology
open scoped BigOperators
/-- The rational-valued sequence n ↦ φ(k^j n + r). -/
noncomputable def allBaseTotientKernelSeq (k j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (k ^ j * n + r)
/-- Two initial channels and, through level e, the channels whose residues are not divisible by k. -/
noncomputable abbrev AllBaseCanonicalIndex (k e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)
/-- The residue k times the selected quotient plus a selected nonzero remainder below k. -/
noncomputable def allBaseCanonicalResidue (k : ℕ) {e : ℕ}
    (x : Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)) : ℕ :=
  k * x.2.1.val + (x.2.2.val + 1)
/-- The two initial zero-residue channels together with all selected residues not divisible by k through level e. -/
noncomputable def allBaseCanonicalFamily (k e : ℕ) : AllBaseCanonicalIndex k e → ℕ → ℚ
  | Sum.inl i => allBaseTotientKernelSeq k i.val 0
  | Sum.inr x => allBaseTotientKernelSeq k (x.1.val + 1) (allBaseCanonicalResidue k x)
/-- All base-k kernel indices at levels zero through e, inclusive. -/
noncomputable abbrev AllBaseThroughLevelIndex (k e : ℕ) := Σ j : Fin (e + 1), Fin (k ^ j.val)
/-- All rational-valued base-k totient subsequences through level e. -/
noncomputable def allBaseThroughLevelFamily (k e : ℕ) : AllBaseThroughLevelIndex k e → ℕ → ℚ
  | ⟨j, r⟩ => allBaseTotientKernelSeq k j.val r.val
/-- The product of 1 − 1/p over primes p dividing k but not u. -/
noncomputable def missingEulerProduct (k u : ℕ) : ℚ :=
  ∏ p ∈ k.primeFactors.filter (fun p => ¬ p ∣ u), (1 - (p : ℚ)⁻¹)
/-- The dyadic section `n ↦ φ(2 ^ j n + r)` of Euler's totient at level `j` and residue `r`, with values in `ℚ` through the cast from `ℕ`. -/
noncomputable def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)
/-- The dyadic kernel indices at levels zero through e, inclusive. -/
noncomputable abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)
/-- The family of rational-valued totient subsequences through dyadic level e. -/
noncomputable def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val
/-- All pairs of a dyadic level j and a residue below 2^j. -/
noncomputable abbrev TotientDyadicKernelIndex := Σ j : ℕ, Fin (2 ^ j)
/-- Every dyadic subsequence n ↦ φ(2^j n + r), viewed as a rational-valued sequence. -/
noncomputable def fullTotientKernelFamily : TotientDyadicKernelIndex → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j r.val
/-- Two initial channels together with every odd-residue channel at a positive dyadic level. -/
noncomputable abbrev TotientOddCoreIndex := Fin 2 ⊕ Σ j : ℕ, Fin (2 ^ j)
/-- The two initial zero-residue channels and all odd-residue dyadic channels, as rational-valued sequences. -/
noncomputable def oddCoreTotientKernelFamily : TotientOddCoreIndex → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j + 1) (2 * r.val + 1)
/-- The inclusion of the two initial and odd-residue channels into the full dyadic index set. -/
noncomputable def fullRetainedChannel : TotientOddCoreIndex → TotientDyadicKernelIndex
  | Sum.inl i => ⟨i.val, ⟨0, by positivity⟩⟩
  | Sum.inr ⟨j, r⟩ => ⟨j + 1, ⟨2 * r.val + 1, by
      have hr := r.isLt
      rw [pow_succ]
      omega⟩⟩
/-- The space of finitely supported rational relations among all dyadic totient subsequences, defined as the kernel of their linear-combination map. -/
noncomputable abbrev FullRelations := LinearMap.ker (Finsupp.linearCombination ℚ fullTotientKernelFamily)
/-- The dyadic channels outside the retained initial and odd-residue channels. -/
noncomputable abbrev FullOmitted := {i : TotientDyadicKernelIndex // i ∉ Set.range fullRetainedChannel}
end PalomarCorpus.E249.CompleteKernelBases

namespace PalomarCorpus.E249.TotientKernelBasis
open scoped BigOperators
open Module
open ArithmeticFunction
open Filter Topology
open Module
/-- The base-`k` kernel channel `n ↦ φ(k ^ j n + r)` at level `j` and residue `r`, with values in `ℚ` through the cast from `ℕ`. -/
noncomputable def kernelSeq (k j r : ℕ) : ℕ → ℚ := fun n =>
  (Nat.totient (k ^ j * n + r) : ℚ)
/-- Index type for the canonical base-`k` family through level `e`: two zero-residue channels, and at each level `j + 1` with `j < e` one channel per pair `(s, u)` with `s < k ^ j` and `u < k - 1`, which parametrises exactly the residues `1 ≤ r < k ^ (j + 1)` with `k` not dividing `r`. -/
noncomputable abbrev CanonicalIndex (k e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)
/-- The canonical residue `k s + (u + 1)` named by a positive-level index `⟨j, (s, u)⟩`. The retained condition is that `k` does not divide the residue, which at a composite base is weaker than the residue being coprime to `k`. -/
noncomputable def canonicalResidue (k : ℕ) {e : ℕ}
    (x : Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)) : ℕ :=
  k * x.2.1.val + (x.2.2.val + 1)
/-- The canonical level-`e` family of base-`k` totient channels: a left index `i ∈ Fin 2` gives `n ↦ φ(k ^ i n)`, and a right index `x` at level `j + 1` gives `n ↦ φ(k ^ (j + 1) n + canonicalResidue k x)`. -/
noncomputable def canonicalFamily (k e : ℕ) : CanonicalIndex k e → ℕ → ℚ
  | Sum.inl i => kernelSeq k i.val 0
  | Sum.inr x => kernelSeq k (x.1.val + 1) (canonicalResidue k x)
/-- Index type for the complete unreduced base-`k` kernel through level `e`: all pairs `⟨j, r⟩` with `j ≤ e` and `r < k ^ j`, so the type has `1 + k + ⋯ + k ^ e` elements. -/
noncomputable abbrev ThroughLevelIndex (k e : ℕ) := Σ j : Fin (e + 1), Fin (k ^ j.val)
/-- The complete unreduced family of base-`k` totient channels through level `e`, sending `⟨j, r⟩` to `n ↦ φ(k ^ j n + r)`. -/
noncomputable def throughLevelFamily (k e : ℕ) : ThroughLevelIndex k e → ℕ → ℚ
  | ⟨j, r⟩ => kernelSeq k j.val r.val
/-- The `ℚ`-linear evaluation map sending a formal combination of the `1 + k + ⋯ + k ^ e` unreduced channel symbols to the corresponding function `ℕ → ℚ`. Its kernel is the module of `ℚ`-linear relations among those channels. -/
noncomputable def relationMap (k e : ℕ) :
    (ThroughLevelIndex k e → ℚ) →ₗ[ℚ] (ℕ → ℚ) :=
  Fintype.linearCombination ℚ (throughLevelFamily k e)
/-- The `ℤ`-linear span, inside the functions `ℕ → ℚ`, of the complete unreduced base-`k` family through level `e`. -/
noncomputable abbrev IntegralChannelSpan (k e : ℕ) :=
  Submodule.span ℤ (Set.range (throughLevelFamily k e))
/-- The unreduced channel retained for each canonical index: a left index `i` gives the zero-residue channel `⟨i, 0⟩`, and a right index `x` at level `j + 1` gives the channel `⟨j + 1, canonicalResidue k x⟩`. The hypotheses `2 ≤ k` and `1 ≤ e` supply the bounds that make these valid indices. -/
noncomputable def retainedChannel (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    CanonicalIndex k e → ThroughLevelIndex k e
  | Sum.inl i =>
      ⟨⟨i.val, by have hi := i.isLt; omega⟩,
        ⟨0, pow_pos (by omega : 0 < k) _⟩⟩
  | Sum.inr x =>
      ⟨⟨x.1.val + 1, by have hx := x.1.isLt; omega⟩,
        ⟨canonicalResidue k x, by
          show k * x.2.1.val + (x.2.2.val + 1) < k ^ (x.1.val + 1)
          have hs : x.2.1.val + 1 ≤ k ^ x.1.val := x.2.1.isLt
          have hu : x.2.2.val < k - 1 := x.2.2.isLt
          calc k * x.2.1.val + (x.2.2.val + 1) < k * x.2.1.val + k := by omega
            _ = k * (x.2.1.val + 1) := by ring
            _ ≤ k * k ^ x.1.val := Nat.mul_le_mul_left k hs
            _ = k ^ (x.1.val + 1) := by ring⟩⟩
/-- The unreduced channel indices through level `e` that are not retained channels. -/
noncomputable abbrev OmittedIntegralChannel (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :=
  { i : ThroughLevelIndex k e // i ∉ Set.range (retainedChannel k e hk he) }
/-- The `ℤ`-linear evaluation sending a finitely supported integer combination of the unreduced channel symbols through level `e` to the corresponding element of their integral span. -/
noncomputable def integralChannelEvaluation (k e : ℕ) :
    (ThroughLevelIndex k e →₀ ℤ) →ₗ[ℤ] IntegralChannelSpan k e :=
  Finsupp.linearCombination ℤ
    (fun i => (⟨throughLevelFamily k e i, Submodule.subset_span ⟨i, rfl⟩⟩ :
      IntegralChannelSpan k e))
/-- The module of integer relations among the unreduced channels through level `e`, the kernel of the integral evaluation. -/
noncomputable abbrev IntegralRelations (k e : ℕ) :=
  LinearMap.ker (integralChannelEvaluation k e)
end PalomarCorpus.E249.TotientKernelBasis
