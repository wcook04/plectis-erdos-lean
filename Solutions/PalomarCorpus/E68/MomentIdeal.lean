/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.PaperCompleteMomentIdeal
import Solutions.PalomarCorpus.E68.Shared

open scoped BigOperators
open Finsupp

namespace PalomarCorpus.E68.MomentIdeal
export PalomarCorpus.E68.Shared (adjacentDifference canonicalKernel channelBasisColumn channelLCM channelNumerator channelSynthesis channelWeight factorialMoment isolatedChannelUnit kernelCoordinates)

noncomputable def channelScalar (n : ℕ) : ℤ := isolatedChannelUnit n 1

noncomputable def finiteScalarGcd (D N : ℕ) : ℕ :=
  (Finset.Icc (D + 1) N).gcd (fun n => (channelScalar n).natAbs)

noncomputable def kernelOne (D : ℕ) : ℤ := canonicalKernel D 1

noncomputable def Admissible (f : ℕ →₀ ℤ) : Prop :=
  ∀ n ∈ f.support, 2 ≤ n

noncomputable def LowChannels (D : ℕ) (f : ℕ →₀ ℤ) : Prop :=
  ∀ d ∈ Finset.Icc 2 D, channelNumerator f d = 0

noncomputable def AttainsMoment (D : ℕ) (m : ℤ) : Prop :=
  ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧ factorialMoment f = m

noncomputable def minimumMoment (D p : ℕ) : ℤ :=
  let G : ℤ := finiteScalarGcd D (D * (2 * p - 1))
  (channelLCM D : ℤ) * (G / (Int.gcd G (kernelOne D) : ℤ))

noncomputable def PrimitiveVector (f : ℕ →₀ ℤ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → ¬ ∃ g : ℕ →₀ ℤ, f = (k : ℤ) • g

noncomputable def coefficientContent (f : ℕ →₀ ℤ) : ℕ :=
  f.support.gcd (fun n => (f n).natAbs)

theorem attainable_moment_ideal {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) (m : ℤ) :
    AttainsMoment D m ↔ minimumMoment D p ∣ m := by
  simpa [channelWeight, channelNumerator, factorialMoment, channelLCM,
    adjacentDifference, isolatedChannelUnit, channelScalar, finiteScalarGcd,
    channelBasisColumn, channelSynthesis, kernelCoordinates, canonicalKernel,
    kernelOne, Admissible, LowChannels, AttainsMoment, minimumMoment,
    PrimitiveVector, coefficientContent, ErdosProblems.Erdos68.channelWeight,
    ErdosProblems.Erdos68.channelNumerator, ErdosProblems.Erdos68.factorialMoment,
    ErdosProblems.Erdos68.channelLCM, ErdosProblems.Erdos68.adjacentDifference,
    ErdosProblems.Erdos68.isolatedChannelUnit,
    ErdosProblems.Erdos68.PaperComplete.channelScalar,
    ErdosProblems.Erdos68.PaperComplete.finiteScalarGcd,
    ErdosProblems.Erdos68.PaperComplete.channelBasisColumn,
    ErdosProblems.Erdos68.PaperComplete.channelSynthesis,
    ErdosProblems.Erdos68.PaperComplete.kernelCoordinates,
    ErdosProblems.Erdos68.PaperComplete.canonicalKernel,
    ErdosProblems.Erdos68.PaperComplete.kernelOne,
    ErdosProblems.Erdos68.PaperComplete.Admissible,
    ErdosProblems.Erdos68.PaperComplete.LowChannels,
    ErdosProblems.Erdos68.PaperComplete.AttainsMoment,
    ErdosProblems.Erdos68.PaperComplete.minimumMoment,
    ErdosProblems.Erdos68.PaperComplete.PrimitiveVector,
    ErdosProblems.Erdos68.PaperComplete.coefficientContent] using
    ErdosProblems.Erdos68.PaperComplete.attainable_moment_ideal hD hp hDp hpD m

theorem exact_moment_ideal_with_primitive_attainment {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    0 < minimumMoment D p ∧
    (∀ m : ℤ, AttainsMoment D m ↔ minimumMoment D p ∣ m) ∧
    ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧
      factorialMoment f = minimumMoment D p ∧ PrimitiveVector f := by
  simpa [channelWeight, channelNumerator, factorialMoment, channelLCM,
    adjacentDifference, isolatedChannelUnit, channelScalar, finiteScalarGcd,
    channelBasisColumn, channelSynthesis, kernelCoordinates, canonicalKernel,
    kernelOne, Admissible, LowChannels, AttainsMoment, minimumMoment,
    PrimitiveVector, coefficientContent, ErdosProblems.Erdos68.channelWeight,
    ErdosProblems.Erdos68.channelNumerator, ErdosProblems.Erdos68.factorialMoment,
    ErdosProblems.Erdos68.channelLCM, ErdosProblems.Erdos68.adjacentDifference,
    ErdosProblems.Erdos68.isolatedChannelUnit,
    ErdosProblems.Erdos68.PaperComplete.channelScalar,
    ErdosProblems.Erdos68.PaperComplete.finiteScalarGcd,
    ErdosProblems.Erdos68.PaperComplete.channelBasisColumn,
    ErdosProblems.Erdos68.PaperComplete.channelSynthesis,
    ErdosProblems.Erdos68.PaperComplete.kernelCoordinates,
    ErdosProblems.Erdos68.PaperComplete.canonicalKernel,
    ErdosProblems.Erdos68.PaperComplete.kernelOne,
    ErdosProblems.Erdos68.PaperComplete.Admissible,
    ErdosProblems.Erdos68.PaperComplete.LowChannels,
    ErdosProblems.Erdos68.PaperComplete.AttainsMoment,
    ErdosProblems.Erdos68.PaperComplete.minimumMoment,
    ErdosProblems.Erdos68.PaperComplete.PrimitiveVector,
    ErdosProblems.Erdos68.PaperComplete.coefficientContent] using
    ErdosProblems.Erdos68.PaperComplete.exact_moment_ideal_with_primitive_attainment
      hD hp hDp hpD

theorem minimum_moment_content_one {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧
      factorialMoment f = minimumMoment D p ∧ coefficientContent f = 1 := by
  simpa [channelWeight, channelNumerator, factorialMoment, channelLCM,
    adjacentDifference, isolatedChannelUnit, channelScalar, finiteScalarGcd,
    channelBasisColumn, channelSynthesis, kernelCoordinates, canonicalKernel,
    kernelOne, Admissible, LowChannels, AttainsMoment, minimumMoment,
    PrimitiveVector, coefficientContent, ErdosProblems.Erdos68.channelWeight,
    ErdosProblems.Erdos68.channelNumerator, ErdosProblems.Erdos68.factorialMoment,
    ErdosProblems.Erdos68.channelLCM, ErdosProblems.Erdos68.adjacentDifference,
    ErdosProblems.Erdos68.isolatedChannelUnit,
    ErdosProblems.Erdos68.PaperComplete.channelScalar,
    ErdosProblems.Erdos68.PaperComplete.finiteScalarGcd,
    ErdosProblems.Erdos68.PaperComplete.channelBasisColumn,
    ErdosProblems.Erdos68.PaperComplete.channelSynthesis,
    ErdosProblems.Erdos68.PaperComplete.kernelCoordinates,
    ErdosProblems.Erdos68.PaperComplete.canonicalKernel,
    ErdosProblems.Erdos68.PaperComplete.kernelOne,
    ErdosProblems.Erdos68.PaperComplete.Admissible,
    ErdosProblems.Erdos68.PaperComplete.LowChannels,
    ErdosProblems.Erdos68.PaperComplete.AttainsMoment,
    ErdosProblems.Erdos68.PaperComplete.minimumMoment,
    ErdosProblems.Erdos68.PaperComplete.PrimitiveVector,
    ErdosProblems.Erdos68.PaperComplete.coefficientContent] using
    ErdosProblems.Erdos68.PaperComplete.minimum_moment_content_one hD hp hDp hpD

theorem minimumMoment_independent_prime {D p q : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D)
    (hq : q.Prime) (hDq : D / 2 < q) (hqD : q ≤ D) :
    minimumMoment D p = minimumMoment D q := by
  simpa [channelWeight, channelNumerator, factorialMoment, channelLCM,
    adjacentDifference, isolatedChannelUnit, channelScalar, finiteScalarGcd,
    channelBasisColumn, channelSynthesis, kernelCoordinates, canonicalKernel,
    kernelOne, Admissible, LowChannels, AttainsMoment, minimumMoment,
    PrimitiveVector, coefficientContent, ErdosProblems.Erdos68.channelWeight,
    ErdosProblems.Erdos68.channelNumerator, ErdosProblems.Erdos68.factorialMoment,
    ErdosProblems.Erdos68.channelLCM, ErdosProblems.Erdos68.adjacentDifference,
    ErdosProblems.Erdos68.isolatedChannelUnit,
    ErdosProblems.Erdos68.PaperComplete.channelScalar,
    ErdosProblems.Erdos68.PaperComplete.finiteScalarGcd,
    ErdosProblems.Erdos68.PaperComplete.channelBasisColumn,
    ErdosProblems.Erdos68.PaperComplete.channelSynthesis,
    ErdosProblems.Erdos68.PaperComplete.kernelCoordinates,
    ErdosProblems.Erdos68.PaperComplete.canonicalKernel,
    ErdosProblems.Erdos68.PaperComplete.kernelOne,
    ErdosProblems.Erdos68.PaperComplete.Admissible,
    ErdosProblems.Erdos68.PaperComplete.LowChannels,
    ErdosProblems.Erdos68.PaperComplete.AttainsMoment,
    ErdosProblems.Erdos68.PaperComplete.minimumMoment,
    ErdosProblems.Erdos68.PaperComplete.PrimitiveVector,
    ErdosProblems.Erdos68.PaperComplete.coefficientContent] using
    ErdosProblems.Erdos68.PaperComplete.minimumMoment_independent_prime
      hD hp hDp hpD hq hDq hqD

end PalomarCorpus.E68.MomentIdeal
