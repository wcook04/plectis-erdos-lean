/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.PaperCompleteMomentIdeal
import Solutions.PalomarCorpus.E68_07.Statement

open scoped BigOperators
open Finsupp

namespace PalomarCorpus.E68.MomentIdeal

noncomputable def PrimitiveVector (f : ℕ →₀ ℤ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → ¬ ∃ g : ℕ →₀ ℤ, f = (k : ℤ) • g

theorem attainable_moment_ideal {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) (m : ℤ) :
    AttainsMoment D m ↔ minimumMoment D p ∣ m := by
  exact ErdosProblems.Erdos68.PaperComplete.attainable_moment_ideal hD hp hDp hpD m

theorem exact_moment_ideal_with_primitive_attainment {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    0 < minimumMoment D p ∧
    (∀ m : ℤ, AttainsMoment D m ↔ minimumMoment D p ∣ m) ∧
    ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧
      factorialMoment f = minimumMoment D p ∧ PrimitiveVector f := by
  exact ErdosProblems.Erdos68.PaperComplete.exact_moment_ideal_with_primitive_attainment hD hp hDp hpD

theorem minimum_moment_content_one {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧
      factorialMoment f = minimumMoment D p ∧ coefficientContent f = 1 := by
  exact ErdosProblems.Erdos68.PaperComplete.minimum_moment_content_one hD hp hDp hpD

theorem minimumMoment_independent_prime {D p q : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D)
    (hq : q.Prime) (hDq : D / 2 < q) (hqD : q ≤ D) :
    minimumMoment D p = minimumMoment D q := by
  exact ErdosProblems.Erdos68.PaperComplete.minimumMoment_independent_prime hD hp hDp hpD hq hDq hqD

end PalomarCorpus.E68.MomentIdeal
