/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1049, band x

Erdős problem #1049 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1049` under the Challenge size ceiling; it does not replace it.
-/

open scoped LaurentSeries
open scoped PowerSeries
open scoped Polynomial
open scoped RatFunc
open Filter
open Topology

namespace PalomarCorpus.E1049.PaperStatementsX
open scoped LaurentSeries
open scoped PowerSeries
open scoped Polynomial
open scoped RatFunc
open Filter
open Topology
/-- The substitution `z ↦ z ^ k` on `ℚ((z))`, as a ring homomorphism. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.subs, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def subs (k : ℕ) : ℚ⸨X⸩ →+* ℚ⸨X⸩ :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (kpos k))
    (fun _ _ h => mul_left_cancel₀ (kpos_pos k).ne' h)
    (fun _ _ => ⟨fun h => le_of_mul_le_mul_left h (kpos_pos k),
      fun h => mul_le_mul_of_nonneg_left h (kpos_pos k).le⟩)
/-- `f` satisfies a `k`-Mahler functional equation: there are polynomials `p 0, …, p d` over `ℚ` with `p 0 ≠ 0` and `∑_{i ≤ d} pᵢ(z) · f(z^{k^i}) = 0`. The nonvanishing of the coefficient of the *unshifted* function is part of the definition, as in Adamczewski–Bell; the paper's proof is written exactly to produce it. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.IsMahler, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsMahler (k : ℕ) (f : ℚ⸨X⸩) : Prop :=
  ∃ (d : ℕ) (p : ℕ → ℚ[X]), p 0 ≠ 0 ∧
    ∑ i ∈ Finset.range (d + 1), algebraMap ℚ[X] ℚ⸨X⸩ (p i) * subs (k ^ i) f = 0
/-- The theorem of Adamczewski and Bell [Thm. 1.1, p. 6], as a hypothesis: for multiplicatively independent `k, l ≥ 2`, a Laurent series over `ℚ` that is both `k`-Mahler and `l`-Mahler is a rational function. This is the only external input; it is proved neither here nor in Mathlib. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.AdamczewskiBell, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def AdamczewskiBell : Prop :=
  ∀ k l : ℕ, 2 ≤ k → 2 ≤ l → (∀ a b : ℕ, k ^ a = l ^ b → a = 0 ∧ b = 0) →
    ∀ f : ℚ⸨X⸩, IsMahler k f → IsMahler l f →
      f ∈ Set.range (algebraMap (RatFunc ℚ) ℚ⸨X⸩)
/-- `ℒ(z) = ∑_{n ≥ 1} zⁿ/(1 - zⁿ) = ∑_{n ≥ 1} τ(n) zⁿ`, the divisor generating series, as a formal Laurent series over `ℚ`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.divisorLambert, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def divisorLambert : ℚ⸨X⸩ :=
  HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.mk fun n => (n.divisors.card : ℚ))
/-- States long1049:res:nomahler from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.no_finite_simultaneous_two_three_system in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem no_finite_simultaneous_two_three_system (hAB : AdamczewskiBell) :
    ¬ ∃ V : Submodule (RatFunc ℚ) ℚ⸨X⸩,
        Module.Finite (RatFunc ℚ) V ∧
        divisorLambert ∈ V ∧
        (∀ f ∈ V, subs 2 f ∈ V) ∧ (∀ f ∈ V, subs 3 f ∈ V) := by
  sorry
end PalomarCorpus.E1049.PaperStatementsX
