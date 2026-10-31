/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1049_06

Every non-theorem declaration of `PalomarCorpus/E1049_06/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped LaurentSeries
open scoped PowerSeries
open scoped Polynomial
open scoped RatFunc
open Filter
open Topology

namespace PalomarCorpus.E1049_06.Shared
/-- `ℒ(z) = ∑_{n ≥ 1} zⁿ/(1 - zⁿ) = ∑_{n ≥ 1} τ(n) zⁿ`, the divisor generating series, as a formal Laurent series over `ℚ`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.divisorLambert, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def divisorLambert : ℚ⸨X⸩ :=
  HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.mk fun n => (n.divisors.card : ℚ))
/-- `max k 1`, as an integer. Using `max k 1` keeps the substitution below a total function of `k`; every statement about it carries `1 ≤ k`, where it is `k`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.kpos, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def kpos (k : ℕ) : ℤ := ((max k 1 : ℕ) : ℤ)
/-- Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.kpos_pos, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def kpos_pos (k : ℕ) : 0 < kpos k := by
  have h : 1 ≤ max k 1 := le_max_right k 1
  have h' : (1 : ℤ) ≤ ((max k 1 : ℕ) : ℤ) := by exact_mod_cast h
  exact lt_of_lt_of_le zero_lt_one h'
/-- The substitution `z ↦ z ^ k` on `ℚ((z))`, as a ring homomorphism. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.subs, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def subs (k : ℕ) : ℚ⸨X⸩ →+* ℚ⸨X⸩ :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (kpos k))
    (fun _ _ h => mul_left_cancel₀ (kpos_pos k).ne' h)
    (fun _ _ => ⟨fun h => le_of_mul_le_mul_left h (kpos_pos k),
      fun h => mul_le_mul_of_nonneg_left h (kpos_pos k).le⟩)
end PalomarCorpus.E1049_06.Shared

namespace PalomarCorpus.E1049.PaperStatementsX
open scoped LaurentSeries
open scoped PowerSeries
open scoped Polynomial
open scoped RatFunc
open Filter
open Topology
export PalomarCorpus.E1049_06.Shared (divisorLambert kpos kpos_pos subs)
/-- `f` satisfies a `k`-Mahler functional equation: there are polynomials `p 0, …, p d` over `ℚ` with `p 0 ≠ 0` and `∑_{i ≤ d} pᵢ(z) · f(z^{k^i}) = 0`. The nonvanishing of the coefficient of the *unshifted* function is part of the definition, as in Adamczewski-Bell; the paper's proof is written exactly to produce it. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.IsMahler, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsMahler (k : ℕ) (f : ℚ⸨X⸩) : Prop :=
  ∃ (d : ℕ) (p : ℕ → ℚ[X]), p 0 ≠ 0 ∧
    ∑ i ∈ Finset.range (d + 1), algebraMap ℚ[X] ℚ⸨X⸩ (p i) * subs (k ^ i) f = 0
/-- The theorem of Adamczewski and Bell [Thm. 1.1, p. 6], as a hypothesis: for multiplicatively independent `k, l ≥ 2`, a Laurent series over `ℚ` that is both `k`-Mahler and `l`-Mahler is a rational function. This is the only external input; it is proved neither here nor in Mathlib. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.AdamczewskiBell, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def AdamczewskiBell : Prop :=
  ∀ k l : ℕ, 2 ≤ k → 2 ≤ l → (∀ a b : ℕ, k ^ a = l ^ b → a = 0 ∧ b = 0) →
    ∀ f : ℚ⸨X⸩, IsMahler k f → IsMahler l f →
      f ∈ Set.range (algebraMap (RatFunc ℚ) ℚ⸨X⸩)
end PalomarCorpus.E1049.PaperStatementsX

namespace PalomarCorpus.E1049.PaperStructuresL
open scoped LaurentSeries
open scoped PowerSeries
open scoped Polynomial
open scoped RatFunc
open Filter
open Topology
export PalomarCorpus.E1049_06.Shared (divisorLambert kpos kpos_pos subs)
end PalomarCorpus.E1049.PaperStructuresL
