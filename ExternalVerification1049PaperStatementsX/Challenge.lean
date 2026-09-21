/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1049

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1049.PaperCompleteR21.SimultaneousMahlerSystem`.
-/

open scoped LaurentSeries
open scoped PowerSeries
open scoped Polynomial
open scoped RatFunc
open Filter
open Topology

namespace Erdos249257.ExternalVerification1049PaperStatementsX

noncomputable def subs (k : ℕ) : ℚ⸨X⸩ →+* ℚ⸨X⸩ :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (kpos k))
    (fun _ _ h => mul_left_cancel₀ (kpos_pos k).ne' h)
    (fun _ _ => ⟨fun h => le_of_mul_le_mul_left h (kpos_pos k),
      fun h => mul_le_mul_of_nonneg_left h (kpos_pos k).le⟩)

noncomputable def IsMahler (k : ℕ) (f : ℚ⸨X⸩) : Prop :=
  ∃ (d : ℕ) (p : ℕ → ℚ[X]), p 0 ≠ 0 ∧
    ∑ i ∈ Finset.range (d + 1), algebraMap ℚ[X] ℚ⸨X⸩ (p i) * subs (k ^ i) f = 0

noncomputable def AdamczewskiBell : Prop :=
  ∀ k l : ℕ, 2 ≤ k → 2 ≤ l → (∀ a b : ℕ, k ^ a = l ^ b → a = 0 ∧ b = 0) →
    ∀ f : ℚ⸨X⸩, IsMahler k f → IsMahler l f →
      f ∈ Set.range (algebraMap (RatFunc ℚ) ℚ⸨X⸩)

noncomputable def divisorLambert : ℚ⸨X⸩ :=
  HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.mk fun n => (n.divisors.card : ℚ))

/-- States long1049:res:nomahler from the long record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.no_finite_simultaneous_two_three_system in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem no_finite_simultaneous_two_three_system (hAB : AdamczewskiBell) :
    ¬ ∃ V : Submodule (RatFunc ℚ) ℚ⸨X⸩,
        Module.Finite (RatFunc ℚ) V ∧
        divisorLambert ∈ V ∧
        (∀ f ∈ V, subs 2 f ∈ V) ∧ (∀ f ∈ V, subs 3 f ∈ V) := by
  sorry

end Erdos249257.ExternalVerification1049PaperStatementsX
