/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1049

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `a25cb360bef8dd818dde14b5fb752244304af354` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1049.PaperCompleteR21.SimultaneousMahlerSystem`,
`ErdosProblems.Erdos1049.PaperCompleteR21.SimultaneousMahlerSystemUnconditional`.
-/

open scoped LaurentSeries
open scoped PowerSeries
open scoped Polynomial
open scoped RatFunc
open Filter
open Topology

namespace Erdos249257.ExternalVerification1049PaperStructuresL

noncomputable def divisorLambert : ℚ⸨X⸩ :=
  HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.mk fun n => (n.divisors.card : ℚ))

noncomputable def kpos (k : ℕ) : ℤ := ((max k 1 : ℕ) : ℤ)

noncomputable def kpos_pos (k : ℕ) : 0 < kpos k := by
  have h : 1 ≤ max k 1 := le_max_right k 1
  have h' : (1 : ℤ) ≤ ((max k 1 : ℕ) : ℤ) := by exact_mod_cast h
  exact lt_of_lt_of_le zero_lt_one h'

noncomputable def subs (k : ℕ) : ℚ⸨X⸩ →+* ℚ⸨X⸩ :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (kpos k))
    (fun _ _ h => mul_left_cancel₀ (kpos_pos k).ne' h)
    (fun _ _ => ⟨fun h => le_of_mul_le_mul_left h (kpos_pos k),
      fun h => mul_le_mul_of_nonneg_left h (kpos_pos k).le⟩)

/-- States long1049:res:nomahler from the long record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperCompleteR21.no_finite_simultaneous_two_three_system_unconditional
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem no_finite_simultaneous_two_three_system_unconditional :
    ¬ ∃ V : Submodule (RatFunc ℚ) ℚ⸨X⸩,
        Module.Finite (RatFunc ℚ) V ∧
        divisorLambert ∈ V ∧
        (∀ f ∈ V, subs 2 f ∈ V) ∧ (∀ f ∈ V, subs 3 f ∈ V) := by
  sorry

end Erdos249257.ExternalVerification1049PaperStructuresL
