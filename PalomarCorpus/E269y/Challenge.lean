/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #269, band y

Erdős problem #269 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E269` under the Challenge size ceiling; it does not replace it.
-/

open Polynomial
open scoped BigOperators

namespace PalomarCorpus.E269.PaperStatementsY
open Polynomial
open scoped BigOperators
/-- The Hecke--Mahler series `F_θ(β,α) = ∑_{n≥1} ∑_{k=1}^{⌊nθ⌋} β^n α^k`. The outer index runs over all `n ≥ 0`; the inner sum is empty at `n = 0`. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.heckeMahlerSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def heckeMahlerSeries (θ β α : ℝ) : ℝ :=
  ∑' n : ℕ, ∑ k ∈ Finset.Icc 1 ⌊(n : ℝ) * θ⌋₊, β ^ n * α ^ k
/-- Bugeaud and Laurent, Theorem 1.1, in the case `ρ = 0` due to Loxton and van der Poorten, Theorem 8, p. 40: the Hecke--Mahler series takes transcendental values at nonzero algebraic arguments inside the stated region. This is the one external input of the two-prime theorem. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.BugeaudLaurentTranscendence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def BugeaudLaurentTranscendence : Prop :=
  ∀ θ β α : ℝ, Irrational θ → 0 < θ → θ < 1 →
    IsAlgebraic ℚ β → IsAlgebraic ℚ α → β ≠ 0 → α ≠ 0 →
    |β| < 1 → |β| * |α| ^ θ < 1 →
    Transcendental ℚ (heckeMahlerSeries θ β α)
/-- Exact value named `A` on the page; this definition makes no arithmetic assertion. Local copy of ErdosProblems.Erdos269.PaperR7.twoPrimeHeckeValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def twoPrimeHeckeValue (p q : ℕ) : ℝ :=
  ∑' n : ℕ, ((p : ℝ)⁻¹) ^ n *
    ((q : ℝ)⁻¹) ^ ⌊(n : ℝ) * Real.logb q p⌋₊
/-- States long269:res:lead-two-prime, res:two-prime-transcendence from the long record and the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR21.transcendental_heckeValue in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem transcendental_heckeValue (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Transcendental ℚ (twoPrimeHeckeValue p q) := by
  sorry
end PalomarCorpus.E269.PaperStatementsY
