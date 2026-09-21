/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1041, band i

Erdős problem #1041 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1041` under the Challenge size ceiling; it does not replace it.
-/

open Set
open Polynomial

namespace PalomarCorpus.E1041.PaperStatementsI
open Set
open Polynomial
/-- The scale that sends the two outermost roots of `T_n` to `-1` and `1`. Local copy of ErdosProblems.Erdos1041.SharpCollinearChebyshev.endpointScale, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def endpointScale (n : ℕ) : ℝ :=
  Real.cos (Real.pi / (2 * (n : ℝ)))
/-- The sharp normalised height. A later algebraic simplification rewrites this as `1 / (2^(n-1) * cos(pi/(2n))^n)`. Local copy of ErdosProblems.Erdos1041.SharpCollinearChebyshev.comparisonBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def comparisonBound (n : ℕ) : ℝ :=
  |((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n|
/-- States prop:sharp-collinear-chebyshev-comparator from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.SharpCollinearChebyshev.exists_peak_le_comparisonBound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_peak_le_comparisonBound
    {m : ℕ} {p : ℝ[X]} {c : Fin (m + 1) → ℝ}
    (hp : p.IsMonicOfDegree (m + 2))
    (hc : StrictMono c) (ha : -1 < c 0) (hb : c (Fin.last m) < 1)
    (hpa : p.eval (-1) = 0) (hpb : p.eval 1 = 0)
    (hpalt : ∀ i : Fin m,
      p.eval (c i.castSucc) * p.eval (c i.succ) < 0)
    (hc_mem : ∀ i : Fin (m + 1), |c i| ≤ 1) :
    ∃ i : Fin (m + 1), |p.eval (c i)| ≤ comparisonBound (m + 2) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsI
