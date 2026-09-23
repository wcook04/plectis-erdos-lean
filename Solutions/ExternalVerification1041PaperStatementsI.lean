/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos1041.SharpCollinearChebyshev

/-!
# Independent restatements for Erdős problem #1041

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1041.SharpCollinearChebyshev`.
-/

open Set
open Polynomial

namespace Erdos249257.ExternalVerification1041PaperStatementsI

noncomputable def endpointScale (n : ℕ) : ℝ :=
  Real.cos (Real.pi / (2 * (n : ℝ)))

noncomputable def comparisonBound (n : ℕ) : ℝ :=
  |((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n|

theorem exists_peak_le_comparisonBound
    {m : ℕ} {p : ℝ[X]} {c : Fin (m + 1) → ℝ}
    (hp : p.IsMonicOfDegree (m + 2))
    (hc : StrictMono c) (ha : -1 < c 0) (hb : c (Fin.last m) < 1)
    (hpa : p.eval (-1) = 0) (hpb : p.eval 1 = 0)
    (hpalt : ∀ i : Fin m,
      p.eval (c i.castSucc) * p.eval (c i.succ) < 0)
    (hc_mem : ∀ i : Fin (m + 1), |c i| ≤ 1) :
    ∃ i : Fin (m + 1), |p.eval (c i)| ≤ comparisonBound (m + 2) := @ErdosProblems.Erdos1041.SharpCollinearChebyshev.exists_peak_le_comparisonBound m p c hp hc ha hb hpa hpb hpalt hc_mem

end Erdos249257.ExternalVerification1041PaperStatementsI
