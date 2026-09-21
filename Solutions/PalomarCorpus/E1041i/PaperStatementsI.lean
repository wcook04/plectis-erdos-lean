/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.SharpCollinearChebyshev
import Solutions.PalomarCorpus.E1041i.Statement

open Set
open Polynomial

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsI

theorem exists_peak_le_comparisonBound
    {m : ℕ} {p : ℝ[X]} {c : Fin (m + 1) → ℝ}
    (hp : p.IsMonicOfDegree (m + 2))
    (hc : StrictMono c) (ha : -1 < c 0) (hb : c (Fin.last m) < 1)
    (hpa : p.eval (-1) = 0) (hpb : p.eval 1 = 0)
    (hpalt : ∀ i : Fin m,
      p.eval (c i.castSucc) * p.eval (c i.succ) < 0)
    (hc_mem : ∀ i : Fin (m + 1), |c i| ≤ 1) :
    ∃ i : Fin (m + 1), |p.eval (c i)| ≤ comparisonBound (m + 2) := @ErdosProblems.Erdos1041.SharpCollinearChebyshev.exists_peak_le_comparisonBound m p c hp hc ha hb hpa hpb hpalt hc_mem

end PalomarCorpus.E1041.PaperStatementsI
