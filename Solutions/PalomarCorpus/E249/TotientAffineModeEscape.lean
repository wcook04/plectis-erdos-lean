/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos249.TotientAffineModeEscape
import Solutions.PalomarCorpus.E249.Shared

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.TotientAffineModeEscape
export PalomarCorpus.E249.Shared (totientBlock)

noncomputable def pureDyadicEndpointError (H c : ℕ) (k : ℤ) : ℤ :=
  totientBlock H c - k * ((2 : ℤ) ^ H - 1)

noncomputable def EventuallyAffinePureDyadicEndpointError (c : ℕ) (k : ℤ) : Prop :=
  ∃ A B : ℤ, ∃ H0 : ℕ, ∀ H, H0 ≤ H →
    pureDyadicEndpointError H c k = A * H + B

theorem not_eventuallyAffine_pureDyadicEndpointError (c : ℕ) (k : ℤ) :
    ¬ EventuallyAffinePureDyadicEndpointError c k := by
  simpa only [EventuallyAffinePureDyadicEndpointError,
    pureDyadicEndpointError, totientBlock,
    ErdosProblems.Erdos249.PeriodMultipleEscape.EventuallyAffinePureDyadicEndpointError,
    ErdosProblems.Erdos249.PeriodMultipleEscape.pureDyadicEndpointError,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.totientBlock] using
    ErdosProblems.Erdos249.PeriodMultipleEscape.not_eventuallyAffine_pureDyadicEndpointError c k

end PalomarCorpus.E249.TotientAffineModeEscape
