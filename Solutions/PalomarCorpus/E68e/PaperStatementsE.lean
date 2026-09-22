/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.ChannelIntegralCongruence
import ErdosProblems.Erdos68.PaperCompleteExisting
import Solutions.PalomarCorpus.E68e.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E68.PaperStatementsE

theorem product_lcm_pairwise_gcd (xs : List ℕ) :
    xs.prod ∣ listLCM xs * pairwiseGCDProduct xs := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos68.PaperComplete.product_lcm_pairwise_gcd xs

end PalomarCorpus.E68.PaperStatementsE
