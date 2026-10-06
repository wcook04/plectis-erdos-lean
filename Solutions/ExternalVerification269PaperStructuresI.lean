/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos269.DistinctHeightIrrationality

/-!
# Independent restatements for Erdős problem #269

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `436f55ebdafa67e4af0fff79f621c13f2ded12bf` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos269.DistinctHeightIrrationality`.
-/

open Finset
open Filter
open Topology

namespace Erdos249257.ExternalVerification269PaperStructuresI

noncomputable def jumpPoints235 : Set ℕ :=
  {t | ∃ n, 1 ≤ n ∧ (t = 2 ^ n ∨ t = 3 ^ n ∨ t = 5 ^ n)}

noncomputable def runningHeight235 (t : ℕ) : ℕ :=
  2 ^ Nat.log 2 t * 3 ^ Nat.log 3 t * 5 ^ Nat.log 5 t

noncomputable def distinctHeightSum235 : ℝ :=
  1 + ∑' t : jumpPoints235, (1 : ℝ) / (runningHeight235 t : ℝ)

theorem distinctHeightSum235_irrational : Irrational distinctHeightSum235 := by
  first
  | exact @ErdosProblems.Erdos269.distinctHeightSum235_irrational
    done
  | set_option smartUnfolding false in
    exact @ErdosProblems.Erdos269.distinctHeightSum235_irrational
    done
  | apply ErdosProblems.Erdos269.distinctHeightSum235_irrational <;> assumption
    done
  | simpa only [distinctHeightSum235, jumpPoints235, runningHeight235] using ErdosProblems.Erdos269.distinctHeightSum235_irrational
    done
  | set_option smartUnfolding false in
    with_unfolding_all exact @ErdosProblems.Erdos269.distinctHeightSum235_irrational
    done
  | with_unfolding_all exact @ErdosProblems.Erdos269.distinctHeightSum235_irrational
    done

end Erdos249257.ExternalVerification269PaperStructuresI
