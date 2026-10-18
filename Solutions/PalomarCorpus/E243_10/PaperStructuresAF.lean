/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR21.NonintegralRegularRate
import Solutions.PalomarCorpus.E243_10.Statement

open Filter

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E243.PaperStructuresAF

theorem nonintegral_regular_rate_irrational
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (l : ℝ) (hl : 1 < l) (hnonint : ∀ d : ℕ, l ≠ (d : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) ^ l *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + l / (n : ℝ))))
      atTop (nhds 0)) :
    Irrational (∑' n : ℕ, 1 / (a n : ℝ)) := by
  first
  | exact @ErdosProblems.Erdos243.PaperCompleteR21.nonintegral_regular_rate_irrational a ha hpos l hl hnonint hrate
    done
  | set_option smartUnfolding false in
    exact @ErdosProblems.Erdos243.PaperCompleteR21.nonintegral_regular_rate_irrational a ha hpos l hl hnonint hrate
    done
  | apply ErdosProblems.Erdos243.PaperCompleteR21.nonintegral_regular_rate_irrational <;> assumption
    done
  | simpa using ErdosProblems.Erdos243.PaperCompleteR21.nonintegral_regular_rate_irrational
    done
  | set_option smartUnfolding false in
    with_unfolding_all exact @ErdosProblems.Erdos243.PaperCompleteR21.nonintegral_regular_rate_irrational a ha hpos l hl hnonint hrate
    done
  | with_unfolding_all exact @ErdosProblems.Erdos243.PaperCompleteR21.nonintegral_regular_rate_irrational a ha hpos l hl hnonint hrate
    done

end PalomarCorpus.E243.PaperStructuresAF
