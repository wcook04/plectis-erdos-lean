/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos243.PaperCompleteR21.NonintegralRegularRate

/-!
# Independent restatements for Erdős problem #243

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `436f55ebdafa67e4af0fff79f621c13f2ded12bf` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos243.PaperCompleteR21.NonintegralRegularRate`.
-/

open Filter

namespace Erdos249257.ExternalVerification243PaperStructuresAF

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

end Erdos249257.ExternalVerification243PaperStructuresAF
