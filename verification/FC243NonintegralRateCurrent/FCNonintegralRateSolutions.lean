-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0

import ErdosProblems.Erdos243.PaperCompleteR21.NonintegralRegularRate

open Filter
open scoped Topology BigOperators

namespace Erdos243

/-- Exact zero-indexed receiving statement for the nonintegral regular-rate
irrationality theorem. Summability is derived by the source theorem. -/
theorem erdos_243.variants.nonintegral_regular_rate
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (l : ℝ) (hl : 1 < l) (hnonint : ∀ d : ℕ, l ≠ (d : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) ^ l *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + l / (n : ℝ))))
      atTop (nhds 0)) :
    Irrational (∑' n : ℕ, 1 / (a n : ℝ)) := by
  exact ErdosProblems.Erdos243.PaperCompleteR21.nonintegral_regular_rate_irrational
    a ha hpos l hl hnonint hrate

#print axioms erdos_243.variants.nonintegral_regular_rate

end Erdos243
