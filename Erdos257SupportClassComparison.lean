-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
/-
Build root for the #257 R8 support-class comparison. It imports the three comparison modules
and the two finite-union closures, so one default target elaborates the whole closure in CI.

* `AnalyticIncomparability`: `exists_strengthened_not_old_or_weighted_host`,
  `old_cover_class_strictly_smaller`, `exists_incomparable_hosts_with_mixed_heredity`.
* `CoverGaugeComplete`, `ReverseStrengthenedHost`: the scalar gauge minimisation and the
  squarefree divisor-cube host used by the strengthened-but-not-old witness.
* `WeightedFiniteUnion`, `StrengthenedCoverFiniteUnion`: finite-union closure of the weighted
  class and of the strengthened-cover class (with closure constant 3).
-/

import ErdosProblems.Erdos257.PaperCompleteR8.AnalyticIncomparability
import ErdosProblems.Erdos257.PaperCompleteR8.CoverGaugeComplete
import ErdosProblems.Erdos257.PaperCompleteR8.ReverseStrengthenedHost
import ErdosProblems.Erdos257.PaperCompleteR8.WeightedFiniteUnion
import ErdosProblems.Erdos257.PaperCompleteR8.StrengthenedCoverFiniteUnion
