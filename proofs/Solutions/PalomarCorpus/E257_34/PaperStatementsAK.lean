/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusExactTransition
import Erdos249257.BooleanMobiusLocalRepair
import ErdosProblems.Erdos257.PaperCompleteR21.MersenneQuotientRowRecurrences
import Solutions.PalomarCorpus.E257_34.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAK
export PalomarCorpus.E257_34.Shared (endpointDivisorContribution localBinarySuffix localMersenneQuotient localPrefixQuotient)

theorem paper_floor_quotient_geometric_sum {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient M d = ∑ j ∈ Finset.Icc 1 (M / d), 2 ^ (M - j * d) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_floor_quotient_geometric_sum M d hd

theorem paper_next_floor_quotient {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient (M + 1) d =
      2 * localMersenneQuotient M d + (if d ∣ M + 1 then 1 else 0) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_next_floor_quotient M d hd

theorem paper_next_floor_quotient_no_fixed_point {M d : ℕ} (hd : 2 ≤ d)
    (hfix : localMersenneQuotient (M + 1) d = localMersenneQuotient M d) :
    localMersenneQuotient M d = 0 ∧ localMersenneQuotient (M + 1) d = 0 := @ErdosProblems.Erdos257.PaperCompleteR21.paper_next_floor_quotient_no_fixed_point M d hd hfix

theorem paper_next_quotient_sum {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d) :
    localPrefixQuotient D (M + 1) =
      2 * localPrefixQuotient D M + endpointDivisorContribution D (M + 1) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_next_quotient_sum D M hD

theorem paper_repair_integer_eq_endpoint_defect {D : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d)
    (hbelow : localPrefixQuotient D M ≤ halfEndpointTarget M) :
    localRepairInteger D 1 (M + 1) = localEndpointDefect D (M + 1) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_repair_integer_eq_endpoint_defect D M hM hD hbelow

theorem paper_signed_endpoint_defect_succ {D : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d) :
    localEndpointDefect D (M + 1) =
      2 * localEndpointDefect D M + 1 -
        (endpointDivisorContribution D (M + 1) : ℤ) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_signed_endpoint_defect_succ D M hM hD

theorem paper_signed_endpoint_recurrence (D : Finset ℕ) (k n : ℕ) :
    localRepairInteger D k n =
      2 * (localBinarySuffix D k (n - 1) : ℤ) + 1 -
        (endpointDivisorContribution D n : ℤ) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_signed_endpoint_recurrence D k n

end PalomarCorpus.E257.PaperStatementsAK
