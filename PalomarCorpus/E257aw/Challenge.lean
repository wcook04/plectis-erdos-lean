/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band w

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Set
open scoped BigOperators

namespace PalomarCorpus.E257.PaperStructuresAW
open Filter
open Set
open scoped BigOperators
/-- Structural part of an endpoint-by-endpoint repair trajectory. The arithmetic producer receipts are separated into `GlobalBooleanMobiusRepairFeasible` below. Local copy of Erdos249257.BooleanMobiusGlobalRepairTrajectory, restated so the compared statements elaborate against Mathlib alone. -/
structure BooleanMobiusGlobalRepairTrajectory where
  bit : ℕ → ℕ → Bool
  frozen_step : ∀ {n d : ℕ}, 2 * d ≤ n → bit (n + 1) d = bit n d
/-- Number of selected lower ranks which divide the next endpoint. Local copy of Erdos249257.endpointDivisorContribution, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def endpointDivisorContribution (D : Finset ℕ) (n : ℕ) : ℕ :=
  (D.filter fun d ↦ d ∣ n).card
/-- The finite Boolean support displayed by row `n`. Coordinates zero and one are normalized away at the definition boundary. Local copy of Erdos249257.globalRepairStageSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def globalRepairStageSupport (bit : ℕ → ℕ → Bool) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter fun d ↦ bit n d = true
/-- The part of row `n` which is already frozen before its upper-half rewrite. Local copy of Erdos249257.globalRepairLowerSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def globalRepairLowerSupport (bit : ℕ → ℕ → Bool) (n : ℕ) : Finset ℕ :=
  (globalRepairStageSupport bit n).filter fun d ↦ d ≤ n / 2
/-- The integral part of `2^M / (2^d - 1)`. Local copy of Erdos249257.localMersenneQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
/-- Sum of the integral quotient contributions of a finite Boolean support. Local copy of Erdos249257.localPrefixQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d
/-- The carry left after reading the nonterminating binary expansion of `2⁻ᵏ` through place `M` and subtracting the quotient contributions of `D`. The theorem below proves that the truncating natural subtraction is honest in the endpoint situation where it is used. Local copy of Erdos249257.localBinarySuffix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localBinarySuffix (D : Finset ℕ) (k M : ℕ) : ℕ :=
  2 ^ (M - k) - localPrefixQuotient D M - 1
/-- The next signed Boolean--Möbius coefficient supplied by the binary carry recurrence. Local copy of Erdos249257.localRepairInteger, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localRepairInteger (D : Finset ℕ) (k n : ℕ) : ℤ :=
  2 * (localBinarySuffix D k (n - 1) : ℤ) + 1 -
    (endpointDivisorContribution D n : ℤ)
/-- States record:257bm-c3 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_compatible_first_condition_gives_nonneg in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_compatible_first_condition_gives_nonneg
    (T : BooleanMobiusGlobalRepairTrajectory)
    (hbound : ∀ n : ℕ, 2 ≤ n →
      2 ^ (endpointDivisorContribution (globalRepairLowerSupport T.bit n) n - 1)
          - 1 ≤
        localBinarySuffix (globalRepairLowerSupport T.bit n) 1 (n - 1))
    {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ localRepairInteger (globalRepairLowerSupport T.bit n) 1 n := by
  sorry
end PalomarCorpus.E257.PaperStructuresAW
