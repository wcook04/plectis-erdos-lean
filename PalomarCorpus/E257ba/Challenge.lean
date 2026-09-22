/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band a

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology

namespace PalomarCorpus.E257.PaperStructuresBA
open scoped BigOperators
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
/-- The integral part of `2^M / (2^d - 1)`. Local copy of Erdos249257.localMersenneQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
/-- Sum of the integral quotient contributions of a finite Boolean support. Local copy of Erdos249257.localPrefixQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d
/-- The exact rational Mersenne weight `1 / (2^n - 1)`. Its meaningful support indices are positive; at index zero Lean's division convention gives zero. Local copy of Erdos249257.mersenneWeightRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)
/-- The exact finite Mersenne value of a Boolean lower support. Local copy of Erdos249257.localMersennePrefixValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersennePrefixValue (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, mersenneWeightRat d
/-- An exact row together with a protected below-half core. Every support rank outside the core lies strictly above `cutoff`, and the current endpoint lies below `2 * cutoff`. These two inequalities force the next first crossing to occur late enough to give strict endpoint progress. Local copy of Erdos249257.ProtectedExactLocalMersenneRow, restated so the compared statements elaborate against Mathlib alone. -/
structure ProtectedExactLocalMersenneRow where
  endpoint : ℕ
  cutoff : ℕ
  support : Finset ℕ
  core : Finset ℕ
  endpoint_six : 6 ≤ endpoint
  cutoff_four : 4 ≤ cutoff
  core_subset : core ⊆ support
  new_above_cutoff : ∀ d ∈ support, d ∉ core → cutoff < d
  core_bounds : ∀ d ∈ core, 2 ≤ d ∧ d ≤ cutoff
  support_bounds : ∀ d ∈ support, 2 ≤ d ∧ d ≤ endpoint
  exact_quotient :
    localPrefixQuotient support endpoint = 2 ^ (endpoint - 1) - 1
  core_below_half : localMersennePrefixValue core < (1 / 2 : ℚ)
  two_mem_core : 2 ∈ core
  endpoint_lt_twice_cutoff : endpoint < 2 * cutoff
/-- The remaining arithmetic socket in the protected-core construction. Whenever a below-half core is crossed by rank `c`, adjoining `c` must already reach the integral half target at endpoint `2c-2`. By `localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff`, this is exactly the sharp `c-2`-bit capacity needed by the strict-upper skipped-core fill. The deficit hypothesis records that `c` is a genuine crossing rank. Local copy of Erdos249257.SkippedCoreCriticalQuotientSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SkippedCoreCriticalQuotientSupply : Prop :=
  ∀ (D : Finset ℕ) (c : ℕ),
    4 ≤ c →
    (∀ d ∈ D, 2 ≤ d ∧ d < c) →
    localMersennePrefixValue D < (1 / 2 : ℚ) →
    (1 / 2 : ℚ) - localMersennePrefixValue D < mersenneWeightRat c →
    2 ^ ((2 * c - 2) - 1) ≤
      localPrefixQuotient (insert c D) (2 * c - 2)
/-- States record:257bm-c5 from the long record for Erdős problem #257. Transported from Erdos249257.exists_laterProtectedExactLocalMersenneRow in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_laterProtectedExactLocalMersenneRow
    (hcap : SkippedCoreCriticalQuotientSupply)
    (s : ProtectedExactLocalMersenneRow) :
    ∃ t : ProtectedExactLocalMersenneRow, s.endpoint < t.endpoint := by
  sorry
end PalomarCorpus.E257.PaperStructuresBA
