/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band q

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Set
open Topology
open scoped BigOperators

namespace PalomarCorpus.E257.PaperStatementsQ
open Filter
open Set
open Topology
open scoped BigOperators
/-- The exact binary affine orbit driven by the fresh coefficient word `a`. Local copy of Erdos249257.affineBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}` — the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- The integer carry whose state at time `N` is the packet's `K_{N+1}`. Local copy of Erdos249257.HalfCarryReachability.integerHalfCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1
/-- The canonical integer half carry measured relative to the signed Möbius solution. Index `N` corresponds to the packet's state `e_{N+1}`. Local copy of Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusCenteredHalfCarry (A : Set ℕ) (N : ℕ) : ℤ :=
  integerHalfCarry A N - 1
/-- The integral part of `2^M / (2^d - 1)`. Local copy of Erdos249257.localMersenneQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
/-- Sum of the integral quotient contributions of a finite Boolean support. Local copy of Erdos249257.localPrefixQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d
/-- The two fresh coefficient rows, measured relative to the three units contributed by the centred recurrence itself. Local copy of Erdos249257.pairedCenteredForcing, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def pairedCenteredForcing (A : Set ℕ) (N : ℕ) : ℤ :=
  2 * (supportCoeff A (N + 2) : ℤ) +
    (supportCoeff A (N + 3) : ℤ) - 3
/-- States record:257rig-c17 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_integerHalfCarry_eq_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_exact_row_integerHalfCarry_eq_one
    {D : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d)
    (hexact : localPrefixQuotient D M = 2 ^ (M - 1) - 1) :
    integerHalfCarry (↑D : Set ℕ) (M - 1) = 1 := by
  sorry
/-- States record:257rig-c17 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_integerHalfCarry_eq_two_pow_sub_localPrefixQuotient in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_integerHalfCarry_eq_two_pow_sub_localPrefixQuotient
    {D : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d) :
    integerHalfCarry (↑D : Set ℕ) (M - 1) =
      (2 : ℤ) ^ (M - 1) - (localPrefixQuotient D M : ℤ) := by
  sorry
/-- States record:257hg-k12 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_mobiusCenteredHalfCarry_add_two in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_mobiusCenteredHalfCarry_add_two (A : Set ℕ) (N : ℕ) :
    mobiusCenteredHalfCarry A (N + 2) =
      4 * mobiusCenteredHalfCarry A N - pairedCenteredForcing A N := by
  sorry
end PalomarCorpus.E257.PaperStatementsQ
