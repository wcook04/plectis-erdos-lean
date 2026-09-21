/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.BinaryTailWindowTransfer`, `Erdos249257.CertificateKernel`,
`Erdos249257.GenericTailOrbitRigidity`, `Erdos249257.HalfCarryReachability`,
`Erdos249257.HalfCarrySelectedWindow`, `Erdos249257.HalfCylinderFiniteShadow`,
`Erdos249257.HalfDivisorUnitDrop`, `Erdos249257.SublogDivisorCoverage`,
`ErdosProblems.Erdos257.PaperCompleteR20.CarryCollapseCorrespondence`,
`ErdosProblems.Erdos257.PaperCompleteR20.CofinalCarryCollapse`,
`ErdosProblems.Erdos257.PaperCompleteR21.EventualNonnegativeMargin`,
`ErdosProblems.Erdos257.PaperCompleteR21.LinearChannelAndMiddleCellExclusion`,
`ErdosProblems.Erdos257.PaperCompleteR21.SkipSafetyAndDivisorZeroRuns`,
`ErdosProblems.Erdos257.PaperCompleteR21.SquareDepthAndHalfMembershipEquivalences`,
`ErdosProblems.Erdos257.PaperCompleteR21.TerminalStripExactRowGap`.
-/

open Filter
open Set
open Topology

namespace Erdos249257.ExternalVerification257PaperStatementsAL

noncomputable def CoeffZeroWindow (f : ℕ → ℕ) (N h : ℕ) : Prop :=
  ∀ j : ℕ, j < h → f (N + j + 1) = 0

noncomputable abbrev HalfWord (N : ℕ) := Fin (N + 1) → Bool

noncomputable def halfStripBound (n : ℕ) : ℕ :=
  2 * Nat.sqrt n + 4

noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1

noncomputable def mobiusCenteredHalfCarry (A : Set ℕ) (N : ℕ) : ℤ :=
  integerHalfCarry A N - 1

noncomputable def wordSupport {N : ℕ} (a : HalfWord N) : Set ℕ :=
  {n | ∃ h : n < N + 1, a ⟨n, h⟩ = true}

noncomputable def extendHalfWord {N : ℕ} (a : HalfWord N) (β : Bool) : HalfWord (N + 1) :=
  Fin.lastCases β a

noncomputable def SupportCoeffZeroWindow (A : Set ℕ) (N h : ℕ) : Prop :=
  CoeffZeroWindow (supportCoeff A) N h

noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

/-- States record:257bm-c1, record:257bm-c4 from the long record for Erdős problem #257.
Transported from Erdos249257.HalfCarryReachability.finite_boolSupport_ne_half in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem finite_boolSupport_ne_half
    (A : Set ℕ) (hfinite : A.Finite) (hzero : 0 ∉ A) :
    erdosSupportSeries 2 A ≠ (1 : ℝ) / 2 := by
  sorry

/-- States thm:sqrt-bound-route from the long record for Erdős problem #257. Transported from
Erdos249257.HalfCarryReachability.infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound
    (A : Set ℕ) (hzero : 0 ∉ A) (hone : 1 ∉ A)
    (hnonneg : ∀ N : ℕ, 0 ≤ mobiusCenteredHalfCarry A N)
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry A N : ℝ) ≤
        2 * Real.sqrt (N : ℝ) + 4) :
    A.Infinite ∧ erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  sorry

/-- States lem:collapse-mech, record:257hg-i6, thm:mobius-centred-nonneg from the long record
for Erdős problem #257. Transported from
Erdos249257.HalfCarryReachability.integerHalfCarry_eq_scaled_residual_add_tail in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem integerHalfCarry_eq_scaled_residual_add_tail
    (A : Set ℕ) (hone : 1 ∉ A) (N : ℕ) :
    (integerHalfCarry A N : ℝ) =
      (2 : ℝ) ^ (N + 1) * ((1 : ℝ) / 2 - erdosSupportSeries 2 A) +
        binaryCoeffTail (supportCoeff A) (N + 1) := by
  sorry

/-- States record:257bm-i17 from the long record for Erdős problem #257. Transported from
Erdos249257.HalfCylinderFiniteShadow.supportCoeff_insert_divisor in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem supportCoeff_insert_divisor
    (A : Set ℕ) {d n : ℕ} (hd : d ∈ n.divisors) (hdA : d ∉ A) :
    supportCoeff (insert d A) n = supportCoeff A n + 1 := by
  sorry

/-- States record:257bm-i17 from the long record for Erdős problem #257. Transported from
Erdos249257.HalfDivisorUnitDrop.supportCoeff_boundaryPair_unitDrop_at_double in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem supportCoeff_boundaryPair_unitDrop_at_double
    {N : ℕ} (a : HalfWord N) (left right : HalfWord (N + 1))
    (hleft : left = extendHalfWord a true)
    (hright : right = extendHalfWord a false) :
    supportCoeff (wordSupport left) (2 * (N + 1)) =
      supportCoeff (wordSupport right) (2 * (N + 1)) + 1 := by
  sorry

/-- States lem:half-divisor-unit-drop, record:257bm-i17 from the long record for Erdős problem
#257. Transported from
Erdos249257.HalfDivisorUnitDrop.supportCoeff_extend_true_eq_false_add_one_at_double in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem supportCoeff_extend_true_eq_false_add_one_at_double
    {N : ℕ} (a : HalfWord N) :
    supportCoeff (wordSupport (extendHalfWord a true)) (2 * (N + 1)) =
      supportCoeff (wordSupport (extendHalfWord a false)) (2 * (N + 1)) + 1 := by
  sorry

/-- States prop:collapse from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR20.half_of_cofinal_absolute_carry in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_of_cofinal_absolute_carry (A : Set ℕ) (hone : 1 ∉ A)
    (C D : ℝ)
    (h : ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ := by
  sorry

/-- States lem:sqrt-witness, lem:sqwitness from the long record for Erdős problem #257.
Transported from ErdosProblems.Erdos257.PaperCompleteR20.square_depth_witness in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem square_depth_witness (A : Set ℕ) (hone : 1 ∉ A)
    (hhalf : erdosSupportSeries 2 A = (1 : ℝ) / 2)
    (k : ℕ) (hk : 1 ≤ k) :
    (integerHalfCarry A (k^2-1) : ℝ) = binaryCoeffTail (supportCoeff A) (k^2) ∧
    binaryCoeffTail (supportCoeff A) (k^2) ≤ 2*(k : ℝ)+4 ∧
    (halfStripBound (k^2) : ℝ) = 2*(k : ℝ)+4 := by
  sorry

/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_coeffTail_le_index_add_two in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_coeffTail_le_index_add_two (A : Set ℕ) (m : ℕ) :
    binaryCoeffTail (supportCoeff A) m ≤ (m : ℝ) + 2 := by
  sorry

/-- States record:257hg-k12 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_cofiniteRightTail_ne_zero_centeredEndpoint in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_cofiniteRightTail_ne_zero_centeredEndpoint
    (A : Set ℕ) (D : ℕ) (hone : 1 ∉ A)
    (hseries : erdosSupportSeries 2 A < (1 : ℝ) / 2)
    (hcofinite : Set.Ioi D ⊆ A) :
    mobiusCenteredHalfCarry A (2 * D + 1) ≠ 0 := by
  sorry

/-- States prop:strip-equiv from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_relaxed_constant_six_every_depth in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_relaxed_constant_six_every_depth
    (A : Set ℕ) (hone : 1 ∉ A) (hvalue : erdosSupportSeries 2 A = (1 : ℝ) / 2)
    (M : ℕ) (hM : 1 ≤ M) : := by
  sorry

/-- States lem:sqwitness from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_square_depth_terminal_bound in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_square_depth_terminal_bound (A : Set ℕ) (hone : 1 ∉ A)
    (hhalf : erdosSupportSeries 2 A = (1 : ℝ) / 2) (k : ℕ) (hk : 1 ≤ k) :
    (integerHalfCarry A (k ^ 2 - 1) : ℝ) = binaryCoeffTail (supportCoeff A) (k ^ 2) ∧
      binaryCoeffTail (supportCoeff A) (k ^ 2) ≤ 2 * (k : ℝ) + 4 ∧
      (halfStripBound (k ^ 2) : ℝ) = 2 * (k : ℝ) + 4 := by
  sorry

/-- States record:257rig-c17 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_terminal_strip_forces_half_membership in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_terminal_strip_forces_half_membership
    (hcofinal : ∀ N : ℕ, ∃ M : ℕ, max N 1 ≤ M ∧ ∃ D : Finset ℕ,
      (∀ d ∈ D, 2 ≤ d ∧ d ≤ M) ∧ := by
  sorry

/-- States record:257rig-i4a from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_zero_run_le_eps_logb in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_zero_run_le_eps_logb
    (A : Set ℕ) (hinf : A.Infinite) (hzero : 0 ∉ A)
    (p : ℤ) (c v : ℕ) (hv : 0 < v) (_hvodd : Odd v)
    (hvalue : erdosSupportSeries 2 A = (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ N h : ℕ, 1 ≤ N →
        SupportCoeffZeroWindow A (c + N) h →
        (h : ℝ) ≤ ε * Real.logb 2 (N : ℝ) + B := by
  sorry

/-- States record:257rig-i4a from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_zero_run_le_of_mem in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_zero_run_le_of_mem
    (A : Set ℕ) {a : ℕ} (hapos : 0 < a) (haA : a ∈ A) {N h : ℕ}
    (hwindow : SupportCoeffZeroWindow A N h) :
    h ≤ a - 1 := by
  sorry

end Erdos249257.ExternalVerification257PaperStatementsAL
