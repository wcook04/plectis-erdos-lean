/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_28

Every non-theorem declaration of `PalomarCorpus/E249_28/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset
open Filter
open Topology

namespace PalomarCorpus.E249.PaperStructuresQ
open Finset
open Filter
open Topology
/-- Local definition pivotOffset, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def pivotOffset (L s : ℕ) : ℕ := L - s + 1
/-- Local definition pivotArgument, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def pivotArgument (N L s : ℕ) : ℕ := N + pivotOffset L s
/-- Local definition pivotPrime, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def pivotPrime (N L s : ℕ) : ℕ :=
  (pivotArgument N L s).primeFactors.toList.foldl Nat.max 1
/-- Local definition pivotCofactor, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def pivotCofactor (N L s : ℕ) : ℕ :=
  pivotArgument N L s / pivotPrime N L s
/-- Local definition pivotSupplier, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def pivotSupplier (X L s N : ℕ) : Prop :=
  let p := pivotPrime N L s
  let m := pivotCofactor N L s
  p.Prime ∧ m * p = pivotArgument N L s ∧ 0 < m ∧
    m ≤ Nat.sqrt X / 2 ∧ 2 * Nat.sqrt X < p
/-- Local definition instDecidablePivotSupplier, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable instance instDecidablePivotSupplier (X L s N : ℕ) : Decidable (pivotSupplier X L s N) := by
  unfold pivotSupplier
  infer_instance
/-- Local definition pivotSupplierBases, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def pivotSupplierBases (X L s : ℕ) : Finset ℕ :=
  (Finset.Ico X (2 * X)).filter (pivotSupplier X L s)
/-- Local definition AdmissibleDepth, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def AdmissibleDepth (h s X L : ℕ) : Prop :=
  h ≤ L - s ∧ 16 * (2 * X + h + L + 2) ≤ 2 ^ L
/-- Local definition admissibleDepth_witness, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def admissibleDepth_witness (h s X : ℕ) :
    AdmissibleDepth h s X (h + s + Nat.log 2 X + 10) := by
  refine ⟨by omega, ?_⟩
  have hA : h + s + 1 ≤ 2 ^ (h + s) := Nat.lt_two_pow_self
  have hB : X + 1 ≤ 2 * 2 ^ (Nat.log 2 X) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
    rw [pow_succ] at this; omega
  have hlog : Nat.log 2 X ≤ X := Nat.log_le_self 2 X
  have hpow : 2 ^ (h + s + Nat.log 2 X + 10) = 2 ^ (h + s) * 2 ^ (Nat.log 2 X) * 1024 := by
    rw [pow_add, pow_add]; norm_num
  rw [hpow]
  have hprod : (h + s + 1) * (X + 1) ≤ 2 ^ (h + s) * (2 * 2 ^ (Nat.log 2 X)) :=
    Nat.mul_le_mul hA hB
  have h1 : 16 * (2 * X + h + (h + s + Nat.log 2 X + 10) + 2)
      ≤ 512 * ((h + s + 1) * (X + 1)) := by
    nlinarith [Nat.zero_le (h * X), Nat.zero_le (s * X)]
  have h2 : 512 * ((h + s + 1) * (X + 1)) ≤ 2 ^ (h + s) * 2 ^ (Nat.log 2 X) * 1024 := by
    calc 512 * ((h + s + 1) * (X + 1))
        ≤ 512 * (2 ^ (h + s) * (2 * 2 ^ (Nat.log 2 X))) := Nat.mul_le_mul_left _ hprod
      _ = 2 ^ (h + s) * 2 ^ (Nat.log 2 X) * 1024 := by ring
  omega
/-- Local definition dickmanCut, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def dickmanCut (X t : ℕ) : ℝ :=
  4 * Real.sqrt X + 2 * (t : ℝ) / Real.sqrt X
/-- Local definition exists_admissibleDepth, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def exists_admissibleDepth (h s X : ℕ) : ∃ L, AdmissibleDepth h s X L :=
  ⟨_, admissibleDepth_witness h s X⟩
/-- Local definition instDecidablePredNatAdmissibleDepth, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable instance instDecidablePredNatAdmissibleDepth (h s X : ℕ) : DecidablePred (AdmissibleDepth h s X) := fun L => by
  unfold AdmissibleDepth; infer_instance
/-- Local definition minimalDepth, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def minimalDepth (h s X : ℕ) : ℕ := Nat.find (exists_admissibleDepth h s X)
/-- Local definition minimalOffset, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def minimalOffset (h s X : ℕ) : ℕ := pivotOffset (minimalDepth h s X) s
/-- Local definition minimalCut, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def minimalCut (h s X : ℕ) : ℝ := dickmanCut X (minimalOffset h s X)
/-- Local definition smoothCount, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def smoothCount (x : ℕ) (y : ℝ) : ℕ :=
  ((Icc 1 x).filter (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card
end PalomarCorpus.E249.PaperStructuresQ

namespace PalomarCorpus.E249.PaperStatementsAJ
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
/-- The window discrepancy `A_{h,N,L} = ∑_{j=0}^{L-1} (φ(N+h+1+j) - φ(N+1+j))·2^{L-1-j}`: the depth-`L` truncation of `2^L·(R_{N+h} - R_N)`. Local copy of Erdos249257.TotientTailPeriodKiller.windowDiscrepancy, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
end PalomarCorpus.E249.PaperStatementsAT
