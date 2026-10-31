/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #243, record section 7.3: counting jumps before a prime power can be lost

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #243, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #243 remains open, and no theorem in
this entry decides it.
-/

open Filter
open scoped BigOperators
open scoped Topology

namespace PalomarCorpus.E243.PaperStatementsA
/-- Index set of the barrier family: `k` indexes the barrier `(2 * k + 1) * p` lying in the window `(p * Q / 4, p * Q / 2]`. Local copy of ErdosProblems.Erdos243.barrierIdx, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def barrierIdx (Q : ℕ) : Finset ℕ := Finset.Icc ((Q + 4) / 8) ((Q - 2) / 4)
/-- States long243:res:epochenergy from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.mem_barrierIdx_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mem_barrierIdx_iff {Q : ℕ} (hQ : 16 ≤ Q) (k : ℕ) :
    k ∈ barrierIdx Q ↔ Q < 4 * (2 * k + 1) ∧ 2 * (2 * k + 1) ≤ Q := by
  sorry
end PalomarCorpus.E243.PaperStatementsA

namespace PalomarCorpus.E243.PaperStatementsK
/-- The running maximum `max_{k ≤ n} u k` of a natural-valued sequence, given by `runningMax u 0 = u 0` and `runningMax u (n+1) = max (runningMax u n) (u (n+1))`. -/
noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))
/-- States long243:res:epochenergy from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.epoch_energy_named_crossing_set in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem epoch_energy_named_crossing_set
    (a u v w hc : ℕ → ℕ) (p l s τ : ℕ) (J : Finset ℕ)
    (hp : p.Prime)
    (hp3 : 3 ≤ p)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hcentre : ∀ n, s ≤ n → 2 * ((u n : ℤ) - (w n : ℤ)).natAbs < u n)
    (hprot : p ^ l ∣ v s)
    (hQ : 16 ≤ p ^ l)
    (hRs : 4 * runningMax u s < p * p ^ l)
    (hsτ : s < τ)
    (hτ : p * p ^ l ≤ 2 * u τ)
    (hτfirst : ∀ n, s < n → n < τ → 2 * u n < p * p ^ l)
    (hJ : ∀ n, n ∈ J ↔ (s ≤ n ∧ n < τ ∧ ∃ b : ℕ, Odd b ∧ p ∣ b ∧
      p * p ^ l < 4 * b ∧ 2 * b ≤ p * p ^ l ∧
      b ≤ u (n + 1) ∧ ∀ j, s ≤ j → j < n → u (j + 1) < b)) :
    (∀ n ∈ J, runningMax u n < u (n + 1) ∧ hc n = 1 ∧ u n + 3 ≤ u (n + 1)) ∧
      p * p ^ l ≤ (8 * p + 8) * J.card
        + 4 * ∑ n ∈ J, (u (n + 1) - u n - 2) + 8 * p := by
  sorry
end PalomarCorpus.E243.PaperStatementsK

namespace PalomarCorpus.E243.PaperStatementsD
open Filter
open scoped BigOperators
open scoped Topology
/-- States long243:res:energycriterion from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.energy_window_real_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem energy_window_real_bound {pr P K X : ℝ}
    (hpr : 3 ≤ pr) (hPsq : pr * pr ≤ P) (hP16 : 16 * pr ≤ P)
    (hK : 0 ≤ K) (hX : 0 ≤ X)
    (hineq : P ≤ (8 * pr + 8) * K + 4 * X + 8 * pr) :
    (1 : ℝ) / 16 ≤ K / Real.sqrt (P / 2) + X / (P / 2) := by
  sorry
end PalomarCorpus.E243.PaperStatementsD

namespace PalomarCorpus.E243.PaperStructuresU
open Filter
open scoped BigOperators
open scoped Topology
/-- **The standing hypotheses of §`long243:sec:records`.** These are exactly the hypotheses of Problem `long243:res:problem`: a strictly increasing sequence of positive integers with `a (n+1) / a n ^ 2 → 1` and rational reciprocal sum, presented by an explicit integer numerator `num` and positive natural denominator `den`. The section's integer tails are the canonical ones constructed from this data; they are definitions below, not further hypotheses. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit, restated so the compared statements elaborate against Mathlib alone. -/
structure StandingOrbit where
  a : ℕ → ℕ
  num : ℤ
  den : ℕ
  a_strictMono : StrictMono a
  a_pos : ∀ n, 0 < a n
  den_pos : 0 < den
  hasSum : HasSum (fun n ↦ 1 / (a n : ℝ)) ((num : ℝ) / (den : ℝ))
  growth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat
/-- Local definition C, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.C (O : StandingOrbit) : ℕ → ℕ := canonicalNaturalNumerator O.a O.num O.den
/-- The denominator q multiplied by the product of the first n terms of a. -/
noncomputable def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n
/-- Local definition D, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.D (O : StandingOrbit) : ℕ → ℕ := canonicalDenominator O.a O.den
/-- Local definition G, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.G (O : StandingOrbit) (n : ℕ) : ℕ := Nat.gcd (O.C n) (O.D n)
/-- Local definition u, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.u (O : StandingOrbit) (n : ℕ) : ℕ := O.C n / O.G n
/-- The running maximum `max_{k ≤ n} u k` of a natural-valued sequence, given by `runningMax u 0 = u 0` and `runningMax u (n+1) = max (runningMax u n) (u (n+1))`. -/
noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))
/-- Local definition R, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.R (O : StandingOrbit) : ℕ → ℕ := runningMax O.u
/-- Local definition jump, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.jump (O : StandingOrbit) (n : ℕ) : ℕ := O.u (n + 1) - O.u n
/-- Local definition energy, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.energy (O : StandingOrbit) (n : ℕ) : ℝ :=
  if O.R n < O.u (n + 1) then
    (if 3 ≤ O.jump n then 1 / Real.sqrt ((O.u n : ℝ)) else 0)
      + ((O.jump n - 2 : ℕ) : ℝ) / (O.u n : ℝ)
  else 0
/-- Local definition energySqrt, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.energySqrt (O : StandingOrbit) (n : ℕ) : ℝ :=
  if O.R n < O.u (n + 1) then ((O.jump n - 2 : ℕ) : ℝ) / Real.sqrt ((O.u n : ℝ))
  else 0
/-- States long243:res:energycriterion from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt_summable_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem energySqrt_summable_iff (O : StandingOrbit) :
    Summable O.energySqrt ↔
      ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1 := by
  sorry
/-- States long243:res:energycriterion from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy_criterion in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem energy_criterion (O : StandingOrbit) :
    (Summable O.energy ↔
        ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) ∧
      (Summable O.energySqrt ↔
        ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) := by
  sorry
/-- States long243:res:energycriterion from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy_le_two_energySqrt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem energy_le_two_energySqrt (O : StandingOrbit) (n : ℕ) : O.energy n ≤ 2 * O.energySqrt n := by
  sorry
/-- States long243:res:energycriterion from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy_summable_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem energy_summable_iff (O : StandingOrbit) :
    Summable O.energy ↔
      ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1 := by
  sorry
/-- States long243:res:energycriterion from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.exists_late_energy_window in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_late_energy_window (O : StandingOrbit) (hunb : ∀ M : ℕ, ∃ n, M < O.u n) (S : ℕ) :
    ∃ (s τ : ℕ) (J : Finset ℕ), S ≤ s ∧ s < τ ∧ (∀ n ∈ J, s ≤ n ∧ n < τ) ∧
      (1 : ℝ) / 16 ≤ ∑ n ∈ J, O.energy n := by
  sorry
end PalomarCorpus.E243.PaperStructuresU
