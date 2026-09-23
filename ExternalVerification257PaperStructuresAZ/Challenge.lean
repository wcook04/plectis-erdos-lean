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
`Erdos249257.BooleanMobiusLocalRepair`, `Erdos249257.HalfCylinderConcreteSeamAdapter`,
`Erdos249257.HalfCylinderIntegerGreedy`,
`ErdosProblems.Erdos257.PaperCompleteR21.ThreeBranchRowDynamics`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification257PaperStructuresAZ

noncomputable abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool

noncomputable def SeamRowWord.ofList {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    SeamRowWord s :=
  fun i => bits.get (Fin.cast hlen.symm i)

noncomputable def SeamRowWord.toNatWord {s : ℕ} (b : SeamRowWord s) : ℕ → Bool :=
  fun d => if h : 2 ≤ d ∧ d < s then b ⟨d - 2, by omega⟩ else false

noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C

noncomputable def integerGreedyBits_length (weights : List ℕ) (C : ℕ) :
    (integerGreedyBits weights C).length = weights.length := by
  induction weights generalizing C with
  | nil => simp [integerGreedyBits]
  | cons w ws ih =>
      simp only [integerGreedyBits]
      split <;> simp [ih]

noncomputable def rowPulse (s d : ℕ) : ℕ :=
  (if d ∣ 2 * s + 2 then 1 else 0) +
    2 * (if d ∣ 2 * s + 1 then 1 else 0)

noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s

noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)

noncomputable def seamWeightsFrom (s : ℕ) : ℕ → List ℕ
  | d =>
      if h : d < s then
        truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega

noncomputable def seamWeights (s : ℕ) : List ℕ :=
  seamWeightsFrom s 2

noncomputable def seamWeightsFrom_eq_cons {s d : ℕ} (h : d < s) :
    seamWeightsFrom s d =
      truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1) := by
  rw [seamWeightsFrom]
  simp [h]

noncomputable def seamWeightsFrom_eq_nil {s d : ℕ} (h : s ≤ d) :
    seamWeightsFrom s d = [] := by
  rw [seamWeightsFrom]
  simp [Nat.not_lt.mpr h]

noncomputable def seamWeightsFrom_length_eq (s d : ℕ) :
    (seamWeightsFrom s d).length = s - d := by
  by_cases hds : d < s
  · rw [seamWeightsFrom_eq_cons hds, List.length_cons,
      seamWeightsFrom_length_eq s (d + 1)]
    omega
  · rw [seamWeightsFrom_eq_nil (by omega)]
    simp
    omega
termination_by s - d
decreasing_by omega

noncomputable def seamWeights_length_eq (s : ℕ) :
    (seamWeights s).length = s - 2 := by
  unfold seamWeights
  exact seamWeightsFrom_length_eq s 2

noncomputable def seamGreedyWord (s : ℕ) : SeamRowWord s :=
  SeamRowWord.ofList
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
    (by rw [integerGreedyBits_length, seamWeights_length_eq])

noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)

noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d

noncomputable def IsRowLower (n : ℕ) (D : Finset ℕ) : Prop :=
  D ⊆ Finset.Ico 2 n ∧
    localPrefixQuotient D (2 * n) ≤ seamSubsetTarget n ∧
      ∀ S, S ⊆ Finset.Ico 2 n →
        localPrefixQuotient S (2 * n) ≤ seamSubsetTarget n →
          localPrefixQuotient S (2 * n) ≤ localPrefixQuotient D (2 * n)

noncomputable def IsRowUpper (n : ℕ) (B : Finset ℕ) : Prop :=
  B ⊆ Finset.Ico 2 n ∧
    seamSubsetTarget n < localPrefixQuotient B (2 * n) ∧
      ∀ S, S ⊆ Finset.Ico 2 n →
        seamSubsetTarget n < localPrefixQuotient S (2 * n) →
          localPrefixQuotient B (2 * n) ≤ localPrefixQuotient S (2 * n)

noncomputable def rowSupport (n : ℕ) (b : SeamRowWord n) : Finset ℕ :=
  (Finset.Ico 2 n).filter (fun d => b.toNatWord d = true)

noncomputable def greedySupport (n : ℕ) : Finset ℕ := rowSupport n (seamGreedyWord n)

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_dynamics in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem paper_dynamics {n : ℕ} (hn : 5 ≤ n) {D B D' : Finset ℕ}
    (hD : IsRowLower n D) (hB : IsRowUpper n B) (hD' : IsRowLower (n + 1) D')
    {r o pm pp rem : ℕ}
    (hr : localPrefixQuotient D (2 * n) + r = seamSubsetTarget n)
    (ho : seamSubsetTarget n + o = localPrefixQuotient B (2 * n))
    (hpm : pm = ∑ d ∈ D, rowPulse n d)
    (hpp : pp = ∑ d ∈ B, rowPulse n d)
    (hrem : localPrefixQuotient D' (2 * (n + 1)) + rem = seamSubsetTarget (n + 1)) :
    D = greedySupport n ∧
      pm ≤ 2 * (n - 2) ∧ pp ≤ 2 * (n - 2) ∧
      ((rem : ℤ) =
        if 4 * (o : ℤ) + (pp : ℤ) ≤ 2 ^ (n + 1) then
          (2 : ℤ) ^ (n + 1) - 4 * (o : ℤ) - (pp : ℤ)
        else if 4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ) < 2 ^ (n + 2) + 4 then
          4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ)
        else 4 * (r : ℤ) - 2 ^ (n + 1) - (pm : ℤ) - 4) ∧
      (((rem : ℚ) - 2 ^ (n + 1)) / 2 ^ (n + 1) =
        if 4 * (o : ℤ) + (pp : ℤ) ≤ 2 ^ (n + 1) then
          -((4 * (o : ℚ) + (pp : ℚ)) / 2 ^ (n + 1))
        else if 4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ) < 2 ^ (n + 2) + 4 then
          2 * (((r : ℚ) - 2 ^ n) / 2 ^ n) + 2 - (pm : ℚ) / 2 ^ (n + 1)
        else 2 * (((r : ℚ) - 2 ^ n) / 2 ^ n) - ((pm : ℚ) + 4) / 2 ^ (n + 1)) := by
  sorry

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_greedy_rule in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_greedySupport_greedy_rule {n : ℕ} (hn : 5 ≤ n) {d : ℕ}
    (hd : 2 ≤ d) (hdn : d < n) :
    d ∈ greedySupport n ↔
      truncatedMersenneWeight n d +
          ∑ e ∈ (greedySupport n).filter (fun e => e < d),
            truncatedMersenneWeight n e ≤ seamSubsetTarget n := by
  sorry

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_isRowLower in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_greedySupport_isRowLower {n : ℕ} (hn : 5 ≤ n) :
    IsRowLower n (greedySupport n) := by
  sorry

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_mem in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_greedySupport_mem {n d : ℕ} (hd : 2 ≤ d) (hdn : d < n) :
    d ∈ greedySupport n ↔ seamGreedyWord n ⟨d - 2, by omega⟩ = true := by
  sorry

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_greedy_step in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_greedy_step {n d : ℕ} (hd : d < n) (C : ℕ) :
    integerGreedyBits (seamWeightsFrom n d) C =
      (decide (truncatedMersenneWeight n d ≤ C)) ::
        integerGreedyBits (seamWeightsFrom n (d + 1))
          (if truncatedMersenneWeight n d ≤ C then
            C - truncatedMersenneWeight n d else C) := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresAZ
