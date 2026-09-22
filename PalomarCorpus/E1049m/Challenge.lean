/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1049, band m

Erdős problem #1049 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1049` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators
open Polynomial

namespace PalomarCorpus.E1049.PaperStatementsM
open scoped BigOperators
open Polynomial
/-- The four simultaneous endpoint congruences for a coefficient pair: bottom and top jets in both channels. Local copy of ErdosProblems.Erdos1049.FourJetSignature, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev FourJetSignature (R S : ℕ) :=
  (ZMod (3 ^ R) × ZMod (3 ^ R)) ×
    (ZMod (2 ^ S) × ZMod (2 ^ S))
/-- Difference of the two binary indicator vectors; this is not a polynomial pair. Local copy of ErdosProblems.Erdos1049.PaperR7.selectorDifference, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def selectorDifference {ι : Type*} (s t : ι → Bool) : ι → ℤ :=
  fun i => (if s i then 1 else 0) - (if t i then 1 else 0)
/-- Integer homogeneous evaluation of an integral polynomial at `(3,2)`, using the declared ambient width `W`. Local copy of ErdosProblems.Erdos1049.homEvalThreeTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def homEvalThreeTwo (W : ℕ) (P : Polynomial ℤ) : ℤ :=
  ∑ i ∈ Finset.range (W + 1), P.coeff i * 3 ^ i * 2 ^ (W - i)
/-- The bottom `3`-adic endpoint jet of depth `R`. Local copy of ErdosProblems.Erdos1049.bottomJet3, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def bottomJet3 (R W : ℕ) (P : Polynomial ℤ) : ZMod (3 ^ R) :=
  homEvalThreeTwo W P
/-- The top `2`-adic endpoint jet of depth `S`. Local copy of ErdosProblems.Erdos1049.topJet2, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def topJet2 (S W : ℕ) (P : Polynomial ℤ) : ZMod (2 ^ S) :=
  homEvalThreeTwo W P
/-- Four-jet signature of one integral coefficient pair. Local copy of ErdosProblems.Erdos1049.fourJetSignature, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def fourJetSignature (R S W : ℕ) (U V : Polynomial ℤ) :
    FourJetSignature R S :=
  ((bottomJet3 R W U, bottomJet3 R W V),
    (topJet2 S W U, topJet2 S W V))
/-- Sum of the four-jet signatures selected by a binary coefficient vector. Local copy of ErdosProblems.Erdos1049.selectedFourJetSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def selectedFourJetSum {n : ℕ} (R S W : ℕ)
    (forms : Fin n → Polynomial ℤ × Polynomial ℤ)
    (ε : Fin n → Bool) : FourJetSignature R S :=
  ∑ i, if ε i then
    fourJetSignature R S W (forms i).1 (forms i).2
  else 0
/-- One proposition containing every conclusion of the displayed jet theorem, including its exact target cardinality and sufficient width. Local copy of ErdosProblems.Erdos1049.PaperR7.PaperJetWitness, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PaperJetWitness {M : ℕ} (R S W : ℕ)
    (forms : Fin M → Polynomial ℤ × Polynomial ℤ) : Prop :=
  ∃ s t : Fin M → Bool, s ≠ t ∧
    selectedFourJetSum R S W forms s = selectedFourJetSum R S W forms t ∧
    selectorDifference s t ≠ 0 ∧
    (∀ i, selectorDifference s t i = -1 ∨ selectorDifference s t i = 0 ∨
      selectorDifference s t i = 1) ∧
    (∑ i, selectorDifference s t i •
      fourJetSignature R S W (forms i).1 (forms i).2) = 0
/-- States long1049:res:endpoints from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperR7.endpoint_residues in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem endpoint_residues (W : ℕ) (P : Polynomial ℤ) :
    (homEvalThreeTwo W P : ZMod 3) = (P.coeff 0 : ZMod 3) * 2 ^ W ∧
    (homEvalThreeTwo W P : ZMod 2) = (P.coeff W : ZMod 2) * 3 ^ W ∧
    ((P.coeff 0 = 1 ∨ P.coeff 0 = -1) →
      ¬ (3 : ℤ) ∣ homEvalThreeTwo W P) ∧
    ((P.coeff W = 1 ∨ P.coeff W = -1) →
      ¬ (2 : ℤ) ∣ homEvalThreeTwo W P) := by
  sorry
/-- States long1049:res:nomult from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperR7.endpoint_scalar_content_exclusion in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem endpoint_scalar_content_exclusion (W : ℕ) (U V : Polynomial ℤ)
    (hU : U.coeff W = 1 ∨ U.coeff W = -1)
    (hV : V.coeff 0 = 1 ∨ V.coeff 0 = -1) :
    (∀ c U₀ V₀ : ℤ,
      homEvalThreeTwo W U = c * U₀ →
      homEvalThreeTwo W V = c * V₀ →
      ¬ (2 : ℤ) ∣ c ∧ ¬ (3 : ℤ) ∣ c) ∧
    (∀ c : ℤ, c ∣ homEvalThreeTwo W U → c ∣ homEvalThreeTwo W V →
      ¬ (2 : ℤ) ∣ c ∧ ¬ (3 : ℤ) ∣ c) := by
  sorry
/-- States long1049:res:jetkernel, res:jetkernel from the long record and the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperR7.fourJet_paper_statement in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fourJet_paper_statement {M R S W : ℕ}
    (forms : Fin M → Polynomial ℤ × Polynomial ℤ) :
    Fintype.card (FourJetSignature R S) = (3 ^ R) ^ 2 * (2 ^ S) ^ 2 ∧
    (Fintype.card (FourJetSignature R S) < 2 ^ M → PaperJetWitness R S W forms) ∧
    (0 < R → 4 * R + 2 * S ≤ M → PaperJetWitness R S W forms) := by
  sorry
/-- States long1049:res:rankfortyone from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperR7.rank_fortyone in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rank_fortyone {M T S W : ℕ}
    (forms : Fin M → Polynomial ℤ × Polynomial ℤ)
    (hT : 0 < T) (hM : 130 * T + 2 * S ≤ M) :
    (∃ s t : Fin M → Bool, s ≠ t ∧
      selectedFourJetSum (41 * T) S W forms s =
        selectedFourJetSum (41 * T) S W forms t) ∧
      2 ^ (129 + 2 * S) < Fintype.card (FourJetSignature 41 S) := by
  sorry
end PalomarCorpus.E1049.PaperStatementsM
