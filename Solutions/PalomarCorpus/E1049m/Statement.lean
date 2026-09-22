/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1049m

Every non-theorem declaration of `PalomarCorpus/E1049m/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E1049.PaperStatementsM
