/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.PaperFiniteAssembliesR7
import ErdosProblems.Erdos1049.ZudilinConeArithmetic
import Solutions.PalomarCorpus.E1049m.Statement

open scoped BigOperators
open Polynomial

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStatementsM

theorem endpoint_residues (W : ℕ) (P : Polynomial ℤ) :
    (homEvalThreeTwo W P : ZMod 3) = (P.coeff 0 : ZMod 3) * 2 ^ W ∧
    (homEvalThreeTwo W P : ZMod 2) = (P.coeff W : ZMod 2) * 3 ^ W ∧
    ((P.coeff 0 = 1 ∨ P.coeff 0 = -1) →
      ¬ (3 : ℤ) ∣ homEvalThreeTwo W P) ∧
    ((P.coeff W = 1 ∨ P.coeff W = -1) →
      ¬ (2 : ℤ) ∣ homEvalThreeTwo W P) := @ErdosProblems.Erdos1049.PaperR7.endpoint_residues W P

theorem endpoint_scalar_content_exclusion (W : ℕ) (U V : Polynomial ℤ)
    (hU : U.coeff W = 1 ∨ U.coeff W = -1)
    (hV : V.coeff 0 = 1 ∨ V.coeff 0 = -1) :
    (∀ c U₀ V₀ : ℤ,
      homEvalThreeTwo W U = c * U₀ →
      homEvalThreeTwo W V = c * V₀ →
      ¬ (2 : ℤ) ∣ c ∧ ¬ (3 : ℤ) ∣ c) ∧
    (∀ c : ℤ, c ∣ homEvalThreeTwo W U → c ∣ homEvalThreeTwo W V →
      ¬ (2 : ℤ) ∣ c ∧ ¬ (3 : ℤ) ∣ c) := @ErdosProblems.Erdos1049.PaperR7.endpoint_scalar_content_exclusion W U V hU hV

theorem fourJet_paper_statement {M R S W : ℕ}
    (forms : Fin M → Polynomial ℤ × Polynomial ℤ) :
    Fintype.card (FourJetSignature R S) = (3 ^ R) ^ 2 * (2 ^ S) ^ 2 ∧
    (Fintype.card (FourJetSignature R S) < 2 ^ M → PaperJetWitness R S W forms) ∧
    (0 < R → 4 * R + 2 * S ≤ M → PaperJetWitness R S W forms) := @ErdosProblems.Erdos1049.PaperR7.fourJet_paper_statement M R S W forms

theorem rank_fortyone {M T S W : ℕ}
    (forms : Fin M → Polynomial ℤ × Polynomial ℤ)
    (hT : 0 < T) (hM : 130 * T + 2 * S ≤ M) :
    (∃ s t : Fin M → Bool, s ≠ t ∧
      selectedFourJetSum (41 * T) S W forms s =
        selectedFourJetSum (41 * T) S W forms t) ∧
      2 ^ (129 + 2 * S) < Fintype.card (FourJetSignature 41 S) := @ErdosProblems.Erdos1049.PaperR7.rank_fortyone M T S W forms hT hM

end PalomarCorpus.E1049.PaperStatementsM
