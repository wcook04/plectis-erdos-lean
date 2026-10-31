/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.PaperCompleteR21.TailPrefixLattice
import Solutions.PalomarCorpus.E1049_09.Statement

open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStructuresV

theorem tail_prefix_lattice (a b : ℕ) (hb : 1 ≤ b) (hba : b < a) (hab : Nat.Coprime a b) :
    (∀ m, 0 < tailQ a b m ∧ Int.gcd (tailQ a b m) (tailP a b m) = 1) ∧
    (∀ m, IsCoprime (tailQ a b m) ((a : ℤ) * b)) ∧
    (∀ m, (b : ℤ) ∣ tailP a b m) ∧
    (∀ M, 2 ≤ M →
      tailPrefixLattice a b M = (⊤ : Submodule ℤ ℤ).prod (Submodule.span ℤ {(b : ℤ)}) ∧
      (∃ snf : Module.Basis.SmithNormalForm (tailPrefixLattice a b M) (Fin 2) 2,
          snf.a = ![1, (b : ℤ)]) ∧
      (∀ n, Nonempty (Module.Basis.SmithNormalForm (tailPrefixLattice a b M) (Fin 2) n) → n = 2) ∧
      (∀ snf : Module.Basis.SmithNormalForm (tailPrefixLattice a b M) (Fin 2) 2,
          snf.a 0 ∣ snf.a 1 → IsUnit (snf.a 0) ∧ Associated (snf.a 1) (b : ℤ)) ∧
      (Finset.univ : Finset (Fin M × Fin M)).gcd
          (fun ij => tailMinor a b ij.1 ij.2) = (b : ℤ) ∧
      (∀ D : ℕ, 1 ≤ D →
        (rowModD D '' (tailPrefixLattice a b M : Set (ℤ × ℤ))).ncard = D ^ 2 / Nat.gcd b D)) ∧
    (∀ m (w : ℚ), w ≠ 0 → ∀ (c : ℚ) (A B : ℤ), c ≠ 0 →
      (A : ℚ) = c * (w * tailQ a b m) → (B : ℚ) = c * (w * tailP a b m) →
      (∃ k : ℤ, k ≠ 0 ∧ (A, B) = k • tailRow a b m) ∧
      ((A / (Int.gcd A B : ℤ), B / (Int.gcd A B : ℤ)) = tailRow a b m ∨
        (A / (Int.gcd A B : ℤ), B / (Int.gcd A B : ℤ)) = -tailRow a b m)) := @ErdosProblems.Erdos1049.PaperCompleteR21.TailLattice.tail_prefix_lattice a b hb hba hab

end PalomarCorpus.E1049.PaperStructuresV
