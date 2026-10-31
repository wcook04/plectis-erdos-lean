/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos1049.PaperCompleteR21.TailPrefixLattice

/-!
# Independent restatements for Erdős problem #1049

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `6917e15ec4abc2623512254da93221e446eeb707` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1049.PaperCompleteR21.TailPrefixLattice`.
-/

open Finset

namespace Erdos249257.ExternalVerification1049PaperStructuresV

noncomputable def rowModD (D : ℕ) (v : ℤ × ℤ) : ZMod D × ZMod D := ((v.1 : ZMod D), (v.2 : ZMod D))

noncomputable def tailPartialSum (a b m : ℕ) : ℚ :=
  ∑ r ∈ Icc 1 m, ((b : ℚ) / a) ^ r / (1 - ((b : ℚ) / a) ^ r)

noncomputable def tailP (a b m : ℕ) : ℤ := (tailPartialSum a b m).num

noncomputable def tailQ (a b m : ℕ) : ℤ := ((tailPartialSum a b m).den : ℤ)

noncomputable def tailMinor (a b i j : ℕ) : ℤ := tailQ a b i * tailP a b j - tailP a b i * tailQ a b j

noncomputable def tailRow (a b m : ℕ) : ℤ × ℤ := (tailQ a b m, tailP a b m)

noncomputable def tailPrefixLattice (a b M : ℕ) : Submodule ℤ (ℤ × ℤ) :=
  Submodule.span ℤ (tailRow a b '' Set.Iio M)

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

end Erdos249257.ExternalVerification1049PaperStructuresV
