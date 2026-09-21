/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249ak

Every non-theorem declaration of `PalomarCorpus/E249ak/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

namespace PalomarCorpus.E249.PaperStatementsAK
/-- Large prime-ray layers escape every prescribed finite prime support. Local copy of ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.FinitePrimeSupportEscape, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FinitePrimeSupportEscape (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ S : Finset ℕ, ∃ Q₀ : ℕ, ∀ q : ℕ,
    q.Prime → Q₀ ≤ q →
      ∀ p ∈ S, p.Prime → ¬ p ∣ C (m * q)
/-- `qstar` is the exact first displayed denominator at which a gap certificate fails. This is the small checker-facing contract emitted by the untrusted Stern--Brocot producer: all smaller positive denominators pass, while `qstar` itself fails. Local copy of GapFareyBound.IsFirstGapFailure, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsFirstGapFailure (V K H qstar : ℕ) : Prop :=
  (∀ q : ℕ, 0 < q → q < qstar → (q * V) % 2 ^ K + q * H < 2 ^ K) ∧
    ¬ ((qstar * V) % 2 ^ K + qstar * H < 2 ^ K)
/-- The closed-form cylinder mass at the coprime node `(a,b)`: `M(a,b) = 1/((2ᵃ-1)(2ᵇ-1)) = P(a ∣ X)·P(b ∣ Y)`. Local copy of GcdMomentCalculus.cylinderMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cylinderMass (a b : ℕ+) : ℝ :=
  1 / (((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1))
/-- The depth-`d` finite unfolding of the mediant recursion: sum the stop mass `1/(2^{a+b}-1)` at every node of the first `d` generations of the subtree rooted at `(a,b)`, under the children `(a+b, b)` and `(a, a+b)`. Local copy of GcdMomentCalculus.sternBrocotDepthMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sternBrocotDepthMass : ℕ → ℕ+ → ℕ+ → ℝ
  | 0, _, _ => 0
  | (dp + 1), a, b =>
      1 / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
        + sternBrocotDepthMass dp (a + b) b + sternBrocotDepthMass dp a (a + b)
end PalomarCorpus.E249.PaperStatementsAK
