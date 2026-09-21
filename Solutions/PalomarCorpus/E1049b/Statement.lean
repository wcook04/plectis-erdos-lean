/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1049b

Every non-theorem declaration of `PalomarCorpus/E1049b/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E1049.PaperStatementsB
open scoped BigOperators
/-- Local copy of ErdosProblems.Erdos1049.AllRow.S, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev S := PowerSeries ℤ
/-- Equality of all coefficients strictly below `D`. Local copy of ErdosProblems.Erdos1049.AllRow.Agree, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Agree (D : ℕ) (f g : S) : Prop :=
  ∀ d, d < D → PowerSeries.coeff d f = PowerSeries.coeff d g
/-- A finite ratio with constant term one in the state variable. Local copy of ErdosProblems.Erdos1049.AllRow.finiteRatio, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def finiteRatio (a : ℕ → S) (K n : ℕ) : S :=
  1 + ∑ s ∈ Finset.range K,
    a (s + 1) * PowerSeries.X ^ ((n + 1) * (s + 1))
/-- Row exponent in a form compatible with the canonical row proposition. Local copy of ErdosProblems.Erdos1049.AllRow.rowExponent, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rowExponent (j l : ℕ) : ℕ := j * (j + 1) / 2 + j * l
/-- The finite arithmetic core of a coordinatewise rational-base corridor. `digit` abstracts the final divisor coefficient that is individually cleared. Local copy of ErdosProblems.Erdos1049.CoordinatewiseCorridor, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CoordinatewiseCorridor
    (a b N K Q digit : ℕ) : Prop :=
  0 < a ∧ 0 < Q ∧ 0 < digit ∧ digit ≤ N + K ∧
    a ^ K ∣ Q * digit ∧
    Q * b ^ (N + K + 1) < a ^ (K + 1)
/-- `H(q^{n+1}) = 1 + ∑_{s ≥ 1} a_s(q) q^{(n+1)s}`, the untruncated ratio. Each coefficient is the corresponding coefficient of a long enough truncation, which is exactly what the infinite sum means: the term of index `s` has order at least `s + 1`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.paperRatio, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperRatio (a : ℕ → S) (n : ℕ) : S :=
  PowerSeries.mk fun d => PowerSeries.coeff d (finiteRatio a (d + 1) n)
/-- `H̄ = H mod q`, an ordinary power series in `X` over `ℤ`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.paperReducedSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperReducedSeries (a : ℕ → S) : PowerSeries ℤ :=
  PowerSeries.mk fun s => if s = 0 then 1 else PowerSeries.constantCoeff (a s)
/-- `h_r = [X^r] H̄(X)^{-1}`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.paperReciprocal, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperReciprocal (a : ℕ → S) (r : ℕ) : ℤ :=
  PowerSeries.coeff r (PowerSeries.invOfUnit (paperReducedSeries a) 1)
end PalomarCorpus.E1049.PaperStatementsB
