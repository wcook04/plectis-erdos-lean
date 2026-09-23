/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1049_05

Every non-theorem declaration of `PalomarCorpus/E1049_05/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open Polynomial
universe u

namespace PalomarCorpus.E1049_05.Shared
/-- The finite arithmetic core of one coordinatewise clearing scheme at the base a/b: the conjunction of a > 0, Q > 0, 0 < digit <= N + K, the divisibility a^K dividing Q times digit, and the tail inequality Q b^(N+K+1) < a^(K+1). Here Q is the accumulated clearing factor and digit the coefficient being cleared, while N and K are the two window parameters: K is the exponent of a in the divisibility and K + 1 its exponent in the tail inequality, N + K bounds digit, and N + K + 1 is the exponent of b. The bound digit <= N + K is the only property of that coefficient used. -/
noncomputable def CoordinatewiseCorridor
    (a b N K Q digit : ℕ) : Prop :=
  0 < a ∧ 0 < Q ∧ 0 < digit ∧ digit ≤ N + K ∧
    a ^ K ∣ Q * digit ∧
    Q * b ^ (N + K + 1) < a ^ (K + 1)
/-- The homogeneous evaluation H_W(P) = sum over 0 <= i <= W of (coefficient of X^i in P) times 3^i times 2^(W - i), an integer attached to an integer polynomial P and a declared width W; it equals 2^W P(3/2) when the degree of P is at most W. It is linear in P. Coefficients of P in degrees above W are discarded, so the value depends on the declared width and not on P alone. -/
noncomputable def homEvalThreeTwo (W : ℕ) (P : Polynomial ℤ) : ℤ :=
  ∑ i ∈ Finset.range (W + 1), P.coeff i * 3 ^ i * 2 ^ (W - i)
end PalomarCorpus.E1049_05.Shared

namespace PalomarCorpus.E1049.PaperStatementsM
open scoped BigOperators
open Polynomial
export PalomarCorpus.E1049_05.Shared (homEvalThreeTwo)
/-- The four simultaneous endpoint congruences for a coefficient pair: bottom and top jets in both channels. Local copy of ErdosProblems.Erdos1049.FourJetSignature, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev FourJetSignature (R S : ℕ) :=
  (ZMod (3 ^ R) × ZMod (3 ^ R)) ×
    (ZMod (2 ^ S) × ZMod (2 ^ S))
/-- Difference of the two binary indicator vectors; this is not a polynomial pair. Local copy of ErdosProblems.Erdos1049.PaperR7.selectorDifference, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def selectorDifference {ι : Type*} (s t : ι → Bool) : ι → ℤ :=
  fun i => (if s i then 1 else 0) - (if t i then 1 else 0)
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

namespace PalomarCorpus.E1049.PaperStatementsF
open Polynomial
export PalomarCorpus.E1049_05.Shared (homEvalThreeTwo)
/-- Integer homogeneous evaluation at a reduced numerator--denominator pair. The existing `homEvalThreeTwo` is the specialization `(a,b) = (3,2)`. This generic form is the arithmetic object used in Proposition 3.6 of the paper. Local copy of ErdosProblems.Erdos1049.homEval, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def homEval (a b W : ℕ) (P : Polynomial ℤ) : ℤ :=
  ∑ i ∈ Finset.range (W + 1), P.coeff i * a ^ i * b ^ (W - i)
end PalomarCorpus.E1049.PaperStatementsF

namespace PalomarCorpus.E1049.PaperStatementsT
open scoped BigOperators
end PalomarCorpus.E1049.PaperStatementsT

namespace PalomarCorpus.E1049.PaperStatementsK
open scoped BigOperators
/-- Natural-valued magnitude of the forcing term in the cleared recurrence. Local copy of ErdosProblems.Erdos1049.rationalBaseForcingNat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalBaseForcingNat
    (s B : ℕ) (coeff : ℕ → ℕ) (N : ℕ) : ℕ :=
  B * coeff (N + 1) * s ^ (N + 1)
end PalomarCorpus.E1049.PaperStatementsK

namespace PalomarCorpus.E1049.PaperStatementsB
open scoped BigOperators
export PalomarCorpus.E1049_05.Shared (CoordinatewiseCorridor)
end PalomarCorpus.E1049.PaperStatementsB

namespace PalomarCorpus.E1049.RationalBaseBarrier
open scoped BigOperators
export PalomarCorpus.E1049_05.Shared (CoordinatewiseCorridor)
/-- The rational number formed by the first N coordinates of the divisor-style series at the rational base r/s: the sum over 0 <= m < N of coeff(m+1) s^(m+1) / r^(m+1). -/
noncomputable def rationalBasePrefixQ
    (r s : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ m ∈ Finset.range N,
    coeff (m + 1) * s ^ (m + 1) / r ^ (m + 1)
/-- The denominator-cleared tail state B r^N (F - prefix_N) attached to a putative value F of the series at the rational base r/s, where B is the assumed clearing constant and prefix_N is the rational prefix above. -/
noncomputable def rationalBaseClearedTailQ
    (r s B F : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  B * r ^ N * (F - rationalBasePrefixQ r s coeff N)
end PalomarCorpus.E1049.RationalBaseBarrier

namespace PalomarCorpus.E1049.PaperStatementsN
open scoped BigOperators
/-- Twice the proposed common denominator exponent `Eₙ = (3n² - n) / 2`. Local copy of ErdosProblems.Erdos1049.rationalPadeDenExpTwice, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalPadeDenExpTwice (n : ℤ) : ℤ :=
  3 * n * n - n
/-- Twice the denominator exponent of the `k`-th summand in the homogenised little-`q` Legendre `P` polynomial. Local copy of ErdosProblems.Erdos1049.rationalPadePSummandDenExpTwice, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalPadePSummandDenExpTwice (n k : ℤ) : ℤ :=
  2 * (k * (n - k) + n * k) + k * (k - 1)
/-- Twice the maximal denominator exponent in the `Q`-summand calculation, after the change of variables `j = n - m - 1`. Local copy of ErdosProblems.Erdos1049.rationalPadeQMaxDenExpTwice, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalPadeQMaxDenExpTwice (n m : ℤ) : ℤ :=
  let j := n - m - 1
  2 * (n * n - n) + j * j + 2 * j * m + j - m * m + 3 * m
end PalomarCorpus.E1049.PaperStatementsN
