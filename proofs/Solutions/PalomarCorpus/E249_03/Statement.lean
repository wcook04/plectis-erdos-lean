/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_03

Every non-theorem declaration of `PalomarCorpus/E249_03/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset
open Filter
open Set

namespace PalomarCorpus.E249.PaperStatementsAK
end PalomarCorpus.E249.PaperStatementsAK

namespace PalomarCorpus.E249.PaperStatementsAU
open Finset
/-- The window discrepancy `A_{h,N,L} = ∑_{j=0}^{L-1} (φ(N+h+1+j) - φ(N+1+j))·2^{L-1-j}`: the depth-`L` truncation of `2^L·(R_{N+h} - R_N)`. Local copy of Erdos249257.TotientTailPeriodKiller.windowDiscrepancy, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- Predicate for a real quantity to be an integer. Local copy of Erdos249257.DiagonalPincerDecomposition.IsIntegralValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsIntegralValue (x : ℝ) : Prop := x ∈ Set.range ((↑) : ℤ → ℝ)
/-- The residue angle used by the first additive character. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstAngle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi *
    (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
      ((2 ^ L : ℤ) : ℝ))
/-- The complex first additive character of the endpoint discrepancy. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstExp, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((windowFirstAngle h N L : ℂ) * Complex.I)
/-- Fixed-shift fibre-free counted window-phase anti-concentration. The sample `T` may be any nonempty subset of a cofinal dyadic block. Local copy of Erdos249257.TotientTailPeriodKiller.DTWWindowSeparatedPairsAt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DTWWindowSeparatedPairsAt (h : ℕ) : Prop :=
  ∀ X₀ : ℕ, ∃ X L : ℕ, ∃ T : Finset ℕ,
      ∃ P : Finset (ℕ × ℕ), ∃ δ : ℝ,
      max X₀ 1 ≤ X ∧
      T.Nonempty ∧
      T ⊆ Finset.Ico X (2 * X) ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      P ⊆ T.product T ∧
      0 ≤ δ ∧
      (∀ p ∈ P,
        δ ≤ ‖windowFirstExp h p.1 L - windowFirstExp h p.2 L‖) ∧
      2 * (T.card : ℝ) ^ 2 / 5 ≤ (P.card : ℝ) * δ ^ 2
/-- Fibre-free counted window-phase anti-concentration at every positive shift; neither primality nor a pivot factorization is part of the statement. Local copy of Erdos249257.TotientTailPeriodKiller.DTWWindowSeparatedPairs, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DTWWindowSeparatedPairs : Prop :=
  ∀ h : ℕ, 0 < h → DTWWindowSeparatedPairsAt h
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
/-- **The supply normal form.** For every ray `d ≥ 1` and every basepoint threshold `c`, some multiple period `t·d` admits a certified kill at some `N ≥ c`. The odd part of a hypothetical denominator selects the ray; the kill contradicts the tail-period law on it. Local copy of ErdosProblems.Erdos249.PeriodMultipleEscape.PeriodMultipleKillSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PeriodMultipleKillSupply : Prop :=
  ∀ d : ℕ, 0 < d → ∀ c : ℕ,
    ∃ t N L : ℕ, 0 < t ∧ c ≤ N ∧ certifiedKill (t * d) N L
end PalomarCorpus.E249.PaperStatementsAU

namespace PalomarCorpus.E249.PaperStatementsAZ
open Filter
open Set
/-- The radius of the balanced-pulse family at location `m`. Local copy of Erdos249257.balancedPulseRadius, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def balancedPulseRadius (m : ℕ) : ℕ := (m + 1) / 2
/-- A two-site pulse whose mass can be moved from position `m` to `m+1` without changing its binary-series value. Local copy of Erdos249257.balancedPulseCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def balancedPulseCoeff (m r : ℕ) : ℕ → ℕ := fun n ↦
  if n = m then balancedPulseRadius m - r
  else if n = m + 1 then 2 * r
  else 0
/-- The binary coefficient series `X_c = ∑_{n≥1} c(n)/2^n`. Local copy of Erdos249257.binaryCoeffSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)
/-- The scaled tail `T_c(N) = ∑_{j≥1} c(N+j)/2^j`. Local copy of Erdos249257.binaryCoeffTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)
end PalomarCorpus.E249.PaperStatementsAZ

namespace PalomarCorpus.E249.PaperStatementsD
open Filter
open Set
/-- The exact binary affine orbit driven by the fresh coefficient word `a`. Local copy of Erdos249257.affineBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)
end PalomarCorpus.E249.PaperStatementsD

namespace PalomarCorpus.E249.PaperStructuresR
/-- Local definition VUSymbol, copied so the compared statements of this entry elaborate against Mathlib alone. -/
structure VUSymbol where
  valuation : ℕ
  unit : ℤ
/-- Local definition VUCompatible, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def VUCompatible (u : ℕ) (σ : VUSymbol) (c : ℤ) : Prop :=
  Odd σ.unit ∧
    ∃ z : ℤ,
      c = (2 : ℤ) ^ σ.valuation * (σ.unit + (2 : ℤ) ^ u * z)
/-- Local definition VUOrbit, copied so the compared statements of this entry elaborate against Mathlib alone. -/
inductive VUOrbit (u : ℕ) : ℤ → List VUSymbol → List ℤ → Prop
  | nil (e : ℤ) : VUOrbit u e [] []
  | cons (e c e' : ℤ) (σ : VUSymbol) (symbols : List VUSymbol)
      (states : List ℤ) (hcompat : VUCompatible u σ c)
      (hstep : e' = 2 * e + c) (htail : VUOrbit u e' symbols states) :
      VUOrbit u e (σ :: symbols) (e' :: states)
/-- Local definition vuRadius, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def vuRadius (u : ℕ) (σ : VUSymbol) : ℤ :=
  (2 : ℤ) ^ (σ.valuation + u - 1)
end PalomarCorpus.E249.PaperStructuresR

namespace PalomarCorpus.E249.PaperStatementsG
/-- The crude two-tail cost attached to an inverse/adjugate row. Recovering `φ(x)` as `2 R_(x-1) - R_x` and applying `R_M ≤ M+2` termwise gives the factor `2(x+1) + (x+2)`. Local copy of Erdos249257.totientAdjugateTailCost, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientAdjugateTailCost
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (x : ι → ℕ) : ℚ :=
  ∑ i, |w i| * (2 * ((x i : ℚ) + 1) + ((x i : ℚ) + 2))
end PalomarCorpus.E249.PaperStatementsG

namespace PalomarCorpus.E249.PaperStatementsI
open Finset
/-- The window step `a_n = φ(n+h) - φ(n)` driving the carry recurrence. Local copy of Erdos249257.TotientTailPeriodKiller.deltaTotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
/-- `periodLcm t = lcm(1, …, t)`: the universal period at scale `t`. Every primitive period `h₀ ≤ t` divides it. Local copy of Erdos249257.TotientTailPeriodKiller.periodLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
/-- State anchors corresponding to the exact whole-ray letters at `q * periodLcm t`, for `2 ≤ q < t`. Local copy of Erdos249257.TotientTailPeriodKiller.lcmAnchorStates, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmAnchorStates (t : ℕ) : Finset ℕ :=
  (Finset.Ico 2 t).image (fun q => (q - 1) * periodLcm t)
/-- A state which is `-A` on a finite anchor set and zero elsewhere. Local copy of Erdos249257.TotientTailPeriodKiller.sparsePulseState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sparsePulseState (A : ℤ) (S : Finset ℕ) (k : ℕ) : ℤ :=
  if k ∈ S then -A else 0
/-- The zero-based forcing letter determined by `c_{i+1} = 2c_i - a_i`. Local copy of Erdos249257.TotientTailPeriodKiller.sparsePulseLetter, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sparsePulseLetter (A : ℤ) (S : Finset ℕ) (i : ℕ) : ℤ :=
  2 * sparsePulseState A S i - sparsePulseState A S (i + 1)
/-- The LCM pulse forcing word. Local copy of Erdos249257.TotientTailPeriodKiller.lcmAnchorPulseLetter, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmAnchorPulseLetter (t i : ℕ) : ℤ :=
  sparsePulseLetter (Nat.totient (periodLcm t) : ℤ) (lcmAnchorStates t) i
/-- The LCM pulse state with amplitude `φ(periodLcm t)`. Local copy of Erdos249257.TotientTailPeriodKiller.lcmAnchorPulseState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmAnchorPulseState (t k : ℕ) : ℤ :=
  sparsePulseState (Nat.totient (periodLcm t) : ℤ) (lcmAnchorStates t) k
end PalomarCorpus.E249.PaperStatementsI
