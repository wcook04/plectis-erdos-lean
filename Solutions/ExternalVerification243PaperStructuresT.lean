/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos243.PaperCompleteR21.AmplifiedRecordEquivalence
import ErdosProblems.Erdos243.PaperCompleteR21.ReducedDenominatorPrimePowers
import ErdosProblems.Erdos243.PaperCompleteR7.CanonicalState
import ErdosProblems.Erdos243.PrimitiveRecordBarrier

/-!
# Independent restatements for Erdős problem #243

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos243.PaperCompleteR21.AmplifiedRecordEquivalence`,
`ErdosProblems.Erdos243.PaperCompleteR21.ReducedDenominatorPrimePowers`,
`ErdosProblems.Erdos243.PaperCompleteR7.CanonicalState`,
`ErdosProblems.Erdos243.PrimitiveRecordBarrier`.
-/

open Filter
open Asymptotics
open scoped BigOperators
open scoped Topology

namespace Erdos249257.ExternalVerification243PaperStructuresT

structure StandingOrbit where
  /-- The multiplier sequence `a n`. -/
  a : ℕ → ℕ
  /-- The numerator of the rational reciprocal sum. -/
  num : ℤ
  /-- The denominator of the rational reciprocal sum. -/
  den : ℕ
  /-- `1 ≤ a 1 < a 2 < ⋯`. -/
  a_strictMono : StrictMono a
  /-- Positivity of the multipliers. -/
  a_pos : ∀ n, 0 < a n
  /-- Positivity of the denominator of the sum. -/
  den_pos : 0 < den
  /-- `∑ 1 / a n = num / den ∈ ℚ`. -/
  hasSum : HasSum (fun n ↦ 1 / (a n : ℝ)) ((num : ℝ) / (den : ℝ))
  /-- `a (n+1) / a n ^ 2 → 1`. -/
  growth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1)

noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j

noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)

noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat

noncomputable def StandingOrbit.C (O : StandingOrbit) : ℕ → ℕ := canonicalNaturalNumerator O.a O.num O.den

noncomputable def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n

noncomputable def StandingOrbit.D (O : StandingOrbit) : ℕ → ℕ := canonicalDenominator O.a O.den

noncomputable def StandingOrbit.EventuallySylvester (O : StandingOrbit) : Prop :=
  ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1

noncomputable def StandingOrbit.G (O : StandingOrbit) (n : ℕ) : ℕ := Nat.gcd (O.C n) (O.D n)

noncomputable def StandingOrbit.u (O : StandingOrbit) (n : ℕ) : ℕ := O.C n / O.G n

noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

noncomputable def StandingOrbit.R (O : StandingOrbit) : ℕ → ℕ := runningMax O.u

noncomputable def StandingOrbit.v (O : StandingOrbit) (n : ℕ) : ℕ := O.D n / O.G n

noncomputable def StandingOrbit.redErr (O : StandingOrbit) (n : ℕ) : ℤ := (O.v n : ℤ) - ((O.a n : ℤ) - 1) * (O.u n : ℤ)

noncomputable def StandingOrbit.negPart (O : StandingOrbit) (n : ℕ) : ℕ := (-O.redErr n).toNat

noncomputable def StandingOrbit.amp (O : StandingOrbit) (n : ℕ) : ℝ := (O.R n : ℝ) * (O.negPart n : ℝ) / (O.u n : ℝ)

noncomputable def StandingOrbit.canc (O : StandingOrbit) (n : ℕ) : ℕ := O.G (n + 1) / O.G n

noncomputable def StandingOrbit.delta (O : StandingOrbit) (n : ℕ) : ℝ :=
  max 0 ((O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) - 1)

/-! ### Transport bridges

A copied structure is a separate type from its source, and a copied recursive
definition is a separate compilation of the same recursion, so a statement that
mentions one is not proved by direct application. The bridges below are what the
transports use; they are generated, elaborated here, and recorded as derived
transport in the entry metadata.
-/

/-- The copied structure `StandingOrbit` and its source `ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit` carry the same
fields, so each converts into the other field by field. -/
def StandingOrbit_transport_toSrc (x : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit :=
  ⟨x.a, x.num, x.den, x.a_strictMono, x.a_pos, x.den_pos, x.hasSum, x.growth⟩

/-- The inverse of `StandingOrbit_transport_toSrc`. -/
def StandingOrbit_transport_ofSrc (x : ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit) :
    StandingOrbit :=
  ⟨x.a, x.num, x.den, x.a_strictMono, x.a_pos, x.den_pos, x.hasSum, x.growth⟩

@[simp] theorem StandingOrbit_transport_toSrc_a
    (x : StandingOrbit) :
    (StandingOrbit_transport_toSrc x).a = x.a := rfl

@[simp] theorem StandingOrbit_transport_ofSrc_a
    (x : ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit) :
    (StandingOrbit_transport_ofSrc x).a = x.a := rfl

@[simp] theorem StandingOrbit_transport_toSrc_num
    (x : StandingOrbit) :
    (StandingOrbit_transport_toSrc x).num = x.num := rfl

@[simp] theorem StandingOrbit_transport_ofSrc_num
    (x : ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit) :
    (StandingOrbit_transport_ofSrc x).num = x.num := rfl

@[simp] theorem StandingOrbit_transport_toSrc_den
    (x : StandingOrbit) :
    (StandingOrbit_transport_toSrc x).den = x.den := rfl

@[simp] theorem StandingOrbit_transport_ofSrc_den
    (x : ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit) :
    (StandingOrbit_transport_ofSrc x).den = x.den := rfl

@[simp] theorem StandingOrbit_C_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C (StandingOrbit_transport_toSrc O) = StandingOrbit.C O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C]; done)
  | (funext a; fun_induction StandingOrbit.C a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C, *]; done)
  | (funext a; simp [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C]; done)
  | (funext a b; fun_induction StandingOrbit.C a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C, *]; done)
  | (funext a b; simp [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C]; done)
  | (funext a b c; fun_induction StandingOrbit.C a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C, *]; done)
  | (funext a b c; simp [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C]; done)
  | (simp [StandingOrbit.C, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.C]; done)

@[simp] theorem StandingOrbit_D_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D (StandingOrbit_transport_toSrc O) = StandingOrbit.D O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.D a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.D a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.D a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def]; done)
  | (simp [StandingOrbit.D, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.D, StandingOrbit_C_transport_def]; done)

@[simp] theorem StandingOrbit_EventuallySylvester_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester (StandingOrbit_transport_toSrc O) = StandingOrbit.EventuallySylvester O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.EventuallySylvester a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.EventuallySylvester a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.EventuallySylvester a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)
  | (simp [StandingOrbit.EventuallySylvester, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.EventuallySylvester, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def]; done)

@[simp] theorem StandingOrbit_G_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G (StandingOrbit_transport_toSrc O) = StandingOrbit.G O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.G a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.G a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.G a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def]; done)
  | (simp [StandingOrbit.G, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.G, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def]; done)

@[simp] theorem StandingOrbit_u_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u (StandingOrbit_transport_toSrc O) = StandingOrbit.u O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.u a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.u a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.u a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def]; done)
  | (simp [StandingOrbit.u, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.u, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def]; done)

/-- The local copy of `ErdosProblems.Erdos243.runningMax` is the same function. -/
theorem runningMax_transport_def : @runningMax = @ErdosProblems.Erdos243.runningMax := by
  first
  | (rfl; done)
  | (simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (funext a; fun_induction runningMax a <;> simp only [ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, *]; done)
  | (funext a; induction a <;> simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, *]; done)
  | (funext a; simp [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (funext a b; fun_induction runningMax a b <;> simp only [ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, *]; done)
  | (funext a b; simp [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (funext a b c; fun_induction runningMax a b c <;> simp only [ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, *]; done)
  | (funext a b c; simp [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)
  | (simp [runningMax, ErdosProblems.Erdos243.runningMax, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def]; done)

@[simp] theorem StandingOrbit_R_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R (StandingOrbit_transport_toSrc O) = StandingOrbit.R O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.R a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.R a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.R a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)
  | (simp [StandingOrbit.R, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def]; done)

@[simp] theorem StandingOrbit_v_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v (StandingOrbit_transport_toSrc O) = StandingOrbit.v O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.v a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.v a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.v a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def]; done)
  | (simp [StandingOrbit.v, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.v, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def]; done)

@[simp] theorem StandingOrbit_redErr_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr (StandingOrbit_transport_toSrc O) = StandingOrbit.redErr O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.redErr a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.redErr a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.redErr a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def]; done)
  | (simp [StandingOrbit.redErr, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.redErr, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def]; done)

@[simp] theorem StandingOrbit_negPart_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart (StandingOrbit_transport_toSrc O) = StandingOrbit.negPart O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.negPart a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.negPart a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.negPart a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def]; done)
  | (simp [StandingOrbit.negPart, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.negPart, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def]; done)

@[simp] theorem StandingOrbit_amp_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp (StandingOrbit_transport_toSrc O) = StandingOrbit.amp O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.amp a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.amp a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.amp a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def]; done)
  | (simp [StandingOrbit.amp, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def]; done)

@[simp] theorem StandingOrbit_canc_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc (StandingOrbit_transport_toSrc O) = StandingOrbit.canc O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.canc a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.canc a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.canc a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def]; done)
  | (simp [StandingOrbit.canc, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def]; done)

@[simp] theorem StandingOrbit_delta_transport_def (O : StandingOrbit) :
    ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta (StandingOrbit_transport_toSrc O) = StandingOrbit.delta O := by
  first
  | (rfl; done)
  | (simp only [StandingOrbit.delta, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [StandingOrbit.delta, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def]; done)
  | (funext a; fun_induction StandingOrbit.delta a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def, *]; done)
  | (funext a; induction a <;> simp only [StandingOrbit.delta, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def, *]; done)
  | (funext a; simp [StandingOrbit.delta, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [StandingOrbit.delta, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def]; done)
  | (funext a b; fun_induction StandingOrbit.delta a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [StandingOrbit.delta, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def, *]; done)
  | (funext a b; simp [StandingOrbit.delta, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [StandingOrbit.delta, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def]; done)
  | (funext a b c; fun_induction StandingOrbit.delta a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [StandingOrbit.delta, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def, *]; done)
  | (funext a b c; simp [StandingOrbit.delta, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def]; done)
  | (simp [StandingOrbit.delta, ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def]; done)

theorem R_delta_sub_amp_tendsto_zero (O : StandingOrbit) :
    Tendsto (fun n ↦ (O.R n : ℝ) * O.delta n - O.amp n) atTop (𝓝 0) := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def, StandingOrbit_delta_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R_delta_sub_amp_tendsto_zero (StandingOrbit_transport_toSrc O)

theorem R_le_of_u_le (O : StandingOrbit) {c N : ℕ} (h : ∀ n, N ≤ n → O.u n ≤ c * n) :
    ∀ n, N ≤ n → O.R n ≤ O.R N + c * n := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def, StandingOrbit_delta_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R_le_of_u_le (StandingOrbit_transport_toSrc O) c N h

theorem Rdelta_bddAbove_iff_amp (O : StandingOrbit) :
    (∃ K : ℝ, ∀ᶠ n in atTop, O.amp n ≤ K) ↔
      (∃ K : ℝ, ∀ᶠ n in atTop, (O.R n : ℝ) * O.delta n ≤ K) := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def, StandingOrbit_delta_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Rdelta_bddAbove_iff_amp (StandingOrbit_transport_toSrc O)

theorem amp_bddAbove_iff_sylvester (O : StandingOrbit) :
    O.EventuallySylvester ↔ ∃ K : ℝ, ∀ᶠ n in atTop, O.amp n ≤ K := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def, StandingOrbit_delta_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp_bddAbove_iff_sylvester (StandingOrbit_transport_toSrc O)

theorem coprimeMultiplier_cofinal (O : StandingOrbit) (N : ℕ) :
    ∃ n, N ≤ n ∧ Nat.Coprime (O.a n) (O.D n) := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def, StandingOrbit_delta_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.coprimeMultiplier_cofinal (StandingOrbit_transport_toSrc O) N

theorem criticalRate (O : StandingOrbit)
    (hδ : (fun n : ℕ ↦ O.delta n) =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ))) :
    (O.EventuallySylvester ↔ (fun n : ℕ ↦ (O.u n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ))) ∧
      (O.EventuallySylvester ↔
        (fun n : ℕ ↦ (O.negPart n : ℝ)) =O[atTop] (fun _ : ℕ ↦ (1 : ℝ))) := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def, StandingOrbit_delta_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.criticalRate (StandingOrbit_transport_toSrc O) hδ

theorem criticalRate_counterexample (O : StandingOrbit)
    (hδ : (fun n : ℕ ↦ O.delta n) =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ)))
    (hns : ¬ O.EventuallySylvester) :
    Filter.limsup (fun n ↦ (((O.u n : ℝ) / (n : ℝ) : ℝ) : EReal)) atTop = ⊤ ∧
      Filter.limsup (fun n ↦ ((O.negPart n : ℝ) : EReal)) atTop = ⊤ := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def, StandingOrbit_delta_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.criticalRate_counterexample (StandingOrbit_transport_toSrc O) hδ hns

theorem delta_negPart_comparison (O : StandingOrbit) :
    ∃ N, ∀ n, N ≤ n →
      |O.delta n - (O.negPart n : ℝ) / (O.u n : ℝ)| ≤ 3 / (O.a n : ℝ) := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def, StandingOrbit_delta_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta_negPart_comparison (StandingOrbit_transport_toSrc O)

theorem largePrime_coprimeMultiplier (O : StandingOrbit) (B : ℕ) (N : ℕ) :
    ∃ n, N ≤ n ∧ Nat.Coprime (O.a n) (O.D n) ∧
      ∃ p, Nat.Prime p ∧ p ∣ O.a n ∧ B < p := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def, StandingOrbit_delta_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.largePrime_coprimeMultiplier (StandingOrbit_transport_toSrc O) B N

theorem primeBlock_supply (O : StandingOrbit) (B N₀ : ℕ) (hcanc : ∀ m, N₀ ≤ m → O.canc m ≤ B) :
    ∀ j : ℕ, ∃ T, N₀ ≤ T ∧ ∃ P : Finset ℕ, P.card = j ∧
      ∀ p ∈ P, Nat.Prime p ∧ B < p ∧ p ∣ O.v T := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def, StandingOrbit_delta_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.primeBlock_supply (StandingOrbit_transport_toSrc O) B N₀ hcanc

theorem recordAmplified (O : StandingOrbit) :
    (O.EventuallySylvester ↔
        Filter.limsup (fun n ↦ ((O.amp n : ℝ) : EReal)) atTop ≠ ⊤) ∧
      (O.EventuallySylvester ↔
        Filter.limsup (fun n ↦ (((O.R n : ℝ) * O.delta n : ℝ) : EReal)) atTop ≠ ⊤) ∧
      (Filter.limsup (fun n ↦ ((O.amp n : ℝ) : EReal)) atTop = 0 ∨
        Filter.limsup (fun n ↦ ((O.amp n : ℝ) : EReal)) atTop = ⊤) ∧
      (Filter.limsup (fun n ↦ (((O.R n : ℝ) * O.delta n : ℝ) : EReal)) atTop = 0 ∨
        Filter.limsup (fun n ↦ (((O.R n : ℝ) * O.delta n : ℝ) : EReal)) atTop = ⊤) := by
  simpa only [StandingOrbit_transport_toSrc_a, StandingOrbit_transport_toSrc_den, StandingOrbit_transport_toSrc_num, StandingOrbit_C_transport_def, StandingOrbit_D_transport_def, StandingOrbit_EventuallySylvester_transport_def, StandingOrbit_G_transport_def, StandingOrbit_u_transport_def, runningMax_transport_def, StandingOrbit_R_transport_def, StandingOrbit_v_transport_def, StandingOrbit_redErr_transport_def, StandingOrbit_negPart_transport_def, StandingOrbit_amp_transport_def, StandingOrbit_canc_transport_def, StandingOrbit_delta_transport_def] using @ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.recordAmplified (StandingOrbit_transport_toSrc O)

end Erdos249257.ExternalVerification243PaperStructuresT
