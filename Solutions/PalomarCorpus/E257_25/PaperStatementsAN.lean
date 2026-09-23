/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.CertificateKernel
import Erdos249257.HalfCylinderIntegerGreedy
import ErdosProblems.Erdos257.PaperCompleteR21.MersenneQuotientRowRecurrences
import ErdosProblems.Erdos257.PaperCompleteR21.OddReciprocalDenominators
import Solutions.PalomarCorpus.E257_25.Statement

open scoped BigOperators
open Filter
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAN
export PalomarCorpus.E257_25.Shared (supportCoeff)

noncomputable def endpointDivisorContribution (D : Finset ℕ) (n : ℕ) : ℕ :=
  (D.filter fun d ↦ d ∣ n).card

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

noncomputable def finiteErdosSum (F : Finset Nat) (b : Nat) : Rat :=
  ∑ n ∈ F, 1 / ((b : Rat) ^ n - 1)

theorem supportCoeff_insert_eq_add_indicator
    (A : Set ℕ) {d n : ℕ} (hdA : d ∉ A) :
    supportCoeff (insert d A) n =
      supportCoeff A n + if d ∈ n.divisors then 1 else 0 := @Erdos249257.HalfCylinderIntegerGreedy.supportCoeff_insert_eq_add_indicator A d n hdA

theorem paper_endpoint_term_counts_divisors {D : Finset ℕ} {n : ℕ}
    (hn : 0 < n) :
    endpointDivisorContribution D n = (D.filter fun d ↦ d ∣ n).card ∧
      endpointDivisorContribution D n = supportCoeff (↑D : Set ℕ) n := @ErdosProblems.Erdos257.PaperCompleteR21.paper_endpoint_term_counts_divisors D n hn

theorem paper_finiteErdosSum_den_odd (F : Finset ℕ) (h0 : 0 ∉ F) :
    Odd (finiteErdosSum F 2).den := @ErdosProblems.Erdos257.PaperCompleteR21.paper_finiteErdosSum_den_odd F h0

theorem paper_finite_support_series_ne_half
    (A : Set ℕ) (hfinite : A.Finite) (hzero : 0 ∉ A) :
    erdosSupportSeries 2 A ≠ (1 : ℝ) / 2 := @ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_support_series_ne_half A hfinite hzero

theorem paper_half_representing_support_is_infinite
    (A : Set ℕ) (hzero : 0 ∉ A)
    (hvalue : erdosSupportSeries 2 A = (1 : ℝ) / 2) :
    A.Infinite := @ErdosProblems.Erdos257.PaperCompleteR21.paper_half_representing_support_is_infinite A hzero hvalue

end PalomarCorpus.E257.PaperStatementsAN
