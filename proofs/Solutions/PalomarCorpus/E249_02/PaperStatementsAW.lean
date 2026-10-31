/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.GenericTailOrbitRigidity
import ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel
import ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodelEndpoint
import ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates
import Solutions.PalomarCorpus.E249_02.Statement

open scoped BigOperators
open Filter
open Set

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsAW
export PalomarCorpus.E249_02.Shared (certificate discrepancy dyadicBase gamma value)

theorem exact_series (B P : ℕ) (hBP : B < P) :
    binaryCoeffSeries (gamma B P) = 2 -
      (∑ n ∈ Finset.range (B + 1), ((n - Nat.totient n : ℕ) : ℝ) / 2 ^ n) -
      1 / ((2 : ℝ) ^ P - 1) := @ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.exact_series B P hBP

theorem value_cast (B P : ℕ) (hBP : B < P) :
    binaryCoeffSeries (gamma B P) = (value B P : ℝ) := @ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.value_cast B P hBP

theorem certificate_sound (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n)
    (h N L : ℕ) (hcert : certificate c h N L) :
    binaryCoeffTail c (N + h) - binaryCoeffTail c N ∉ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.certificate_sound c hc h N L hcert

theorem generic_tail_period (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n)
    (p : ℤ) (e m h N : ℕ) (hm : 0 < m) (hN : e ≤ N)
    (hdvd : m ∣ 2 ^ h - 1)
    (hS : binaryCoeffSeries c = (p : ℝ) / ((2 : ℝ) ^ e * m)) :
    binaryCoeffTail c (N + h) - binaryCoeffTail c N ∈ Set.range ((↑) : ℤ → ℝ) := @ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.generic_tail_period c hc p e m h N hm hN hdvd hS

theorem scaled_difference (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (h N L : ℕ) :
    (2 : ℝ) ^ L * (binaryCoeffTail c (N + h) - binaryCoeffTail c N) -
      (discrepancy c h N L : ℝ) =
      binaryCoeffTail c (N + h + L) - binaryCoeffTail c (N + L) := @ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.scaled_difference c hc h N L

theorem scaled_tail_split (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (N L : ℕ) :
    (2 : ℝ) ^ L * binaryCoeffTail c N =
      (windowPrefix c N L : ℝ) + binaryCoeffTail c (N + L) := @ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.scaled_tail_split c hc N L

theorem truncation_error_bound (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (h N L : ℕ) :
    |(2 : ℝ) ^ L * (binaryCoeffTail c (N + h) - binaryCoeffTail c N) -
      (discrepancy c h N L : ℝ)| ≤ (N : ℝ) + h + L + 2 := @ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.truncation_error_bound c hc h N L

end PalomarCorpus.E249.PaperStatementsAW
