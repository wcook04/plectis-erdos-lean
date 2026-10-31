/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E251_08

Every non-theorem declaration of `PalomarCorpus/E251_08/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset
open scoped BigOperators
open Filter
open scoped BigOperators Topology
open Filter Topology

namespace PalomarCorpus.E251.ShiftedFourPrimeCounting
open Finset
/-- The zero-based enumeration of the primes in increasing order, so that `prime0 0 = 2`, `prime0 1 = 3`, and `prime0 n` is the `(n + 1)`st prime. -/
noncomputable def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n
/-- The `n`th consecutive prime gap in the zero-based indexing, `prime0 (n + 1) - prime0 n`. The subtraction is truncated subtraction of natural numbers, which agrees with the ordinary difference because the primes increase; the first values are 1, 2, 2, 4, 2, 4. -/
noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n
/-- The finite set of indices `n` below `N` at which the shifted gap difference `g (n + h) - g n`, computed in the integers, equals `r`. -/
noncomputable def shiftedMatches (h N : ℕ) (r : ℤ) : Finset ℕ := by
  classical
  exact (range N).filter (fun n => (primeGap0 (n + h) : ℤ) - primeGap0 n = r)
/-- The finite set of triples `(x, d, s)` with `x < prime0 N`, both `d` and `s` at most `H`, `0 < d < s`, `d + r > 0`, and all four of `x`, `x + d`, `x + s` and `x + s + d + r` prime, the last computed in the integers and cast back, which loses nothing because `0 < d + r`. These are the separated four-prime configurations produced by a shifted gap coincidence inside a window of total span at most `H`. -/
noncomputable def quadCandidates (N H : ℕ) (r : ℤ) : Finset ((ℕ × ℕ) × ℕ) := by
  classical
  exact (((range (prime0 N)).product (range (H + 1))).product (range (H + 1))).filter
    (fun z => 0 < z.1.2 ∧ z.1.2 < z.2 ∧ 0 < (z.1.2 : ℤ) + r ∧
      Nat.Prime z.1.1 ∧ Nat.Prime (z.1.1 + z.1.2) ∧ Nat.Prime (z.1.1 + z.2) ∧
      Nat.Prime (((z.1.1 : ℤ) + z.2 + z.1.2 + r).toNat))
/-- A set of natural numbers has density zero when for every positive real `ε` all sufficiently large `N` have fewer than `ε * N` elements below `N`. -/
noncomputable def ZeroDensity (s : Set ℕ) : Prop := by
  classical
  exact ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    (((range N).filter (fun n => n ∈ s)).card : ℝ) < ε * N
/-- The explicit sieve hypothesis, which this package does not prove: for every positive real `ε` there is a threshold beyond which every `N` admits a window length `H` with `(h + 1) * prime0 (N + h + 1) + (H + 1) * (number of four-prime candidates below N with window H and shift r) < ε * N * (H + 1)`. It is a named external input, not a theorem of this entry. -/
noncomputable def SeparatedQuadSieve_target (h : ℕ) (r : ℤ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ H : ℕ,
    ((h + 1 : ℕ) : ℝ) * prime0 (N + (h + 1)) +
      (H + 1 : ℕ) * ((quadCandidates N H r).card : ℝ) < ε * N * (H + 1 : ℕ)
end PalomarCorpus.E251.ShiftedFourPrimeCounting

namespace PalomarCorpus.E251.SparseRationalisation
open scoped BigOperators
open Filter
open scoped BigOperators Topology
open Finset
open Filter Topology
/-- Upper Banach density zero in reciprocal-integer form: for every positive natural `R` there is a length `L₀` such that every half-open interval `[a, a + L)` with `L ≥ L₀` contains at most `L / R` elements of `S`, written as `R` times the count being at most `L`. The bound is uniform in the starting point `a`. -/
noncomputable def UpperBanachZero (S : Set ℕ) : Prop := by
  classical
  exact ∀ R : ℕ, 0 < R → ∃ L₀ : ℕ, ∀ a L : ℕ, L₀ ≤ L →
    R * ((Finset.Ico a (a + L)).filter (fun n => n ∈ S)).card ≤ L
/-- The starting indices `N` in the finite set `I` whose length-`m` block `i ↦ a (N + i)` belongs to the set of blocks `event`. -/
noncomputable def eventStarts {α : Type*} (a : ℕ → α) (I : Finset ℕ) (m : ℕ)
    (event : Set (Fin m → α)) : Finset ℕ := by
  classical
  exact I.filter (fun N => (fun i : Fin m => a (N + i.val)) ∈ event)
/-- The iterated logarithm `n ↦ log (log (n + 3))`. -/
noncomputable def iterlog (n : ℕ) : ℝ := Real.log (Real.log ((n : ℝ) + 3))
/-- The envelope `n ↦ (log (n + 3)) ^ α`, a real power of the natural logarithm. -/
noncomputable def polylog (α : ℝ) (n : ℕ) : ℝ := (Real.log ((n : ℝ) + 3)) ^ α
/-- The spacing `(k + 4) ^ 2` between consecutive support centres at schedule level `k`. -/
noncomputable def gap (k : ℕ) : ℕ := (k + 4) ^ 2
/-- The digit capacity `4 (k + 3)! 2 ^ gap k` available at schedule level `k`. -/
noncomputable def amplitude (k : ℕ) : ℕ := 4 * (k + 3).factorial * 2 ^ gap k
/-- Level `k` is ready at index `n` for the envelope `f` when every index `m ≥ n` has `amplitude k ≤ f m` in the reals and `amplitude k ≤ m + 1` in the naturals. -/
noncomputable def Ready (f : ℕ → ℝ) (n k : ℕ) : Prop :=
  ∀ m, n ≤ m → (amplitude k : ℝ) ≤ f m ∧ amplitude k ≤ m + 1
/-- The level used after the centre `n` when the current level is `k`: `k + 1` if level `k + 1` is ready at `n`, and `k` otherwise. -/
noncomputable def upgrade (f : ℕ → ℝ) (n k : ℕ) : ℕ := by
  classical
  exact if Ready f n (k + 1) then k + 1 else k
/-- The schedule state (centre, level) at step `j` for the envelope `f`: `(start, 0)` at step `0`, and from the state `(c, k)` the next centre is `n = c + gap k`, with level `upgrade f n k`. -/
noncomputable def state (f : ℕ → ℝ) (start : ℕ) : ℕ → ℕ × ℕ
  | 0 => (start, 0)
  | j + 1 =>
      let s := state f start j
      let n := s.1 + gap s.2
      (n, upgrade f n s.2)
/-- The `j`-th support centre of the schedule for the envelope `f` begun at `start`, the first coordinate of the schedule state; the centres increase strictly with `j`. -/
noncomputable def centre (f : ℕ → ℝ) (start j : ℕ) : ℕ := (state f start j).1
/-- The values of `c` lying in the half-open interval `[a, a + L)`, as a finite set of natural numbers. -/
noncomputable def supportSlice (c : ℕ → ℕ) (a L : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico a (a + L)).filter (fun n => n ∈ Set.range c)
/-- The proportion of starting indices `N` in `[X, 2 X)` whose length-`m` block of `a` belongs to `E`: the number of such `N` divided by `X`. -/
noncomputable def eventFrequency {α : Type*} (a : ℕ → α) (X m : ℕ)
    (E : Set (Fin m → α)) : ℝ := (eventStarts a (Finset.Ico X (2 * X)) m E).card / (X : ℝ)
/-- The mean over starting indices `N` in `[X, 2 X)` of the test `Φ` evaluated at `N` and at the length-`m` block of `a` starting at `N`, the sum divided by `X`. -/
noncomputable def testMean {α : Type*} (a : ℕ → α) (X m : ℕ)
    (Φ : ℕ → (Fin m → α) → ℝ) : ℝ :=
  (∑ N ∈ Finset.Ico X (2 * X), Φ N (fun i => a (N + i.val))) / X
/-- The total variation distance between the length-`m` block distributions of `a` and `b` over starting indices in `[X, 2 X)`, in the supremum-over-events convention: the supremum over all sets `E` of blocks of `|eventFrequency a X m E - eventFrequency b X m E|`. -/
noncomputable def blockTV {α : Type*} (a b : ℕ → α) (X m : ℕ) : ℝ :=
  sSup (Set.range (fun E : Set (Fin m → α) => |eventFrequency a X m E - eventFrequency b X m E|))
end PalomarCorpus.E251.SparseRationalisation
