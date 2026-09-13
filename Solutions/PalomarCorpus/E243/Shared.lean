/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

open Filter
open scoped BigOperators
open Finset
open scoped Topology

namespace PalomarCorpus.E243.Shared
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j

noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1

end PalomarCorpus.E243.Shared

