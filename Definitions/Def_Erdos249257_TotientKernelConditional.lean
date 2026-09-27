import Definitions.Def_Erdos249257_TotientKernelIndex
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Conditional exact rank for the all-base totient kernel

This module separates the two layers of the expected all-base theorem.

* The arithmetic layer is unconditional: a composite-base residue divisible
  by `k` reduces to the corresponding lower-level section by an explicit
  nonzero rational scalar.  Iterating this relation proves that the
  filtration-compatible family indexed by `TotientKernelIndex k e` spans the
  complete kernel through level `e`.
* The exact-rank conclusion is conditional on linear independence of that
  canonical family.  That hypothesis is precisely the external mathematical
  input; no theorem of Martin is formalised or assumed as an axiom here.
-/

namespace Erdos249257

open Module

/-- The `(j,r)` base-`k` kernel channel of Euler's totient, viewed over `ℚ`. -/
def allBaseTotientKernelSeq (k j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (k ^ j * n + r)
























end Erdos249257
