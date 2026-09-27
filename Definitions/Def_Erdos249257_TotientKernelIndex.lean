import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite indices for the all-base totient kernel

This module records the combinatorial part of the expected finite-level
all-base totient-kernel basis.  There are two distinguished zero-residue
indices, followed at level `j + 1` by residues written uniquely in the form

`k * q + (d + 1)`, with `q < k^j` and `d < k - 1`.

For `k ≥ 2`, these coordinates give positive residues below `k^(j+1)` that
are not divisible by `k`.  Their finite cardinality is

`2 + ∑ j in range e, k^j * (k - 1) = k^e + 1`.

This is only the index and cardinality layer.  It does not assert linear
independence of the corresponding totient sections; that theorem remains an
external mathematical input in the all-base argument.
-/

namespace Erdos249257

/-- The two distinguished zero-residue channels, conventionally denoted
`F00` and `F10`. -/
inductive TotientKernelHeadIndex
  | F00
  | F10
  deriving DecidableEq

instance : Fintype TotientKernelHeadIndex where
  elems := {.F00, .F10}
  complete := by
    intro i
    cases i <;> simp

























/-! ## Exact fixed-level residue coordinates -/























end Erdos249257
