import Definitions.Def_Erdos249257_TotientKernelIndex
import Definitions.Def_Erdos249257_TotientKernelConditional
import Definitions.Def_Erdos249257_TotientMahlerDefect
import Definitions.Def_Erdos249257_AllBaseTotientKernel
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.PrimesCongruentOne

open Erdos249257
open Module Matrix

open Erdos249257

theorem Erdos249257.finrank_allBaseTotientKernel_eq_of_linearIndependent (k e : ℕ) (hk : 2 ≤ k)
    (hli : LinearIndependent ℚ (allBaseCanonicalFamily k e)) :
    finrank ℚ (Submodule.span ℚ (Set.range (allBaseCanonicalFamily k e))) =
      k ^ e + 1 := by sorry
