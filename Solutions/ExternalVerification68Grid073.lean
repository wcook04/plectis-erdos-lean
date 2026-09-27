-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import ErdosProblems.Erdos68.FiniteLeadBlocks.Grid073

/-!
Ordinary source-only replay of one unchanged, custodied arithmetic leaf.
This module introduces no evaluator, oracle, IO action or runtime hook.
A successful build checks only the 996 terms from 299010 through 300005;
it does not establish the other 73 blocks or factorial nondivisibility.
-/
namespace Solutions.ExternalVerification68Grid073
open ErdosProblems.Erdos68.PaperComplete.FiniteLead

/-- The exact retained leaf statement, without weakening its scale or range. -/
theorem exact_leaf :
    kernelFloorBlock (2 ^ 5025679) 299010 996 = KernelBlocks.Grid073.value :=
  KernelBlocks.Grid073.checked

/-- A one-unit altered witness is rejected by the checked exact equality. -/
theorem altered_witness_rejected :
    kernelFloorBlock (2 ^ 5025679) 299010 996 ≠ KernelBlocks.Grid073.value + 1 := by
  rw [KernelBlocks.Grid073.checked]
  exact Nat.ne_of_lt (Nat.lt_succ_self _)

set_option pp.all true in
#check exact_leaf
#print axioms ErdosProblems.Erdos68.PaperComplete.FiniteLead.KernelBlocks.Grid073.checked
#print axioms exact_leaf
#print axioms altered_witness_rejected
end Solutions.ExternalVerification68Grid073
