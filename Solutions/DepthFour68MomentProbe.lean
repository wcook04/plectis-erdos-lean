/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos68.PaperCoverageV5.MomentExamples

/-!
Exact-statement probes for the depth-four moment ideal. The source includes
all finite supports through the proved infinite-tail gcd, and constructs a
specific admissible primitive vector. These checks are separate from native
Prove2Me submission and from Comparator acceptance.
-/
open ErdosProblems.Erdos68.PaperComplete
open ErdosProblems.Erdos68.PaperCoverageV5

example (m : ℤ) : AttainsMoment 4 m ↔ (1380 : ℤ) ∣ m :=
  exact_depth_four_ideal m

example : AttainsMoment 4 1380 ∧
    ∀ m : ℤ, AttainsMoment 4 m → 0 < m → 1380 ≤ m :=
  depth_four_minimum

example : Admissible depthFourVector ∧ LowChannels 4 depthFourVector ∧
    factorialMoment depthFourVector = 1380 ∧ coefficientContent depthFourVector = 1 :=
  ⟨depthFourVector_admissible, depthFourVector_channels,
    depthFourVector_moment, depthFourVector_content_one⟩

-- Reject use of the ideal theorem with an incorrect divisibility modulus.
-- This is a type-check control, not a proof that every other modulus is false.
example (m : ℤ) : True := by
  fail_if_success
    have wrong : AttainsMoment 4 m ↔ (1381 : ℤ) ∣ m := by
      exact exact_depth_four_ideal m
  trivial

#print axioms ErdosProblems.Erdos68.PaperCoverageV5.scalar_tail_gcd_four
#print axioms ErdosProblems.Erdos68.PaperCoverageV5.exact_depth_four_ideal
#print axioms ErdosProblems.Erdos68.PaperCoverageV5.depth_four_minimum
#print axioms ErdosProblems.Erdos68.PaperCoverageV5.depthFourVector_content_one
