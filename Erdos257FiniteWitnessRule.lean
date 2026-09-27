-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
/-
Build root for the #257 finite monotone witness rule. The source theorem realises every
nonconstant upward-closed rule on a finite prime set by a positive host with divergent
reciprocal sum and irrational support series on every infinite subset in every base at least two.

This default target compiles WitnessLogicIrrational and its source closure in normal CI.
-/

import ErdosProblems.Erdos257.WitnessLogicIrrational

#print axioms ErdosProblems.Erdos257.finite_monotone_witness_rule_realised
