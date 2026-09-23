import Erdos257PeriodNoncollapse.HalfCylinderLargestSkipInduction
import Erdos257PeriodNoncollapse.HalfCylinderProducerLowerBound
import Erdos257PeriodNoncollapse.HalfCylinderFinalMiddleCellEscape
import Erdos257PeriodNoncollapse.HalfCylinderLastProducerContradiction

/-
The paper repository's copy of this module does not declare the results below; they were proved in
this corpus. A shim can only publish a name the library has, so this module keeps them, and keeps them
exactly as they were written: it is the corpus module with every declaration the library already carries
removed, and the shim imported in their place. No statement, hypothesis, proof or name is changed here.
-/

/-!
# The last seam producer versus an eventual right tail

If the integer seam were eventually right, the explicit false terminal at
row thirteen would have a last successor row `D` with false terminal.  That
last non-right transition is either an upper producer or a middle producer.

The upper case is impossible unconditionally: its terminal-augmented affine
carry is at most `-8`, while the eventual right tail puts the corresponding
lazy endpoint below `1/2`.

The middle case is reduced to the exact, weak inequality that its positive
affine carry beats the complete future divisor-incidence tail.  A convenient
stronger socket asks only for the already-proved square-root majorant.  This
is substantially weaker than the exponential largest-skip socket.
-/

namespace Erdos257PeriodNoncollapse

open Set Filter
open HalfCylinderIntegerGreedy

noncomputable section

/-! ## The remaining middle-producer socket -/

private theorem lastProducer_seamWeights_fourteen :
    seamWeights 14 =
      [89478485, 38347922, 17895697, 8659208, 4260880, 2113665,
        1052688, 525314, 262400, 131136, 65552, 32772] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num : 2 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 3 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 4 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 5 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 6 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 7 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 8 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 9 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 10 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 11 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 12 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 13 < 14),
    seamWeightsFrom_eq_nil (by norm_num : 14 ≤ 14)]
  norm_num [truncatedMersenneWeight]

private theorem lastProducer_seamSubsetTarget_fourteen :
    seamSubsetTarget 14 = 134201344 := by
  norm_num [seamSubsetTarget]

private theorem lastProducer_integerGreedyBits_fourteen :
    integerGreedyBits (seamWeights 14) (seamSubsetTarget 14) =
      [true, true, false, false, true, true,
        false, false, false, false, false, false] := by
  rw [lastProducer_seamWeights_fourteen,
    lastProducer_seamSubsetTarget_fourteen]
  norm_num [integerGreedyBits]

/-- The terminal rank `13` is skipped in the exact row-fourteen seam word. -/
theorem seamGreedy_terminal_false_at_thirteen :
    SeamRowWord.terminal (by omega)
      (seamGreedyWord (13 + 1)) = false := by
  change (seamGreedyWord 14) ⟨11, by omega⟩ = false
  simp [seamGreedyWord, SeamRowWord.ofList,
    lastProducer_integerGreedyBits_fourteen]

/-! ## A named last false terminal -/

end

end Erdos257PeriodNoncollapse
