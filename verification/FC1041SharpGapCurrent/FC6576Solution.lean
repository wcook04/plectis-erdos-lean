import ExternalVerification.FC1041SharpGap.Solution

namespace Erdos1041

theorem erdos_1041.variants.sharp_collinear_gap {m : ℕ} (Y : Fin (m + 2) → ℝ)
    (hY : StrictMono Y) (hY0 : Y 0 = -1)
    (hY1 : Y (Fin.last (m + 1)) = 1) :
    ∃ i : Fin (m + 1), ∀ x ∈ Set.Icc (Y i.castSucc) (Y i.succ),
      |∏ j, (x - Y j)| ≤
        1 / (2 ^ ((m + 2) - 1) *
          Real.cos (Real.pi / (2 * (((m + 2 : ℕ) : ℝ)))) ^ (m + 2)) := by
  exact ErdosProblems.Erdos1041.PaperCompleteR21.exists_gap_le_sharpClosedForm Y hY hY0 hY1

#print axioms erdos_1041.variants.sharp_collinear_gap

end Erdos1041
