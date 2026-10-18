/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.DyadicPrefixCompression
import Solutions.PalomarCorpus.E257_26.Statement

open Set

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresCL

theorem dyadicResidualIntNumerator_coprime_oddDenominator
    (p r : ℤ) (c D : ℕ) (hDodd : Odd D)
    (hrD : r.natAbs.Coprime D) :
    (dyadicResidualIntNumerator p r c D).natAbs.Coprime D := by
  first
  | exact @Erdos249257.dyadicResidualIntNumerator_coprime_oddDenominator p r c D hDodd hrD
    done
  | set_option smartUnfolding false in
    exact @Erdos249257.dyadicResidualIntNumerator_coprime_oddDenominator p r c D hDodd hrD
    done
  | apply Erdos249257.dyadicResidualIntNumerator_coprime_oddDenominator <;> assumption
    done
  | simpa only [dyadicResidualIntNumerator, dyadicResidualIntRat] using Erdos249257.dyadicResidualIntNumerator_coprime_oddDenominator
    done
  | set_option smartUnfolding false in
    with_unfolding_all exact @Erdos249257.dyadicResidualIntNumerator_coprime_oddDenominator p r c D hDodd hrD
    done
  | with_unfolding_all exact @Erdos249257.dyadicResidualIntNumerator_coprime_oddDenominator p r c D hDodd hrD
    done

theorem dyadicResidualInt_denominator_sandwich
    (p r : ℤ) (c D : ℕ) (hDpos : 0 < D)
    (hND : (dyadicResidualIntNumerator p r c D).natAbs.Coprime D) :
    D ∣ (dyadicResidualIntRat p r c D).den ∧
      (dyadicResidualIntRat p r c D).den ∣ 2 ^ c * D := by
  first
  | exact @Erdos249257.dyadicResidualInt_denominator_sandwich p r c D hDpos hND
    done
  | set_option smartUnfolding false in
    exact @Erdos249257.dyadicResidualInt_denominator_sandwich p r c D hDpos hND
    done
  | apply Erdos249257.dyadicResidualInt_denominator_sandwich <;> assumption
    done
  | simpa only [dyadicResidualIntNumerator, dyadicResidualIntRat] using Erdos249257.dyadicResidualInt_denominator_sandwich
    done
  | set_option smartUnfolding false in
    with_unfolding_all exact @Erdos249257.dyadicResidualInt_denominator_sandwich p r c D hDpos hND
    done
  | with_unfolding_all exact @Erdos249257.dyadicResidualInt_denominator_sandwich p r c D hDpos hND
    done

end PalomarCorpus.E257.PaperStructuresCL
