/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #1049 height-region placement at base `3 / 2`

This Mathlib-only interface fixes two parameter regions for a reduced rational
base `a / b` and places `3 / 2` against both.

`BundschuhVaananenHeightRegion` is the elementary parameter inequality
`log b / log a < 1/2 - 1/π²` appearing in the published Bundschuh--Väänänen
criterion.  `ZudilinHeightRegion` is the inequality `log b / log a < 81/200`.
The second threshold is defined here; it is not a published criterion.

The exact integer obstruction `3^81 < 2^200` puts `log 2 / log 3` strictly
above `81/200`, so `3 / 2` lies outside `ZudilinHeightRegion`.  The published
Bundschuh--Väänänen margin is smaller than that threshold, so `3 / 2` also
lies outside `BundschuhVaananenHeightRegion`.

Every statement here is an inequality between explicit parameters.  Membership
in a region is applicability of a method and not an irrationality theorem;
failure of membership is inapplicability and proves neither rationality nor
irrationality.  No analytic theorem is imported as an axiom, and nothing here
decides the arithmetic nature of any Lambert value.
-/

namespace Erdos249257.ExternalVerification1049PublishedHeightRegions

/-- The height region of the published Bundschuh--Väänänen criterion, written
for a reduced rational base `a / b`.  This records only the elementary
parameter inequality; the external analytic theorem is not internalized. -/
def BundschuhVaananenHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < 1 / 2 - 1 / Real.pi ^ 2

/-- The parameter region cut out by the single inequality
`log b / log a < 81 / 200`; no analytic hypotheses are included. -/
def ZudilinHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < (81 : ℝ) / 200

/-- The exact integer comparison placing `3 / 2` beyond the `81 / 200`
threshold defined above. -/
theorem threeHalves_zudilin_power_obstruction :
    3 ^ 81 < 2 ^ 200 := by
  sorry

/-- The height ratio of `3 / 2` is strictly larger than `81 / 200`. -/
theorem eightyOneTwoHundredths_lt_threeHalves_log_ratio :
    (81 : ℝ) / 200 < Real.log 2 / Real.log 3 := by
  sorry

/-- The height region defined above does not contain `3 / 2`.  This is a
method boundary, not a rationality or irrationality theorem for the
corresponding Lambert value. -/
theorem threeHalves_outside_zudilinHeightRegion :
    ¬ ZudilinHeightRegion 3 2 := by
  sorry

/-- The Bundschuh--Väänänen height region also does not contain `3 / 2`; its
margin is smaller than the threshold already crossed above. -/
theorem threeHalves_outside_bundschuhVaananenHeightRegion :
    ¬ BundschuhVaananenHeightRegion 3 2 := by
  sorry

end Erdos249257.ExternalVerification1049PublishedHeightRegions
