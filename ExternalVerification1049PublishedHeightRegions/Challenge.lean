/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #1049 height-region placement at base `31 / 4`

This Mathlib-only interface fixes two parameter regions for a reduced rational
base `a / b` and places `31 / 4` against both.

`BundschuhVaananenHeightRegion` is the elementary parameter inequality
`log b / log a < 1/2 - 1/π²` appearing in the published Bundschuh--Väänänen
criterion.  `ZudilinHeightRegion` is the inequality `log b / log a < 81/200`.
The second threshold is defined here; it is not a published criterion.

Two placements are stated.  The exact integer certificate `4^200 < 31^81` puts
`log 4 / log 31` below `81/200`, and the height ratio is invariant under a
common positive power, so every base `31^r / 4^r` with `r ≥ 1` satisfies the
same threshold.  The certificate `31² < 4⁵` puts `log 4 / log 31` above `2/5`,
and `1/2 - 1/π² < 2/5`, so `31 / 4` lies outside the Bundschuh--Väänänen
region.

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

/-- The exact integer comparison behind the `31 / 4` parameter certificate. -/
theorem thirtyoneFour_power_certificate : 4 ^ 200 < 31 ^ 81 := by
  sorry

/-- The logarithmic height ratio is invariant under a common positive power. -/
theorem zudilinHeightRegion_pow (a b r : ℕ) (hr : 0 < r)
    (h : ZudilinHeightRegion a b) :
    ZudilinHeightRegion (a ^ r) (b ^ r) := by
  sorry

/-- Every positive power of `31 / 4` satisfies the `81 / 200` threshold. -/
theorem thirtyoneFour_power_mem_zudilinHeightRegion (r : ℕ) (hr : 0 < r) :
    ZudilinHeightRegion (31 ^ r) (4 ^ r) := by
  sorry

/-- The base `31 / 4` lies outside the Bundschuh--Väänänen height region. -/
theorem thirtyoneFour_outside_bundschuhVaananenHeightRegion :
    ¬ BundschuhVaananenHeightRegion 31 4 := by
  sorry

end Erdos249257.ExternalVerification1049PublishedHeightRegions
