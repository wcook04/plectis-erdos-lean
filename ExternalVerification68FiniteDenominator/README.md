# The full finite denominator exclusion

The selected theorem `full_finite_denominator_exclusion` says that every
representation of the literal series `Σ n≥2, 1/(n!−1)` as `a/q`, with integer
`a` and positive natural `q`, satisfies all three bounds:

- `2^39990 ≤ q`;
- `fareyLeftDenominator + fareyRightDenominator ≤ q`;
- `10^12040 < q`.

The two Farey denominators are the exact hexadecimal numerals in the source
certificate. Challenge imports only Mathlib and states the series and numerals
independently. It assumes neither reducedness nor a certificate-validity
predicate. Solution directly applies the full source theorem. The older
`finite_denominator_exclusion` remains as an unselected compatibility projection;
it is not a second comparison entry. `comparator.json` and `AxiomAudit.lean`
select the full theorem. The deliberate-negative Solution omits the Farey-sum
conjunct, and its Comparator replay must reject that type mismatch.

This is a prepared comparison candidate. The twelve-module source closure and
Lean 4.30 environment recorded in `source_binding.json` match the public base
`8e01c98d8e76286b876361478138e39c670fd1b0` byte for byte. The original
source compiled in run `36276879997`; the selected full wrapper is new.
That run printed standard-only axioms for the old two-bound bridge; a direct
axiom print for the full source endpoint was not retained. These new wrappers
have **not** been elaborated, axiom-audited or independently compared.
The earlier private preparation root was Lean 4.29.1 with one differing
dependency. `source_binding.json` records that history separately from this
public Lean 4.30 target.

For bounded offline checks against the retained original source checkout, run:

```sh
python3 ExternalVerification68FiniteDenominator/check_contract.py \
  --source-root /path/to/retained-c93-source --self-test
```

The check verifies all twelve source and both environment hashes, trusted
imports, literal numerals, the full statement, selection, and audit coverage.
Its corruption controls are source checks, not Lean or Comparator verdicts.
The 21,114-byte, 29-line Challenge fits the existing hard limits of 102,400 bytes
and 1,000 lines in the source repository's `scripts/check_axiom_budget.py`.

This family is now a default CI build target, so the release gate compiles its
Challenge, Solution, AxiomAudit and NegativeSolution modules. Inspect the
full-target axiom output in that run; the release gate's automated axiom
comparison covers Palomar entries, not this family. For a focused reproduction,
explicitly build `ExternalVerification68FiniteDenominator.Challenge`,
`.Solution`, `.AxiomAudit` and `.NegativeSolution`. Then run the positive and
deliberate-negative configurations
with the supported independent Comparator/NanoDa runner. Existing two-bound
receipts cannot accept this changed selection. No public acceptance or service
submission is recorded here. Irrationality and the separate factorial-divisibility
exclusion remain outside this theorem.

The branch-local `.github/workflows/e68-comparator-replay.yml` runs that focused
reproduction on a hosted Linux runner after a branch push. It restores the newest
corpus build, rebuilds Challenge from source, checks the twelve-module binding,
prints the selected theorem's axioms, and uses the pinned Comparator toolchain
and supported systemd sandbox for both configurations. The positive result must
contain NanoDa and Lean kernel acceptance; the deliberately weakened Solution
must fail with the exact statement-mismatch diagnostic and no kernel acceptance.
`scripts/e68_comparator_replay.py` writes raw stage logs and an exact-head JSON
receipt to the `e68-exact-comparator-replay` Actions artifact. A prepared workflow
or green offline contract check is not an independent replay result.
