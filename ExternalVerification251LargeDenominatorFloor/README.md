# The paper's finite denominator exclusion for Erdős #251

For either the zero-based prime series or the prime-gap series, a rational
representation `a / b` with `a : ℤ`, `b : ℕ` and `0 < b` must satisfy
`2 ^ 39997 ≤ b ∧ 10 ^ 12040 < b`. This is the exact endpoint of the long
paper's `long251:res:cfexclusion`. It does not prove irrationality or an
irrationality measure. The previously checked `E251_02` endpoint with
`2 ^ 589` and `10 ^ 177` remains a separate, smaller certificate.

The proof uses the finite prime-prefix enclosure at 80,200 primes below
1,023,068. Two explicit Farey neighbours strictly enclose that interval and
have determinant one; a rational between them has denominator at least the
sum of their denominators. The source proves the stronger floors `2 ^ 40062`
and `10 ^ 12059`, then weakens them to the paper's printed bounds. The
prime-gap series is two less than the prime series, which preserves the
denominator bound.

`Challenge.lean` independently defines the two series using Mathlib only.
The separate root module `Erdos251LargeCertificateSolution.lean` applies
`ErdosProblems.Erdos251.PaperR7.LargeCertificate.denominator_floor_both`.
`comparator.json` selects only that transported endpoint. The solution has a
separate module root from the protected Challenge and a non-default Lake
library, so this 250-block certificate is an explicit replay target.

`source-transport.json` records all 256 local modules in the source endpoint's
import closure at paper commit `7f3dbf0947c387335ffd392b689eea5721017d84`.
Every listed source file is copied byte for byte. The inherited computational
options in those certificate blocks are preserved. An independent Python
sieve and Horner fold confirms the final state, both strict bracket
inequalities, determinant one and the numeric bounds:

```sh
python3 ExternalVerification251LargeDenominatorFloor/verify_transport.py
```

That command checks source identity and integer arithmetic only. It does not
replace Lean elaboration, the axiom audit, Comparator or independent kernel
replay. In particular the source pin uses Lean 4.29.1 and this target uses
4.30.0; all four acceptance stages remain pending for this transport.

After resource admission, build only this family and print its axioms:

```sh
LEAN_NUM_THREADS=1 lake build ExternalVerification251LargeDenominatorFloor.Challenge Erdos251LargeCertificateSolution
lake env lean ExternalVerification251LargeDenominatorFloor/AxiomAudit.lean
```

Run Comparator with this family's `comparator.json` on the supported verifier
host and retain its independent-kernel receipt. A successful build or axiom
audit alone must not promote the paper coverage row. Acceptance needs the exact
selected declaration, Challenge, Solution, configuration and source commit
bound to a successful comparison receipt. No existing Palomar entry or
accepted comparison receipt is changed by this preparation.
