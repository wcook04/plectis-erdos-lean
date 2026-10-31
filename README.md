# Plectis Erdős Lean

Lean 4 proofs from research on eight Erdős problems. Each result keeps its
statement in one file and its proof in another, and
[Comparator](https://github.com/leanprover/comparator) compares the two, so a
reviewer can read the statement without reading the proof.

**Theorem to try first.** Let *b* ≥ 2 be an integer and let *A* be an infinite set
of positive integers such that the sum of 1/*a* over *a* in *A* is finite. Then the
sum of 1/(*b*<sup>*a*</sup> - 1) over *a* in *A* is irrational.

**See it with nothing installed:**
[Palomar registry entry](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-21-000018&version=1) ·
[statement](ExternalVerification257ReciprocalSupport/Challenge.lean) ·
[proof](Solutions/ExternalVerification257ReciprocalSupport.lean) ·
[build log for this proof on `main`](https://github.com/wcook04/plectis-erdos-lean/actions/runs/41245506245)

**Build this one proof** with [elan](https://leanprover-community.github.io/get_started.html)
and Git. The first run needs network access and several gigabytes of disk. It
downloads about 8,500 compiled Mathlib files, then compiles the 38 modules of
this repository that the proof uses.

```sh
git clone --filter=blob:none https://github.com/wcook04/plectis-erdos-lean.git
cd plectis-erdos-lean
lake exe cache get
lake build ExternalVerification257ReciprocalSupport.AxiomAudit
```

The build prints that the theorem depends on axioms `propext`,
`Classical.choice` and `Quot.sound`, then `Build completed successfully`.

**Next:** [inspect this result](#inspect-one-result) ·
[what Lean and Comparator leave out](#what-lean-and-comparator-establish) ·
[arriving from Formal Conjectures](#arriving-from-formal-conjectures) ·
[the eight problems](#the-eight-problems) ·
[folder map](#where-things-live)

Will Cook directs this work and is not a mathematician. AI agents did most of
the research and drafting, and no human mathematical peer review is recorded for
any entry. Erdős problem #1041 is answered for the exact Formal Conjectures statement by a
counterexample due to ani, and the other seven problems remain open. The other
results here are restricted results, obstructions and reformulations, set out
per problem in [the table below](#the-eight-problems).

## Inspect one result

The theorem above has one folder and one proof file.

| To see | Open |
|---|---|
| The exact statement | [`Challenge.lean`](ExternalVerification257ReciprocalSupport/Challenge.lean). Its `sorry` is deliberate, because this file only states the theorem. |
| The proof | [`Solutions/ExternalVerification257ReciprocalSupport.lean`](Solutions/ExternalVerification257ReciprocalSupport.lean), which imports [the source proof](Erdos257PeriodNoncollapse/AllBaseReciprocalSupportIrrationality.lean) and contains no `sorry`. |
| The axioms | [`AxiomAudit.lean`](ExternalVerification257ReciprocalSupport/AxiomAudit.lean), which prints them when built. |
| What Comparator was told to compare | [`comparator.json`](ExternalVerification257ReciprocalSupport/comparator.json), which names one theorem, three permitted axioms and the NanoDa kernel. |
| Scope, sources and attribution | [`formalization.yaml`](ExternalVerification257ReciprocalSupport/formalization.yaml). |

The exponent condition concerns the reciprocals of the exponents, and supports
with a divergent reciprocal sum are outside the theorem, so #257 itself remains
open. Erdős printed the pairwise-coprime case in 1968 and stated, without
printing the argument, that coprimality could be dropped. The proof here was
written independently, with no priority claim.

Three outside records exist for this theorem, and each is bound to one version
of it.

| Record | What it states | What it leaves out |
|---|---|---|
| [Palomar verification run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/35192583926) | Comparator and the Lean and NanoDa kernels accepted the proof at commit [`c39cea6a`](https://github.com/wcook04/plectis-erdos-lean/tree/c39cea6a976747d132a848d26f110b9c608d5a45) under Lean 4.29.0. | The current `main`, which uses Lean 4.30.0. |
| [Palomar review and registration](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-21-000018&version=1) | A language model reviewed the entry, found no blocking problem and left one comment: the informal proof account omits the step where infinitude gives a strict minimum. The entry was then registered on 21 October 2026. | Human review. Palomar has no human editorial step. |
| [Formal Conjectures #6529](https://github.com/google-deepmind/formal-conjectures/pull/6529) | Two reviewers approved earlier revisions, and the request was merged on 9 October 2026, adding a subtype version of the statement. | Every other claim in this repository. |

## What Lean and Comparator establish

Lean's kernel accepts a proof of the exact formal statement, on the axioms the
audit prints, against the pinned Mathlib.

Comparator goes further for selected declarations. It compiles the statement
apart from the proof, confirms the proof proves that same statement, and refuses
axioms outside the list in `comparator.json`. With NanoDa enabled, a second
kernel runs on the exported proof.

Neither tool establishes that a result is new or important, or that the formal
statement says what its English description says. That last judgement comes
from reading `Challenge.lean`, and a Challenge that states less than the
surrounding prose would still pass. Where the literature does not settle
novelty, `formalization.yaml` records it as unassessed.

Comparator also covers only what a run selected. `comparator.json` lists the
selected theorems, and a result for one commit does not carry over to another.
`lake build` does not run Comparator. Comparator confines the proof with
[landrun](https://github.com/zouuup/landrun), which needs Linux, and
[`palomar-replay.yml`](.github/workflows/palomar-replay.yml) lists the steps that
build and run it. That workflow is a diagnostic, because statement and proof
share a workspace. A run of
[`fc-trusted-comparator-preflight.yml`](.github/workflows/fc-trusted-comparator-preflight.yml)
prepares and protects the statement before the proof runs.

## Arriving from Formal Conjectures

Proof links in Formal Conjectures requests point to commits pinned in this
repository, usually inside [`verification/`](verification/README.md). Each folder
there is a separate Lake project with its own toolchain and manifest, and the
main build does not import it.

| Folder | What it holds |
|---|---|
| `verification/FC*Current/` | Adapters proving the exact Formal Conjectures declaration in Lean 4.33.1 with the Mathlib commit Formal Conjectures pinned. |
| `verification/FC257ReciprocalSupport/` and three others without `Current` | Frozen copies of an original proof under Lean 4.29.1. |
| `source-binding.json` in each folder | The original commit, and a digest for every copied file. |

As of 31 October 2026, five contributions have been merged into Formal
Conjectures and 14 requests are open. The
[Formal Conjectures crosswalk](https://github.com/wcook04/plectis-erdos/blob/main/docs/verification/FORMAL_CONJECTURES_CROSSWALK.md)
lists each request with its reviews, and sets the 19 formal declarations beside
the runs that compared them. Those runs are hosted by this project. A merge
accepts the scoped upstream change, and an approval on an open request applies
to that request at that commit.

## The eight problems

Each entry folder holds the full statement in `formalization.yaml`, and
[`PROBLEMS.md`](PROBLEMS.md) gives the longer account of each problem.

| Problem | Selected result here | Entry | Original problem |
|---|---|---|---|
| [#68](https://www.erdosproblems.com/68) | An explicit cubic lower bound on the support radius of a finite system of factorial channels, under stated divisibility hypotheses. | [`ChannelRadius`](ExternalVerification68ChannelRadius/) | Open |
| [#243](https://www.erdosproblems.com/243) | Rigidity of the integer orbit when its centred error has a one-sided bound and normalised vanishing, both assumed: the orbit eventually follows the Sylvester recurrence. | [`BoundedNegativePartRigidity`](ExternalVerification243BoundedNegativePartRigidity/) | Open |
| [#249](https://www.erdosproblems.com/249) | Irrationality of the sum over *n* of (φ(*n*) mod *m*)/2<sup>*n*</sup> for every *m* ≥ 3. The series with φ(*n*) itself is not covered. | [`ResidueClassTotientSeries`](ExternalVerification249ResidueClassTotientSeries/) | Open |
| [#251](https://www.erdosproblems.com/251) | Any rational value of the prime-gap series has denominator at least 2<sup>589</sup>, decided in the Lean kernel. Irrationality is not proved. | [`KernelDenominatorFloor`](ExternalVerification251KernelDenominatorFloor/) | Open |
| [#257](https://www.erdosproblems.com/257) | The theorem at the top of this page. | [`ReciprocalSupport`](ExternalVerification257ReciprocalSupport/) | Open |
| [#269](https://www.erdosproblems.com/269) | For the primes 2, 3 and 5, an equivalence between a local window escape and irrationality of the running-LCM value. Neither side is proved. | [`WindowEscapeEquivalence`](ExternalVerification269WindowEscapeEquivalence/) | Open |
| [#1041](https://www.erdosproblems.com/1041) | The exact Formal Conjectures path-length statement is refuted using [ani's degree-seven construction](https://www.erdosproblems.com/forum/thread/1041#post-8861), and two-root distance bounds and straight-line obstructions are proved separately. | [`FC1041HausdorffCounterexample`](verification/FC1041HausdorffCounterexample/) and [`CriticalGeometry`](ExternalVerification1041CriticalGeometry/) | Answered for that statement. Independent human review of its match with the 1958 wording is not recorded. |
| [#1049](https://www.erdosproblems.com/1049) | Irrationality of the sum over *m* ≥ 1 of 1/((*a*/*b*)<sup>*m*</sup> - 1) for coprime integers *a* > *b* ≥ 1 in an explicit region, which contains 31/4 and its positive powers and excludes 3/2. | [`PalomarCorpus/E1049_01`](PalomarCorpus/E1049_01/) and [`RationalBaseContour`](ExternalVerification1049RationalBaseContour/) | Open |

The entry names above omit the `ExternalVerification<problem>` prefix of their
folders. The 38 theorem families are listed in
[`docs/theorem-families.md`](docs/theorem-families.md).

## Where things live

The root holds more than 370 folders because Lake finds each library by its
top-level name, and Palomar and Comparator records point at those paths. They
fall into a few groups.

| Location | Contents |
|---|---|
| `ExternalVerification<problem><Name>/` | 365 folders, each with `Challenge.lean`, `AxiomAudit.lean`, `comparator.json` and `formalization.yaml`. [38 of them](docs/theorem-families.md) are the theorem families. The `PaperStatements*` and `PaperStructures*` folders restate theorems from the papers against Mathlib alone. |
| [`PalomarCorpus/`](PalomarCorpus/README.md) | 143 entries, in the order the papers state their theorems. |
| [`Solutions/`](Solutions/) | The proof for each entry, under a separate module prefix so that Palomar's protected Challenge directory cannot shadow it. |
| [`Erdos249257/`](Erdos249257/), [`Erdos257PeriodNoncollapse/`](Erdos257PeriodNoncollapse/), [`ErdosProblems/`](ErdosProblems/) | The Lean mathematics that the Solutions import. |
| [`verification/`](verification/README.md) | Separate projects for [Formal Conjectures](#arriving-from-formal-conjectures). |
| [`scripts/`](scripts/CONVENIENCE_BUILDS.md) | Build runner, axiom audit and release tools, with the build guide. |
| [`docs/`](docs/theorem-families.md), [`METHOD.md`](METHOD.md), [`PROBLEMS.md`](PROBLEMS.md) | The family list, how AI models were used, and each problem's unresolved step. |
| [`snapshot/`](snapshot/README.md), `PlectisSnapshot/` | Records of the first public export, tag `v0.1.1`. |
| [`skills/`](skills/lean-checkpoint-entry/SKILL.md) | The procedure for writing or reviewing an entry. |

An entry in `PalomarCorpus/E<problem>_<NN>/` has the same four files, and its
proof is `Solutions/PalomarCorpus/E<problem>_<NN>.lean`. Its adapters import a
generated `Statement.lean`, the Challenge without its theorems, so that the
constants Comparator walks are the same on both sides.

<a id="palomar-publication-surface"></a>

## Palomar registry

[Palomar](https://palomar-registry.org) is a public registry of Lean
formalisations. It has three separate steps, and they establish different things.

1. **Verification** is a machine run. Comparator compares the selected statements
   with the proof, and independent kernels run on the exported proof.
2. **Editorial review** is automatic. A language model judges the statement
   against the informal account and Palomar's published standard, and
   [Palomar states](https://palomar-registry.org/about) that this review "does not
   accept, approve, or endorse a result".
3. **Registration** follows when the review finds no blocking problem and the
   submitter chooses to register. The entry is then bound to one commit.

Ten editions from this repository were recorded as registered when
[last observed on 22 October 2026](https://github.com/wcook04/plectis-erdos/blob/main/docs/verification/palomar_registry_status.json).
That record gives each edition's commit, configuration and selected declarations.
Registration does not carry over to `main` or to another commit, and the `E1041_01`
intake has not been registered. As Palomar's
[statement](https://palomar-registry.org/statement) sets out, an entry does not
certify novelty, relevance or a match with the informal statement.

<details>
<summary>The 143 paper-order entries, by problem</summary>

<!-- palomar-entry-table:begin (generated; do not edit by hand) -->
The Palomar entries are packed in the order the papers state their theorems; [`PalomarCorpus/README.md`](PalomarCorpus/README.md) lists every entry with its theorem count and title.

| Problem | Entries | Theorems |
|---|---|---:|
| #68 | `E68_01` to `E68_10` | 73 |
| #243 | `E243_01` to `E243_11` | 140 |
| #249 | `E249_01` to `E249_33` | 622 |
| #251 | `E251_01` to `E251_08` | 87 |
| #257 | `E257_01` to `E257_52` | 651 |
| #269 | `E269_01` to `E269_11` | 92 |
| #1041 | `E1041_01` to `E1041_08` | 107 |
| #1049 | `E1049_01` to `E1049_10` | 117 |
| Total | 143 entries | 1889 |
<!-- palomar-entry-table:end -->

</details>

## Larger builds

Python 3.11 or later runs the build tools. This command builds every default
target, the 38 families and the full paper-order corpus:

```sh
python3 scripts/build_launch_targets.py
```

Appending `--plan` lists the targets without Lean or Mathlib. The
[build guide](scripts/CONVENIENCE_BUILDS.md) covers changed-module builds, reports
and the release population. Each project in `verification/` has its own pins.

## How AI was used

[`METHOD.md`](METHOD.md) describes the method. Models without repository access
received copies of the relevant sources and returned proposed arguments, and
agents with tool access formalised them in Lean. Each result is accepted through
the same Challenge, Solution and axiom audit, whoever proposed the argument.
Will Cook is the responsible maintainer.

## Papers and videos

- [`wcook04/plectis-erdos`](https://github.com/wcook04/plectis-erdos) holds the papers, research records and the [credit record](https://github.com/wcook04/plectis-erdos#credit) for prior mathematics, public contributions and reader feedback.
- The [mathematics website](https://wcook04.github.io/practical-formal-verification/maths/) and [maths map](https://wcook04.github.io/practical-formal-verification/maths/universe.html) connect papers, results and Lean sources.
- [Plectis Atlas](https://wcook04.github.io/plectis-atlas/) is a separate reader for OpenAI's mathematics release, and the [Plectis toolkit](https://github.com/wcook04/practical-formal-verification) holds reusable Python components.
- Videos: [the maths map](https://www.youtube.com/watch?v=u4f-fk1o13k), [a proof of the #257 theorem above, starting with examples](https://www.youtube.com/watch?v=uWCqtRkJ8P0) and [an introduction to Plectis](https://www.youtube.com/watch?v=MBmVMMogXTA). A Lean proof does not cover the argument spoken in a video.

The project builds on [Lean](https://lean-lang.org/) and
[Mathlib](https://github.com/leanprover-community/mathlib4), with problems and
references from [erdosproblems.com](https://www.erdosproblems.com/).

## Contribute and cite

Report a broken entry, build command or release package through
[`CONTRIBUTING.md`](CONTRIBUTING.md). Mathematical arguments, corrections and
explanations go to the
[contribution guide of the research repository](https://github.com/wcook04/plectis-erdos/blob/main/CONTRIBUTING.md).

Cite this repository through [`CITATION.cff`](CITATION.cff), at the commit you
read. Code and documentation are [Apache-2.0](LICENSE), and
[`REUSE.toml`](REUSE.toml) records the attribution policy.
