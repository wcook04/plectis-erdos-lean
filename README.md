# Plectis Erdős Lean

[Will Cook’s home page: all projects and videos](https://wcook04.github.io/)

This repository contains Lean source for results related to eight mathematical
problems posed by Paul Erdős. **Lean** is a language for writing mathematical
statements and proofs that a computer can check. The [research repository](https://github.com/wcook04/plectis-erdos)
contains the papers and explanations; this repository contains the proof files
and commands for checking them.

For selected results, the statement and proof are kept in separate files.
[Comparator](https://github.com/leanprover/comparator) checks the proposed proof
against the separately written statement and its permitted assumptions. You
can read that statement to see exactly what is being claimed.

**Theorem to try first.** Let *b* ≥ 2 be an integer and let *A* be an infinite set
of positive integers such that the sum of 1/*a* over *a* in *A* is finite. Then the
sum of 1/(*b*<sup>*a*</sup> - 1) over *a* in *A* is irrational.

**See it with nothing installed:**
[Proof in Palomar, an online registry](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-21-000018&version=1) ·
[statement](proofs/families/ExternalVerification257ReciprocalSupport/Challenge.lean) ·
[proof](proofs/Solutions/ExternalVerification257ReciprocalSupport.lean) ·
[build log for this proof on `main`](https://github.com/wcook04/plectis-erdos-lean/actions/runs/41245506245)

**Build this one proof.** Install Lean with
[elan](https://leanprover-community.github.io/get_started.html) and install Git.
`lake`, Lean’s build tool, comes with Lean. The first run needs network access and several gigabytes of disk. It
downloads about 8,500 compiled files from **Mathlib**, Lean’s mathematics
library, then compiles the 38 source files in this repository that the proof uses.

```sh
git clone --filter=blob:none https://github.com/wcook04/plectis-erdos-lean.git
cd plectis-erdos-lean
lake exe cache get
lake build ExternalVerification257ReciprocalSupport.AxiomAudit
```

An **axiom** is an assumption the checker permits without a proof. The build
prints that this theorem uses the axioms `propext`,
`Classical.choice` and `Quot.sound`, then `Build completed successfully`.

**Next:** [inspect this result](#inspect-one-result) ·
[what Lean and Comparator leave out](#what-lean-and-comparator-establish) ·
[arriving from Formal Conjectures](#arriving-from-formal-conjectures) ·
[the eight problems](#the-eight-problems) ·
[folder map](#where-things-live)

[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) is a
separate collection of mathematical conjectures written in Lean. Some results
here have been submitted to that collection.

Will Cook directs this work and is not a mathematician. AI agents did most of
the research and drafting. Apart from the reviews of requests to Formal Conjectures,
no human mathematical peer review is recorded. Erdős problem #1041 is answered for the exact Formal Conjectures statement by a
counterexample due to ani, and the other seven problems remain open. The other
results here are restricted results, obstructions and reformulations, set out
per problem in [the list below](#the-eight-problems).

## Inspect one result

The theorem above has one folder and one proof file.

- **The exact statement:** [`Challenge.lean`](proofs/families/ExternalVerification257ReciprocalSupport/Challenge.lean).
  Here `sorry` marks a deliberately omitted proof: this file supplies only the statement to compare against.
- **The proof:** [open its Lean file](proofs/Solutions/ExternalVerification257ReciprocalSupport.lean),
  which imports [the source proof](Erdos257PeriodNoncollapse/AllBaseReciprocalSupportIrrationality.lean) and contains no `sorry`.
- **The axioms:** [`AxiomAudit.lean`](proofs/families/ExternalVerification257ReciprocalSupport/AxiomAudit.lean),
  which prints them when built.
- **What Comparator was told to compare:** [`comparator.json`](proofs/families/ExternalVerification257ReciprocalSupport/comparator.json),
  which names one theorem, three permitted axioms and NanoDa, an additional proof-checking program.
- **Scope, sources and attribution:** [`formalization.yaml`](proofs/families/ExternalVerification257ReciprocalSupport/formalization.yaml).

The condition is about the sum of `1/a` over the exponents in the set A.
Sets for which that sum diverges are outside this theorem, so it does not
answer problem #257 for every infinite set. Erdős printed the pairwise-coprime case in 1968 and stated, without
printing the argument, that coprimality could be dropped. The proof here was
written independently, with no priority claim.

Three outside records exist for this theorem, and each is bound to one version
of it.

- **[Palomar verification run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/35192583926):**
  Comparator and the Lean and NanoDa kernels accepted the proof at commit
  [`c39cea6a`](https://github.com/wcook04/plectis-erdos-lean/tree/c39cea6a976747d132a848d26f110b9c608d5a45)
  under Lean 4.29.0. That run does not check the current `main`, which uses Lean 4.30.0.
- **[Palomar review and registration](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-21-000018&version=1):**
  A language model reviewed the entry, found no blocking problem and left one comment:
  the informal proof account omits the step where infinitude gives a strict minimum.
  The entry was then registered on 21 October 2026. This was not human review;
  Palomar has no human editorial step.
- **[Formal Conjectures #6529](https://github.com/google-deepmind/formal-conjectures/pull/6529):**
  Two reviewers approved earlier revisions, and the request was merged on 9 October 2026,
  adding a version of the statement to that collection. This does not establish
  any other claim in this repository.

## What Lean and Comparator establish

Lean’s kernel, the small core program that checks proofs, accepts a proof of
the exact statement written in Lean. It uses the axioms the audit prints and
the version of Mathlib fixed by this repository’s dependency file.

Comparator checks the theorems named in its configuration file. It compiles the statement
apart from the proof, confirms the proof proves that same statement, and refuses
axioms outside the list in `comparator.json`. With NanoDa enabled, that additional program also checks the proof.

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

[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) is a
separate collection of mathematical conjectures written in Lean. This repository
contains proofs and adapters, short pieces of Lean code that put a proof into
the exact statement that collection asks for.

Proof links in Formal Conjectures requests point to commits pinned in this
repository, usually inside [`verification/`](verification/README.md). Each folder
there is a separate project with its own Lean version and dependency list.
The main build does not include those projects.

- Folders named `FC*Current` inside [`verification/`](verification/README.md)
  contain adapters proving the exact Formal Conjectures declaration in Lean 4.33.1,
  with the Mathlib commit Formal Conjectures pinned.
- [`FC257ReciprocalSupport`](verification/FC257ReciprocalSupport/) and three
  other folders without `Current` contain frozen copies of an original proof
  under Lean 4.29.1.
- `source-binding.json` in each folder records the original commit and a
  digest for every copied file.

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

- **[#68](https://www.erdosproblems.com/68) — Open** An explicit cubic lower bound on the support radius of a finite system of factorial channels, under stated divisibility hypotheses. Entry: [`ChannelRadius`](proofs/families/ExternalVerification68ChannelRadius).

- **[#243](https://www.erdosproblems.com/243) — Open** Rigidity of the integer orbit when its centred error has a one-sided bound and normalised vanishing, both assumed: the orbit eventually follows the Sylvester recurrence. Entry: [`BoundedNegativePartRigidity`](proofs/families/ExternalVerification243BoundedNegativePartRigidity).

- **[#249](https://www.erdosproblems.com/249) — Open** Irrationality of the sum over *n* of (φ(*n*) mod *m*)/2<sup>*n*</sup> for every *m* ≥ 3. The series with φ(*n*) itself is not covered. Entry: [`ResidueClassTotientSeries`](proofs/families/ExternalVerification249ResidueClassTotientSeries).

- **[#251](https://www.erdosproblems.com/251) — Open** Any rational value of the prime-gap series has denominator at least 2<sup>589</sup>, decided in the Lean kernel. Irrationality is not proved. Entry: [`KernelDenominatorFloor`](proofs/families/ExternalVerification251KernelDenominatorFloor).

- **[#257](https://www.erdosproblems.com/257) — Open** The theorem at the top of this page. Entry: [`ReciprocalSupport`](proofs/families/ExternalVerification257ReciprocalSupport).

- **[#269](https://www.erdosproblems.com/269) — Open** For the primes 2, 3 and 5, an equivalence between a local window escape and irrationality of the running-LCM value. Neither side is proved. Entry: [`WindowEscapeEquivalence`](proofs/families/ExternalVerification269WindowEscapeEquivalence).

- **[#1041](https://www.erdosproblems.com/1041) — Answered for that statement. Independent human review of its match with the 1958 wording is not recorded.** The exact Formal Conjectures path-length statement is refuted using [ani's degree-seven construction](https://www.erdosproblems.com/forum/thread/1041#post-8861), and two-root distance bounds and straight-line obstructions are proved separately. Entry: [`FC1041HausdorffCounterexample`](verification/FC1041HausdorffCounterexample/) and [`CriticalGeometry`](proofs/families/ExternalVerification1041CriticalGeometry).

- **[#1049](https://www.erdosproblems.com/1049) — Open** Irrationality of the sum over *m* ≥ 1 of 1/((*a*/*b*)<sup>*m*</sup> - 1) for coprime integers *a* > *b* ≥ 1 in an explicit region, which contains 31/4 and its positive powers and excludes 3/2. Entry: [`proofs/PalomarCorpus/E1049_01`](proofs/PalomarCorpus/E1049_01) and [`RationalBaseContour`](proofs/families/ExternalVerification1049RationalBaseContour).

The entry names above omit the `ExternalVerification<problem>` prefix of their
folders. The 38 theorem families are listed in
[`docs/theorem-families.md`](docs/theorem-families.md).

## Where things live

Start with the [proof folder guide](proofs/README.md).

- [`proofs/families/`](proofs/families/): folders for individual statements and
  their checking configuration. The [38 selected groups](docs/theorem-families.md)
  are included in the release checks. Other generated folders also live here;
  their presence alone does not establish that they have passed those checks.
- [`proofs/PalomarCorpus/`](proofs/PalomarCorpus/README.md): 143 groups of statements,
  arranged in the order the papers present their theorems.
- [`proofs/Solutions/`](proofs/Solutions/): proofs and small pieces of Lean code
  that connect them to the separately written statements.
- [`Erdos249257/`](Erdos249257/), [`Erdos257PeriodNoncollapse/`](Erdos257PeriodNoncollapse/)
  and [`ErdosProblems/`](ErdosProblems/): the underlying mathematical proofs and definitions.
- [`verification/`](verification/README.md): separate projects for checking
  contributions to Formal Conjectures against its Lean and Mathlib versions.
- [`scripts/`](scripts/CONVENIENCE_BUILDS.md): build, proof-audit and release tools.
- [`docs/`](docs/theorem-families.md), [`METHOD.md`](METHOD.md), [`PROBLEMS.md`](PROBLEMS.md):
  selected statement list, research method and remaining questions.
- [`snapshot/`](snapshot/README.md) and `PlectisSnapshot/`: records of the first
  public export, tagged `v0.1.1`.
- [`skills/`](skills/lean-checkpoint-entry/SKILL.md): instructions for writing or
  reviewing an entry.

The proof source is grouped under `proofs/`, but Lean module names and build
commands retain their original names. The [folder guide](proofs/README.md)
explains that distinction for contributors.

<a id="palomar-publication-surface"></a>

## Palomar registry

[Palomar](https://palomar-registry.org) is a public registry of mathematical statements and proofs written in Lean. It has three separate steps, and they establish different things.

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
That record gives each edition's commit, configuration and selected statements.
Registration does not carry over to `main` or to another commit, and the `E1041_01`
intake has not been registered. As Palomar's
[statement](https://palomar-registry.org/statement) sets out, an entry does not
certify novelty, relevance or a match with the informal statement.

<details>
<summary>The 143 paper-order entries, by problem</summary>

<!-- palomar-entry-table:begin (generated; do not edit by hand) -->
The Palomar entries are packed in the order the papers state their theorems; [`proofs/PalomarCorpus/README.md`](proofs/PalomarCorpus/README.md) lists every entry with its theorem count and title.

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
and which proofs are included in a release. Each project in `verification/` has its own pins.

## How AI was used

[`METHOD.md`](METHOD.md) describes the method. Models without repository access
received copies of the relevant sources and returned proposed arguments, and
agents with tool access formalised them in Lean. The checking procedure compares a proposed proof with its separate statement
and lists its permitted assumptions, whoever proposed the argument.
Will Cook is the responsible maintainer.

## Papers and videos

[Will Cook’s project index](https://wcook04.github.io/) connects this corpus to
the other projects.

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
