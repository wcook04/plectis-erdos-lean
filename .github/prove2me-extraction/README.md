# Pinned Prove2Me extraction

This is a read-only extraction job for pinned public Lean sources. It does
not call the Prove2Me API or publish a theorem. The exact source commits,
Lean/Mathlib pins, selected declarations, input module hashes, and official
extractor hashes are in `manifest.json`. The current mixed-support #257 inventory has 67 modules and
three project prefixes; #243 has 54 modules and one prefix; #249 has 11 modules
and three prefixes. The input inventory
does not assert a declaration dependency graph or source positions.

The new workflow cannot receive `workflow_dispatch` while it is absent from
the default branch. A push to the exact dedicated branch
`codex/prove2me-remote-extraction-20260924` runs the reviewed `request.json`.
The current reviewed request selects **#257 mixed-support extraction**
at `c93c2e4dd86a2e317e0cb650ea244fee1afd59c2`. Its root is
`ErdosProblems.Erdos257.PaperCompleteR8.ArbitraryWeightMixedClaim`; the selected
endpoint is `arbitraryWeightMixedSupport_allBase_hereditary`. All 67 modules
are retained. The theorem assumes finite-prime weighted binary mass on E and
an arbitrary positive-weight logarithmic cover of V; it concludes all-base
hereditary irrationality on E union V. It does not prove irrationality on an
arbitrary infinite support. The proof chooses a common sample for both
budgets; separate small-return witnesses would not suffice.

This updates only the #257 case. The historical weighted #257 extraction
remains frozen under its earlier manifests; accepted proofs are not repeated
by this request. All seven other cases and the global extractor pins are
unchanged. The full #1041 counterexample extraction 36300898010 succeeded;
its original GitHub artifact 10926345599, metadata, exact manifest and verified
13-module/four-target intake were retained before this request advanced.
#251 retains both full-strength denominator endpoints and all 250 streaming
certificate blocks in its 256-module closure. #269 retains both targets over
15 modules; #1049 retains all eight targets over 59 modules.
Do not push another request while an extraction is active: branch concurrency
cancels the in-progress job. Advance one selected request only after consuming
the preceding job's terminal receipt and preserving its artifact.
If Stage 2 hits the job limit, the graph and completed partial files remain in
the run artifact. Set `problem` to `243` in a later reviewed commit to use the
other source pin, or `257` for this mixed-support case. The CLI explicitly admits
only these eight reviewed cases. Every push that changes this directory or the workflow file
launches a run; an unchanged branch does not rerun.

The job restores only a compatible compiled corpus cache from existing CI,
then builds the selected import roots with Lean 4.30.0 and the pinned Mathlib
cache. It never saves a new cache. Lake checks the restored build traces against
the pinned sources; a cache hit alone is not proof that a module built. The job
then runs Prove2Me's official Stage 1 script. `full` additionally
runs the official Stage 2 script on each module. The runner verifies the exact
source inputs and extractor bytes before Lean, checks the selected declaration
rows after Stage 1, samples runner disk against a 2 GiB free-space floor, and
retains logs and JSONL output as a seven-day artifact. The job has a 330-minute
limit; Stage 1 has a 20-minute limit; each Stage 2 file has a five-minute limit.
Stage 1 must succeed before Stage 2 starts. Returned spans are tied to the
source file hashes in the manifest.

Static preparation can be checked without running Lean:

```sh
python3 .github/prove2me-extraction/run.py select
python3 .github/prove2me-extraction/run.py prepare --problem 257 --source /path/to/c93c2e4-checkout --out /tmp/p2m-257
python3 .github/prove2me-extraction/run.py prepare --problem 243 --source /path/to/4fe59e0-checkout --out /tmp/p2m-243
python3 .github/prove2me-extraction/run.py prepare --problem 249 --source /path/to/c93c2e4-checkout --out /tmp/p2m-249
```

Source checkouts must be at the exact manifest commits. The `prepare`
commands verify every audited source hash and the prepared Stage 1 script hash
without launching Lean.

The #249 extraction uses the recorded Lean 4.30 source. Correspondence with
the paper's Lean 4.29.1 source and the eventual staged upload still requires
elaborated type and axiom checks. Extraction alone is neither platform
submission nor personal review, and it does not complete whole-paper coverage.

The additional cases use the same pinned official extractors and Lean 4.30 /
Mathlib environment. #269 selects uniform kernel rank/nonseparation and
admissible modular minors; this does not prove irrationality of the three-prime
sum. #1049 retains all eight selected rational-base threshold, measure and
printed-constant endpoints and their existing source attribution. The supported
#68 and #1049 snapshots still need their recorded cross-edition elaborated checks.
