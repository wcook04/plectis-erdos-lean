# Pinned Prove2Me extraction

This is a read-only extraction job for two public Lean source commits. It does
not call the Prove2Me API or publish a theorem. The exact source commits,
Lean/Mathlib pins, selected declarations, input module hashes, and official
extractor hashes are in `manifest.json`. The #257 inventory has 73 modules and
three project prefixes; #243 has 54 modules and one prefix. The input inventory
does not assert a declaration dependency graph or source positions.

The new workflow cannot receive `workflow_dispatch` while it is absent from
the default branch. A push to the exact dedicated branch
`codex/prove2me-remote-extraction-20260924` runs the reviewed `request.json`.
The initial request selects **#257 full extraction**. Stage 1 checks its actual
graph and selected declarations before Stage 2 runs on the 73 audited modules.
If Stage 2 hits the job limit, the graph and completed partial files remain in
the run artifact. Set `problem` to `243` in a later reviewed commit to use the
other source pin. Every push that changes this directory or the workflow file
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
```

Source checkouts must be at the exact manifest commits. The two `prepare`
commands verify every audited source hash and the prepared Stage 1 script hash
without launching Lean.
