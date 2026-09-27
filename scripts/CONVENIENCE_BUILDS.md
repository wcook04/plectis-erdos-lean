# Reproduce a Lean Convenience build

Run the same command as CI from the repository root with Python 3.11 or later:

```sh
python3 scripts/build_launch_targets.py --changed-from origin/main
```

Use the actual parent ref for a stacked pull request. The runner checks changed
Lean modules in dependency order before the full `defaultTargets` list. A focused
failure stops that run immediately; unattempted targets stay visible in the report.
Use `--keep-going` only when collecting independent launch-target failures is worth
the extra build time. Lean Release Gate calls this same workflow and runner, then requires its
publication axiom audit. Comparator acceptance remains separate.

To inspect the selection without installing Lean, append `--plan`. To reproduce
one module quickly, use `--focus Namespace.Module --focused-only`; the resulting
`focused-pass` explicitly does not claim a complete launch build. Remove
`--focused-only` for full validation.

The JSON report is `.lake/convenience-target-report.json`. It records the source
commit, source digest, toolchain, runner digest, target outcomes, compiler errors
and elapsed time. Complete compiler output is compressed under
`.lake/convenience-logs/`; CI uploads both even when the build fails. GitHub's job
summary lists attempted and unattempted targets, with errors linked to source
lines. A timeout, cancellation, log limit or source change cannot produce a pass.

Defaults are one hour per compiler module and five hours for the complete run.
A library target may contain thousands of modules, so it has no separate default
wall-clock cap. An explicit `--target-budget` can impose one when needed. `--module-budget`, `--target-budget` and
`--total-budget` accept finite positive seconds. The runner prints a heartbeat
every minute and only inspects compiler processes descended from its own Lake
process. A timeout stops that process group and preserves completed build files.

For an older source branch, dispatch the **current workflow** with `source_ref`
set to that branch or full commit, and optionally set `focus`. Do not select the
old branch as the workflow ref: that selects its old workflow and old safeguards.
The source and runner revisions are recorded separately. Branches, tags and
abbreviated commits are resolved to a full commit before source checkout; the
resolved commit is the one checked, even if a branch moves during setup. A setup
report is created before either checkout and retained even if checkout or Lean
installation fails. Negative regression tests isolate their annotations and
summaries from the hosting workflow. For example, once the
infrastructure is on main:

```sh
gh workflow run lean.yml --repo wcook04/plectis-erdos-lean --ref main \
  -f source_ref=BRANCH_OR_COMMIT -f focus=Namespace.Module
```

The fast infrastructure tests run before package installation or cache hydration:

```sh
python3 -m unittest discover -s scripts -p 'test_build_launch_targets.py' -v
```

Completed modules are cached after successful or failed builds of the current ref.
Keys include the toolchain, dependencies, ref, source commit and run attempt.
GitHub isolates PR caches to their merge ref; retries can reuse partial progress.
Manual checks of another source never save these caches. Lake still checks source
hashes and compiler traces, and every run must complete all required validation.

Main-targeting PRs run the complete build once through Lean Release Gate, including
its publication audit. The convenience trigger handles other PR bases and manual
checks. A newer release-gate push cancels the obsolete run on that ref.

For a quick manual check before a complete run, add `-f focused_only=true` to
the dispatch. This produces an explicit `focused-pass`, checks the selected
modules and their import closure, and does not establish full launch coverage.
Pull requests and release validation always default to the complete launch set;
a publication audit refuses focused-only mode.
