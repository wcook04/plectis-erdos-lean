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

## Release population and candidate admission

`release-entries.json` declares the legacy Comparator release entries and support
libraries. It was migrated from the reviewed release defaults at commit
`8e01c98d8e76286b876361478138e39c670fd1b0`. It is independent of `defaultTargets`:
changing a developer build focus must never change manifest membership, audit
selection, or the release build. Palomar keeps its own existing enumeration.
Auxiliary Challenge directories are not added by discovery.

The release gate calls the shared runner with `--release`, which includes every
declared entry and support library before the publication audit. `--focused-only`
is rejected in that mode. Use `--focus Namespace.Module --focused-only` for a
source check; the result is `focused-pass`, never release qualification. Preserve
package configuration when preparing a focused checkout; pass the focus to the
runner or workflow dispatch instead.

Before publishing an exact candidate, run the same cheap command as Release tooling:

```sh
python3 scripts/build_release_manifest.py --check-tooling \
  --out /tmp/release-tools/manifest.json --sums-out /tmp/release-tools/SHA256SUMS \
  --diagnostics /tmp/release-tools/diagnostics.json
```

Run this in a clean checkout of the candidate. Compare the selected identities
and support obligations with the reviewed predecessor; inventory changes require
separate review. Missing/empty inventories or a source-only schema never exempt a
release attempt. The command records metadata admission only, retains per-command
logs and failure JSON, and never asserts compiler or Comparator success. CI uploads
that directory even when manifest construction fails. No Lean installation is needed.

The shared workflow consumes the declared release population and uploads failure diagnostics. Legacy driver admission remains supported for older branches and fails if their build defaults omit a required target.
