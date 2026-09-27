# Reproduce a Lean Convenience build

Run the same command as CI from the repository root with Python 3.11 or later:

```sh
python3 scripts/build_launch_targets.py --changed-from origin/main
```

Use the actual parent ref for a stacked pull request. The runner checks changed
Lean modules in dependency order before the full `defaultTargets` list. A focused
failure stops that run immediately; unattempted targets stay visible in the report.
Use `--keep-going` only when collecting independent launch-target failures is worth
the extra build time. The publication release and Comparator checks are separate.

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

Defaults are one hour per compiler module, 90 minutes per launch target and five
hours for the complete run. `--module-budget`, `--target-budget` and
`--total-budget` accept finite positive seconds. The runner prints a heartbeat
every minute and only inspects compiler processes descended from its own Lake
process. A timeout stops that process group and preserves completed build files.

For an older source branch, dispatch the **current workflow** with `source_ref`
set to that branch or full commit, and optionally set `focus`. Do not select the
old branch as the workflow ref: that selects its old workflow and old safeguards.
The source and runner revisions are recorded separately. For example, once the
infrastructure is on main:

```sh
gh workflow run lean.yml --repo wcook04/plectis-erdos-lean --ref main \
  -f source_ref=BRANCH_OR_COMMIT -f focus=Namespace.Module
```

The fast infrastructure tests run before package installation or cache hydration:

```sh
python3 -m unittest discover -s scripts -p 'test_build_launch_targets.py' -v
```

Only builds of main itself save shared corpus caches. PRs and manual runs against
another source may restore caches, but compiler traces still decide what rebuilds;
a cached file or a focused pass is never a substitute for complete validation.
