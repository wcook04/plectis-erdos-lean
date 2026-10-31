<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Contribute

This repository holds Lean entries, adapters and release tools. The
[research repository](https://github.com/wcook04/plectis-erdos) holds the
mathematical research, papers and public claim registry.

Changes reach `main` through pull requests. Files under `PalomarCorpus/` come from
a generator outside this repository, so report a problem in one of them as an
issue.

## Report a packaging or replay problem

[Open an issue](https://github.com/wcook04/plectis-erdos-lean/issues/new)
with the source commit, exact entry or configuration, command, toolchain and
the relevant error output. Include whether you used current main or a pinned
historical edition. A result for one edition does not transfer to another.

For a patch, explain the failing action and the resulting behaviour. Preserve
unrelated entries and recorded source pins. A change to a Challenge changes the
statement being checked; it is not a repair to the proof of the old statement.

Follow the [build guide](scripts/CONVENIENCE_BUILDS.md) for the affected tools.
For a build-runner change, the fast regression suite is:

```sh
python3 -m unittest discover -s scripts -p 'test_build_launch_targets.py' -v
```

Include the checks you actually ran and their limits. A build plan, source
compilation, axiom audit and protected Comparator replay establish different
things. Do not describe one as another.

## Return mathematical work

Bring a proof, correction, reference or clearer explanation to the primary
repository's [contribution guide](https://github.com/wcook04/plectis-erdos/blob/main/CONTRIBUTING.md).
You can contribute without a clone or Lean installation. Preserve the exact
statement, source commit, argument, evidence, limitations and requested credit.
The primary repository records accepted work and its provenance under its
[credit policy](https://github.com/wcook04/plectis-erdos/blob/main/docs/research-commons/CREDIT_POLICY.md).
