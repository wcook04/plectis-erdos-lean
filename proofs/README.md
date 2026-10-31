# Statements and proofs

This folder contains Lean statements and the proofs supplied for checking them.
Lean is a language in which a computer checks mathematical proofs. See the
[main README](../README.md) for a first result and the commands to check it.

- [`families/`](families/) groups individual statements and their checking
  configuration. The folders retain names beginning `ExternalVerification`.
- [`PalomarCorpus/`](PalomarCorpus/README.md) groups statements in the order
  their theorems appear in the papers.
- [`Solutions/`](Solutions/) contains the proofs and the code connecting them
  to those statements. Keeping the proof separate lets the checker compare it
  with the intended statement.

## Build a proof

Run build commands from the repository root. For example:

```sh
lake build ExternalVerification257ReciprocalSupport.AxiomAudit
```

Lake is Lean's build tool. The name after `lake build` is a Lean module name,
not a filesystem path. The `srcDir` settings in the root Lake configuration
point it at the folders here, so module names do not acquire a `proofs` prefix.
Imports such as `Solutions.PalomarCorpus.E257_01` also keep their original names.

Links to an older commit still refer to the files at that commit. A successful
proof check for an old version does not establish a check of the current source.
