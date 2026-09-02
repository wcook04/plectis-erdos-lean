---
name: lean-checkpoint-entry
description: >-
  Author or review a Lean checkpoint entry: a statement-isolated Challenge, a Solution
  that proves it unchanged, and an axiom audit that prints what the proof depends on.
  Use when accepting a mathematical argument from a source you cannot supervise, when
  adding a verified theorem family to this repository, or when reviewing one someone
  else added. Trigger words: checkpoint entry, Comparator entry, Challenge and Solution,
  axiom audit, accept a returned proof, verify a delegated argument, add a Lean entry.
---

# Lean checkpoint entry

A checkpoint entry is an acceptance certificate for a mathematical claim. It answers
one question and refuses the others: **does this proof establish this exact statement,
and on which axioms.**

It does not ask who wrote the proof. That is the point. A model with no tools, a
research group's system, and a person all pass or fail on the same terms, which is
what makes it possible to accept an argument you could not watch being produced.
`METHOD.md` explains where such arguments come from in this programme.

## The five files

```
<Entry>/Challenge.lean        the statement, fixed, unproved
Solutions/<Entry>.lean        the proof of that statement
<Entry>/AxiomAudit.lean       what the proof depends on
<Entry>/comparator.json       binds the three
<Entry>/formalization.yaml    scope, sources, attribution, known divergences
```

The Solution sits under its own module prefix because the registry compiles each
Challenge into a protected directory that shadows every module sharing its prefix.

## Authoring order, and why it is this order

**1. Write the Challenge first, before the proof exists.**

This is the whole discipline. A statement written after a proof drifts toward what
the proof happens to establish. Write what you want to be true, in full generality,
with every hypothesis explicit, and leave it unproved:

```lean
theorem my_entry_statement
    (f : Polynomial ℂ) (hf : f.Monic) (hdeg : 3 ≤ f.natDegree) :
    ∃ z w, z ≠ w ∧ MyProperty f z w := by
  sorry
```

That `sorry` is deliberate and is the only permitted one in an entry. It marks the
Challenge as a specification.

**2. State the boundary before you look for a proof.**

In `formalization.yaml`, record what the statement does and does not cover, which
hypotheses are load-bearing, what the informal claim was, and where the formal
statement is narrower. Doing this before the proof stops the boundary from being
written to match whatever was achievable.

**3. Prove the Challenge statement, unchanged.**

`Solutions/<Entry>.lean` proves the declaration the Challenge names. Not a variant,
not a specialisation, not a restatement with an added hypothesis. If the proof needs
a hypothesis the Challenge does not carry, the Challenge was wrong and is rewritten
before the proof is accepted, in the open, rather than adjusted quietly to fit.

There is no `sorry` here and no `axiom`. A `sorry` in a Solution is fatal.

**4. Audit the axioms.**

```lean
#print axioms myEntryDeclaration
```

`AxiomAudit.lean` prints the dependency set for every selected declaration. Read the
output. `sorryAx` means a proof somewhere in the chain is incomplete even though the
file compiled, and it is the failure this step exists to catch. Anything outside the
expected budget is a finding, not a formality.

**5. Bind it.**

`comparator.json` names the Challenge, the Solution and the audited declarations.
This is the configuration a registry submission points at.

## Reviewing an entry

Read in this order, and stop at the first failure.

1. **Read the Challenge, not the prose.** The certificate is exactly as strong as
   the statement. A Challenge that states less than the README claims still passes
   the machine check, so this is where a review earns its keep.
2. **Check the Solution proves that declaration.** Same name, same statement, same
   hypotheses.
3. **Read the axiom output.** Look for `sorryAx` first, then anything unexpected.
4. **Check `formalization.yaml` against what you just read.** Divergences that are
   recorded are a boundary. Divergences that are not recorded are a defect.
5. **Ask what it does not establish.** A checked theorem is not a reviewed theorem,
   not a new theorem, and not an important one. Novelty is a literature question and
   the machine has no opinion on it.

## Accepting an argument from an unsupervised source

When the input is a returned argument rather than your own work, three things change,
and none of them is the acceptance test.

**Treat the return as a floor.** It establishes that a route reaches a certain depth.
The entry should carry the strongest statement you can prove, which is often stronger
than the return: looser constants tightened, unnecessary hypotheses removed, an
endpoint pushed to where the return's own identities already reached.

**Verify every cited object exists.** A returned argument may name a lemma, an API, a
constant or a paper that does not exist, and this is common enough to check by
default rather than on suspicion.

**Do not let the return write the Challenge.** The statement is yours. A Challenge
copied from a return inherits whatever the return was willing to prove, which is the
drift this whole discipline exists to prevent.

## Anti-patterns

- **Statement drift.** Writing or weakening the Challenge after seeing what the proof
  achieved. The entry still compiles and certifies less than a reader will assume.
- **Trusting a green build.** A file that compiles can still depend on `sorryAx`
  further up the chain. Compilation is not the check; the audit is.
- **Reviewing the prose.** Summaries are written by whoever wanted the result. The
  Challenge is the only thing the machine agreed to.
- **Provenance as evidence.** That an argument came from a strong model, or a
  respected source, changes nothing about whether it passes. Provenance-blindness is
  the property that makes the format worth having.
- **Novelty by absence.** Not finding prior art is not evidence of novelty. Record it
  as unassessed.

## Build

```sh
lake exe cache get
lake build
```

`scripts/check_axiom_budget.py` shows the audit shape used across this repository.
