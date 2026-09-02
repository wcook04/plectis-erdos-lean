# Method: delegating mathematics to a model that has no tools

This repository is the checked surface of a research programme. This document
describes how the work reaches the models that do a large part of it, and what
makes the result safe to accept. The mathematics is in the entries. The method is
here because the method is reusable and the mathematics is specific.

## The problem the method solves

Two capabilities of a language model are commonly treated as one, and they are
separable.

**Reasoning depth** is whether a model can invent the mathematics: find the route,
construct the argument, see that a lemma is available.

**Harness fitness** is whether a model can drive tools: read a repository, run a
checker, iterate against a compiler, hold a long session.

A model can be strong on one and absent on the other. At any given moment the
strongest available reasoner is often the one reachable only through a chat
interface, with no tool access, no view of a repository, and one response per
question. The usual response is to wait until that model is integrated into a
coding harness. Waiting costs the months in which it is strongest.

The method here gets checked mathematical work out of such a model. Three phases,
and the boundary is crossed once.

## COMPILE

The model cannot fetch, so the corpus travels to it. Each delegation is a flat
directory of about twenty files: byte-identical copies of committed sources,
grouped into dossiers with a stated reading order, plus one instruction file and a
manifest. Everything the argument might need is inside, and anything that does not
fit is reachable at a commit-pinned URL whose digest was verified before the
directory was frozen.

The bundle carries four things that matter more than volume.

The **exact parent statement**, with its digest, so the model cannot drift onto an
easier target.

The **activation frontier**: the strongest results already established, each with
its exact hypotheses and the paths that back it. These are premises to spend, not
results to reproduce.

A **dominance map** over every claim-bearing row for the problem. Rediscovering a
result the corpus already holds is a failed delegation, so the map exists to make
that detectable rather than flattering.

A **no-go bank**: the routes already refuted, with the counterexample that killed
each one. A model with one response should not spend it on a route that is known
to be dead.

## DELEGATE

The instruction file is a mandate rather than a question. It is written against the
specific failure modes of a model that has no tools and one turn: summarising the
bundle, stopping at a reduction, offering to continue later, presenting a
rediscovery as new. The contract states that the only complete deliverable is a
proof of the parent theorem, that every reduction promotes its residual inside the
same response, and that there is no later turn to defer to.

The model returns prose. Prose is a hypothesis.

## VERIFY

Nothing in the delegation touches this repository. Lean, the computations, the
integration and the claim status stay on the side that can check them. A returned
argument becomes a claim only by passing the entry format that every directory here
uses.

- `<Entry>/Challenge.lean` fixes the statement, and does not prove it.
- `Solutions/<Entry>.lean` proves that statement, unchanged.
- `<Entry>/AxiomAudit.lean` prints the axioms each selected declaration depends on,
  so `sorryAx` cannot hide inside a proof that appears to compile.
- `<Entry>/comparator.json` binds the three together.

The load-bearing property is that this test **never asks who produced the work**.
It asks what was proved and on which axioms. A frontier reasoner with no tools,
another group's system, and a person with a pencil are accepted on identical terms,
and are refused on identical terms. That is what makes it possible to accept work
from a source you cannot supervise, and it is the reason the format is worth
publishing separately from the results it certified.

## What a returned argument is worth

A return sets a floor. It establishes that a route reaches at least a certain
depth. The repository version is expected to be stronger, and in this programme it
repeatedly has been: several results here began as a returned argument whose
constants were loose, whose hypotheses were heavier than necessary, or whose
endpoint stopped short of what its own identities supported.

Several delegations against one problem are worth more than the sum of their
returns, because each runs blind to the others. One may prove exactly the lemma
another needed. Two may stop at the same wall from different starting points, which
says something about the frontier that either alone does not. Finding those is
work, and it is where most of the value in this method is realised.

None of that changes the acceptance test. A composed argument is checked the same
way a single one is.

## Reusing this

The two artifacts worth copying are the bundle format and the entry format, and
neither depends on the mathematics here.

To adopt the entry format, take any directory in this repository as a template. The
requirements are that the statement is fixed before the work, that the proof is
compiled against the fixed statement rather than a restatement, and that the axiom
dependency set is printed rather than assumed. `scripts/check_axiom_budget.py`
shows the audit shape used here.

To adopt the bundle format, the requirements are that every source is byte-identical
to a named commit, that the strongest existing results are stated as premises, that
known-dead routes are listed, and that the instruction is a mandate with a single
acceptable terminal deliverable.

Neither requires this repository, this problem set, this proof assistant, or any
particular model.

## Limits

The certificate is exactly as strong as the Challenge statement. A Challenge that
states less than the surrounding prose claims will still pass, so reading the
Challenge is the review, and the prose is not.

An axiom audit reports dependencies. It does not report whether the theorem is
interesting, whether it is new, or whether the formal statement captures the
informal one. Those remain human judgements, and this repository records novelty as
unassessed wherever the literature does not settle it.

The method produces checked theorems. It does not produce reviewed ones. No human
mathematical peer review is claimed for any entry in this release, and every parent
problem addressed here is open.
