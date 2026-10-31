# A cubic polygonal connector

A monic cubic is given by its three roots, counted with multiplicity, all strictly inside the unit disc. Two distinct indices admit an explicit two-segment path through a hub. Every point of this path lies in the open unit lemniscate, and its actual extended variation on [0,2] is less than two. The path is continuous and of bounded variation. Squarefreeness guarantees distinct endpoint values; repeated-root indices may yield a constant path.

The Challenge imports only Mathlib. It writes the factorization hypothesis and curve conclusions explicitly and defines the hub by its two affine pieces. No root-count supplier, critical-value bound or path theorem is a hypothesis. The Solution unfolds the source curve definitions and transports `PaperCubicCompletion.cubic_paper_complete`.

This is a degree-three result with strict root containment. It claims neither the closed-disc boundary nor the general-degree problem. Novelty is unassessed. The focused wrapper build and axiom audit passed on 8 September 2026. The selected theorem uses only `propext`, `Classical.choice`, and `Quot.sound`. Supported-runner Comparator replay remains pending; no Palomar submission has been made.

The additional `monic_cubic_connector` selection states monicity, degree three,
and the literal condition that every root has norm less than one. It supplies
root endpoints and the same explicit hub and curve bounds, with distinct
endpoints when the polynomial is squarefree. Its Solution transports
`PaperCubicMonic.monic_cubic_connector`; no factorization witness is assumed.
The new wrapper selection awaits elaboration and axiom audit. The earlier
build and audit above apply only to `cubic_paper_complete`.

`comparator.json` selects both statements. Run
`comparator-monic-negative-mismatch.json` separately: it selects only
`monic_cubic_connector`, supplied deliberately with type `True`. Acceptance
requires a theorem-type mismatch for this name, not a build error or timeout.
The existing cubic selection remains in the positive configuration. Both
positive replay and the dedicated monic negative replay remain pending.
