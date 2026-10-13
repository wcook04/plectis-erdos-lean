# The exact initial term of Zudilin's normalized Hankel determinant

For each rank N, the integer formal power series H_N has exact order
E_N=N(N−1)(2N−1)/6 and satisfies 2^N [q^E_N] H_N=(N!)²(N+1)!.
The wrapper defines the actual normalized moments coefficientwise at x=z=1.
Rank zero uses the empty determinant. No additional row hypothesis is imposed.

This fixed-rank formal-power-series result is distinct from the fixed-real-base,
rank-to-infinity asymptotic submitted in FC PR6780. Zudilin's classical q-order
lower bound is the precursor. The rational-base irrationality problem remains open.

The ten-file import closure is byte-identical to the original checking source
and public reader corpus; source-binding.json records exact commits and hashes.
The library glob contains precisely those ten files, so the actual Lake library
closure adds no unrelated modules. The wrapper is the eleventh local module.

Run `lake build FC1049OrderCoeffSolution` in this directory. Source compilation
and protected actual-FC receiving comparison are separate obligations. No compiler,
receiving certification, independent review or acceptance is claimed by this draft.
