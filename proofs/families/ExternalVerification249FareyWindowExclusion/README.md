# Erdős #249: Farey-window denominator exclusion

Machine-checked: `∑_{n≥0} φ(n)/2^n` is not `a/d` for any integer `a` and any
denominator `1 ≤ d ≤ 79639646646701375323355774875831053`, and therefore no
rational `p` with `p.den` in that range equals the series. The compared
theorems are
`tsum_totient_div_pow_two_ne_int_div_of_den_le_79639646646701375323355774875831053`
and
`tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053`.
This is a finite exclusion, not irrationality. Erdős #249 remains open.

The Challenge imports only Mathlib and restates the two Mathlib totient-tsum
statements. The Solution imports `Erdos257PeriodNoncollapse.CertificateKernel`
and cites those source theorems. NanoDa is enabled; permitted axioms are
`propext`, `Quot.sound`, and `Classical.choice`.

`lakefile.toml` registration remains for the integrating agent. No submission
has occurred; novelty is unassessed.
