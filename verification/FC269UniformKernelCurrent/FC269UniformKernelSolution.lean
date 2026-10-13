import ErdosProblems.Erdos269.KernelCarryRank

namespace ThreePrimeRunningLcm

open scoped BigOperators

/-- The smooth lattice value attached to the exponent triple $(i,j,k)$. -/
noncomputable def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k

/-- The product of the largest pure prime powers not exceeding $x$.
For pairwise distinct primes and $x \ge 1$, this is the LCM of the positive
$\{p,q,r\}$-smooth integers at most $x$. -/
noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x

/-- The rational reciprocal running-LCM kernel on the smooth lattice. -/
noncomputable def threePrimeKernelQ (p q r i j k : ℕ) : ℚ :=
  (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹

/-- For three pairwise distinct primes, the reciprocal running-LCM kernel has
nonsingular minors of every order, with the same row and column indices in
every third-coordinate layer. Consequently it has no finite representation
$K(i,j,k)=\sum_{\ell<d}f_\ell(i)G_\ell(j,k)$ over $\mathbb Q$.
This structural statement does not decide the rationality of the scalar
running-LCM series in Erdős Problem 269.

*Source:* Cook, Theorem `res:infinite-rank` in the paper cited above.
-/
theorem uniform_rank_and_nonseparation {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (_hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (∀ n : ℕ, ∃ I J : Fin n → ℕ,
      Function.Injective I ∧ Function.Injective J ∧
      ∀ k : ℕ, (Matrix.det fun a b : Fin n =>
        threePrimeKernelQ p q r (I a) (J b) k) ≠ 0) ∧
    (∀ d : ℕ, ¬ ∃ (f : Fin d → ℕ → ℚ) (G : Fin d → ℕ → ℕ → ℚ),
      ∀ i j k, threePrimeKernelQ p q r i j k = ∑ l : Fin d, f l i * G l j k) := by
  exact ⟨ErdosProblems.Erdos269.exists_uniform_nonsingular_threePrimeKernel_minor_of_prime hp hq hr hpr hqr,
    ErdosProblems.Erdos269.not_finite_separable_threePrimeKernel hp hq hr hpr hqr⟩

end ThreePrimeRunningLcm

#print axioms ThreePrimeRunningLcm.uniform_rank_and_nonseparation
