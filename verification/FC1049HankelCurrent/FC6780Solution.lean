import Solutions.PalomarCorpus.E1049_08.PaperStatementsU

namespace GeometricMomentHankel

open Filter Finset
open scoped Topology BigOperators

noncomputable def leadC (N : ℕ) : ℝ := ((N.factorial : ℝ) ^ 2 * ((N + 1).factorial : ℝ)) / 2 ^ N
/-- The finite $q$-product $(a;q)_n$. -/
noncomputable def qPochhammerFinite (a q : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)
/-- The infinite $q$-product, expressed through its logarithmic series. -/
noncomputable def qPochhammerInfinity (a q : ℝ) : ℝ :=
  Real.exp (∑' k : ℕ, Real.log (1 - a * q ^ k))
/-- The summand of Zudilin's normalized moment at $x=z=1$. -/
noncomputable def actualMomentTerm (q : ℝ) (m t : ℕ) : ℝ :=
  q ^ ((m + 1) * t) * (qPochhammerFinite q q m) ^ 3 *
    qPochhammerFinite (q ^ (t + 1)) q m /
      qPochhammerFinite (q ^ (m + t + 1)) q (m + 1)
/-- Zudilin's normalized moment $v_m^*(q)$. -/
noncomputable def actualMoment (q : ℝ) (m : ℕ) : ℝ :=
  ∑' t : ℕ, actualMomentTerm q m t
/-- The Hankel matrix $(v_{i+j}^*(q))_{0\le i,j<N}$. -/
noncomputable def actualMomentHankel (q : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => actualMoment q (i.val + j.val)
/-- The term $z^n/(1-z^n)$ of the Lambert series. -/
noncomputable def lambertTerm {K : Type*} [NormedField K] (z : K) (n : ℕ) : K :=
  z ^ n / (1 - z ^ n)
/-- The Lambert series $\sum_{n\ge0}z^n/(1-z^n)$; the zeroth term is zero. -/
noncomputable def lambert {K : Type*} [NormedField K] (z : K) : K :=
  ∑' n : ℕ, lambertTerm z n


theorem fixed_base_asymptotic {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ K : ℝ, 0 < K ∧
      Tendsto (fun N : ℕ => (actualMomentHankel q N).det /
        (K * leadC N * q ^ (N * (N - 1) * (2 * N - 1) / 6) *
          qPochhammerInfinity q q ^ (2 * N) *
          (N : ℝ) ^ (-8 * lambert q))) atTop (𝓝 1) := by
  exact PalomarCorpus.E1049.PaperStatementsU.sharp_fixed_base_exists hq0 hq1

end GeometricMomentHankel

#print axioms GeometricMomentHankel.fixed_base_asymptotic
