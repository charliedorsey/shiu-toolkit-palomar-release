module

public import ShiuPublic.VaelisEulerUniformCutoff

public section

namespace Shiu
open scoped BigOperators

/-- Uniform finite-prime-power Euler majorant for every bounded non-squarefree
smooth family; a single common exponent cutoff, with no loss of multiplicity. -/
theorem bounded_smooth_mass_le_uniform_finite_euler
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : ClassicalEnvelope f A) (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (X : ℕ) (hX : 0 < X) (s : ℝ) :
    (∑ n ∈ boundedSmoothSet S X, f n / (n : ℝ) ^ s) ≤
      ∏ p ∈ S, ∑ j ∈ Finset.range (((∏ p ∈ S, p) ^ X) + 2),
          f (p ^ j) / (p : ℝ) ^ ((j : ℝ) * s) := by
  let T : ℕ := (∏ p ∈ S, p) ^ X
  have hmass := bounded_smooth_mass_le_finite_euler hf S hprime X s
  rw [bounded_smooth_base_primeFactors S hprime X hX] at hmass
  calc
    _ ≤ ∏ p ∈ S, ∑ j ∈ Finset.range (T.factorization p + 1),
        f (p ^ j) / ((p ^ j : ℕ) : ℝ) ^ s := by simpa [T] using hmass
    _ ≤ ∏ p ∈ S, ∑ j ∈ Finset.range (T + 2),
        f (p ^ j) / ((p ^ j : ℕ) : ℝ) ^ s := by
      apply Finset.prod_le_prod₀
      · intro p hp
        apply Finset.sum_nonneg
        intro j hj
        exact div_nonneg (hf.nonnegative _) (Real.rpow_nonneg (by positivity) _)
      · intro p hp
        have hle := bounded_smooth_base_factorization_le S hprime X p hX hp
        have hsub : Finset.range (T.factorization p + 1) ⊆ Finset.range (T+2) :=
          Finset.range_mono (by change T.factorization p ≤ T at hle; omega)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun j hj _ => div_nonneg (hf.nonnegative _) (Real.rpow_nonneg (by positivity) _))
    _ = ∏ p ∈ S, ∑ j ∈ Finset.range (T + 2),
        f (p ^ j) / (p : ℝ) ^ ((j : ℝ) * s) := by
      apply Finset.prod_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]

#print axioms Shiu.bounded_smooth_mass_le_uniform_finite_euler
end Shiu
