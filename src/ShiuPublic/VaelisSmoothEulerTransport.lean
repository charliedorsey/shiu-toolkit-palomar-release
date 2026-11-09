module

public import ShiuPublic.VaelisSmoothDivisor
public import ShiuPublic.FiniteEulerDivisors
public import ShiuPublic.PrimePowerEnvelope

public section

namespace Shiu
open scoped BigOperators

/-- Bounded original non-squarefree smooth mass is controlled by the EXACT finite
prime-power Euler factors of the containing divisor product. -/
theorem bounded_smooth_mass_le_finite_euler
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : ClassicalEnvelope f A) (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (X : ℕ) (s : ℝ) :
    (∑ n ∈ boundedSmoothSet S X, f n / (n : ℝ) ^ s) ≤
      ∏ p ∈ ((∏ p ∈ S, p) ^ X).primeFactors,
        ∑ j ∈ Finset.range (((∏ p ∈ S, p) ^ X).factorization p + 1),
          f (p ^ j) / ((p ^ j : ℕ) : ℝ) ^ s := by
  have hnzero : (∏ p ∈ S, p) ^ X ≠ 0 := by
    have hprod : 0 < ∏ p ∈ S, p := by
      apply Finset.prod_pos
      intro p hp
      exact (hprime p hp).pos
    positivity
  have hmass := bounded_smooth_mass_le_divisor_mass S X
    (fun n => f n / (n : ℝ) ^ s)
    (fun n => div_nonneg (hf.nonnegative n) (Real.rpow_nonneg (by positivity) _))
    hprime
  rw [← finite_euler_divisor_rankin f hf.multiplicative _ hnzero s] at hmass
  exact hmass

#print axioms Shiu.bounded_smooth_mass_le_finite_euler
end Shiu
