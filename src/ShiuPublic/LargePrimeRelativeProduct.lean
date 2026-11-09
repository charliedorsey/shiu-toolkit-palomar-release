module

public import ShiuPublic.LargePrimeEulerFactor
public import ShiuPublic.RelativeEulerFinite
public import ShiuPublic.PrimePowerEnvelope

public section

/-! Real large-prime finite Euler product comparison for the classical
weight class, with exact shifted ordinary-prime contribution and explicit
quadratic higher-power error. No use of squarefree support. -/

namespace Shiu
open scoped BigOperators

/-- Full finite large-prime Euler comparison at any real Rankin shift.
The finite set S contains primes where 2A <= p^(1-delta). -/
theorem classical_large_prime_relative_product
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : ClassicalEnvelope f A)
    (S : Finset ℕ) (N : ℕ) (δ : ℝ)
    (hS : ∀ p ∈ S, p.Prime)
    (hgate : ∀ p ∈ S, 2 * A ≤ (p : ℝ) ^ (1-δ)) :
    (∏ p ∈ S, ∑ j ∈ Finset.range (N+2),
        f (p ^ j) / (p : ℝ) ^ ((j : ℝ) * (1-δ))) ≤
      Real.exp (∑ p ∈ S,
        (f p / (p : ℝ) ^ (1-δ) +
         2 * (A / (p : ℝ) ^ (1-δ)) ^ 2)) := by
  apply relative_euler_product_of_local S
    (fun p => ∑ j ∈ Finset.range (N+2),
      f (p ^ j) / (p : ℝ) ^ ((j : ℝ) * (1-δ)))
    (fun p => f p / (p : ℝ) ^ (1-δ))
    (fun p => 2 * (A / (p : ℝ) ^ (1-δ)) ^ 2)
  · intro p hp
    apply Finset.sum_nonneg
    intro j hj
    exact div_nonneg (hf.nonnegative _) (Real.rpow_nonneg (by positivity) _)
  · intro p
    exact div_nonneg (hf.nonnegative _) (Real.rpow_nonneg (by positivity) _)
  · intro p
    positivity
  · intro p hp
    exact large_prime_euler_factor_at_rankin_scale
      (fun n => f n) A δ p N hf.A_nonnegative
      (hS p hp).pos hf.multiplicative.map_one
      (hgate p hp)
      (fun m hm => hf.prime_power p m (hS p hp) (by omega))

#print axioms Shiu.classical_large_prime_relative_product
end Shiu
