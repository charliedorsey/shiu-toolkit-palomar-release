module

public import Mathlib

public section

/-! A reusable finite relative Euler comparison for a set of large primes.
No squarefree support, and no limit passage is asserted. -/
namespace Shiu
open scoped BigOperators

/-- A fully source-neutral, finite relative-product bound from pointwise
local factor upper bounds, preserving the exact first-prime mass. -/
theorem relative_euler_product_of_local
    (S : Finset ℕ) (L u v : ℕ → ℝ)
    (hL : ∀ p ∈ S, 0 ≤ L p)
    (hu : ∀ p, 0 ≤ u p)
    (hv : ∀ p, 0 ≤ v p)
    (hpoint : ∀ p ∈ S, L p ≤ 1 + u p + v p) :
    (∏ p ∈ S, L p) ≤
      Real.exp (∑ p ∈ S, (u p + v p)) := by
  calc
    (∏ p ∈ S, L p) ≤
      ∏ p ∈ S, (1 + (u p + v p)) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          exact hL p hp
        · intro p hp
          simpa [add_assoc] using hpoint p hp
    _ ≤ Real.exp (∑ p ∈ S, (u p + v p)) := by
      simpa using (Real.prod_one_add_le_exp_sum S
        (fun p => add_nonneg (hu p) (hv p)))

#print axioms Shiu.relative_euler_product_of_local
end Shiu
