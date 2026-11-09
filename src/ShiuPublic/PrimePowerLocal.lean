module

public import Mathlib

public section

/-!
A source-independent quantitative local Euler-factor tail for a
nonnegative arithmetic function with controlled prime powers.
This is an elementary *local* ingredient, not a short-interval AP theorem.
-/

namespace Shiu
open Finset

/-- Uniform bound on a finite geometric progression when 0 <= t <= 1/2. -/
theorem geometric_sum_le_two (t : ℝ) (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / 2) (n : ℕ) :
    (∑ j ∈ Finset.range n, t ^ j) ≤ 2 := by
  let S : ℝ := ∑ j ∈ Finset.range n, t ^ j
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hgeom : S * (1 - t) = 1 - t ^ n := by
    exact geom_sum_mul_neg t n
  have hp : 0 ≤ t ^ n := pow_nonneg ht0 n
  have hhalf : (1 / 2 : ℝ) ≤ 1 - t := by linarith
  nlinarith

/-- The complete prime-power range of exponents >=2 costs at most
two times the first square contribution. -/
theorem geometric_tail_le_two_square (t : ℝ) (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / 2) (n : ℕ) :
    (∑ j ∈ Finset.range n, t ^ (j + 2)) ≤ 2 * t ^ 2 := by
  have hsum := geometric_sum_le_two t ht0 ht n
  have heq : (∑ j ∈ Finset.range n, t ^ (j + 2)) =
      t ^ 2 * (∑ j ∈ Finset.range n, t ^ j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← pow_add]
    ring
  rw [heq]
  nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hsum)]

/-- Uniform prime-power Euler tail from f(p^m) <= A^m. The cutoff
assumption p >= 2A is only for this simplified, explicit constant. -/
theorem controlled_prime_power_tail
    (f : ℕ → ℝ) (A : ℝ) (p n : ℕ)
    (hA : 0 ≤ A) (hp : 0 < p)
    (hpA : 2 * A ≤ (p : ℝ))
    (hpower : ∀ m : ℕ, 2 ≤ m → f (p ^ m) ≤ A ^ m) :
    (∑ j ∈ Finset.range n,
      f (p ^ (j + 2)) / (p : ℝ) ^ (j + 2)) ≤
      2 * (A / (p : ℝ)) ^ 2 := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hrat0 : 0 ≤ A / (p : ℝ) := div_nonneg hA hpR.le
  have hrat : A / (p : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hpR).mpr
    nlinarith
  calc
    (∑ j ∈ Finset.range n,
      f (p ^ (j + 2)) / (p : ℝ) ^ (j + 2)) ≤
      ∑ j ∈ Finset.range n, (A / (p : ℝ)) ^ (j + 2) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [div_pow]
        exact div_le_div_of_nonneg_right
          (hpower (j + 2) (by omega)) (pow_nonneg hpR.le _)
    _ ≤ 2 * (A / (p : ℝ)) ^ 2 :=
      geometric_tail_le_two_square _ hrat0 hrat n

#print axioms Shiu.geometric_sum_le_two
#print axioms Shiu.geometric_tail_le_two_square
#print axioms Shiu.controlled_prime_power_tail
end Shiu
