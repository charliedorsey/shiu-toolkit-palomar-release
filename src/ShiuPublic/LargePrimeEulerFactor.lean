module

public import ShiuPublic.ShiftedPrimePowerTail

public section

/-!
Finite local Euler factor control without squarefree support.
The first two terms are kept exact and all exponents >= 2 are
charged to the already verified shifted geometric tail.
-/
namespace Shiu
open scoped BigOperators

/-- Exact finite shift of the Euler factor: the first two terms
are f(1)=1 and f(p)/R, retaining all higher prime powers. -/
theorem local_euler_split_two
    (f : ℕ → ℝ) (p N : ℕ) (R : ℝ) (hone : f 1 = 1) :
    (∑ j ∈ Finset.range (N+2), f (p ^ j) / R ^ j) =
    1 + f p / R +
      ∑ j ∈ Finset.range N, f (p ^ (j+2)) / R ^ (j+2) := by
  rw [show N+2 = 2+N by omega, Finset.sum_range_add]
  simp [Finset.sum_range_succ, hone, add_comm, add_left_comm, add_assoc]

/-- Complete finite local Euler bound from the prime-power envelope. -/
theorem large_prime_euler_factor_at_real_scale
    (f : ℕ → ℝ) (A R : ℝ) (p N : ℕ)
    (hA : 0 ≤ A) (hR : 0 < R) (hone : f 1 = 1)
    (hhalf : 2*A ≤ R)
    (hpower : ∀ m : ℕ, 2 ≤ m → f (p ^ m) ≤ A ^ m) :
    (∑ j ∈ Finset.range (N+2), f (p ^ j) / R ^ j) ≤
      1 + f p / R + 2 * (A / R) ^ 2 := by
  rw [local_euler_split_two f p N R hone]
  have htail := power_tail_at_real_scale f A R p N hA hR hhalf hpower
  linarith

/-- This is the exact local-factor bound required by the Rankin
relative Euler-product comparison, at denominator p^(1-delta). -/
theorem large_prime_euler_factor_at_rankin_scale
    (f : ℕ → ℝ) (A δ : ℝ) (p N : ℕ)
    (hA : 0 ≤ A) (hp : 0 < p) (hone : f 1 = 1)
    (hhalf : 2*A ≤ (p : ℝ) ^ (1-δ))
    (hpower : ∀ m : ℕ, 2 ≤ m → f (p ^ m) ≤ A ^ m) :
    (∑ j ∈ Finset.range (N+2),
        f (p ^ j) / (p : ℝ) ^ ((j : ℝ) * (1-δ))) ≤
      1 + f p / (p : ℝ) ^ (1-δ) +
        2 * (A / (p : ℝ) ^ (1-δ)) ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have heq (j : ℕ) :
      ((p : ℝ) ^ (1-δ)) ^ j =
      (p : ℝ) ^ ((j : ℝ) * (1-δ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpR.le]
    congr 1
    push_cast
    ring
  simp_rw [← heq]
  exact large_prime_euler_factor_at_real_scale f A
    ((p : ℝ) ^ (1-δ)) p N hA (Real.rpow_pos_of_pos hpR _)
    hone hhalf hpower

#print axioms Shiu.local_euler_split_two
#print axioms Shiu.large_prime_euler_factor_at_real_scale
#print axioms Shiu.large_prime_euler_factor_at_rankin_scale
end Shiu
