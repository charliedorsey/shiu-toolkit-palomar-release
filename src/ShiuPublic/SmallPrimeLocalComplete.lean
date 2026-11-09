module

public import ShiuPublic.SmallPrimeFactorBridge

public section

/-! A finite small-prime local Euler factor with all prime powers,
absorbed by the fixed 1/2-geometric envelope. -/
namespace Shiu
open scoped BigOperators

theorem small_prime_complete_local_factor
    (f : ℕ → ℝ) (p N : ℕ)
    (hp : 2 ≤ p) (B δ : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hquarter : δ ≤ 1/4)
    (hone : f 1 = 1)
    (hfgrowth : ∀ m : ℕ, 1 ≤ m →
        f (p ^ m) ≤ B * ((p : ℝ) ^ ((m : ℝ) * (1/4 : ℝ)))) :
    (∑ j ∈ Finset.range (N+1),
      f (p^j) / (p : ℝ) ^ ((j : ℕ) * (1-δ))) ≤
    1 + B / (1 - (p : ℝ)^(-(1/2 : ℝ))) := by
  have hscale : δ + (1/4 : ℝ) < 1 := by linarith
  have htail := small_prime_euler_geometric f p N hp B (1/4 : ℝ) δ
    hB hδ hscale hfgrowth
  have hfixed := small_prime_geometric_uniform p hp B δ hB hδ hquarter
  have hsplit : (∑ j ∈ Finset.range (N+1),
      f (p^j) / (p : ℝ)^((j : ℕ)*(1-δ))) =
    1 + (∑ j ∈ Finset.range N,
      f (p^(j+1))/(p : ℝ)^((j+1 : ℕ)*(1-δ))) := by
    rw [show N+1=1+N by omega, Finset.sum_range_add]
    simp only [Finset.sum_range_one, pow_zero, one_mul, hone, Nat.cast_zero, zero_mul, Real.rpow_zero, div_one]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Nat.add_comm, Nat.cast_add, Nat.cast_one, add_comm]
  have htail2 : (∑ j ∈ Finset.range N,
      f (p^(j+1))/(p : ℝ)^((j+1 : ℕ)*(1-δ))) ≤
      B / (1 - (p : ℝ)^(-(1-δ-1/4))) := by
    convert htail using 1 <;> ring
  rw [hsplit]
  linarith

#print axioms Shiu.small_prime_complete_local_factor
end Shiu
