module

public import Mathlib

public section

/-!
Uniform finite quadratic correction for the large-prime Euler factors.
No hidden prime number theorem or infinite-product convergence.
-/
namespace Shiu
open Finset
open scoped BigOperators

/-- The complete inverse-square mass of any primes at most P is <= 1.
Actually S can be *any* subset of integers in (1,P]. -/
theorem finite_inverse_square_mass_le_one
    (S : Finset ℕ) (P : ℕ) (hP : 1 ≤ P)
    (hS : ∀ q ∈ S, 2 ≤ q ∧ q ≤ P) :
    (∑ q ∈ S, ((q : ℝ) ^ 2)⁻¹) ≤ 1 := by
  have hsubset : S ⊆ Finset.Ioc 1 P := by
    intro q hq
    rcases hS q hq with ⟨hq2, hqP⟩
    exact Finset.mem_Ioc.mpr ⟨by omega, hqP⟩
  calc
    (∑ q ∈ S, ((q : ℝ) ^ 2)⁻¹) ≤
        ∑ q ∈ Finset.Ioc 1 P, ((q : ℝ) ^ 2)⁻¹ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro q hq hnot
          positivity
    _ ≤ (1 : ℝ)⁻¹ - (P : ℝ)⁻¹ :=
      by simpa only [Nat.cast_one] using
        (sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := P)
          (by norm_num) hP)
    _ ≤ 1 := by
      have hnonneg : 0 ≤ (P : ℝ)⁻¹ := by positivity
      norm_num

/-- Any pointwise quadratic correction dominated by C/q^2
has a uniformly bounded total cost independent of S and P. -/
theorem finite_quadratic_euler_budget
    (S : Finset ℕ) (P : ℕ) (C : ℝ)
    (hP : 1 ≤ P) (hC : 0 ≤ C)
    (hS : ∀ q ∈ S, 2 ≤ q ∧ q ≤ P) :
    (∑ q ∈ S, C * ((q : ℝ) ^ 2)⁻¹) ≤ C := by
  rw [← Finset.mul_sum]
  have hmass := finite_inverse_square_mass_le_one S P hP hS
  nlinarith [mul_nonneg hC (sub_nonneg.mpr hmass)]

#print axioms Shiu.finite_inverse_square_mass_le_one
#print axioms Shiu.finite_quadratic_euler_budget
end Shiu
