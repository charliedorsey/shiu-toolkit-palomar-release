module

public import Mathlib

public section

namespace Shiu
open scoped BigOperators

/-- The original finite smooth input family: positive integers up to X with all prime factors in S. -/
@[expose] def boundedSmoothSet (S : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun n => n.primeFactors ⊆ S)

/-- Every bounded smooth integer divides a single finite product, with ALL prime powers retained. -/
theorem bounded_smooth_dvd_product_pow
    (S : Finset ℕ) (X n : ℕ) (hn : n ≠ 0)
    (hnX : n ≤ X) (hS : n.primeFactors ⊆ S) :
    n ∣ (∏ p ∈ S, p) ^ X := by
  have ha : n ∣ (∏ p ∈ n.primeFactors, p) ^ n :=
    Nat.dvd_prod_primeFactors_pow_self hn
  have hb : (∏ p ∈ n.primeFactors, p) ^ n ∣
      (∏ p ∈ S, p) ^ X := by
    have hprod : (∏ p ∈ n.primeFactors, p) ∣ (∏ p ∈ S, p) :=
      Finset.prod_dvd_prod_of_subset _ _ id hS
    exact pow_dvd_pow_of_dvd_of_le hprod hnX
  exact ha.trans hb

/-- Every bounded smooth weighted sum injects into one finite divisor sum.
No squarefree support: divisors include arbitrary prime powers. -/
theorem bounded_smooth_mass_le_divisor_mass
    (S : Finset ℕ) (X : ℕ) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (hprime : ∀ p ∈ S, p.Prime) :
    (∑ n ∈ boundedSmoothSet S X, w n) ≤
      ∑ n ∈ ((∏ p ∈ S, p) ^ X).divisors, w n := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    have h := Finset.mem_filter.mp hn
    have hnI := Finset.mem_Icc.mp h.1
    have hpos : n ≠ 0 := by omega
    have hdvd := bounded_smooth_dvd_product_pow S X n hpos hnI.2 h.2
    have hbase : 0 < ∏ p ∈ S, p := by
      apply Finset.prod_pos
      intro p hp
      exact (hprime p hp).pos
    exact Nat.mem_divisors.mpr ⟨hdvd, pow_ne_zero _ (by omega)⟩
  · intro n _ _
    exact hw n

#print axioms Shiu.bounded_smooth_dvd_product_pow
#print axioms Shiu.bounded_smooth_mass_le_divisor_mass
end Shiu
