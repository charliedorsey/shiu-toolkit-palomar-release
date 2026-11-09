module

public import Shiu.Classical

public section

/-!
# Modulus-one prime-mass and classical-coefficient positivity

All statements are exact consequences of the pinned source.
-/
namespace Shiu.API
open scoped BigOperators

/-- Omitting prime terms with p|k only decreases the nonnegative
prime mass. In modulus 1 no primes are omitted. -/
theorem primeMass_le_modulus_one
    (f : ArithmeticFunction ℝ) (x k : ℕ)
    (hf : ∀ n : ℕ, 0 ≤ f n) :
    PaperB.M4B.primeMass f x k ≤ PaperB.M4B.primeMass f x 1 := by
  change (∑ p ∈ Nat.primesLE x with ¬ p ∣ k, f p / p) ≤
    (∑ p ∈ Nat.primesLE x with ¬ p ∣ 1, f p / p)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hpbase : p ∈ Nat.primesLE x :=
      (Finset.mem_filter.mp hp).1
    exact Finset.mem_filter.mpr ⟨hpbase,
      (Nat.prime_of_mem_primesLE hpbase).not_dvd_one⟩
  · intro p hp hnot
    have hpbase : p ∈ Nat.primesLE x :=
      (Finset.mem_filter.mp hp).1
    have hp0 : (0 : ℝ) ≤ (p : ℝ) :=
      Nat.cast_nonneg _
    exact div_nonneg (hf p) hp0

/-- The original classical constant is nonnegative for A,B>=0.
It is the exact source coefficient, not an adjusted estimate. -/
theorem classicalConstant_nonneg (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ classicalConstant A B := by
  have hS (Q : ℕ) :
      0 ≤ Shiu.smallPrimeConstant Q B := by
    have h := Shiu.small_prime_product_uniform
      Q B ∅ (fun _ => (0 : ℝ)) hB
      (by simp) (by simp) (by simp)
    have hone : (1 : ℝ) ≤ Shiu.smallPrimeConstant Q B := by
      simpa using h
    linarith
  unfold classicalConstant
    PaperB.M4B.corvethClassicalClassIConstant
    PaperB.M4B.classicalShiuClassIVConstant
  have hC1 := hS (Shiu.fixedPrimePowerCutoff A 1)
  have hC4 := hS (Shiu.fixedPrimePowerCutoff A
    (PaperB.M4B.classicalClassIVRankinD A))
  positivity

#print axioms primeMass_le_modulus_one
#print axioms classicalConstant_nonneg
end Shiu.API
