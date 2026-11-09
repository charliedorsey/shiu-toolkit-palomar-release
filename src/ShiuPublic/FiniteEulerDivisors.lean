module

public import ShiuPublic.FiniteEulerVectors

public section

/-!
Exact finite non-squarefree Euler expansion over *ordinary integers*.
The natural number indexing is a divisor set; exponents retain
multiplicity through prime-power divisors of n.
-/

namespace Shiu
open ArithmeticFunction
open scoped ArithmeticFunction.zeta BigOperators

/-- General finite divisor Euler formula: no squarefree restriction. -/
theorem finite_euler_divisor_product
    (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative)
    (n : ℕ) (hn : n ≠ 0) :
    (∏ p ∈ n.primeFactors,
      ∑ j ∈ Finset.range (n.factorization p + 1), f (p ^ j)) =
      ∑ d ∈ n.divisors, f d := by
  let g : ArithmeticFunction ℝ := f * (ζ : ArithmeticFunction ℝ)
  have hg : g.IsMultiplicative :=
    hf.mul (isMultiplicative_zeta.natCast)
  have hfactor : g n =
      ∏ p ∈ n.primeFactors, g (p ^ n.factorization p) := by
    have h := hg.multiplicative_factorization g hn
    simpa only [Finsupp.prod, Nat.support_factorization] using h
  calc
    (∏ p ∈ n.primeFactors,
      ∑ j ∈ Finset.range (n.factorization p + 1), f (p ^ j)) =
      ∏ p ∈ n.primeFactors, g (p ^ n.factorization p) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
        simpa only [g, coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hprime]
    _ = g n := hfactor.symm
    _ = ∑ d ∈ n.divisors, f d := by
      simpa only [g] using
        (coe_mul_zeta_apply (f := f) (x := n))

/-- Shifted arithmetic function, including all prime powers. -/
noncomputable def shiftedWeight
    (f : ArithmeticFunction ℝ) (s : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n / (n : ℝ) ^ s, by simp⟩

/-- The Rankin shift preserves multiplicativity. -/
theorem shiftedWeight_multiplicative
    (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative) (s : ℝ) :
    (shiftedWeight f s).IsMultiplicative := by
  constructor
  · simp [shiftedWeight, hf.map_one]
  · intro m n hcop
    change f (m * n) / ((m * n : ℕ) : ℝ) ^ s =
      (f m / (m : ℝ) ^ s) * (f n / (n : ℝ) ^ s)
    rw [hf.map_mul_of_coprime hcop, Nat.cast_mul,
      Real.mul_rpow (by positivity) (by positivity)]
    ring

/-- Exact non-squarefree Euler expansion over natural divisors at
the real Rankin scale s, with each prime exponent respected. -/
theorem finite_euler_divisor_rankin
    (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative)
    (n : ℕ) (hn : n ≠ 0) (s : ℝ) :
    (∏ p ∈ n.primeFactors,
      ∑ j ∈ Finset.range (n.factorization p + 1),
        f (p ^ j) / ((p ^ j : ℕ) : ℝ) ^ s) =
      ∑ d ∈ n.divisors, f d / (d : ℝ) ^ s := by
  exact
    finite_euler_divisor_product (shiftedWeight f s)
      (shiftedWeight_multiplicative f hf s) n hn

#print axioms Shiu.finite_euler_divisor_product
#print axioms Shiu.shiftedWeight_multiplicative
#print axioms Shiu.finite_euler_divisor_rankin
end Shiu
