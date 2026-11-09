module

public import ShiuPublic.VaelisSmoothEulerTransport

public section

namespace Shiu
open scoped BigOperators

/-- No new primes appear in the divisor-exhaustion product for positive X. -/
theorem bounded_smooth_base_primeFactors (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (X : ℕ) (hX : 0 < X) :
    ((∏ p ∈ S, p) ^ X).primeFactors = S := by
  rw [Nat.primeFactors_pow _ (by omega)]
  exact Nat.primeFactors_prod hprime

/-- The actual exponent cutoff needed in the finite divisor Euler product is at most the containing integer. -/
theorem bounded_smooth_base_factorization_le (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (X p : ℕ) (hX : 0 < X)
    (hp : p ∈ S) :
    ((∏ p ∈ S, p) ^ X).factorization p ≤ (∏ p ∈ S, p) ^ X := by
  have hle := Nat.mul_factorization_le (n := (∏ p ∈ S, p) ^ X) (p := p)
  have hp1 : 1 ≤ p := (hprime p hp).one_le
  have hmono := Nat.mul_le_mul_right
    (((∏ p ∈ S, p) ^ X).factorization p) hp1
  omega

#print axioms Shiu.bounded_smooth_base_primeFactors
#print axioms Shiu.bounded_smooth_base_factorization_le
end Shiu
