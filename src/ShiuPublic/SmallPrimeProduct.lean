module

public import ShiuPublic.SmallPrimeEuler

public import ChallengeDefs.SmallPrime

public section

/-! Fixed finite-prime Euler envelope: every selected small-prime factor
is bounded by a single explicit product independent of P, k, and r. -/
namespace Shiu
open scoped BigOperators

/- Explicit finite exceptional-prime Euler constant. -/
-- Shared Mathlib-only source definition: ChallengeDefs.SmallPrime.smallPrimeConstant

/-- Every local-factor majorant is absorbed into the fixed product. -/
theorem small_prime_product_uniform
    (Q : ℕ) (B : ℝ) (S : Finset ℕ) (L : ℕ → ℝ)
    (hB : 0 ≤ B)
    (hS : S ⊆ Nat.primesLE Q)
    (hL0 : ∀ q ∈ S, 0 ≤ L q)
    (hL : ∀ q ∈ S,
      L q ≤ 1 + B / (1 - (q : ℝ) ^ (-(1/2 : ℝ)))) :
    (∏ q ∈ S, L q) ≤ smallPrimeConstant Q B := by
  let g : ℕ → ℝ :=
    fun q => 1 + B / (1 - (q : ℝ) ^ (-(1/2 : ℝ)))
  have hgnonneg (q : ℕ) (hq : q ∈ Nat.primesLE Q) :
      0 ≤ g q := by
    have hprime : q.Prime := (Nat.mem_primesLE.mp hq).2
    have hq2 : 2 ≤ q := hprime.two_le
    have hreal : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
    have hpow : (q : ℝ) ^ (-(1/2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hreal (by norm_num)
    dsimp [g]
    have hden : 0 < 1 - (q : ℝ) ^ (-(1/2 : ℝ)) := sub_pos.mpr hpow
    positivity
  calc
    (∏ q ∈ S, L q) ≤ ∏ q ∈ S, g q := by
      apply Finset.prod_le_prod₀
      · intro q hq; exact hL0 q hq
      · intro q hq; exact hL q hq
    _ ≤ ∏ q ∈ Nat.primesLE Q, g q := by
      apply Finset.prod_le_prod_of_subset_of_one_le₀ hS
        (fun q hq => hgnonneg q (hS hq))
      intro q hq hnot
      have hn := hgnonneg q hq
      dsimp [g] at hn ⊢
      have hprime : q.Prime := (Nat.mem_primesLE.mp hq).2
      have hreal : (1 : ℝ) < q := by exact_mod_cast hprime.one_lt
      have hpow : (q : ℝ) ^ (-(1/2 : ℝ)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hreal (by norm_num)
      have hden : 0 < 1 - (q : ℝ) ^ (-(1/2 : ℝ)) := sub_pos.mpr hpow
      have hquot : 0 ≤ B / (1 - (q : ℝ) ^ (-(1/2 : ℝ))) :=
        div_nonneg hB hden.le
      linarith
    _ = smallPrimeConstant Q B := rfl

#print axioms Shiu.small_prime_product_uniform
end Shiu
