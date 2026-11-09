module

public import ShiuPublic.SmallPrimeLocalComplete
public import ShiuPublic.LargePrimeMassCorrection

public section

/-! Finite relative Euler theorem split at a fixed exceptional-prime
cutoff, with all powers and a shell-independent explicit factor. -/
namespace Shiu
open scoped BigOperators

/-- Full finite prime-power Euler factor bound for a partition into
small and large primes. All constants independent of shell parameters. -/
theorem classical_relative_euler_partition
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : ClassicalEnvelope f A)
    (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n →
      f n ≤ B * (n : ℝ)^(1/4 : ℝ))
    (Ssmall Slarge : Finset ℕ) (N P Q : ℕ) (D δ : ℝ)
    (hP : 1 ≤ P) (hδ : 0 ≤ δ) (hquarter : δ ≤ 1/4)
    (hsmall : Ssmall ⊆ Nat.primesLE Q)
    (hlarge : ∀ q ∈ Slarge, q.Prime ∧ q ≤ P)
    (hgate : ∀ q ∈ Slarge, 2*A ≤ (q : ℝ)^(1-δ))
    (hpow : ∀ q ∈ Slarge, (q : ℝ)^δ ≤ Real.exp D)
    (hdisjoint : Disjoint Ssmall Slarge) :
    (∏ q ∈ Ssmall ∪ Slarge,
      ∑ j ∈ Finset.range (N+2),
        f (q^j)/(q : ℝ)^((j : ℝ)*(1-δ))) ≤
      smallPrimeConstant Q B *
        Real.exp ((∑ q ∈ Slarge,
          (f q/(q : ℝ) +
           f q*((q : ℝ)^δ-1)/(q : ℝ))) +
          2*A^2*Real.exp (2*D)) := by
  have hsmallProd :
      (∏ q ∈ Ssmall, ∑ j ∈ Finset.range (N+2),
        f (q^j)/(q : ℝ)^((j : ℝ)*(1-δ))) ≤
      smallPrimeConstant Q B := by
    apply small_prime_product_uniform Q B Ssmall
      (fun q => ∑ j ∈ Finset.range (N+2),
        f (q^j)/(q : ℝ)^((j : ℝ)*(1-δ)))
      hB hsmall
    · intro q hq
      apply Finset.sum_nonneg
      intro j hj
      exact div_nonneg (hf.nonnegative _)
        (Real.rpow_nonneg (by positivity) _)
    · intro q hq
      have hprime : q.Prime :=
        (Nat.mem_primesLE.mp (hsmall hq)).2
      have hgr (m : ℕ) (hm : 1 ≤ m) :
          f (q ^ m) ≤ B * (q : ℝ)^((m : ℝ)*(1/4 : ℝ)) := by
        convert hgrowth (q^m) (by have hh := hprime.two_le; have := pow_pos (by omega : 0 < q) m; omega) using 1
        rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]

      exact small_prime_complete_local_factor (fun n => f n) q (N+1)
        hprime.two_le B δ hB hδ hquarter hf.multiplicative.map_one hgr
  have hlargeProd := classical_large_prime_mass_uniform hf Slarge N P D δ
    hP hlarge hgate hpow
  have hconstant : 0 ≤ smallPrimeConstant Q B := by
    have h : (1 : ℝ) ≤ smallPrimeConstant Q B := by
      have ht := small_prime_product_uniform Q B ∅ (fun _ => 1) hB
        (Finset.empty_subset _) (by simp) (by simp)
      simpa using ht
    linarith
  have hlargeNonneg : 0 ≤ (∏ q ∈ Slarge,
    ∑ j ∈ Finset.range (N+2),
      f (q^j)/(q : ℝ)^((j : ℝ)*(1-δ))) := by
    apply Finset.prod_nonneg
    intro q hq
    apply Finset.sum_nonneg
    intro j hj
    exact div_nonneg (hf.nonnegative _)
      (Real.rpow_nonneg (by positivity) _)
  rw [Finset.prod_union hdisjoint]
  exact mul_le_mul hsmallProd hlargeProd hlargeNonneg hconstant

#print axioms Shiu.classical_relative_euler_partition
end Shiu
