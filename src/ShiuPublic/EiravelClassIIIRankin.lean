module

public import ShiuPublic.VaelisSmoothDivisor
public import ShiuPublic.CorvethClassicalClassIII

public section

open scoped BigOperators

namespace Eiravel

/-!
A finite full-prime-power Rankin input for the unrestricted Shiu Class III.
This intentionally counts *all* smooth positive integers, not only squarefree ones.
The source finite sieve set is Shiu.boundedSmoothSet, unchanged.
-/

/-- The unrestricted finite smooth cardinality is controlled by a genuinely
non-squarefree divisor Euler mass. No squarefree hypothesis on the source. -/
theorem full_power_smooth_rankin_divisor
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (X : ℕ) (hX : 0 < X) (eta : ℝ) (heta : 0 ≤ eta) :
    ((Shiu.boundedSmoothSet S X).card : ℝ) ≤
      (X : ℝ) ^ eta *
        (∑ n ∈ ((∏ p ∈ S, p) ^ X).divisors, (n : ℝ) ^ (-eta)) := by
  classical
  let T := Shiu.boundedSmoothSet S X
  have hw : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ (-eta) := by
    intro n
    positivity
  have hpt : ∀ n ∈ T, (1 : ℝ) ≤
      (X : ℝ) ^ eta * (n : ℝ) ^ (-eta) := by
    intro n hn
    obtain ⟨hnI, -⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hnI
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnXR : (n : ℝ) ≤ (X : ℝ) := by exact_mod_cast hnX
    have hpow : (n : ℝ) ^ eta ≤ (X : ℝ) ^ eta :=
      Real.rpow_le_rpow hnpos.le hnXR heta
    calc
      (1 : ℝ) = (n : ℝ) ^ eta * (n : ℝ) ^ (-eta) := by
        rw [← Real.rpow_add hnpos]
        simp
      _ ≤ (X : ℝ) ^ eta * (n : ℝ) ^ (-eta) :=
        mul_le_mul_of_nonneg_right hpow (hw n)
  have hsum :
      (T.card : ℝ) ≤
        (X : ℝ) ^ eta * (∑ n ∈ T, (n : ℝ) ^ (-eta)) := by
    calc
      (T.card : ℝ) = ∑ _n ∈ T, (1 : ℝ) := by simp
      _ ≤ ∑ n ∈ T, (X : ℝ) ^ eta * (n : ℝ) ^ (-eta) :=
        Finset.sum_le_sum fun n hn => hpt n hn
      _ = (X : ℝ) ^ eta * (∑ n ∈ T, (n : ℝ) ^ (-eta)) := by
        rw [Finset.mul_sum]
  have hdiv := Shiu.bounded_smooth_mass_le_divisor_mass
    S X (fun n => (n : ℝ) ^ (-eta)) hw hprime
  have hprod : 0 ≤ (X : ℝ) ^ eta := by positivity
  exact hsum.trans (mul_le_mul_of_nonneg_left hdiv hprod)

#print axioms Eiravel.full_power_smooth_rankin_divisor

end Eiravel

namespace Eiravel

/-- The physical unrestricted Class III prefix is counted at its own ceiling z,
not at the ambient height x. This removes an unnecessary x^eta loss from the
Rankin prefactor. Multiplicities and k-coprimality are unchanged. -/
theorem corveth_full_power_classIII_rankin_at_z
    (x z k : ℕ) (hz : 0 < z) (eta : ℝ) (heta : 0 ≤ eta) :
    ((PaperB.M4B.corvethClassicalClassIIIFactors x z k).card : ℝ) ≤
      (z : ℝ) ^ eta *
      (∑ n ∈
          ((∏ p ∈ Nat.primesLE (PaperB.M4B.shiuLogLogSmoothThreshold x), p) ^ z).divisors,
          (n : ℝ) ^ (-eta)) := by
  classical
  let S : Finset ℕ :=
    Nat.primesLE (PaperB.M4B.shiuLogLogSmoothThreshold x)
  have hs : PaperB.M4B.corvethClassicalClassIIIFactors x z k ⊆
      Shiu.boundedSmoothSet S z := by
    intro b hb
    have hb1 := Finset.mem_filter.mp hb
    have hb2 := Finset.mem_filter.mp hb1.1
    have hbI := Finset.mem_Icc.mp hb2.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hbI.1, hb1.2.1⟩, hb2.2⟩
  have hcard :
      ((PaperB.M4B.corvethClassicalClassIIIFactors x z k).card : ℝ) ≤
        ((Shiu.boundedSmoothSet S z).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hs
  exact hcard.trans
    (full_power_smooth_rankin_divisor S
      (fun p hp => Nat.prime_of_mem_primesLE hp) z hz eta heta)

#print axioms Eiravel.corveth_full_power_classIII_rankin_at_z

end Eiravel
