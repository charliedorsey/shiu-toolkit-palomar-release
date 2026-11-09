module

public import ShiuPublic.VaelisClassicalSmoothTailOriginal

public section

namespace Shiu
open scoped BigOperators

/-- Non-squarefree Class IV prefix: same original interval, coprimality,
and prime ceiling, dropping only the squarefree gate. -/
@[expose] def classicalClassIVPrefixSet (z k p : ℕ) : Finset ℕ :=
  (Finset.Icc (Nat.sqrt z) z).filter
    (fun b => b.Coprime k ∧ ∀ q ∈ b.primeFactors, q ≤ p)

/-- Non-squarefree actual source prefix enters the exact smooth-tail family
with no collapse of repeated prime factors. -/
theorem classical_classIV_prefix_subset_smooth_tail
    (z k p : ℕ) (hz : 1 ≤ Nat.sqrt z) :
    classicalClassIVPrefixSet z k p ⊆
      boundedSmoothTailSet ((Nat.primesLE p).filter (fun q => ¬ q ∣ k))
        (Nat.sqrt z) z := by
  intro b hb
  obtain ⟨hbI, ⟨hcop, hceil⟩⟩ := Finset.mem_filter.mp hb
  obtain ⟨hbLo, hbHi⟩ := Finset.mem_Icc.mp hbI
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨hz.trans hbLo, hbHi⟩
    · intro q hq
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hqdvd : q ∣ b := Nat.dvd_of_mem_primeFactors hq
      have hnot : ¬ q ∣ k := by
        intro hqk
        have hqone : q ∣ 1 := by
          rw [← hcop.gcd_eq_one]
          exact Nat.dvd_gcd hqdvd hqk
        exact hqprime.not_dvd_one hqone
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_primesLE.mpr ⟨hceil q hq, hqprime⟩, hnot⟩
  · exact hbLo

/-- Full non-squarefree prefix mass is bounded by the source smooth-tail sum. -/
theorem classical_classIV_prefix_harmonic_le_smooth_tail
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : ClassicalEnvelope f A)
    (z k p : ℕ) (hz : 1 ≤ Nat.sqrt z) :
    (∑ b ∈ classicalClassIVPrefixSet z k p, f b / (b : ℝ)) ≤
      ∑ b ∈ boundedSmoothTailSet
          ((Nat.primesLE p).filter (fun q => ¬ q ∣ k)) (Nat.sqrt z) z,
          f b / (b : ℝ) := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (classical_classIV_prefix_subset_smooth_tail z k p hz)
    (fun b hb _ => div_nonneg (hf.nonnegative b) (by positivity))

/-- First actual non-squarefree Class IV prefix supplier with explicit
Cendrel Euler mass and the sharp Rankin factor. -/
theorem classical_classIV_prefix_harmonic_le_original_rankin
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : ClassicalEnvelope f A) (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n → f n ≤ B * (n : ℝ)^(1/4 : ℝ))
    (z k p : ℕ) (hz : 1 ≤ Nat.sqrt z) (D : ℝ)
    (hD : 0 < D) (hP : Real.exp (4*D) ≤ (p : ℝ))
    (hδ : 0 ≤ D / Real.log (p : ℝ)) :
    (∑ b ∈ classicalClassIVPrefixSet z k p, f b / (b : ℝ)) ≤
      (Nat.sqrt z : ℝ)^(-(D/Real.log (p : ℝ))) *
      (smallPrimeConstant (fixedPrimePowerCutoff A D) B *
        Real.exp (PaperB.M4B.primeMass f p k +
          PaperB.M4B.primeRankinCorrection f p k
            (D/Real.log (p : ℝ)) + 2*A^2*Real.exp (2*D))) := by
  have hsub := classical_classIV_prefix_harmonic_le_smooth_tail hf z k p hz
  have hzpos : 0 < z := by
    have hh : Nat.sqrt z ≤ z := Nat.sqrt_le_self z
    omega
  have htail := classical_bounded_smooth_tail_original_mass hf hB hgrowth
    (Nat.sqrt z) z p k hz hzpos D hD hP hδ
  exact hsub.trans htail

#print axioms Shiu.classical_classIV_prefix_subset_smooth_tail
#print axioms Shiu.classical_classIV_prefix_harmonic_le_smooth_tail
#print axioms Shiu.classical_classIV_prefix_harmonic_le_original_rankin
end Shiu
