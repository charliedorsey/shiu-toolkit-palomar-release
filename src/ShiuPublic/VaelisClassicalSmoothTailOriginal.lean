module

public import ShiuPublic.VaelisSmoothTailRankin
public import ShiuPublic.VaelisOriginalSmoothEuler

public section

namespace Shiu
open scoped BigOperators

/-- Original M4B eligible-prime finite smooth tail with full prime powers,
sharp lower threshold, and the paid Cendrel uniform Euler budget. -/
theorem classical_bounded_smooth_tail_original_mass
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : ClassicalEnvelope f A) (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n → f n ≤ B * (n : ℝ)^(1/4 : ℝ))
    (T X P k : ℕ) (hT : 1 ≤ T) (hX : 0 < X) (D : ℝ)
    (hD : 0 < D) (hP : Real.exp (4*D) ≤ (P : ℝ))
    (hδ : 0 ≤ D / Real.log (P : ℝ)) :
    (∑ n ∈ boundedSmoothTailSet
       ((Nat.primesLE P).filter (fun q => ¬ q ∣ k)) T X,
       f n / (n : ℝ)) ≤
      (T : ℝ)^(-(D/Real.log (P : ℝ))) *
      (smallPrimeConstant (fixedPrimePowerCutoff A D) B *
        Real.exp (PaperB.M4B.primeMass f P k +
          PaperB.M4B.primeRankinCorrection f P k
            (D/Real.log (P : ℝ)) + 2*A^2*Real.exp (2*D))) := by
  have htail := bounded_smooth_tail_rankin_le hf
      ((Nat.primesLE P).filter (fun q => ¬ q ∣ k)) T X hT
      (D/Real.log (P : ℝ)) hδ
  have hsource := classical_bounded_smooth_original_mass hf hB hgrowth X P k hX D hD hP
  exact htail.trans (mul_le_mul_of_nonneg_left hsource
    (Real.rpow_nonneg (by positivity) _))

#print axioms Shiu.classical_bounded_smooth_tail_original_mass
end Shiu
