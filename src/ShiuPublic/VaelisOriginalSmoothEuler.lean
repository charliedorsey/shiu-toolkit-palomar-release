module

public import ShiuPublic.VaelisSmoothUniformFinite
public import ShiuPublic.RelativeEulerOriginalMass

public section

namespace Shiu
open scoped BigOperators

/-- Uniform in the height cutoff X: the actual M4B eligible-prime smooth
family is bounded by Cendrel's classical non-squarefree relative Euler budget. -/
theorem classical_bounded_smooth_original_mass
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : ClassicalEnvelope f A)
    (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n →
      f n ≤ B * (n : ℝ)^(1/4 : ℝ))
    (X P k : ℕ) (hX : 0 < X) (D : ℝ)
    (hD : 0 < D)
    (hP : Real.exp (4*D) ≤ (P : ℝ)) :
    (∑ n ∈ boundedSmoothSet
        ((Nat.primesLE P).filter (fun q => ¬ q ∣ k)) X,
      f n / (n : ℝ) ^ (1-D/Real.log (P : ℝ))) ≤
      smallPrimeConstant (fixedPrimePowerCutoff A D) B *
      Real.exp (PaperB.M4B.primeMass f P k +
        PaperB.M4B.primeRankinCorrection f P k
          (D/Real.log (P:ℝ)) + 2*A^2*Real.exp (2*D)) := by
  let S : Finset ℕ := (Nat.primesLE P).filter (fun q => ¬ q ∣ k)
  have hprime : ∀ q ∈ S, q.Prime := by
    intro q hq
    exact Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hq).1
  have ht := bounded_smooth_mass_le_uniform_finite_euler
    hf S hprime X hX (1-D/Real.log (P : ℝ))
  have he := classical_relative_euler_original_mass
    hf hB hgrowth ((∏ q ∈ S, q) ^ X) P k D hD hP
  exact ht.trans (by simpa only [S] using he)

#print axioms Shiu.classical_bounded_smooth_original_mass
end Shiu
