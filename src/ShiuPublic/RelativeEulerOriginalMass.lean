module

public import ShiuPublic.RelativeEulerSourcePrimes
public import PaperB.M4B.ShiuCore

public section

/-! Exact adapter from the classical prime-power Euler product to the
original Shiu prime-mass and Rankin-correction expressions. -/
namespace Shiu
open scoped BigOperators

theorem classical_relative_euler_original_mass
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : ClassicalEnvelope f A)
    (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n →
      f n ≤ B * (n : ℝ)^(1/4 : ℝ))
    (N P k : ℕ) (D : ℝ)
    (hD : 0 < D)
    (hP : Real.exp (4*D) ≤ (P : ℝ)) :
    (∏ q ∈ (Nat.primesLE P).filter (fun q => ¬ q ∣ k),
      ∑ j ∈ Finset.range (N+2),
        f (q^j)/(q : ℝ)^((j : ℝ)*(1-D/Real.log (P:ℝ)))) ≤
      smallPrimeConstant (fixedPrimePowerCutoff A D) B *
      Real.exp (PaperB.M4B.primeMass f P k +
        PaperB.M4B.primeRankinCorrection f P k
          (D/Real.log (P:ℝ)) + 2*A^2*Real.exp (2*D)) := by
  have hS : ∀ q ∈ (Nat.primesLE P).filter (fun q => ¬ q ∣ k),
      q.Prime ∧ q ≤ P := by
    intro q hq
    exact ⟨Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hq).1,
      (Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1).1⟩
  have h := classical_relative_euler_fixed_cutoff hf hB hgrowth
    ((Nat.primesLE P).filter (fun q => ¬ q ∣ k))
    N P D hD hP hS
  simpa only [PaperB.M4B.primeMass,
    PaperB.M4B.primeRankinCorrection,
    Finset.sum_add_distrib, add_assoc] using h

#print axioms Shiu.classical_relative_euler_original_mass
end Shiu
