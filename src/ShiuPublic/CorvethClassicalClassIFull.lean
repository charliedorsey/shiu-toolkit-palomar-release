module

public import ShiuPublic.CorvethClassicalClassI
public import ShiuPublic.CorvethClassicalHarmonicEuler

public section

namespace PaperB.M4B
open scoped BigOperators
noncomputable section

/-- Literal non-squarefree Class I overcount, with the original prime mass,
Rankin correction, and the full prime-power small-prime constant. -/
theorem corveth_classical_classI_rankin_bound
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n → f n ≤ B * (n : ℝ) ^ (1 / 4 : ℝ))
    {x y z k a : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hzy : z ≤ y) (hkz : k * z < y)
    (hzsqrt : 2 ≤ Nat.sqrt z) (hx : x < z ^ 160)
    (hzlarge : Real.exp 4 ≤ (z : ℝ)) :
    classIOvercount f x y z k a ≤
      4 * (1 + A) ^ 320 *
        ((3 * (y : ℝ) / ((k.totient : ℝ) * Real.log (Nat.sqrt z : ℝ)) +
          (z : ℝ) ^ 2) *
          (Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A 1) B *
            Real.exp (primeMass f z k +
              primeRankinCorrection f z k (1 / Real.log (z : ℝ)) +
              2 * A ^ 2 * Real.exp 2))) := by
  have hclass := corveth_classical_classI_harmonic_bound hf ha0 haklt hak
    hyx hzy hkz hzsqrt hx
  have hmass := corveth_classical_coprime_harmonic_rankin hf hB hgrowth z k
    (by have hle := Nat.sqrt_le_self z; omega : 0 < z) hzlarge
  have hR : 0 ≤
      3 * (y : ℝ) / ((k.totient : ℝ) * Real.log (Nat.sqrt z : ℝ)) +
        (z : ℝ) ^ 2 := by
    have hk : 0 < k := by omega
    have hphi : 0 < (k.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hk
    have hlog : 0 < Real.log (Nat.sqrt z : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < Nat.sqrt z by omega)
    positivity
  have hC : 0 ≤ 4 * (1 + A) ^ 320 := by
    positivity
  calc
    classIOvercount f x y z k a ≤
      4 * (1 + A) ^ 320 *
       ((3 * (y : ℝ) / ((k.totient : ℝ) * Real.log (Nat.sqrt z : ℝ)) +
         (z : ℝ) ^ 2) * coprimeHarmonicMass f z k) := by
      simpa [mul_assoc] using hclass
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmass hR) hC

#print axioms corveth_classical_classI_rankin_bound
end
end PaperB.M4B
