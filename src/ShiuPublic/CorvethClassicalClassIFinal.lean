module

public import ShiuPublic.CorvethClassicalClassIFull
public import ShiuPublic.CorvethClassicalClassICorrection

public import ChallengeDefs.ClassI

public section

namespace PaperB.M4B
open scoped BigOperators
noncomputable section

/- Constant independent of x,y,z,k,a: full classical non-squarefree Class I. -/
-- Shared Mathlib-only source definition: ChallengeDefs.ClassI.corvethClassicalClassIConstant

set_option maxHeartbeats 800000 in
theorem corveth_classical_classI_final
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
      corvethClassicalClassIConstant A B *
        ((3 * (y : ℝ) /
            ((k.totient : ℝ) * Real.log (Nat.sqrt z : ℝ)) +
          (z : ℝ) ^ 2) * Real.exp (primeMass f z k)) := by
  let C : ℝ := 4 * (1 + A) ^ 320
  let S : ℝ := Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A 1) B
  let R : ℝ := 3 * (y : ℝ) /
      ((k.totient : ℝ) * Real.log (Nat.sqrt z : ℝ)) + (z : ℝ) ^ 2
  let E : ℝ := ((4 * A * Real.log 4) / Real.log 2) * Real.exp 1 +
    2 * A ^ 2 * Real.exp 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hS : 0 ≤ S := by
    have h := Shiu.small_prime_product_uniform
      (Shiu.fixedPrimePowerCutoff A 1) B
      ∅ (fun _ => (0 : ℝ)) hB (by simp) (by simp) (by simp)
    have h1 : (1 : ℝ) ≤ S := by simpa [S] using h
    linarith
  have hR : 0 ≤ R := by
    have hk : 0 < k := by omega
    have hphi : 0 < (k.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hk
    have hlog : 0 < Real.log (Nat.sqrt z : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < Nat.sqrt z by omega)
    dsimp [R]
    positivity
  have hfull := corveth_classical_classI_rankin_bound hf hB hgrowth
    ha0 haklt hak hyx hzy hkz hzsqrt hx hzlarge
  have hcor := corveth_classical_rankin_one_fixed hf (k := k) hzlarge
  have hExp :
      Real.exp (primeMass f z k +
        primeRankinCorrection f z k (1 / Real.log (z : ℝ)) +
        2 * A ^ 2 * Real.exp 2) ≤
      Real.exp (primeMass f z k) * Real.exp E := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [E]
    linarith [hcor]
  calc
    classIOvercount f x y z k a ≤
      C * (R * (S * Real.exp
        (primeMass f z k +
          primeRankinCorrection f z k (1 / Real.log (z : ℝ)) +
          2 * A ^ 2 * Real.exp 2))) := by
      simpa only [C, R, S] using hfull
    _ ≤ C * (R * (S * (Real.exp (primeMass f z k) * Real.exp E))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hExp hS) hR) hC
    _ = corvethClassicalClassIConstant A B *
        ((3 * (y : ℝ) /
          ((k.totient : ℝ) * Real.log (Nat.sqrt z : ℝ)) +
          (z : ℝ) ^ 2) * Real.exp (primeMass f z k)) := by
      dsimp [corvethClassicalClassIConstant, C, S, R, E]
      ring

#print axioms corveth_classical_classI_final
end
end PaperB.M4B
