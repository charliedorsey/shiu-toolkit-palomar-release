module

public import ShiuPublic.VaelisClassIVRankinExpBudget
public import ShiuPublic.VaelisClassIVMassMonotone

public section

namespace PaperB.M4B
open scoped BigOperators

/-- Cendrel's entire non-squarefree smooth Euler constant is carried through
an original Class IV shell scalar Rankin budget, and the original source prime
mass is enlarged from p to z without losing multiplicities. -/
theorem classical_classIV_shell_bound_of_rankin_budget
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : Shiu.ClassicalEnvelope f A) (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n → f n ≤ B * (n : ℝ)^(1/4 : ℝ))
    {x y z k a p w r : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hzy : z ≤ y) (hk : 0 < k)
    (hzsqrt : 1 ≤ Nat.sqrt z)
    (hw : 2 ≤ w) (hwsq : w ^ 2 ≤ z)
    (hx : x < z ^ 160) (hr : 1 ≤ r)
    (hzwr : z < (w + 1) ^ (r + 1))
    (hpz : p ≤ z)
    (hkb : ∀ b ∈ Shiu.classicalClassIVPrefixSet z k p, k * b < y)
    (D : ℝ) (hD : 0 < D)
    (hP : Real.exp (4 * D) ≤ (p : ℝ))
    (hδ : 0 ≤ D / Real.log (p : ℝ))
    {R : ℝ}
    (hbudget : primeRankinCorrection f p k (D/Real.log (p : ℝ)) -
      (D/Real.log (p : ℝ)) * Real.log ((Nat.sqrt z : ℕ) : ℝ) ≤ -R) :
    classicalClassIVShellOvercount f x y z k a p w ≤
      (4 * (1 + A) ^ (320 * r)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) *
        (Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A D) B *
          Real.exp (primeMass f z k + 2*A^2*Real.exp (2*D) - R)) := by
  have hshell := classical_classIV_shell_bound_of_original_rankin hf hB hgrowth
    ha0 haklt hak hyx hzy hk hzsqrt hw hwsq hx hr hzwr hkb D hD hP hδ
  have hmass := classical_primeMass_mono hf (k := k) hpz
  have hsmall : 0 ≤ Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A D) B := by
    have h := Shiu.small_prime_product_uniform
      (Shiu.fixedPrimePowerCutoff A D) B ∅ (fun _ => (0 : ℝ)) hB
      (by simp) (by simp) (by simp)
    have h1 : (1 : ℝ) ≤ Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A D) B := by
      simpa using h
    linarith
  have hroot : (0 : ℝ) < (Nat.sqrt z : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hzsqrt)
  have hexp := classical_rankin_exponential_budget
    (Nat.sqrt z : ℝ) (D / Real.log (p : ℝ))
    (primeMass f p k) (primeRankinCorrection f p k (D / Real.log (p : ℝ)))
    (2*A^2*Real.exp (2*D)) R hroot hbudget
  have hexpmon :
      Real.exp (primeMass f p k + 2*A^2*Real.exp (2*D) - R) ≤
        Real.exp (primeMass f z k + 2*A^2*Real.exp (2*D) - R) := by
    apply Real.exp_le_exp.mpr
    linarith
  have htail :
      (Nat.sqrt z : ℝ) ^ (-(D / Real.log (p : ℝ))) *
        (Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A D) B *
          Real.exp (primeMass f p k +
            primeRankinCorrection f p k (D / Real.log (p : ℝ)) +
              2*A^2*Real.exp (2*D))) ≤
      Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A D) B *
        Real.exp (primeMass f z k + 2*A^2*Real.exp (2*D) - R) := by
    calc
      _ = Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A D) B *
          ((Nat.sqrt z : ℝ) ^ (-(D / Real.log (p : ℝ))) *
            Real.exp (primeMass f p k +
              primeRankinCorrection f p k (D / Real.log (p : ℝ)) +
              2*A^2*Real.exp (2*D))) := by ring
      _ ≤ Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A D) B *
          Real.exp (primeMass f p k + 2*A^2*Real.exp (2*D) - R) :=
        mul_le_mul_of_nonneg_left hexp hsmall
      _ ≤ _ := mul_le_mul_of_nonneg_left hexpmon hsmall
  have hlog : 0 < Real.log (w : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < w by omega)
  have htot : 0 < (k.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 hk
  have hcoef : 0 ≤
      (4 * (1 + A) ^ (320 * r)) *
        ((3 * (y : ℝ)) / ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) := by
    have hA := hf.A_nonnegative
    positivity
  exact hshell.trans (mul_le_mul_of_nonneg_left htail hcoef)

#print axioms classical_classIV_shell_bound_of_rankin_budget
end PaperB.M4B
