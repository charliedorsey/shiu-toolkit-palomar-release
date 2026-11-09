module

public import EiravelFixedConstantException
public import PaperB.M4B.ShiuCore

public section

namespace PaperB.M4B
open scoped BigOperators

/-- The selected full prime-power exception fits the literal fixed-constant
Shiu target, including Euler primeMass and Euler totient. The *source
covering of every exceptional n* is a separate theorem obligation. -/
theorem eiravel_selected_full_power_exception_shiu_target
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n →
      f n ≤ B * (n : ℝ) ^ (1/1280 : ℝ))
    (x y z k a : ℕ)
    (hx2 : 2 ≤ x) (hz4 : 4 ≤ z)
    (hyx : y ≤ x) (hk : 0 < k)
    (hkz : k * z < y) (hxz : x < z ^ 160) :
    eiravelPowerExceptionalMass f x y k a
        ((Nat.primesLE (Nat.sqrt z)).filter (fun p => ¬ p ∣ k))
        (fun p => p ^ (Nat.log p (Nat.sqrt z) + 1)) ≤
      (56320 * B) *
        (((y : ℝ) / (((k.totient : ℝ)) * Real.log (x : ℝ))) *
           Real.exp (primeMass f x k)) := by
  classical
  have hmassNonneg : 0 ≤ primeMass f x k := by
    unfold primeMass
    apply Finset.sum_nonneg
    intro p hp
    exact div_nonneg (hf.nonnegative p) (Nat.cast_nonneg p)
  have hexp : (1 : ℝ) ≤ Real.exp (primeMass f x k) := by
    have hh : Real.exp 0 ≤ Real.exp (primeMass f x k) :=
      Real.exp_le_exp.mpr hmassNonneg
    simpa using hh
  have hphiPos : (0 : ℝ) < (k.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hk
  have hphiBound : (k.totient : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.totient_le k
  have hphiRatio :
      (y : ℝ) / (k : ℝ) ≤ (y : ℝ) / (k.totient : ℝ) := by
    have hi : (k : ℝ)⁻¹ ≤ (k.totient : ℝ)⁻¹ :=
      inv_anti₀ hphiPos hphiBound
    simpa [div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg y))
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hscaled :
      ((y : ℝ) / (k : ℝ)) / Real.log (x : ℝ) ≤
      ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
        Real.exp (primeMass f x k) := by
    calc
      ((y : ℝ) / (k : ℝ)) / Real.log (x : ℝ) ≤
          ((y : ℝ) / (k.totient : ℝ)) / Real.log (x : ℝ) :=
        div_le_div_of_nonneg_right hphiRatio hlog.le
      _ = (y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ)) := by ring
      _ = ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) * 1 := by ring
      _ ≤ ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
          Real.exp (primeMass f x k) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
  have hBase :=
    eiravel_selected_full_power_exception_fixed_constant
      hf hB hgrowth x y z k a hx2 hz4 hyx hk hkz hxz
  exact hBase.trans
    (mul_le_mul_of_nonneg_left hscaled (by positivity))

#print axioms eiravel_selected_full_power_exception_shiu_target

end PaperB.M4B
