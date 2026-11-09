module

public import EiravelGeneralPowerAP
public import EiravelScalarGeometry
public import EiravelGrowthLog
public import EiravelScalarCombination

public section

namespace PaperB.M4B
open scoped BigOperators

/-- Fixed-constant scalar absorption of the actual eligible full-power
exceptional AP overcount. Both endpoint and reciprocal losses are kept. -/
theorem eiravel_selected_full_power_exception_fixed_constant
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
      (56320 * B) * (((y : ℝ) / (k : ℝ)) / Real.log (x : ℝ)) := by
  let T : ℕ := Nat.sqrt z
  let U : ℕ := Nat.sqrt T
  let Y : ℝ := (y : ℝ) / (k : ℝ)
  let G : ℝ := (x : ℝ) ^ (1/1280 : ℝ)
  let L : ℝ := Real.log (x : ℝ)
  let V : ℝ := (z : ℝ) ^ (1/4 : ℝ)
  let R : ℝ := (U : ℝ) / (T : ℝ) + 2 / ((U+1 : ℕ) : ℝ)
  let E : ℝ := 4 * (((T+1 : ℕ) : ℝ))
  let Mass : ℝ :=
    eiravelPowerExceptionalMass f x y k a
      ((Nat.primesLE T).filter (fun p => ¬ p ∣ k))
      (fun p => p ^ (Nat.log p T + 1))
  have hTR : 0 < T := by
    dsimp [T]
    exact Nat.sqrt_pos.mpr (by omega : 0 < z)
  have hZpos : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hKpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hY : (z : ℝ) ≤ Y := by
    have hreal : (z : ℝ) * (k : ℝ) ≤ (y : ℝ) := by
      have hcast : (k : ℝ) * (z : ℝ) ≤ (y : ℝ) := by
        exact_mod_cast hkz.le
      nlinarith [hcast]
    exact (le_div_iff₀ hKpos).mpr (by simpa [mul_comm] using hreal)
  have hLog : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hGrowth : G * L ≤ 1280 * V := by
    simpa only [G,L,V] using eiravel_growth_log_absorb x z
      (by omega : 1 ≤ z) hxz
  have hRoot : V * (R + E / (z : ℝ)) ≤ 44 := by
    simpa only [V,R,E,T,U, Nat.cast_add, Nat.cast_one,
       add_assoc] using eiravel_nat_sqrt_ratio_budget z hz4
  have hCore :
      G * (Y * R + E) * L ≤ 56320 * Y :=
    eiravel_exception_absorption_core hZpos hY hG hLog.le
      hV hR hE hGrowth hRoot
  have hAP : Mass ≤ (B * G) * (Y * R + E) := by
    have ha := eiravel_eligible_minimal_power_mass_budget
      hf hB hgrowth x y z k a hyx hk hTR
    simpa only [Mass,G,Y,R,E,T,U,Nat.cast_add,Nat.cast_one] using ha
  have hBoundL :
      Mass * L ≤ (56320 * B) * Y := by
    calc
      Mass * L ≤ ((B * G) * (Y * R + E)) * L :=
        mul_le_mul_of_nonneg_right hAP hLog.le
      _ = B * (G * (Y * R + E) * L) := by ring
      _ ≤ B * (56320 * Y) :=
        mul_le_mul_of_nonneg_left hCore hB
      _ = (56320 * B) * Y := by ring
  change Mass ≤ (56320 * B) * (Y / L)
  calc
    Mass ≤ ((56320 * B) * Y) / L :=
      (le_div_iff₀ hLog).2 hBoundL
    _ = (56320 * B) * (Y / L) := by ring

#print axioms eiravel_selected_full_power_exception_fixed_constant

end PaperB.M4B
