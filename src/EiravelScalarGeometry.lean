module

public import Mathlib

public section

namespace PaperB.M4B

/-- A scale-free elementary inequality for the full-power reciprocal
and sharp AP endpoint losses. -/
theorem eiravel_quartic_ratio_budget
    {U T z V : ℝ}
    (hU : 1 ≤ U)
    (hUT : U ^ 2 ≤ T)
    (hTz : T ^ 2 ≤ z)
    (hz64 : z ≤ 64 * U ^ 4)
    (hV : 0 ≤ V)
    (hVfour : V ^ 4 = z) :
    V * (U / T + 2 / (U + 1) + 4 * (T + 1) / z) ≤ 44 := by
  have hUp : 0 < U := by linarith
  have hTp : 0 < T := by nlinarith [sq_nonneg U]
  have hzp : 0 < z := by nlinarith [sq_nonneg T]
  have hUT' : U ≤ T := by nlinarith [sq_nonneg (U - 1)]
  have hTtwice : T + 1 ≤ 2 * T := by nlinarith [sq_nonneg U]
  have hVpow : V ^ 4 ≤ (4 * U) ^ 4 := by
    calc
      V ^ 4 = z := hVfour
      _ ≤ 64 * U ^ 4 := hz64
      _ ≤ (4 * U) ^ 4 := by
        nlinarith [pow_nonneg (by linarith : 0 ≤ U) 4]
  have hVbound : V ≤ 4 * U :=
    le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by positivity) hVpow
  have h1num : V * U ≤ 4 * T := by
    have hm := mul_le_mul_of_nonneg_right hVbound hUp.le
    nlinarith
  have h1 : V * (U / T) ≤ 4 := by
    calc
      _ = (V * U) / T := by ring
      _ ≤ 4 := (div_le_iff₀ hTp).mpr (by nlinarith [h1num])
  have h2num : V * 2 ≤ 8 * (U + 1) := by nlinarith [hVbound]
  have h2 : V * (2 / (U + 1)) ≤ 8 := by
    calc
      _ = (V * 2) / (U + 1) := by ring
      _ ≤ 8 := (div_le_iff₀ (by linarith : 0 < U + 1)).mpr
        (by nlinarith [h2num])
  have hVT : V * (T + 1) ≤ 8 * U * T := by
    calc
      V * (T + 1) ≤ (4 * U) * (T + 1) :=
        mul_le_mul_of_nonneg_right hVbound (by linarith)
      _ ≤ (4 * U) * (2 * T) :=
        mul_le_mul_of_nonneg_left hTtwice (by positivity)
      _ = 8 * U * T := by ring
  have hUtt : U * T ≤ T ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ T-U) (by linarith : 0 ≤ T)]
  have h3num : V * 4 * (T + 1) ≤ 32 * z := by
    nlinarith [hVT, hUtt, hTz]
  have h3 : V * (4 * (T + 1) / z) ≤ 32 := by
    calc
      _ = (V * 4 * (T + 1)) / z := by ring
      _ ≤ 32 := (div_le_iff₀ hzp).mpr (by nlinarith [h3num])
  calc
    V * (U / T + 2 / (U + 1) + 4 * (T + 1) / z) =
        V * (U / T) + V * (2 / (U + 1)) +
          V * (4 * (T + 1) / z) := by ring
    _ ≤ 44 := by linarith

/-- The literal nested integer square roots satisfy the quartic budget,
without enlarging the exceptional prime family. -/
theorem eiravel_nat_sqrt_ratio_budget (z : ℕ) (hz : 4 ≤ z) :
    (z : ℝ) ^ (1/4 : ℝ) *
      (((Nat.sqrt (Nat.sqrt z) : ℕ) : ℝ) / (Nat.sqrt z : ℝ) +
       2 / (((Nat.sqrt (Nat.sqrt z) + 1 : ℕ) : ℝ)) +
       4 * (((Nat.sqrt z + 1 : ℕ) : ℝ)) / (z : ℝ)) ≤ 44 := by
  let T : ℕ := Nat.sqrt z
  let U : ℕ := Nat.sqrt T
  have hTnat : 2 ≤ T := by
    dsimp [T]
    exact Nat.le_sqrt'.mpr (by nlinarith)
  have hUnat : 1 ≤ U := by
    dsimp [U]
    exact Nat.le_sqrt'.mpr (by nlinarith)
  have hUTnat : U ^ 2 ≤ T := Nat.sqrt_le' T
  have hTznat : T ^ 2 ≤ z := Nat.sqrt_le' z
  have hTupperNat : T < (U + 1) ^ 2 := Nat.lt_succ_sqrt' T
  have hzupperNat : z < (T + 1) ^ 2 := Nat.lt_succ_sqrt' z
  have hU : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hUnat
  have hUT : (U : ℝ) ^ 2 ≤ (T : ℝ) := by exact_mod_cast hUTnat
  have hTz : (T : ℝ) ^ 2 ≤ (z : ℝ) := by exact_mod_cast hTznat
  have hTupper : (T : ℝ) < ((U : ℝ) + 1) ^ 2 := by
    exact_mod_cast hTupperNat
  have hzupper : (z : ℝ) < ((T : ℝ) + 1) ^ 2 := by
    exact_mod_cast hzupperNat
  have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast (by omega : 1 ≤ T)
  have hTfour : (T : ℝ) ≤ 4 * (U : ℝ) ^ 2 := by nlinarith
  have hTplus : (T : ℝ) + 1 ≤ 8 * (U : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (U : ℝ)]
  have hsq : ((T : ℝ) + 1) ^ 2 ≤ (8 * (U : ℝ) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hTplus 2
  have hz64 : (z : ℝ) ≤ 64 * (U : ℝ) ^ 4 := by
    nlinarith [hsq]
  have hznonneg : (0 : ℝ) ≤ (z : ℝ) := by positivity
  have hVnonneg : 0 ≤ (z : ℝ) ^ (1/4 : ℝ) := by positivity
  have hVfour : ((z : ℝ) ^ (1/4 : ℝ)) ^ 4 = (z : ℝ) := by
    calc
      ((z : ℝ) ^ (1/4 : ℝ)) ^ 4 =
        ((z : ℝ) ^ (1/4 : ℝ)) ^ (4:ℝ) :=
          (Real.rpow_natCast _ 4).symm
      _ = (z : ℝ) ^ ((1/4 : ℝ) * 4) :=
          (Real.rpow_mul hznonneg _ _).symm
      _ = z := by norm_num
  have hq := eiravel_quartic_ratio_budget
    hU hUT hTz hz64 hVnonneg hVfour
  simpa only [T, U, Nat.cast_add, Nat.cast_one] using hq

#print axioms eiravel_quartic_ratio_budget
#print axioms eiravel_nat_sqrt_ratio_budget

end PaperB.M4B
