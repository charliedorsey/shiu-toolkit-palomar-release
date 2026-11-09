module

public import Mathlib

public section

namespace PaperB.M4B

/-- The x<z^160 gate absorbs growth and logarithm at exponent 1/1280. -/
theorem eiravel_growth_log_absorb
    (x z : ℕ) (hz : 1 ≤ z) (hxz : x < z ^ 160) :
    (x : ℝ) ^ (1/1280 : ℝ) * Real.log (x : ℝ) ≤
      1280 * (z : ℝ) ^ (1/4 : ℝ) := by
  have hxnonneg : (0 : ℝ) ≤ x := by positivity
  have hznonneg : (0 : ℝ) ≤ z := by positivity
  have hzx : (x : ℝ) ≤ (z : ℝ) ^ (160 : ℕ) := by
    exact_mod_cast hxz.le
  have hlog :
      Real.log (x : ℝ) ≤ 1280 * (x : ℝ) ^ (1/1280 : ℝ) := by
    have hh := Real.log_le_rpow_div hxnonneg
      (by norm_num : (0 : ℝ) < 1/1280)
    convert hh using 1 <;> ring
  have hpow :
      (x : ℝ) ^ (1/640 : ℝ) ≤
        ((z : ℝ) ^ (160 : ℕ)) ^ (1/640 : ℝ) :=
    Real.rpow_le_rpow hxnonneg hzx (by norm_num)
  have hxbound :
      (x : ℝ) ^ (1/640 : ℝ) ≤ (z : ℝ) ^ (1/4 : ℝ) := by
    convert hpow using 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hznonneg]
    norm_num
  calc
    (x : ℝ) ^ (1/1280 : ℝ) * Real.log (x : ℝ) ≤
      (x : ℝ) ^ (1/1280 : ℝ) *
        (1280 * (x : ℝ) ^ (1/1280 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hxnonneg _)
    _ = 1280 * (x : ℝ) ^ (1/640 : ℝ) := by
      calc
        _ = 1280 * ((x : ℝ) ^ (1/1280 : ℝ) *
            (x : ℝ) ^ (1/1280 : ℝ)) := by ring
        _ = 1280 * (x : ℝ) ^ (1/640 : ℝ) := by
          rw [← Real.rpow_add_of_nonneg hxnonneg
            (by norm_num : (0 : ℝ) ≤ 1/1280)
            (by norm_num : (0 : ℝ) ≤ 1/1280)]
          norm_num
    _ ≤ 1280 * (z : ℝ) ^ (1/4 : ℝ) :=
      mul_le_mul_of_nonneg_left hxbound (by norm_num)

#print axioms eiravel_growth_log_absorb
end PaperB.M4B
