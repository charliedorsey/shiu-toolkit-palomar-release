module

public import Shiu.ModulusOneGeometry

public section

/-!
# Literal x^(1/4) < y geometry for the nine Bertrand primes

No asymptotic estimate is introduced. The constant 512^4 is
explicit; the final theorem can take a uniform max threshold.
-/
namespace Shiu.API

private theorem real_quarter_fourth (z : ℝ) (hz : 0 ≤ z) :
    (z ^ (1 / 4 : ℝ)) ^ 4 = z := by
  calc
    (z ^ (1 / 4 : ℝ)) ^ 4 =
        z ^ ((1 / 4 : ℝ) * 4) := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_mul hz (1 / 4 : ℝ) 4).symm
    _ = z := by norm_num

private theorem real_threequarters_fourth (z : ℝ) (hz : 0 ≤ z) :
    (z ^ (3 / 4 : ℝ)) ^ 4 = z ^ 3 := by
  calc
    (z ^ (3 / 4 : ℝ)) ^ 4 =
        z ^ ((3 / 4 : ℝ) * 4) := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_mul hz (3 / 4 : ℝ) 4).symm
    _ = z ^ 3 := by norm_num

/-- If y exceeds the explicit constant 512^4, the integer scale
N = floor(sqrt y) satisfies both k=1 covering conditions. -/
theorem modulus_one_real_geometry
    (x y : ℕ) (hxy : (x : ℝ) ^ (1 / 4 : ℝ) < (y : ℝ))
    (hyLarge : 512 ^ 4 < y) :
    ∃ N : ℕ, 0 < N ∧ x < (N + 1) ^ 9 ∧
      (512 * N : ℝ) < (y : ℝ) ^ (3 / 4 : ℝ) := by
  have hxfourR : (x : ℝ) < (y : ℝ) ^ 4 := by
    have h := Real.rpow_lt_rpow
      (Real.rpow_nonneg (Nat.cast_nonneg x) (1 / 4 : ℝ))
      hxy (by norm_num : (0 : ℝ) < 4)
    have hpow : ((x : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℝ) = (x : ℝ) := by
      rw [← Real.rpow_mul (Nat.cast_nonneg x)]
      norm_num
    rw [hpow] at h
    have hyPow : (y : ℝ) ^ (4 : ℝ) = (y : ℝ) ^ (4 : ℕ) := by
      simpa using (Real.rpow_natCast (y : ℝ) 4)
    rw [hyPow] at h
    exact h
  have hxfour : x < y ^ 4 := by
    exact_mod_cast hxfourR
  obtain ⟨hN, hprod, hfour⟩ :=
    modulus_one_natural_geometry x y hxfour hyLarge
  refine ⟨Nat.sqrt y, hN, hprod, ?_⟩
  have hfourR :
      ((512 * Nat.sqrt y : ℕ) : ℝ) ^ 4 <
        ((y : ℝ) ^ (3 / 4 : ℝ)) ^ 4 := by
    rw [real_threequarters_fourth (y : ℝ) (Nat.cast_nonneg y)]
    exact_mod_cast hfour
  have hroot :=
    lt_of_pow_lt_pow_left₀ 4
      (Real.rpow_nonneg (Nat.cast_nonneg y) (3 / 4 : ℝ)) hfourR
  simpa [Nat.cast_mul] using hroot

/-- Explicit uniform x cutoff implies the required large-y window. -/
theorem modulus_one_large_y_of_large_x
    (x y : ℕ)
    (hx : (512 ^ 4) ^ 4 ≤ x)
    (hxy : (x : ℝ) ^ (1 / 4 : ℝ) < (y : ℝ)) :
    512 ^ 4 < y := by
  have hxfour : ((512 ^ 4 : ℕ) : ℝ) ^ 4 ≤
      ((x : ℝ) ^ (1 / 4 : ℝ)) ^ 4 := by
    rw [real_quarter_fourth (x : ℝ) (Nat.cast_nonneg x)]
    exact_mod_cast hx
  have hroot : ((512 ^ 4 : ℕ) : ℝ) ≤
      (x : ℝ) ^ (1 / 4 : ℝ) :=
    le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0)
      (Real.rpow_nonneg (Nat.cast_nonneg x) (1 / 4 : ℝ)) hxfour
  exact_mod_cast lt_of_le_of_lt hroot hxy

#print axioms modulus_one_real_geometry
#print axioms modulus_one_large_y_of_large_x
end Shiu.API
