module

public import ShiuPublic.PrimePowerLocal

public section

/-! Prime-power Euler tails at an arbitrary positive real scale,
including the shifted Rankin denominator p^(1-delta). -/

namespace Shiu

/-- Universal local higher-power tail with an arbitrary denominator R.
This is independent of any squarefree support hypothesis. -/
theorem power_tail_at_real_scale
    (f : ℕ → ℝ) (A R : ℝ) (p N : ℕ)
    (hA : 0 ≤ A) (hR : 0 < R) (hhalf : 2 * A ≤ R)
    (hpower : ∀ m : ℕ, 2 ≤ m → f (p ^ m) ≤ A ^ m) :
    (∑ j ∈ Finset.range N,
      f (p ^ (j + 2)) / R ^ (j + 2)) ≤ 2 * (A / R) ^ 2 := by
  have ht0 : 0 ≤ A / R := div_nonneg hA hR.le
  have ht : A / R ≤ 1 / 2 := by
    apply (div_le_iff₀ hR).mpr
    linarith
  calc
    (∑ j ∈ Finset.range N, f (p ^ (j + 2)) / R ^ (j + 2)) ≤
      ∑ j ∈ Finset.range N, (A / R) ^ (j + 2) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [div_pow]
        exact div_le_div_of_nonneg_right (hpower (j + 2) (by omega))
          (pow_nonneg hR.le _)
    _ ≤ 2 * (A / R) ^ 2 :=
      geometric_tail_le_two_square _ ht0 ht N

/-- The same estimate with the exact Rankin power p^(1-delta). -/
theorem prime_power_tail_at_rankin_scale
    (f : ℕ → ℝ) (A δ : ℝ) (p N : ℕ)
    (hA : 0 ≤ A) (hp : 0 < p)
    (hhalf : 2 * A ≤ (p : ℝ) ^ (1 - δ))
    (hpower : ∀ m : ℕ, 2 ≤ m → f (p ^ m) ≤ A ^ m) :
    (∑ j ∈ Finset.range N,
      f (p ^ (j + 2)) /
        (p : ℝ) ^ ((j + 2 : ℕ) * (1 - δ))) ≤
      2 * (A / (p : ℝ) ^ (1 - δ)) ^ 2 := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hden (m : ℕ) :
      (p : ℝ) ^ ((m : ℕ) * (1 - δ)) =
        ((p : ℝ) ^ (1 - δ)) ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpR.le]
    congr 1
    push_cast
    ring
  simp_rw [hden]
  exact power_tail_at_real_scale f A ((p : ℝ) ^ (1 - δ)) p N
    hA (Real.rpow_pos_of_pos hpR _) hhalf hpower

#print axioms Shiu.power_tail_at_real_scale
#print axioms Shiu.prime_power_tail_at_rankin_scale
end Shiu
