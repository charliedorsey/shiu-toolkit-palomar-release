module

public import Mathlib

public section

namespace Shiu

theorem rankin_delta_quarter
    {D P : ℝ} (hD : 0 < D) (hP : Real.exp (4 * D) ≤ P) :
    0 < D / Real.log P ∧ D / Real.log P ≤ 1 / 4 := by
  have hlog : 4 * D ≤ Real.log P := by
    have he : 0 < Real.exp (4 * D) := Real.exp_pos _
    have hh := Real.log_le_log he hP
    simpa only [Real.log_exp] using hh
  have hlog0 : 0 < Real.log P := by linarith
  constructor
  · positivity
  · apply (div_le_iff₀ hlog0).2
    linarith

theorem rankin_small_power
    {D P q : ℝ} (hD : 0 < D) (hP : Real.exp (4 * D) ≤ P)
    (hq : 1 ≤ q) (hqP : q ≤ P) :
    q ^ (D / Real.log P) ≤ Real.exp D := by
  obtain ⟨hdelta, _⟩ := rankin_delta_quarter hD hP
  have hP1 : 1 < P := by
    have he : 1 < Real.exp (4 * D) := by
      calc
        (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ < Real.exp (4 * D) := Real.exp_lt_exp.mpr (by linarith)
    exact lt_of_lt_of_le he hP
  have hlogP : 0 < Real.log P := Real.log_pos hP1
  have hq0 : 0 < q := by linarith
  rw [Real.rpow_def_of_pos hq0]
  apply Real.exp_le_exp.mpr
  have hlogs : Real.log q ≤ Real.log P := Real.log_le_log hq0 hqP
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hh := mul_le_mul_of_nonneg_left hlogs hdelta.le
  have heq : Real.log P * (D / Real.log P) = D := by field_simp
  nlinarith

#print axioms Shiu.rankin_delta_quarter
#print axioms Shiu.rankin_small_power
end Shiu
