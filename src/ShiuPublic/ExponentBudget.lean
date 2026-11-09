module

public import Mathlib

public section

/-! A completely source-independent admissible exponent budget for the
squarefree Shiu cutoff architecture. These margins only concern powers;
the logarithmic thresholds and finite cutoff ceilings must still be paid. -/

namespace Shiu

/-- Cutoff exponent for a convenient, nonoptimal two-parameter region. -/
noncomputable def cutoffExponent (beta : ℝ) : ℝ := (1 - beta) / 4

/-- A sufficient, strictly interior exponent region:
  theta*(1-beta)>1/40, 0<=beta<1.
It is weaker than the ideal near-boundary delta=(1-beta)/2. -/
theorem exponent_budget (theta beta : ℝ)
    (hb0 : 0 ≤ beta) (hb1 : beta < 1)
    (ht : 0 < theta)
    (hmargin : (1 / 40 : ℝ) < theta * (1 - beta)) :
    0 < cutoffExponent beta ∧
    beta + 2 * cutoffExponent beta < 1 ∧
    beta + cutoffExponent beta < 1 ∧
    1 < 160 * theta * cutoffExponent beta := by
  unfold cutoffExponent
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith [mul_pos ht (sub_pos.mpr hb1)]

/-- The same budget presented with an explicit theta lower bound. -/
theorem exponent_budget_of_theta_bound (theta beta : ℝ)
    (hb0 : 0 ≤ beta) (hb1 : beta < 1)
    (ht : (40 * (1 - beta))⁻¹ < theta) :
    0 < cutoffExponent beta ∧
    beta + 2 * cutoffExponent beta < 1 ∧
    beta + cutoffExponent beta < 1 ∧
    1 < 160 * theta * cutoffExponent beta := by
  have hb : 0 < 40 * (1 - beta) := by positivity
  have ht0 : 0 < theta := lt_trans (inv_pos.mpr hb) ht
  have hm : (1 / 40 : ℝ) < theta * (1 - beta) := by
    have h1 : 1 / (40 * (1 - beta)) < theta := by
      simpa [one_div] using ht
    have h2 := (div_lt_iff₀ hb).mp h1
    nlinarith [mul_pos (by norm_num : (0 : ℝ) < 40) (sub_pos.mpr hb1)]
  exact exponent_budget theta beta hb0 hb1 ht0 hm

#print axioms Shiu.exponent_budget
#print axioms Shiu.exponent_budget_of_theta_bound
end Shiu
