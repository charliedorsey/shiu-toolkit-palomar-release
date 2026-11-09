module

public import ShiuPublic.QuadraticEulerBudget
public import ShiuPublic.RankinPowerGate

public section

namespace Shiu
open scoped BigOperators

theorem shifted_quadratic_uniform
    (S : Finset ℕ) (P : ℕ) (A D δ : ℝ)
    (hA : 0 ≤ A) (hP : 1 ≤ P)
    (hS : ∀ q ∈ S, 2 ≤ q ∧ q ≤ P)
    (hpow : ∀ q ∈ S, (q : ℝ)^δ ≤ Real.exp D) :
    (∑ q ∈ S, 2 * (A / (q : ℝ)^(1-δ))^2) ≤
      2 * A^2 * Real.exp (2*D) := by
  have hlocal (q : ℕ) (hq : q ∈ S) :
      2 * (A / (q : ℝ)^(1-δ))^2 ≤
        (2 * A^2 * Real.exp (2*D)) * ((q : ℝ)^2)⁻¹ := by
    have hqpos : (0 : ℝ) < q := by
      exact_mod_cast (by have hh := (hS q hq).1; omega : 0 < q)
    have hqr : (q : ℝ)^(1-δ) = (q : ℝ) / (q : ℝ)^δ := by
      rw [Real.rpow_sub hqpos, Real.rpow_one]
    have hqdelta : 0 < (q : ℝ)^δ := Real.rpow_pos_of_pos hqpos _
    have h := hpow q hq
    rw [hqr]
    have hid : Real.exp (2*D) = (Real.exp D)^2 := by
      rw [show 2*D = D+D by ring, Real.exp_add]
      ring
    rw [hid]
    have hsq : ((q : ℝ)^δ)^2 ≤ (Real.exp D)^2 :=
      pow_le_pow_left₀ hqdelta.le h 2
    have hden : 0 < (q : ℝ)^2 := sq_pos_of_pos hqpos
    apply (le_div_iff₀ hden).2
    field_simp
    nlinarith [mul_nonneg (sq_nonneg A) (sub_nonneg.mpr hsq)]
  calc
    _ ≤ ∑ q ∈ S, (2*A^2*Real.exp (2*D))*((q : ℝ)^2)⁻¹ := by
      apply Finset.sum_le_sum
      intro q hq
      exact hlocal q hq
    _ ≤ 2*A^2*Real.exp (2*D) :=
      finite_quadratic_euler_budget S P _ hP (by positivity) hS

#print axioms Shiu.shifted_quadratic_uniform
end Shiu
