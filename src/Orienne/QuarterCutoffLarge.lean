module

public import PaperB.M4B.ShiuProgression

public section

open Filter Nat Real

namespace PaperB.M4B

/-- Publication-facing literal naturalized source square-root scale. -/
@[expose] noncomputable def orienneQuarterW (y : ℕ) : ℕ :=
  ⌈((y : ℝ) ^ (1 / 80 : ℝ))⌉₊

/-- Literal square cutoff used in the original fixed-quarter Shiu supplier. -/
@[expose] noncomputable def orienneQuarterZ (y : ℕ) : ℕ :=
  (orienneQuarterW y) ^ 2

/-- The original naturalized cutoff eventually exceeds the unrestricted
Class I endpoint gate exp(4), without changing the chosen power scale. -/
theorem orienne_quarter_cutoff_eventually_exp_four :
    ∀ᶠ y : ℕ in atTop,
      Real.exp (4 : ℝ) ≤ (orienneQuarterZ y : ℝ) := by
  have hT : Tendsto
      (fun y : ℕ => (y : ℝ) ^ (1 / 80 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 / 80 : ℝ))).comp
      tendsto_natCast_atTop_atTop
  have hEvent :=
    hT.eventually (eventually_ge_atTop (Real.exp (2 : ℝ)))
  filter_upwards [hEvent] with y hy
  have hceil : (y : ℝ) ^ (1 / 80 : ℝ) ≤
      (orienneQuarterW y : ℝ) := by
    unfold orienneQuarterW
    exact Nat.le_ceil _
  have hw : Real.exp (2 : ℝ) ≤ (orienneQuarterW y : ℝ) :=
    hy.trans hceil
  calc
    Real.exp (4 : ℝ) = (Real.exp (2 : ℝ)) ^ 2 := by
      rw [show (4 : ℝ) = 2 + 2 by norm_num, Real.exp_add]
      ring
    _ ≤ (orienneQuarterW y : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Real.exp_nonneg _) hw 2
    _ = (orienneQuarterZ y : ℝ) := by
      simp [orienneQuarterZ]

#print axioms orienne_quarter_cutoff_eventually_exp_four
end PaperB.M4B
