module

public import PaperB.M4B.ShiuProgression

public section

/-!
Class IV strengthened large-prime gate: it uses the *unchanged* original
source shell partition and only increases the eventual x-threshold.
-/

open Finset Nat Real Filter

namespace Shiu

private theorem threshold_tends_to_infinity :
    Tendsto PaperB.M4B.shiuLogLogSmoothThreshold atTop atTop := by
  unfold PaperB.M4B.shiuLogLogSmoothThreshold
  apply tendsto_nat_floor_atTop.comp
  have hlog :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog :
      Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  exact hlog.atTop_mul_atTop₀ hloglog

/-- The source's *existing* lower shell threshold is eventually at
least exp(4D(A)), with no alteration to the shell partition. -/
theorem eventually_strong_shell_threshold (A : ℝ) :
    ∀ᶠ x : ℕ in atTop,
      4 ≤ PaperB.M4B.shiuLogLogSmoothThreshold x ∧
      Real.exp (4 * PaperB.M4B.classIVRankinD A) ≤
        (PaperB.M4B.shiuLogLogSmoothThreshold x : ℝ) := by
  let M : ℕ :=
    max 4 ⌈Real.exp (4 * PaperB.M4B.classIVRankinD A)⌉₊
  have hM := threshold_tends_to_infinity.eventually
    (eventually_ge_atTop M)
  filter_upwards [hM] with x hx
  have h4 : 4 ≤ PaperB.M4B.shiuLogLogSmoothThreshold x :=
    (le_max_left 4 ⌈Real.exp (4 * PaperB.M4B.classIVRankinD A)⌉₊).trans hx
  have hceil :
      ⌈Real.exp (4 * PaperB.M4B.classIVRankinD A)⌉₊ ≤
        PaperB.M4B.shiuLogLogSmoothThreshold x :=
    (le_max_right 4 ⌈Real.exp (4 * PaperB.M4B.classIVRankinD A)⌉₊).trans hx
  exact ⟨h4, (Nat.le_ceil _).trans (by exact_mod_cast hceil)⟩

/-- Direct strong gate at each original shell upper endpoint,
with no shell index or cutoff redefinition. -/
theorem strong_gate_at_original_shell
    (A : ℝ) {x z r : ℕ}
    (hz : 2 ≤ z)
    (hL4 : 4 ≤ PaperB.M4B.shiuLogLogSmoothThreshold x)
    (hlarge :
      Real.exp (4 * PaperB.M4B.classIVRankinD A) ≤
        (PaperB.M4B.shiuLogLogSmoothThreshold x : ℝ))
    (hr : r ∈ Finset.Icc 2 (PaperB.M4B.shiuClassIVR0 x z)) :
    Real.exp (4 * PaperB.M4B.classIVRankinD A) ≤
      (PaperB.M4B.classIVShellUpper z r : ℝ) := by
  let L := PaperB.M4B.shiuLogLogSmoothThreshold x
  have hr0 : r ≤ PaperB.M4B.shiuClassIVR0 x z :=
    (Finset.mem_Icc.mp hr).2
  have hLpos : 0 < L := by dsimp [L]; omega
  have hLpow0 : L ^ (PaperB.M4B.shiuClassIVR0 x z) ≤ z := by
    dsimp [PaperB.M4B.shiuClassIVR0]
    exact Nat.pow_log_le_self L (by omega : z ≠ 0)
  have hLpow : L ^ r ≤ z :=
    (Nat.pow_le_pow_right hLpos hr0).trans hLpow0
  have hLp : L ≤ PaperB.M4B.classIVShellUpper z r := by
    dsimp [PaperB.M4B.classIVShellUpper]
    exact (Nat.le_nthRoot_iff (by have hr2 := (Finset.mem_Icc.mp hr).1; omega)).2 hLpow
  exact hlarge.trans (by exact_mod_cast hLp)

#print axioms Shiu.eventually_strong_shell_threshold
#print axioms Shiu.strong_gate_at_original_shell
end Shiu
