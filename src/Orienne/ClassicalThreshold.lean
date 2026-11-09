module

public import ShiuPublic.VaelisClassIVEndpointCorrection
public import PaperB.M4B.ShiuProgression

public section

open Filter Nat Real
namespace PaperB.M4B

private theorem classicalThreshold_tends_to_infinity :
    Tendsto shiuLogLogSmoothThreshold atTop atTop := by
  unfold shiuLogLogSmoothThreshold
  apply tendsto_nat_floor_atTop.comp
  have hlog :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog :
      Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  exact hlog.atTop_mul_atTop₀ hloglog

/-- The actual unrestricted classical Class IV Rankin threshold
is eventually satisfied uniformly in the weight f and the anchor. -/
theorem orienne_classical_shiu_eventually_strong_threshold (A : ℝ) :
    ∃ X0 : ℕ, ∀ x : ℕ, X0 ≤ x →
      4 ≤ shiuLogLogSmoothThreshold x ∧
      Real.exp (4 * classicalClassIVRankinD A) ≤
        (shiuLogLogSmoothThreshold x : ℝ) := by
  let M : ℕ :=
    max 4 ⌈Real.exp (4 * classicalClassIVRankinD A)⌉₊
  have hM := classicalThreshold_tends_to_infinity.eventually
    (eventually_ge_atTop M)
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.1 hM
  refine ⟨X0, ?_⟩
  intro x hx
  have hMx : M ≤ shiuLogLogSmoothThreshold x := hX0 x hx
  have h4 : 4 ≤ shiuLogLogSmoothThreshold x :=
    (le_max_left 4 ⌈Real.exp (4 * classicalClassIVRankinD A)⌉₊).trans hMx
  have hceil :
      ⌈Real.exp (4 * classicalClassIVRankinD A)⌉₊ ≤
        shiuLogLogSmoothThreshold x :=
    (le_max_right 4 ⌈Real.exp (4 * classicalClassIVRankinD A)⌉₊).trans hMx
  exact ⟨h4, (Nat.le_ceil _).trans (by exact_mod_cast hceil)⟩

#print axioms orienne_classical_shiu_eventually_strong_threshold
end PaperB.M4B
