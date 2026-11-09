module

public import ShiuPublic.EiravelClassIIIPrimeMass

public section

open scoped BigOperators Topology
open Finset Nat Real Filter

namespace PaperB.M4B

/-- Fixed-exponent Euler correction constant for the unrestricted all-power
Class III count. It depends on neither x, z nor k. -/
@[expose] noncomputable def eiravelEulerC : ℝ :=
  (1 - (2 : ℝ) ^ (-(1 / 8 : ℝ)))⁻¹

theorem eiravelEulerC_pos : 0 < eiravelEulerC := by
  unfold eiravelEulerC
  apply inv_pos.mpr
  apply sub_pos.mpr
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- Source-level fixed-exponent prime Euler mass is eventually absorbed,
uniformly without reference to k, z, or squarefree support. -/
theorem eiravel_prime_mass_fixed_eta_absorption :
    ∃ X0 : ℕ, ∀ x : ℕ, X0 ≤ x →
      eiravelEulerC *
        primeRankinMass (shiuLogLogSmoothThreshold x) (1 / 8 : ℝ) ≤
          Real.log (x : ℝ) / 1280 := by
  obtain ⟨X1, hX1⟩ := eiravel_primeRankinMass_loglog_upper
  let C : ℝ := eiravelEulerC
  have hC : 0 < C := eiravelEulerC_pos
  let K : ℝ := 32 + 5120 * C
  have hKpos : 0 < K := by dsimp [K]; positivity
  let X2 : ℕ := ⌈Real.exp (Real.exp (K ^ 2))⌉₊
  refine ⟨max X1 X2, ?_⟩
  intro x hx
  have hx1 : X1 ≤ x := (le_max_left X1 X2).trans hx
  have hx2 : X2 ≤ x := (le_max_right X1 X2).trans hx
  have hbaseceil :
      Real.exp (Real.exp (K ^ 2)) ≤ (X2 : ℝ) := by
    dsimp [X2]
    exact Nat.le_ceil _
  have hxbase :
      Real.exp (Real.exp (K ^ 2)) ≤ (x : ℝ) :=
    hbaseceil.trans (by exact_mod_cast hx2)
  have hxpos : (0 : ℝ) < (x : ℝ) :=
    (Real.exp_pos _).trans_le hxbase
  have hlogx :
      Real.exp (K ^ 2) ≤ Real.log (x : ℝ) := by
    rw [← Real.exp_le_exp, Real.exp_log hxpos]
    exact hxbase
  have hlogpos : 0 < Real.log (x : ℝ) :=
    (Real.exp_pos _).trans_le hlogx
  have hll :
      K ^ 2 ≤ Real.log (Real.log (x : ℝ)) := by
    rw [← Real.exp_le_exp, Real.exp_log hlogpos]
    exact hlogx
  let r : ℝ := Real.sqrt (Real.log (Real.log (x : ℝ)))
  have hll0 : 0 ≤ Real.log (Real.log (x : ℝ)) :=
    (sq_nonneg K).trans hll
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrsq : r ^ 2 = Real.log (Real.log (x : ℝ)) := by
    dsimp [r]
    exact Real.sq_sqrt hll0
  have hroot : K ≤ r := by nlinarith
  have hrpos : 0 < r := hKpos.trans_le hroot
  have hr32 : (32 : ℝ) ≤ r := by
    dsimp [K] at hroot
    nlinarith
  have hrlarge : 5120 * C ≤ r := by
    dsimp [K] at hroot
    nlinarith
  have hdel : 4 / r ≤ (1 / 8 : ℝ) := by
    rw [div_le_iff₀ hrpos]
    nlinarith
  have hprime :
      primeRankinMass (shiuLogLogSmoothThreshold x) (1 / 8 : ℝ) ≤
        primeRankinMass (shiuLogLogSmoothThreshold x) (4 / r) := by
    unfold primeRankinMass
    apply Finset.sum_le_sum
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primesLE hp
    have hpge : (1 : ℝ) ≤ p := by exact_mod_cast hpprime.one_le
    exact Real.rpow_le_rpow_of_exponent_le hpge (by linarith)
  have hS1 :
      primeRankinMass (shiuLogLogSmoothThreshold x) (4 / r) ≤
        4 * Real.log (x : ℝ) / r := by
    simpa only [r] using hX1 x hx1
  have hprimebound :
      primeRankinMass (shiuLogLogSmoothThreshold x) (1 / 8 : ℝ) ≤
        4 * Real.log (x : ℝ) / r := hprime.trans hS1
  have hcoef : 4 * C / r ≤ (1 / 1280 : ℝ) := by
    rw [div_le_iff₀ hrpos]
    nlinarith
  calc
    eiravelEulerC *
      primeRankinMass (shiuLogLogSmoothThreshold x) (1 / 8 : ℝ) ≤
        C * (4 * Real.log (x : ℝ) / r) :=
      mul_le_mul_of_nonneg_left hprimebound hC.le
    _ = (4 * C / r) * Real.log (x : ℝ) := by ring
    _ ≤ (1 / 1280 : ℝ) * Real.log (x : ℝ) :=
      mul_le_mul_of_nonneg_right hcoef hlogpos.le
    _ = Real.log (x : ℝ) / 1280 := by ring

#print axioms eiravel_prime_mass_fixed_eta_absorption
end PaperB.M4B
