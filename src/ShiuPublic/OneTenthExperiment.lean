module

/-
Paper B M4B-CORE S13: fixed-quarter progression theorem.
Authorized surface: exact M4B0 ledger row S13 only.

This module consumes the paid S12 assembly theorem.  Private scalar lemmas
naturalize the source cutoff z = y^(1/40); no new analytic ingredient is
introduced.
-/

public import PaperB.M4B.ShiuAssemble
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section

open scoped BigOperators
open Finset Nat Real Filter
open ArithmeticFunction

noncomputable section

namespace PaperB
namespace M4B

/-- Natural square-root representative of the source scale y^(1/40). -/
private def fixedTenthW (y : ℕ) : ℕ :=
  ⌈((y : ℝ) ^ (1 / 32 : ℝ))⌉₊

/-- Naturalized source cutoff z ~= y^(1/40), chosen as a square so that
Nat.sqrt is exact in the S12 logarithmic interfaces. -/
private def fixedTenthZ (y : ℕ) : ℕ :=
  (fixedTenthW y) ^ 2

private theorem fixedTenth_sqrt_z (y : ℕ) :
    Nat.sqrt (fixedTenthZ y) = fixedTenthW y := by
  unfold fixedTenthZ
  rw [pow_two, Nat.sqrt_eq]

private theorem fixedTenth_w_lower (y : ℕ) :
    (y : ℝ) ^ (1 / 32 : ℝ) ≤ (fixedTenthW y : ℝ) := by
  unfold fixedTenthW
  exact Nat.le_ceil _

private theorem fixedTenth_w_upper
    {y : ℕ} (hy1 : 1 ≤ y) :
    (fixedTenthW y : ℝ) <
      2 * (y : ℝ) ^ (1 / 32 : ℝ) := by
  have hyr : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
  have hpow1 : (1 : ℝ) ≤ (y : ℝ) ^ (1 / 32 : ℝ) := by
    have he : (0 : ℝ) ≤ (1 / 32 : ℝ) := by norm_num
    simpa using Real.one_le_rpow hyr he
  have hc :=
    Nat.ceil_lt_add_one
      (Real.rpow_nonneg (Nat.cast_nonneg y) (1 / 32 : ℝ))
  unfold fixedTenthW
  linarith

private theorem fixedTenth_x_lt_z160
    {x y : ℕ}
    (hxpos : 0 < x)
    (hxy : (x : ℝ) ^ (1 / 10 : ℝ) < (y : ℝ)) :
    x < (fixedTenthZ y) ^ 160 := by
  let w := fixedTenthW y
  have hypos : (0 : ℝ) < (y : ℝ) :=
    lt_of_lt_of_le
      (Real.rpow_pos_of_pos (by exact_mod_cast hxpos) _)
      hxy.le
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hxpos
  have hxy4 :
      (x : ℝ) < (y : ℝ) ^ (10 : ℝ) := by
    have h :=
      Real.rpow_lt_rpow
        (Real.rpow_nonneg hxR.le (1 / 10 : ℝ))
        hxy (by norm_num : (0 : ℝ) < 10)
    calc
      (x : ℝ)
          = ((x : ℝ) ^ (1 / 10 : ℝ)) ^ (10 : ℝ) := by
            rw [← Real.rpow_mul hxR.le]
            norm_num
      _ < (y : ℝ) ^ (10 : ℝ) := h
  have hwlo := fixedTenth_w_lower y
  have hwpos : (0 : ℝ) < (w : ℝ) :=
    lt_of_lt_of_le
      (Real.rpow_pos_of_pos hypos (1 / 32 : ℝ))
      (by simpa [w] using hwlo)
  have hy4w :
      (y : ℝ) ^ (10 : ℝ) ≤ (w : ℝ) ^ (320 : ℝ) := by
    have hp :=
      Real.rpow_le_rpow
        (Real.rpow_nonneg hypos.le (1 / 32 : ℝ))
        (by simpa [w] using hwlo)
        (by norm_num : (0 : ℝ) ≤ 320)
    calc
      (y : ℝ) ^ (10 : ℝ)
          = ((y : ℝ) ^ (1 / 32 : ℝ)) ^ (320 : ℝ) := by
            rw [← Real.rpow_mul hypos.le]
            norm_num
      _ ≤ (w : ℝ) ^ (320 : ℝ) := hp
  have hxwR : (x : ℝ) < (w : ℝ) ^ (320 : ℕ) := by
    calc
      (x : ℝ) < (y : ℝ) ^ (10 : ℝ) := hxy4
      _ ≤ (w : ℝ) ^ (320 : ℝ) := hy4w
      _ = (w : ℝ) ^ (320 : ℕ) := rpow_natCast (w : ℝ) 320
  have hxwNat : x < w ^ 320 := by
    exact_mod_cast hxwR
  unfold fixedTenthZ
  dsimp [w] at hxwNat ⊢
  calc
    x < (fixedTenthW y) ^ 320 := hxwNat
    _ = ((fixedTenthW y) ^ 2) ^ 160 := by
      rw [← pow_mul]

private theorem fixedTenth_log_bounds
    {x y : ℕ}
    (hxpos : 0 < x)
    (hxy : (x : ℝ) ^ (1 / 10 : ℝ) < (y : ℝ))
    (hw2 : 2 ≤ fixedTenthW y) :
    Real.log (x : ℝ) ≤
        320 * Real.log (Nat.sqrt (fixedTenthZ y) : ℝ) ∧
      Real.log (x : ℝ) ≤
        160 * Real.log (fixedTenthZ y : ℝ) := by
  have hxz := fixedTenth_x_lt_z160 hxpos hxy
  have hzpos : 0 < fixedTenthZ y := by
    unfold fixedTenthZ
    positivity
  have hsqrt :
      Nat.sqrt (fixedTenthZ y) = fixedTenthW y :=
    fixedTenth_sqrt_z y
  have hsqrtpos : (0 : ℝ) < (Nat.sqrt (fixedTenthZ y) : ℝ) := by
    rw [hsqrt]
    exact_mod_cast (show 0 < fixedTenthW y by omega)
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hxpos
  have hzR : (0 : ℝ) < (fixedTenthZ y : ℝ) := by exact_mod_cast hzpos
  have hxzR :
      (x : ℝ) < ((fixedTenthZ y) ^ 160 : ℕ) := by
    exact_mod_cast hxz
  have hlogZ :
      Real.log (x : ℝ) <
        Real.log (((fixedTenthZ y) ^ 160 : ℕ) : ℝ) :=
    Real.log_lt_log hxR hxzR
  have hlogZ' :
      Real.log (x : ℝ) <
        160 * Real.log (fixedTenthZ y : ℝ) := by
    simpa [Nat.cast_pow, Real.log_pow] using hlogZ
  have hzsq :
      fixedTenthZ y = (Nat.sqrt (fixedTenthZ y)) ^ 2 := by
    rw [hsqrt]
    rfl
  have hlogSq :
      Real.log (fixedTenthZ y : ℝ) =
        2 * Real.log (Nat.sqrt (fixedTenthZ y) : ℝ) := by
    conv_lhs => rw [hzsq]
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  constructor
  · nlinarith
  · exact hlogZ'.le


private theorem eventually_const_mul_rpow_le_rpow
    {C a b : ℝ} (hC : 0 ≤ C) (hab : a < b) :
    ∀ᶠ t : ℝ in atTop, C * t ^ a ≤ t ^ b := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have ht :=
    (tendsto_rpow_atTop hd).eventually
      (eventually_ge_atTop C)
  filter_upwards [ht, eventually_gt_atTop (0 : ℝ)] with t hCt ht0
  calc
    C * t ^ a ≤ t ^ (b - a) * t ^ a :=
      mul_le_mul_of_nonneg_right hCt (Real.rpow_nonneg ht0.le _)
    _ = t ^ b := by
      rw [← Real.rpow_add ht0]
      congr 1
      ring

private theorem eventually_const_mul_log_le_rpow
    {C b : ℝ} (hC : 0 < C) (hb : 0 < b) :
    ∀ᶠ t : ℝ in atTop, C * Real.log t ≤ t ^ b := by
  have ho :=
    (isLittleO_log_rpow_atTop hb).bound
      (show 0 < (1 / C : ℝ) by positivity)
  filter_upwards [ho, eventually_ge_atTop (1 : ℝ)] with t ht ht1
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hpow0 : 0 ≤ t ^ b := Real.rpow_nonneg (by positivity) _
  rw [Real.norm_eq_abs, abs_of_nonneg hlog0,
    Real.norm_eq_abs, abs_of_nonneg hpow0] at ht
  calc
    C * Real.log t ≤ C * ((1 / C) * t ^ b) :=
      mul_le_mul_of_nonneg_left ht hC.le
    _ = t ^ b := by field_simp [hC.ne']

private theorem fixedTenth_z_upper
    {y : ℕ} (hy1 : 1 ≤ y) :
    (fixedTenthZ y : ℝ) <
      4 * (y : ℝ) ^ (1 / 16 : ℝ) := by
  let w := fixedTenthW y
  let t : ℝ := (y : ℝ) ^ (1 / 32 : ℝ)
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  have hw0 : 0 ≤ (w : ℝ) := by positivity
  have hw := fixedTenth_w_upper hy1
  have hsq : (w : ℝ) ^ 2 < (2 * t) ^ 2 := by
    nlinarith
  have ht2 :
      t ^ 2 = (y : ℝ) ^ (1 / 16 : ℝ) := by
    dsimp [t]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (Nat.cast_nonneg y)]
    congr 1
    norm_num
  unfold fixedTenthZ
  norm_num only [Nat.cast_pow]
  dsimp [w] at hsq ⊢
  rw [show (2 * t) ^ 2 = 4 * t ^ 2 by ring, ht2] at hsq
  exact hsq


private theorem tendsto_shiuLogLogSmoothThreshold :
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

private theorem eventually_fixedTenth_threshold
    (A1 : ℝ) :
    ∀ᶠ x : ℕ in atTop,
      4 ≤ shiuLogLogSmoothThreshold x ∧
      Real.exp (classIVRankinD A1) ≤
        (shiuLogLogSmoothThreshold x : ℝ) := by
  let M : ℕ := max 4 ⌈Real.exp (classIVRankinD A1)⌉₊
  have hM :=
    tendsto_shiuLogLogSmoothThreshold.eventually
      (eventually_ge_atTop M)
  filter_upwards [hM] with x hx
  have h4 : 4 ≤ shiuLogLogSmoothThreshold x :=
    (le_max_left 4 ⌈Real.exp (classIVRankinD A1)⌉₊).trans hx
  have hceil :
      ⌈Real.exp (classIVRankinD A1)⌉₊ ≤
        shiuLogLogSmoothThreshold x :=
    (le_max_right 4 ⌈Real.exp (classIVRankinD A1)⌉₊).trans hx
  have hexpceil :
      Real.exp (classIVRankinD A1) ≤
        (⌈Real.exp (classIVRankinD A1)⌉₊ : ℕ) :=
    Nat.le_ceil _
  refine ⟨h4, ?_⟩
  exact hexpceil.trans (by exact_mod_cast hceil)


private theorem fixedTenth_logx_le_four_logy
    {x y : ℕ}
    (hxpos : 0 < x)
    (hxy : (x : ℝ) ^ (1 / 10 : ℝ) < (y : ℝ)) :
    Real.log (x : ℝ) ≤ 10 * Real.log (y : ℝ) := by
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hxpos
  have hyR : (0 : ℝ) < (y : ℝ) :=
    lt_of_lt_of_le
      (Real.rpow_pos_of_pos hxR (1 / 10 : ℝ))
      hxy.le
  have hxy4 :
      (x : ℝ) < (y : ℝ) ^ (10 : ℕ) := by
    have h :=
      Real.rpow_lt_rpow
        (Real.rpow_nonneg hxR.le (1 / 10 : ℝ))
        hxy (by norm_num : (0 : ℝ) < 10)
    calc
      (x : ℝ)
          = ((x : ℝ) ^ (1 / 10 : ℝ)) ^ (10 : ℝ) := by
            rw [← Real.rpow_mul hxR.le]
            norm_num
      _ < (y : ℝ) ^ (10 : ℝ) := h
      _ = (y : ℝ) ^ (10 : ℕ) := rpow_natCast (y : ℝ) 10
  have hlog :=
    Real.log_lt_log hxR
      (by exact_mod_cast hxy4 :
        (x : ℝ) < (((y : ℕ) ^ 10 : ℕ) : ℝ))
  have hlogpow :
      Real.log ((((y : ℕ) ^ 10 : ℕ) : ℝ)) =
        10 * Real.log (y : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  linarith


private theorem eventually_fixedTenth_basic :
    ∀ᶠ y : ℕ in atTop,
      1 ≤ y ∧
      2 ≤ fixedTenthW y ∧
      4 * (y : ℝ) ^ (1 / 16 : ℝ) ≤ (y : ℝ) ∧
      4 * (y : ℝ) ^ (13 / 16 : ℝ) ≤ (y : ℝ) ∧
      16 * (y : ℝ) ^ (7 / 8 : ℝ) ≤ (y : ℝ) ∧
      160 * Real.log (y : ℝ) ≤ (y : ℝ) ^ (1 / 8 : ℝ) ∧
      10 * Real.log (y : ℝ) ≤ (y : ℝ) ^ (1 / 128 : ℝ) := by
  have h1 : ∀ᶠ y : ℕ in atTop, 1 ≤ y := eventually_ge_atTop 1
  have hwReal :
      ∀ᶠ t : ℝ in atTop, (2 : ℝ) ≤ t ^ (1 / 32 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 32)).eventually
      (eventually_ge_atTop 2)
  have hwNat :
      ∀ᶠ y : ℕ in atTop, 2 ≤ fixedTenthW y := by
    have hcomp :=
      tendsto_natCast_atTop_atTop.eventually hwReal
    filter_upwards [hcomp] with y hy
    have hlo := fixedTenth_w_lower y
    have h2R : (2 : ℝ) ≤ (fixedTenthW y : ℝ) := hy.trans hlo
    exact_mod_cast h2R
  have hz :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_const_mul_rpow_le_rpow
        (C := (4 : ℝ)) (a := (1 / 16 : ℝ)) (b := 1)
        (by norm_num) (by norm_num))
  have hkz :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_const_mul_rpow_le_rpow
        (C := (4 : ℝ)) (a := (13 / 16 : ℝ)) (b := 1)
        (by norm_num) (by norm_num))
  have hz2 :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_const_mul_rpow_le_rpow
        (C := (16 : ℝ)) (a := (7 / 8 : ℝ)) (b := 1)
        (by norm_num) (by norm_num))
  have hlog64 :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_const_mul_log_le_rpow
        (C := (160 : ℝ)) (b := (1 / 8 : ℝ))
        (by norm_num) (by norm_num))
  have hlog4 :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_const_mul_log_le_rpow
        (C := (10 : ℝ)) (b := (1 / 128 : ℝ))
        (by norm_num) (by norm_num))
  filter_upwards [h1, hwNat, hz, hkz, hz2, hlog64, hlog4] with
      y hy1 hyw hyz hykz hyz2 hylog64 hylog4
  simpa only [Real.rpow_one] using
    And.intro hy1
      (And.intro hyw
        (And.intro hyz
          (And.intro hykz
            (And.intro hyz2
              (And.intro hylog64 hylog4)))))


private theorem fixedTenth_z_sq_upper
    {y : ℕ} (hy1 : 1 ≤ y) :
    (fixedTenthZ y : ℝ) ^ 2 <
      16 * (y : ℝ) ^ (1 / 8 : ℝ) := by
  have hz := fixedTenth_z_upper hy1
  have hz0 : 0 ≤ (fixedTenthZ y : ℝ) := by positivity
  have hy0 : 0 ≤ (y : ℝ) ^ (1 / 16 : ℝ) := by positivity
  have hs :=
    (sq_lt_sq₀ hz0
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hy0)).2 hz
  calc
    (fixedTenthZ y : ℝ) ^ 2
        < (4 * (y : ℝ) ^ (1 / 16 : ℝ)) ^ 2 := hs
    _ = 16 * (y : ℝ) ^ (1 / 8 : ℝ) := by
      rw [mul_pow]
      norm_num
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (Nat.cast_nonneg y)]
      congr 1
      norm_num

private theorem fixedTenth_eighth_power_lower
    {y : ℕ} (hy1 : 1 ≤ y) :
    (y : ℝ) ^ (1 / 128 : ℝ) ≤
      (fixedTenthZ y : ℝ) ^ (1 / 8 : ℝ) := by
  let w := fixedTenthW y
  have hy0 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
  have hwlo := fixedTenth_w_lower y
  have hpow :=
    Real.rpow_le_rpow
      (Real.rpow_nonneg hy0 (1 / 32 : ℝ))
      (by simpa [w] using hwlo)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hleft :
      ((y : ℝ) ^ (1 / 32 : ℝ)) ^ (1 / 4 : ℝ) =
        (y : ℝ) ^ (1 / 128 : ℝ) := by
    rw [← Real.rpow_mul hy0]
    congr 1
    norm_num
  have hright :
      (w : ℝ) ^ (1 / 4 : ℝ) =
        (fixedTenthZ y : ℝ) ^ (1 / 8 : ℝ) := by
    unfold fixedTenthZ
    dsimp [w]
    norm_num only [Nat.cast_pow]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (Nat.cast_nonneg (fixedTenthW y))]
    congr 1
    norm_num
  rw [hleft] at hpow
  rw [hright] at hpow
  exact hpow


private theorem fixedTenth_scalar_readiness
    {x y k : ℕ}
    (hx2 : 2 ≤ x)
    (hy1 : 1 ≤ y)
    (hyw : 2 ≤ fixedTenthW y)
    (hzyScale :
      4 * (y : ℝ) ^ (1 / 16 : ℝ) ≤ (y : ℝ))
    (hkzScale :
      4 * (y : ℝ) ^ (13 / 16 : ℝ) ≤ (y : ℝ))
    (hz2Scale :
      16 * (y : ℝ) ^ (7 / 8 : ℝ) ≤ (y : ℝ))
    (hlog64 :
      160 * Real.log (y : ℝ) ≤ (y : ℝ) ^ (1 / 8 : ℝ))
    (hlog4 :
      10 * Real.log (y : ℝ) ≤ (y : ℝ) ^ (1 / 128 : ℝ))
    (hxy : (x : ℝ) ^ (1 / 10 : ℝ) < (y : ℝ))
    (hyx : y ≤ x)
    (hkpos : 0 < k)
    (hky : (k : ℝ) < (y : ℝ) ^ (3 / 4 : ℝ)) :
    let z := fixedTenthZ y
    z ≤ y ∧
    k * z < y ∧
    2 ≤ Nat.sqrt z ∧
    x < z ^ 160 ∧
    (z : ℝ) ≤
      ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ) ∧
    Real.log (x : ℝ) ≤ 320 * Real.log (Nat.sqrt z : ℝ) ∧
    Real.log (x : ℝ) ≤ 160 * Real.log (z : ℝ) ∧
    (z : ℝ) ^ 2 ≤
      (y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ)) ∧
    ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 8 : ℝ) ≤
      (y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ)) ∧
    z ≤ x := by
  let z := fixedTenthZ y
  let Y : ℝ := (y : ℝ)
  let K : ℝ := (k : ℝ)
  let Z : ℝ := (z : ℝ)
  have hxpos : 0 < x := lt_of_lt_of_le (by omega : 0 < 2) hx2
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hxpos
  have hyR : (0 : ℝ) < Y := by
    dsimp [Y]
    exact_mod_cast (show 0 < y by omega)
  have hyR1 : (1 : ℝ) ≤ Y := by
    dsimp [Y]
    exact_mod_cast hy1
  have hkR : 0 < K := by
    dsimp [K]
    exact_mod_cast hkpos
  have hzup0 := fixedTenth_z_upper hy1
  have hzup : Z < 4 * Y ^ (1 / 16 : ℝ) := by
    simpa [Z, z, Y] using hzup0
  have hzY : Z ≤ Y := hzup.le.trans hzyScale
  have hzyNat : z ≤ y := by
    have hzyR : (z : ℝ) ≤ (y : ℝ) := by
      simpa [Z, Y] using hzY
    exact_mod_cast hzyR
  have hzR1 : (1 : ℝ) ≤ Z := by
    have hwR : (2 : ℝ) ≤ (fixedTenthW y : ℝ) := by exact_mod_cast hyw
    dsimp [Z, z, fixedTenthZ]
    norm_num only [Nat.cast_pow]
    nlinarith
  have hzRpos : 0 < Z := zero_lt_one.trans_le hzR1
  have hzNatPos : 0 < z := by
    have hzPosR : (0 : ℝ) < (z : ℝ) := by
      simpa [Z] using hzRpos
    exact_mod_cast hzPosR
  have hzsq0 := fixedTenth_z_sq_upper hy1
  have hzsq :
      Z ^ 2 < 16 * Y ^ (1 / 8 : ℝ) := by
    simpa [Z, z, Y] using hzsq0
  have hpow31 :
      Y ^ (3 / 4 : ℝ) * (4 * Y ^ (1 / 16 : ℝ)) =
        4 * Y ^ (13 / 16 : ℝ) := by
    calc
      Y ^ (3 / 4 : ℝ) * (4 * Y ^ (1 / 16 : ℝ))
          = 4 * (Y ^ (3 / 4 : ℝ) * Y ^ (1 / 16 : ℝ)) := by ring
      _ = 4 * Y ^ ((3 / 4 : ℝ) + 1 / 16) := by
        rw [Real.rpow_add hyR]
      _ = 4 * Y ^ (13 / 16 : ℝ) := by norm_num
  have hkzR : K * Z < Y := by
    calc
      K * Z ≤ K * (4 * Y ^ (1 / 16 : ℝ)) :=
        mul_le_mul_of_nonneg_left hzup.le hkR.le
      _ < Y ^ (3 / 4 : ℝ) * (4 * Y ^ (1 / 16 : ℝ)) :=
        mul_lt_mul_of_pos_right hky (by positivity)
      _ = 4 * Y ^ (13 / 16 : ℝ) := hpow31
      _ ≤ Y := hkzScale
  have hkzNat : k * z < y := by
    have hkzR' : (k : ℝ) * (z : ℝ) < (y : ℝ) := by
      simpa [K, Z, Y] using hkzR
    exact_mod_cast hkzR'
  have hsqrt : Nat.sqrt z = fixedTenthW y := by
    simpa [z] using fixedTenth_sqrt_z y
  have hsqrt2 : 2 ≤ Nat.sqrt z := by simpa [hsqrt] using hyw
  have hxz : x < z ^ 160 := by
    simpa [z] using fixedTenth_x_lt_z160 hxpos hxy
  have hlogs :=
    fixedTenth_log_bounds hxpos hxy hyw
  have hlogSqrt :
      Real.log (x : ℝ) ≤ 320 * Real.log (Nat.sqrt z : ℝ) := by
    simpa [z] using hlogs.1
  have hlogZ :
      Real.log (x : ℝ) ≤ 160 * Real.log (z : ℝ) := by
    simpa [z] using hlogs.2
  have hlogx4 := fixedTenth_logx_le_four_logy hxpos hxy
  have hygt1 : (1 : ℝ) < Y := by
    have hxquarter :
        (1 : ℝ) < (x : ℝ) ^ (1 / 10 : ℝ) := by
      exact Real.one_lt_rpow (by exact_mod_cast hx2) (by norm_num)
    exact hxquarter.trans (by simpa [Y] using hxy)
  have hlogY0 : 0 ≤ Real.log Y := (Real.log_pos hygt1).le
  have hlogX0 : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx2)
  have hphiNat : k.totient ≤ k := Nat.totient_le k
  have hphi : (k.totient : ℝ) ≤ K := by
    dsimp [K]
    exact_mod_cast hphiNat
  have hphiPos : (0 : ℝ) < (k.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 hkpos
  have hz2K : K * Z ^ 2 ≤ Y := by
    have hp :
        Y ^ (3 / 4 : ℝ) *
            (16 * Y ^ (1 / 8 : ℝ)) =
          16 * Y ^ (7 / 8 : ℝ) := by
      calc
        Y ^ (3 / 4 : ℝ) * (16 * Y ^ (1 / 8 : ℝ))
            = 16 * (Y ^ (3 / 4 : ℝ) * Y ^ (1 / 8 : ℝ)) := by ring
        _ = 16 * Y ^ ((3 / 4 : ℝ) + 1 / 8) := by
          rw [Real.rpow_add hyR]
        _ = 16 * Y ^ (7 / 8 : ℝ) := by norm_num
    calc
      K * Z ^ 2 ≤ K * (16 * Y ^ (1 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left hzsq.le hkR.le
      _ ≤ Y ^ (3 / 4 : ℝ) * (16 * Y ^ (1 / 8 : ℝ)) :=
        (mul_lt_mul_of_pos_right hky (by positivity)).le
      _ = 16 * Y ^ (7 / 8 : ℝ) := hp
      _ ≤ Y := hz2Scale
  have hzquarter_le : Z ^ (1 / 4 : ℝ) ≤ Z := by
    calc
      Z ^ (1 / 4 : ℝ) ≤ Z ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hzR1 (by norm_num)
      _ = Z := Real.rpow_one Z
  have hzquarterPos : 0 < Z ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos hzRpos _
  have hzabsorb0 :
      Z ≤ (Y / K) * Z ^ (-1 / 4 : ℝ) := by
    have hden : 0 < K * Z ^ (1 / 4 : ℝ) :=
      mul_pos hkR hzquarterPos
    have hmul :
        Z * (K * Z ^ (1 / 4 : ℝ)) ≤ Y := by
      calc
        Z * (K * Z ^ (1 / 4 : ℝ))
            ≤ Z * (K * Z) := by
              gcongr
        _ = K * Z ^ 2 := by ring
        _ ≤ Y := hz2K
    have hdiv : Z ≤ Y / (K * Z ^ (1 / 4 : ℝ)) :=
      (le_div_iff₀ hden).2 hmul
    calc
      Z ≤ Y / (K * Z ^ (1 / 4 : ℝ)) := hdiv
      _ = (Y / K) * Z ^ (-1 / 4 : ℝ) := by
        rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring,
          Real.rpow_neg hzRpos.le]
        field_simp [hkR.ne', (Real.rpow_pos_of_pos hzRpos (1 / 4 : ℝ)).ne']
  have hzabsorb :
      (z : ℝ) ≤
        ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ) := by
    simpa [Z, Y, K, z] using hzabsorb0
  have hlogxY :
      Real.log (x : ℝ) ≤ 10 * Real.log Y := by
    simpa [Y] using hlogx4
  have hz2den :
      Z ^ 2 * ((k.totient : ℝ) * Real.log (x : ℝ)) ≤ Y := by
    have hphil :
        (k.totient : ℝ) * Real.log (x : ℝ) ≤
          K * (10 * Real.log Y) := by
      exact mul_le_mul hphi hlogxY hlogX0.le
        (by positivity)
    have h1 :
        Z ^ 2 * ((k.totient : ℝ) * Real.log (x : ℝ)) ≤
          Z ^ 2 * (K * (10 * Real.log Y)) :=
      mul_le_mul_of_nonneg_left hphil (sq_nonneg Z)
    have h2 :
        Z ^ 2 * (K * (10 * Real.log Y)) ≤
          (16 * Y ^ (1 / 8 : ℝ)) *
            (Y ^ (3 / 4 : ℝ) * (10 * Real.log Y)) := by
      have hL0 : 0 ≤ 10 * Real.log Y := by positivity
      have hA0 : 0 ≤ 16 * Y ^ (1 / 8 : ℝ) := by positivity
      calc
        Z ^ 2 * (K * (10 * Real.log Y))
            ≤ (16 * Y ^ (1 / 8 : ℝ)) * (K * (10 * Real.log Y)) :=
          mul_le_mul_of_nonneg_right hzsq.le (mul_nonneg hkR.le hL0)
        _ ≤ (16 * Y ^ (1 / 8 : ℝ)) *
              (Y ^ (3 / 4 : ℝ) * (10 * Real.log Y)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hky.le hL0) hA0
    have hpow :
        (16 * Y ^ (1 / 8 : ℝ)) *
            (Y ^ (3 / 4 : ℝ) * (10 * Real.log Y)) =
          (160 * Real.log Y) * Y ^ (7 / 8 : ℝ) := by
      calc
        (16 * Y ^ (1 / 8 : ℝ)) *
              (Y ^ (3 / 4 : ℝ) * (10 * Real.log Y))
            = (160 * Real.log Y) *
                (Y ^ (1 / 8 : ℝ) * Y ^ (3 / 4 : ℝ)) := by ring
        _ = (160 * Real.log Y) *
              Y ^ ((1 / 8 : ℝ) + 3 / 4) := by
          rw [Real.rpow_add hyR]
        _ = (160 * Real.log Y) * Y ^ (7 / 8 : ℝ) := by norm_num
    have hlast :
        (160 * Real.log Y) * Y ^ (7 / 8 : ℝ) ≤ Y := by
      calc
        (160 * Real.log Y) * Y ^ (7 / 8 : ℝ)
            ≤ Y ^ (1 / 8 : ℝ) * Y ^ (7 / 8 : ℝ) :=
          mul_le_mul_of_nonneg_right hlog64
            (Real.rpow_nonneg hyR.le _)
        _ = Y := by
          rw [← Real.rpow_add hyR]
          norm_num
    exact h1.trans ((h2.trans_eq hpow).trans hlast)
  have hz2absorb0 :
      Z ^ 2 ≤
        Y / ((k.totient : ℝ) * Real.log (x : ℝ)) := by
    exact (le_div_iff₀ (mul_pos hphiPos hlogX0)).2 hz2den
  have hz2absorb :
      (z : ℝ) ^ 2 ≤
        (y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ)) := by
    simpa [Z, Y, z] using hz2absorb0
  have heighthLower0 := fixedTenth_eighth_power_lower hy1
  have heighthLower :
      Y ^ (1 / 128 : ℝ) ≤ Z ^ (1 / 8 : ℝ) := by
    simpa [Y, Z, z] using heighthLower0
  have hlogToEighth :
      Real.log (x : ℝ) ≤ Z ^ (1 / 8 : ℝ) :=
    hlogxY.trans (hlog4.trans heighthLower)
  have heighthPos : 0 < Z ^ (1 / 8 : ℝ) :=
    Real.rpow_pos_of_pos hzRpos _
  have hdenSmall :
      (k.totient : ℝ) * Real.log (x : ℝ) ≤
        K * Z ^ (1 / 8 : ℝ) := by
    exact mul_le_mul hphi hlogToEighth hlogX0.le hkR.le
  have hsmall0 :
      (Y / K) * Z ^ (-1 / 8 : ℝ) ≤
        Y / ((k.totient : ℝ) * Real.log (x : ℝ)) := by
    have hleft :
        (Y / K) * Z ^ (-1 / 8 : ℝ) =
          Y / (K * Z ^ (1 / 8 : ℝ)) := by
      rw [show (-1 / 8 : ℝ) = -(1 / 8 : ℝ) by ring,
        Real.rpow_neg hzRpos.le]
      field_simp [hkR.ne', heighthPos.ne']
    rw [hleft]
    exact div_le_div_of_nonneg_left
      (by positivity) (mul_pos hphiPos hlogX0) hdenSmall
  have hsmall :
      ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 8 : ℝ) ≤
        (y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ)) := by
    simpa [Y, K, Z, z] using hsmall0
  have hzx : z ≤ x := hzyNat.trans hyx
  exact ⟨hzyNat, hkzNat, hsqrt2, hxz, hzabsorb,
    hlogSqrt, hlogZ, hz2absorb, hsmall, hzx⟩


private theorem fixedTenth_y_ge_of_x_ge_fourth
    {X0 x y : ℕ}
    (hx : (X0 + 1) ^ 10 ≤ x)
    (hxy : (x : ℝ) ^ (1 / 10 : ℝ) < (y : ℝ)) :
    X0 ≤ y := by
  have hmpos : (0 : ℝ) < (X0 + 1 : ℕ) := by positivity
  have hxR :
      (((X0 + 1) ^ 10 : ℕ) : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast hx
  have hr :=
    Real.rpow_le_rpow
      (by positivity : (0 : ℝ) ≤ (((X0 + 1) ^ 10 : ℕ) : ℝ))
      hxR (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hroot :
      ((((X0 + 1) ^ 10 : ℕ) : ℝ)) ^ (1 / 10 : ℝ) =
        ((X0 + 1 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_pow]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hmpos.le]
    norm_num
  rw [hroot] at hr
  have hmY : (((X0 + 1 : ℕ) : ℝ)) < (y : ℝ) :=
    hr.trans_lt hxy
  have hmNat : X0 + 1 < y := by exact_mod_cast hmY
  omega

set_option maxHeartbeats 1800000 in
/-- S13: fixed-quarter selective-Shiu progression theorem, the exact CORE
consumer interface. -/
theorem shiuFixedTenth_progression
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2) :
    ∃ C : ℝ, ∃ X0 : ℕ, ∀ x y k a : ℕ,
      X0 ≤ x →
      (x : ℝ) ^ (1 / 10 : ℝ) < (y : ℝ) →
      y ≤ x →
      (k : ℝ) < (y : ℝ) ^ (3 / 4 : ℝ) →
      0 < a → a < k → a.Coprime k →
      progressionSum f x y k a ≤
        C *
          ((y : ℝ) /
            ((k.totient : ℝ) * Real.log (x : ℝ))) *
          Real.exp (primeMass f x k) := by
  obtain ⟨X12, h12⟩ := shiu_fixed_quarter_assemble hf
  obtain ⟨Y0, hY0⟩ :=
    eventually_atTop.1 eventually_fixedTenth_basic
  obtain ⟨XT, hT⟩ :=
    eventually_atTop.1 (eventually_fixedTenth_threshold A1)
  let X0 : ℕ := max 2 (max X12 (max XT ((Y0 + 1) ^ 10)))
  refine ⟨shiuFixedQuarterAssembleConstant A1 A2, X0, ?_⟩
  intro x y k a hx0 hxy hyx hky ha0 haklt hak
  have hx2 : 2 ≤ x := by
    exact (le_max_left 2 (max X12 (max XT ((Y0 + 1) ^ 10)))).trans hx0
  have hx12 : X12 ≤ x := by
    exact (le_trans (le_max_left X12 (max XT ((Y0 + 1) ^ 10)))
      (le_max_right 2 (max X12 (max XT ((Y0 + 1) ^ 10))))).trans hx0
  have hxT : XT ≤ x := by
    have hXT :
        XT ≤ max X12 (max XT ((Y0 + 1) ^ 10)) :=
      (le_max_left XT ((Y0 + 1) ^ 10)).trans
        (le_max_right X12 (max XT ((Y0 + 1) ^ 10)))
    exact (hXT.trans
      (le_max_right 2 (max X12 (max XT ((Y0 + 1) ^ 10))))).trans hx0
  have hxY :
      (Y0 + 1) ^ 10 ≤ x := by
    have hY :
        (Y0 + 1) ^ 10 ≤ max X12 (max XT ((Y0 + 1) ^ 10)) :=
      (le_max_right XT ((Y0 + 1) ^ 10)).trans
        (le_max_right X12 (max XT ((Y0 + 1) ^ 10)))
    exact (hY.trans
      (le_max_right 2 (max X12 (max XT ((Y0 + 1) ^ 10))))).trans hx0
  have hyY0 : Y0 ≤ y :=
    fixedTenth_y_ge_of_x_ge_fourth hxY hxy
  obtain ⟨hy1, hyw, hzyScale, hkzScale, hz2Scale, hlog64, hlog4⟩ :=
    hY0 y hyY0
  obtain ⟨hL4, hlarge⟩ := hT x hxT
  have hkpos : 0 < k := lt_trans ha0 haklt
  let z := fixedTenthZ y
  obtain ⟨hzy, hkz, hsqrt, hxz, hzabsorb,
      hlogSqrt, hlogZ, hz2absorb, hsmall, hzx⟩ :=
    fixedTenth_scalar_readiness
      hx2 hy1 hyw hzyScale hkzScale hz2Scale hlog64 hlog4
      hxy hyx hkpos hky
  exact h12 x y z k a hx12 hx2 ha0 haklt hak hyx
    hzy hkz hsqrt hxz hL4 hlarge hzabsorb hlogSqrt hlogZ
    hz2absorb hsmall hzx

end M4B
end PaperB

namespace PaperB.M4B

set_option maxHeartbeats 1800000 in
/-- Packaging-only uniform-envelope form of S13.  The constant and threshold
are chosen before the arithmetic function; the proof is the paid fixed-quarter
progression argument with quantifiers reordered. -/
theorem shiuFixedTenth_progression_uniform
    (A1 A2 : ℝ) :
    ∃ X0 : ℕ, ∀ f : ArithmeticFunction ℝ,
      FixedQuarterEnvelope f A1 A2 →
      ∀ x y k a : ℕ,
      X0 ≤ x →
      (x : ℝ) ^ (1 / 10 : ℝ) < (y : ℝ) →
      y ≤ x →
      (k : ℝ) < (y : ℝ) ^ (3 / 4 : ℝ) →
      0 < a → a < k → a.Coprime k →
      progressionSum f x y k a ≤
        shiuFixedQuarterAssembleConstant A1 A2 *
          ((y : ℝ) /
            ((k.totient : ℝ) * Real.log (x : ℝ))) *
          Real.exp (primeMass f x k) := by
  obtain ⟨X12, h12⟩ := shiu_fixed_quarter_assemble_uniform A1 A2
  obtain ⟨Y0, hY0⟩ :=
    eventually_atTop.1 eventually_fixedTenth_basic
  obtain ⟨XT, hT⟩ :=
    eventually_atTop.1 (eventually_fixedTenth_threshold A1)
  let X0 : ℕ := max 2 (max X12 (max XT ((Y0 + 1) ^ 10)))
  refine ⟨X0, ?_⟩
  intro f hf x y k a hx0 hxy hyx hky ha0 haklt hak
  have hx2 : 2 ≤ x := by
    exact (le_max_left 2 (max X12 (max XT ((Y0 + 1) ^ 10)))).trans hx0
  have hx12 : X12 ≤ x := by
    exact (le_trans (le_max_left X12 (max XT ((Y0 + 1) ^ 10)))
      (le_max_right 2 (max X12 (max XT ((Y0 + 1) ^ 10))))).trans hx0
  have hxT : XT ≤ x := by
    have hXT :
        XT ≤ max X12 (max XT ((Y0 + 1) ^ 10)) :=
      (le_max_left XT ((Y0 + 1) ^ 10)).trans
        (le_max_right X12 (max XT ((Y0 + 1) ^ 10)))
    exact (hXT.trans
      (le_max_right 2 (max X12 (max XT ((Y0 + 1) ^ 10))))).trans hx0
  have hxY :
      (Y0 + 1) ^ 10 ≤ x := by
    have hY :
        (Y0 + 1) ^ 10 ≤ max X12 (max XT ((Y0 + 1) ^ 10)) :=
      (le_max_right XT ((Y0 + 1) ^ 10)).trans
        (le_max_right X12 (max XT ((Y0 + 1) ^ 10)))
    exact (hY.trans
      (le_max_right 2 (max X12 (max XT ((Y0 + 1) ^ 10))))).trans hx0
  have hyY0 : Y0 ≤ y :=
    fixedTenth_y_ge_of_x_ge_fourth hxY hxy
  obtain ⟨hy1, hyw, hzyScale, hkzScale, hz2Scale, hlog64, hlog4⟩ :=
    hY0 y hyY0
  obtain ⟨hL4, hlarge⟩ := hT x hxT
  have hkpos : 0 < k := lt_trans ha0 haklt
  let z := fixedTenthZ y
  obtain ⟨hzy, hkz, hsqrt, hxz, hzabsorb,
      hlogSqrt, hlogZ, hz2absorb, hsmall, hzx⟩ :=
    fixedTenth_scalar_readiness
      hx2 hy1 hyw hzyScale hkzScale hz2Scale hlog64 hlog4
      hxy hyx hkpos hky
  exact h12 f hf x y z k a hx12 hx2 ha0 haklt hak hyx
    hzy hkz hsqrt hxz hL4 hlarge hzabsorb hlogSqrt hlogZ
    hz2absorb hsmall hzx

#print axioms shiuFixedTenth_progression_uniform

end PaperB.M4B
