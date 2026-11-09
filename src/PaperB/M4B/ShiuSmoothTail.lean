module

/-
Paper B M4B-CORE S3 completion for S11.
This module closes the specialized squarefree smooth-tail suppression interface
priced in the exact M4B0 ledger.  No new analytic foundation is introduced:
the only prime-distribution input below is pinned Chebyshev theta.
-/

public import PaperB.M4B.ShiuCore
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

public section

open scoped BigOperators
open Finset Nat Real
open ArithmeticFunction

noncomputable section

namespace PaperB
namespace M4B

/-- Finite logarithmic prime harmonic mass used to control the S3 Rankin
correction. -/
def primeLogHarmonic (Y : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE Y, Real.log (p : ℝ) / (p : ℝ)

/-- A deliberately coarse dyadic consequence of Chebyshev theta:
the logarithmic prime harmonic mass costs at most a fixed amount per
base-two shell. -/
theorem primeLogHarmonic_le_dyadic (Y : ℕ) :
    primeLogHarmonic Y ≤
      2 * Real.log 4 * (((Nat.log 2 Y + 1 : ℕ) : ℝ)) := by
  classical
  let P : Finset ℕ := Nat.primesLE Y
  let M : ℕ := Nat.log 2 Y
  let w : ℕ → ℝ := fun p => Real.log (p : ℝ) / (p : ℝ)
  have hmaps : ∀ p ∈ P, Nat.log 2 p ∈ Finset.range (M + 1) := by
    intro p hp
    rw [Finset.mem_range]
    have hpY : p ≤ Y := (Nat.mem_primesLE.mp hp).1
    have hlog : Nat.log 2 p ≤ Nat.log 2 Y :=
      (Nat.log_monotone (b := 2)) hpY
    dsimp [M]
    omega
  have hshell :
      ∀ j ∈ Finset.range (M + 1),
        (∑ p ∈ P with Nat.log 2 p = j, w p) ≤
          2 * Real.log 4 := by
    intro j hj
    let S : Finset ℕ := P.filter (fun p => Nat.log 2 p = j)
    have hpoint : ∀ p ∈ S,
        w p ≤ ((1 : ℝ) / ((2 ^ j : ℕ) : ℝ)) * Real.log (p : ℝ) := by
      intro p hp
      have hpF := Finset.mem_filter.mp hp
      have hpP : p ∈ P := hpF.1
      have hpprime : p.Prime := Nat.prime_of_mem_primesLE hpP
      have hpne : p ≠ 0 := hpprime.ne_zero
      have hpowNat : 2 ^ j ≤ p := by
        have h := Nat.pow_log_le_self 2 hpne
        simpa [hpF.2] using h
      have hpowR : (((2 ^ j : ℕ) : ℝ)) ≤ (p : ℝ) := by
        exact_mod_cast hpowNat
      have hpowpos : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
      have hlog0 : 0 ≤ Real.log (p : ℝ) := by
        exact Real.log_nonneg (by exact_mod_cast hpprime.one_le)
      dsimp [w]
      calc
        Real.log (p : ℝ) / (p : ℝ)
            ≤ Real.log (p : ℝ) / ((2 ^ j : ℕ) : ℝ) :=
          div_le_div_of_nonneg_left hlog0 hpowpos hpowR
        _ = ((1 : ℝ) / ((2 ^ j : ℕ) : ℝ)) *
            Real.log (p : ℝ) := by ring
    have hsub : S ⊆ Nat.primesLE (2 ^ (j + 1)) := by
      intro p hp
      have hpF := Finset.mem_filter.mp hp
      have hpP : p ∈ P := hpF.1
      have hpprime : p.Prime := Nat.prime_of_mem_primesLE hpP
      have hlt := Nat.lt_pow_succ_log_self Nat.one_lt_two p
      have hpLt : p < 2 ^ (j + 1) := by
        simpa [hpF.2, Nat.succ_eq_add_one] using hlt
      exact Nat.mem_primesLE.mpr ⟨Nat.le_of_lt hpLt, hpprime⟩
    have hsumlog :
        (∑ p ∈ S, Real.log (p : ℝ)) ≤
          Chebyshev.theta (2 ^ (j + 1) : ℕ) := by
      rw [Chebyshev.theta_eq_sum_primesLE_log]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p hp _ => Real.log_nonneg
          (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le))
    have htheta :
        Chebyshev.theta (2 ^ (j + 1) : ℕ) ≤
          Real.log 4 * ((2 ^ (j + 1) : ℕ) : ℝ) :=
      Chebyshev.theta_le_log4_mul_x (by positivity)
    change (∑ p ∈ S, w p) ≤ _
    calc
      (∑ p ∈ S, w p)
          ≤ ∑ p ∈ S,
              ((1 : ℝ) / ((2 ^ j : ℕ) : ℝ)) * Real.log (p : ℝ) :=
        Finset.sum_le_sum fun p hp => hpoint p hp
      _ = ((1 : ℝ) / ((2 ^ j : ℕ) : ℝ)) *
          ∑ p ∈ S, Real.log (p : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ ((1 : ℝ) / ((2 ^ j : ℕ) : ℝ)) *
          Chebyshev.theta (2 ^ (j + 1) : ℕ) := by
        exact mul_le_mul_of_nonneg_left hsumlog (by positivity)
      _ ≤ ((1 : ℝ) / ((2 ^ j : ℕ) : ℝ)) *
          (Real.log 4 * ((2 ^ (j + 1) : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left htheta (by positivity)
      _ = 2 * Real.log 4 := by
        norm_num [pow_succ]
        field_simp
  unfold primeLogHarmonic
  change (∑ p ∈ P, w p) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps w]
  calc
    (∑ j ∈ Finset.range (M + 1),
        ∑ p ∈ P with Nat.log 2 p = j, w p)
        ≤ ∑ _j ∈ Finset.range (M + 1), 2 * Real.log 4 :=
      Finset.sum_le_sum fun j hj => hshell j hj
    _ = (((M + 1 : ℕ) : ℝ)) * (2 * Real.log 4) := by simp
    _ = 2 * Real.log 4 * (((Nat.log 2 Y + 1 : ℕ) : ℝ)) := by
      dsimp [M]
      ring


/-- Weighted prime-log mass appearing in the S3 Rankin correction. -/
@[expose] def primeLogRpowMass (Y : ℕ) (ε : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE Y,
    Real.log (p : ℝ) * (p : ℝ) ^ (ε - 1)

/-- Finite dyadic Chebyshev bound for the weighted S3 prime mass.
This is the integration-free replacement for the historical Abel route. -/
theorem primeLogRpowMass_le_dyadic
    (Y : ℕ) {ε : ℝ} (hε1 : ε ≤ 1) :
    primeLogRpowMass Y ε ≤
      2 * Real.log 4 *
        ∑ j ∈ Finset.range (Nat.log 2 Y + 1),
          (((2 ^ j : ℕ) : ℝ)) ^ ε := by
  classical
  let P : Finset ℕ := Nat.primesLE Y
  let M : ℕ := Nat.log 2 Y
  let w : ℕ → ℝ :=
    fun p => Real.log (p : ℝ) * (p : ℝ) ^ (ε - 1)
  have hmaps : ∀ p ∈ P, Nat.log 2 p ∈ Finset.range (M + 1) := by
    intro p hp
    rw [Finset.mem_range]
    have hpY : p ≤ Y := (Nat.mem_primesLE.mp hp).1
    have hlog : Nat.log 2 p ≤ Nat.log 2 Y :=
      (Nat.log_monotone (b := 2)) hpY
    dsimp [M]
    omega
  have hshell :
      ∀ j ∈ Finset.range (M + 1),
        (∑ p ∈ P with Nat.log 2 p = j, w p) ≤
          2 * Real.log 4 * (((2 ^ j : ℕ) : ℝ)) ^ ε := by
    intro j hj
    let S : Finset ℕ := P.filter (fun p => Nat.log 2 p = j)
    let B : ℝ := ((2 ^ j : ℕ) : ℝ)
    have hBpos : 0 < B := by
      dsimp [B]
      positivity
    have hpoint : ∀ p ∈ S,
        w p ≤ Real.log (p : ℝ) * B ^ (ε - 1) := by
      intro p hp
      have hpF := Finset.mem_filter.mp hp
      have hpP : p ∈ P := hpF.1
      have hpprime : p.Prime := Nat.prime_of_mem_primesLE hpP
      have hpne : p ≠ 0 := hpprime.ne_zero
      have hpowNat : 2 ^ j ≤ p := by
        have h := Nat.pow_log_le_self 2 hpne
        simpa [hpF.2] using h
      have hpowR : B ≤ (p : ℝ) := by
        dsimp [B]
        exact_mod_cast hpowNat
      have hrpow :
          (p : ℝ) ^ (ε - 1) ≤ B ^ (ε - 1) := by
        exact Real.rpow_le_rpow_of_nonpos hBpos hpowR
          (sub_nonpos.mpr hε1)
      have hlog0 : 0 ≤ Real.log (p : ℝ) := by
        exact Real.log_nonneg (by exact_mod_cast hpprime.one_le)
      dsimp [w]
      exact mul_le_mul_of_nonneg_left hrpow hlog0
    have hsub : S ⊆ Nat.primesLE (2 ^ (j + 1)) := by
      intro p hp
      have hpF := Finset.mem_filter.mp hp
      have hpP : p ∈ P := hpF.1
      have hpprime : p.Prime := Nat.prime_of_mem_primesLE hpP
      have hlt := Nat.lt_pow_succ_log_self Nat.one_lt_two p
      have hpLt : p < 2 ^ (j + 1) := by
        simpa [hpF.2, Nat.succ_eq_add_one] using hlt
      exact Nat.mem_primesLE.mpr ⟨Nat.le_of_lt hpLt, hpprime⟩
    have hsumlog :
        (∑ p ∈ S, Real.log (p : ℝ)) ≤
          Chebyshev.theta (2 ^ (j + 1) : ℕ) := by
      rw [Chebyshev.theta_eq_sum_primesLE_log]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p hp _ => Real.log_nonneg
          (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le))
    have htheta :
        Chebyshev.theta (2 ^ (j + 1) : ℕ) ≤
          Real.log 4 * ((2 ^ (j + 1) : ℕ) : ℝ) :=
      Chebyshev.theta_le_log4_mul_x (by positivity)
    have hrpowB : 0 ≤ B ^ (ε - 1) := Real.rpow_nonneg hBpos.le _
    have hBsucc :
        (((2 ^ (j + 1) : ℕ) : ℝ)) = B * 2 := by
      dsimp [B]
      norm_num [pow_succ]
    have hBpow :
        B ^ (ε - 1) * B = B ^ ε := by
      rw [← Real.rpow_add_one hBpos.ne' (ε - 1)]
      congr 1
      ring
    change (∑ p ∈ S, w p) ≤ _
    calc
      (∑ p ∈ S, w p)
          ≤ ∑ p ∈ S, Real.log (p : ℝ) * B ^ (ε - 1) :=
        Finset.sum_le_sum fun p hp => hpoint p hp
      _ = (∑ p ∈ S, Real.log (p : ℝ)) * B ^ (ε - 1) := by
        rw [Finset.sum_mul]
      _ ≤ Chebyshev.theta (2 ^ (j + 1) : ℕ) * B ^ (ε - 1) :=
        mul_le_mul_of_nonneg_right hsumlog hrpowB
      _ ≤ (Real.log 4 * ((2 ^ (j + 1) : ℕ) : ℝ)) *
          B ^ (ε - 1) :=
        mul_le_mul_of_nonneg_right htheta hrpowB
      _ = 2 * Real.log 4 * B ^ ε := by
        rw [hBsucc]
        rw [show
          (Real.log 4 * (B * 2)) * B ^ (ε - 1) =
            2 * Real.log 4 * (B ^ (ε - 1) * B) by ring]
        rw [hBpow]
      _ = 2 * Real.log 4 * (((2 ^ j : ℕ) : ℝ)) ^ ε := by
        rfl
  unfold primeLogRpowMass
  change (∑ p ∈ P, w p) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps w]
  calc
    (∑ j ∈ Finset.range (M + 1),
        ∑ p ∈ P with Nat.log 2 p = j, w p)
        ≤ ∑ j ∈ Finset.range (M + 1),
            2 * Real.log 4 * (((2 ^ j : ℕ) : ℝ)) ^ ε :=
      Finset.sum_le_sum fun j hj => hshell j hj
    _ = 2 * Real.log 4 *
        ∑ j ∈ Finset.range (M + 1),
          (((2 ^ j : ℕ) : ℝ)) ^ ε := by
      rw [Finset.mul_sum]
    _ = 2 * Real.log 4 *
        ∑ j ∈ Finset.range (Nat.log 2 Y + 1),
          (((2 ^ j : ℕ) : ℝ)) ^ ε := by
      rfl


/-- The raw Rankin correction is controlled by the weighted prime-log mass.
This is the finite bridge consumed by the S3 suppression specialization. -/
theorem primeRankinCorrection_le_weighted
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    (Y k : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) :
    primeRankinCorrection f Y k ε ≤
      (A1 * ε) * primeLogRpowMass Y ε := by
  classical
  let P : Finset ℕ := (Nat.primesLE Y).filter (fun p => ¬ p ∣ k)
  have hpoint : ∀ p ∈ P,
      f p * ((p : ℝ) ^ ε - 1) / (p : ℝ) ≤
        (A1 * ε) *
          (Real.log (p : ℝ) * (p : ℝ) ^ (ε - 1)) := by
    intro p hp
    have hpP := Finset.mem_filter.mp hp
    have hpprime : p.Prime := Nat.prime_of_mem_primesLE hpP.1
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.pos
    have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.one_le
    have hpow1 : (1 : ℝ) ≤ (p : ℝ) ^ ε :=
      Real.one_le_rpow hp1R hε0
    have hsub0 : 0 ≤ (p : ℝ) ^ ε - 1 := sub_nonneg.mpr hpow1
    have hlog0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1R
    have hself :=
      Real.self_sub_one_le_mul_log
        (Real.rpow_nonneg hpR.le ε)
    have hsub :
        (p : ℝ) ^ ε - 1 ≤
          ε * Real.log (p : ℝ) * (p : ℝ) ^ ε := by
      calc
        (p : ℝ) ^ ε - 1
            ≤ (p : ℝ) ^ ε * Real.log ((p : ℝ) ^ ε) := hself
        _ = ε * Real.log (p : ℝ) * (p : ℝ) ^ ε := by
          rw [Real.log_rpow hpR]
          ring
    have hq0 :
        0 ≤ ((p : ℝ) ^ ε - 1) / (p : ℝ) :=
      div_nonneg hsub0 hpR.le
    have hfp :
        f p * (((p : ℝ) ^ ε - 1) / (p : ℝ)) ≤
          A1 * (((p : ℝ) ^ ε - 1) / (p : ℝ)) :=
      mul_le_mul_of_nonneg_right (hf.prime_le p hpprime) hq0
    have hdiv :
        ((p : ℝ) ^ ε - 1) / (p : ℝ) ≤
          (ε * Real.log (p : ℝ) * (p : ℝ) ^ ε) / (p : ℝ) :=
      (div_le_div_iff_of_pos_right hpR).2 hsub
    calc
      f p * ((p : ℝ) ^ ε - 1) / (p : ℝ)
          = f p * (((p : ℝ) ^ ε - 1) / (p : ℝ)) := by ring
      _ ≤ A1 * (((p : ℝ) ^ ε - 1) / (p : ℝ)) := hfp
      _ ≤ A1 *
          ((ε * Real.log (p : ℝ) * (p : ℝ) ^ ε) / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv hf.A1_nonneg
      _ = (A1 * ε) *
          (Real.log (p : ℝ) * (p : ℝ) ^ (ε - 1)) := by
        rw [Real.rpow_sub hpR, Real.rpow_one]
        field_simp [hpR.ne']
  have hnonneg :
      ∀ p ∈ Nat.primesLE Y,
        0 ≤ (A1 * ε) *
          (Real.log (p : ℝ) * (p : ℝ) ^ (ε - 1)) := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primesLE hp
    have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.one_le
    exact mul_nonneg
      (mul_nonneg hf.A1_nonneg hε0)
      (mul_nonneg (Real.log_nonneg hp1R)
        (Real.rpow_nonneg (by positivity) _))
  unfold primeRankinCorrection primeLogRpowMass
  change
    (∑ p ∈ P, f p * ((p : ℝ) ^ ε - 1) / (p : ℝ)) ≤
      (A1 * ε) *
        ∑ p ∈ Nat.primesLE Y,
          Real.log (p : ℝ) * (p : ℝ) ^ (ε - 1)
  calc
    (∑ p ∈ P, f p * ((p : ℝ) ^ ε - 1) / (p : ℝ))
        ≤ ∑ p ∈ P,
            (A1 * ε) *
              (Real.log (p : ℝ) * (p : ℝ) ^ (ε - 1)) :=
      Finset.sum_le_sum fun p hp => hpoint p hp
    _ ≤ ∑ p ∈ Nat.primesLE Y,
          (A1 * ε) *
            (Real.log (p : ℝ) * (p : ℝ) ^ (ε - 1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun p hp _ => hnonneg p hp)
    _ = (A1 * ε) *
        ∑ p ∈ Nat.primesLE Y,
          Real.log (p : ℝ) * (p : ℝ) ^ (ε - 1) := by
      rw [Finset.mul_sum]


/-- Combine the paid correction bridge with the paid finite dyadic
Chebyshev estimate. -/
theorem primeRankinCorrection_le_dyadic
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    (Y k : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    primeRankinCorrection f Y k ε ≤
      (A1 * ε) *
        (2 * Real.log 4 *
          ∑ j ∈ Finset.range (Nat.log 2 Y + 1),
            (((2 ^ j : ℕ) : ℝ)) ^ ε) := by
  have hbridge :=
    primeRankinCorrection_le_weighted hf Y k hε0
  have hmass := primeLogRpowMass_le_dyadic Y hε1
  exact hbridge.trans
    (mul_le_mul_of_nonneg_left hmass
      (mul_nonneg hf.A1_nonneg hε0))

/-- The generic final step of S3: once the finite scalar Rankin correction
fits inside the chosen logarithmic budget, the raw Rankin engine gives the
desired exponential suppression.  The shell-specific choice of epsilon and
the r*log r budget remain explicit downstream. -/
theorem squarefree_smoothTail_rankin_of_budget
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    (X Y k : ℕ) {ε R : ℝ}
    (hX : 1 ≤ X) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hbudget :
      primeRankinCorrection f Y k ε -
          ε * Real.log (X : ℝ) ≤ -R) :
    squarefreeSmoothTailMass f X Y k ≤
      Real.exp (primeMass f Y k - R) := by
  have hraw :=
    squarefree_smoothTail_rankin_raw hf X Y k hX hε0 hε1
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hX)
  calc
    squarefreeSmoothTailMass f X Y k
        ≤ (X : ℝ) ^ (-ε) *
            Real.exp
              (primeMass f Y k +
                primeRankinCorrection f Y k ε) := hraw
    _ = Real.exp
          (primeMass f Y k +
            primeRankinCorrection f Y k ε -
            ε * Real.log (X : ℝ)) := by
      rw [Real.rpow_def_of_pos hXpos, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (primeMass f Y k - R) := by
      apply Real.exp_le_exp.mpr
      linarith

end M4B
end PaperB
