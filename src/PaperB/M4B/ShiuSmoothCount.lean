module

/-
Paper B M4B-CORE S1 scalar closure.
The raw squarefree Rankin engine lives in ShiuCore; this module supplies the
finite prime-mass reduction and then the eventual log-log specialization.
-/

public import PaperB.M4B.ShiuCore
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section

open scoped BigOperators Topology
open Finset Nat Real Filter
open ArithmeticFunction

noncomputable section

namespace PaperB
namespace M4B

/-- Elementary finite reduction for the S1 Rankin prime mass, split at sqrt Y. -/
theorem primeRankinMass_le_sqrt_split
    (Y : ℕ) {δ : ℝ} (hY : 4 ≤ Y) (hδ : 0 ≤ δ) :
    primeRankinMass Y δ ≤
      ((Y.sqrt + 1 : ℕ) : ℝ) +
        ((Y + 1 : ℕ) : ℝ) * ((Y.sqrt : ℕ) : ℝ) ^ (-δ) := by
  classical
  let P : Finset ℕ := Nat.primesLE Y
  let S : Finset ℕ := P.filter (fun p => p ≤ Y.sqrt)
  let L : Finset ℕ := P.filter (fun p => ¬ p ≤ Y.sqrt)
  let w : ℕ → ℝ := fun p => (p : ℝ) ^ (-δ)
  have hTsqrt : 2 ≤ Y.sqrt := by
    rw [Nat.le_sqrt']
    simpa using hY
  have hsmall_point : ∀ p ∈ S, w p ≤ 1 := by
    intro p hp
    have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
    have hpprime : p.Prime := Nat.prime_of_mem_primesLE hpP
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast hpprime.one_le) (neg_nonpos.mpr hδ)
  have hlarge_point :
      ∀ p ∈ L, w p ≤ ((Y.sqrt : ℕ) : ℝ) ^ (-δ) := by
    intro p hp
    have hpF := Finset.mem_filter.mp hp
    have hpP : p ∈ P := hpF.1
    have hpprime : p.Prime := Nat.prime_of_mem_primesLE hpP
    have hTpNat : Y.sqrt ≤ p := Nat.le_of_lt (lt_of_not_ge hpF.2)
    have hTpos : (0 : ℝ) < (Y.sqrt : ℕ) := by positivity
    unfold w
    exact Real.rpow_le_rpow_of_nonpos hTpos
      (by exact_mod_cast hTpNat) (neg_nonpos.mpr hδ)
  have hScard : S.card ≤ Y.sqrt + 1 := by
    have hsub : S ⊆ Finset.range (Y.sqrt + 1) := by
      intro p hp
      rw [Finset.mem_range]
      have hpS := (Finset.mem_filter.mp hp).2
      omega
    simpa using Finset.card_le_card hsub
  have hLcard : L.card ≤ Y + 1 := by
    have hsub : L ⊆ Finset.range (Y + 1) := by
      intro p hp
      rw [Finset.mem_range]
      have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
      have hple : p ≤ Y := (Nat.mem_primesLE.mp hpP).1
      omega
    simpa using Finset.card_le_card hsub
  have hsmall :
      (∑ p ∈ S, w p) ≤ ((Y.sqrt + 1 : ℕ) : ℝ) := by
    calc
      (∑ p ∈ S, w p) ≤ ∑ _p ∈ S, (1 : ℝ) :=
        Finset.sum_le_sum fun p hp => hsmall_point p hp
      _ = (S.card : ℝ) := by simp
      _ ≤ ((Y.sqrt + 1 : ℕ) : ℝ) := by exact_mod_cast hScard
  have hlarge :
      (∑ p ∈ L, w p) ≤
        ((Y + 1 : ℕ) : ℝ) * ((Y.sqrt : ℕ) : ℝ) ^ (-δ) := by
    calc
      (∑ p ∈ L, w p)
          ≤ ∑ _p ∈ L, ((Y.sqrt : ℕ) : ℝ) ^ (-δ) :=
        Finset.sum_le_sum fun p hp => hlarge_point p hp
      _ = (L.card : ℝ) * ((Y.sqrt : ℕ) : ℝ) ^ (-δ) := by simp
      _ ≤ ((Y + 1 : ℕ) : ℝ) * ((Y.sqrt : ℕ) : ℝ) ^ (-δ) := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast hLcard)
          (Real.rpow_nonneg (by positivity) _)
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not P (fun p => p ≤ Y.sqrt) w
  unfold primeRankinMass
  change (∑ p ∈ P, w p) ≤ _
  calc
    (∑ p ∈ P, w p) =
        (∑ p ∈ S, w p) + (∑ p ∈ L, w p) := by
      simpa [S, L] using hsplit.symm
    _ ≤ ((Y.sqrt + 1 : ℕ) : ℝ) +
        ((Y + 1 : ℕ) : ℝ) * ((Y.sqrt : ℕ) : ℝ) ^ (-δ) :=
      add_le_add hsmall hlarge

/-- Same finite Rankin mass split with an arbitrary positive cutoff.
This is the scalar-facing form of the preceding sqrt split; no new analytic
input is introduced. -/
theorem primeRankinMass_le_cutoff
    (Y T : ℕ) {δ : ℝ} (hT : 1 ≤ T) (hδ : 0 ≤ δ) :
    primeRankinMass Y δ ≤
      ((T + 1 : ℕ) : ℝ) +
        ((Y + 1 : ℕ) : ℝ) * (T : ℝ) ^ (-δ) := by
  classical
  let P : Finset ℕ := Nat.primesLE Y
  let S : Finset ℕ := P.filter (fun p => p ≤ T)
  let L : Finset ℕ := P.filter (fun p => ¬ p ≤ T)
  let w : ℕ → ℝ := fun p => (p : ℝ) ^ (-δ)
  have hTpos : (0 : ℝ) < (T : ℕ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hT)
  have hsmall_point : ∀ p ∈ S, w p ≤ 1 := by
    intro p hp
    have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
    have hpprime : p.Prime := Nat.prime_of_mem_primesLE hpP
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast hpprime.one_le) (neg_nonpos.mpr hδ)
  have hlarge_point :
      ∀ p ∈ L, w p ≤ (T : ℝ) ^ (-δ) := by
    intro p hp
    have hpF := Finset.mem_filter.mp hp
    have hTpNat : T ≤ p := Nat.le_of_lt (lt_of_not_ge hpF.2)
    unfold w
    exact Real.rpow_le_rpow_of_nonpos hTpos
      (by exact_mod_cast hTpNat) (neg_nonpos.mpr hδ)
  have hScard : S.card ≤ T + 1 := by
    have hsub : S ⊆ Finset.range (T + 1) := by
      intro p hp
      rw [Finset.mem_range]
      have hpS := (Finset.mem_filter.mp hp).2
      omega
    simpa using Finset.card_le_card hsub
  have hLcard : L.card ≤ Y + 1 := by
    have hsub : L ⊆ Finset.range (Y + 1) := by
      intro p hp
      rw [Finset.mem_range]
      have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
      have hple : p ≤ Y := (Nat.mem_primesLE.mp hpP).1
      omega
    simpa using Finset.card_le_card hsub
  have hsmall :
      (∑ p ∈ S, w p) ≤ ((T + 1 : ℕ) : ℝ) := by
    calc
      (∑ p ∈ S, w p) ≤ ∑ _p ∈ S, (1 : ℝ) :=
        Finset.sum_le_sum fun p hp => hsmall_point p hp
      _ = (S.card : ℝ) := by simp
      _ ≤ ((T + 1 : ℕ) : ℝ) := by exact_mod_cast hScard
  have hlarge :
      (∑ p ∈ L, w p) ≤
        ((Y + 1 : ℕ) : ℝ) * (T : ℝ) ^ (-δ) := by
    calc
      (∑ p ∈ L, w p) ≤ ∑ _p ∈ L, (T : ℝ) ^ (-δ) :=
        Finset.sum_le_sum fun p hp => hlarge_point p hp
      _ = (L.card : ℝ) * (T : ℝ) ^ (-δ) := by simp
      _ ≤ ((Y + 1 : ℕ) : ℝ) * (T : ℝ) ^ (-δ) :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast hLcard) (Real.rpow_nonneg (by positivity) _)
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not P (fun p => p ≤ T) w
  unfold primeRankinMass
  change (∑ p ∈ P, w p) ≤ _
  calc
    (∑ p ∈ P, w p) =
        (∑ p ∈ S, w p) + (∑ p ∈ L, w p) := by
      simpa [S, L] using hsplit.symm
    _ ≤ ((T + 1 : ℕ) : ℝ) +
        ((Y + 1 : ℕ) : ℝ) * (T : ℝ) ^ (-δ) :=
      add_le_add hsmall hlarge

/-- Rankin count bound using an arbitrary positive finite cutoff. -/
theorem squarefreeSmoothCount_rankin_cutoff
    (X Y T : ℕ) {δ : ℝ}
    (hX : 1 ≤ X) (hT : 1 ≤ T) (hδ : 0 < δ) :
    (squarefreeSmoothCount X Y : ℝ) ≤
      (X : ℝ) ^ δ *
        Real.exp
          (((T + 1 : ℕ) : ℝ) +
            ((Y + 1 : ℕ) : ℝ) * (T : ℝ) ^ (-δ)) := by
  calc
    (squarefreeSmoothCount X Y : ℝ)
        ≤ (X : ℝ) ^ δ * Real.exp (primeRankinMass Y δ) :=
      squarefreeSmooth_rankin X Y hX hδ
    _ ≤ (X : ℝ) ^ δ *
        Real.exp
          (((T + 1 : ℕ) : ℝ) +
            ((Y + 1 : ℕ) : ℝ) * (T : ℝ) ^ (-δ)) := by
      gcongr
      exact primeRankinMass_le_cutoff Y T hT hδ.le

/-- Finite S1 consequence before the final eventual scalar estimate. -/
theorem squarefreeSmoothCount_rankin_split
    (X Y : ℕ) {δ : ℝ}
    (hX : 1 ≤ X) (hY : 4 ≤ Y) (hδ : 0 < δ) :
    (squarefreeSmoothCount X Y : ℝ) ≤
      (X : ℝ) ^ δ *
        Real.exp
          (((Y.sqrt + 1 : ℕ) : ℝ) +
            ((Y + 1 : ℕ) : ℝ) * ((Y.sqrt : ℕ) : ℝ) ^ (-δ)) := by
  calc
    (squarefreeSmoothCount X Y : ℝ)
        ≤ (X : ℝ) ^ δ * Real.exp (primeRankinMass Y δ) :=
      squarefreeSmooth_rankin X Y hX hδ
    _ ≤ (X : ℝ) ^ δ *
        Real.exp
          (((Y.sqrt + 1 : ℕ) : ℝ) +
            ((Y + 1 : ℕ) : ℝ) * ((Y.sqrt : ℕ) : ℝ) ^ (-δ)) := by
      gcongr
      exact primeRankinMass_le_sqrt_split Y hY hδ.le


/-- Naturalized source scale `log X * loglog X` used by S1. -/
@[expose] def shiuLogLogSmoothThreshold (X : ℕ) : ℕ :=
  ⌊Real.log (X : ℝ) * Real.log (Real.log (X : ℝ))⌋₊

/-- S1 scalar closure.  For one fixed absolute constant (here 8), the
squarefree smooth count at Shiu's `log X * loglog X` scale has the required
`exp(C log X / sqrt(loglog X))` upper bound for all sufficiently large X. -/
theorem smoothCount_loglog_upper :
    ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      (squarefreeSmoothCount X (shiuLogLogSmoothThreshold X) : ℝ) ≤
        Real.exp
          (8 * Real.log (X : ℝ) /
            Real.sqrt (Real.log (Real.log (X : ℝ)))) := by
  refine ⟨⌈Real.exp (Real.exp 4)⌉₊, ?_⟩
  intro X hX0
  let u : ℝ := Real.log (X : ℝ)
  let l : ℝ := Real.log u
  let r : ℝ := Real.sqrt l
  let T : ℕ := ⌈Real.exp (l / 2)⌉₊
  let δ : ℝ := 4 / r
  have hbaseceil :
      Real.exp (Real.exp 4) ≤ (⌈Real.exp (Real.exp 4)⌉₊ : ℕ) := by
    exact Nat.le_ceil _
  have hXbase : Real.exp (Real.exp 4) ≤ (X : ℝ) := by
    calc
      Real.exp (Real.exp 4)
          ≤ (⌈Real.exp (Real.exp 4)⌉₊ : ℕ) := hbaseceil
      _ ≤ (X : ℝ) := by exact_mod_cast hX0
  have hXpos : (0 : ℝ) < (X : ℝ) :=
    (Real.exp_pos _).trans_le hXbase
  have hu4 : Real.exp 4 ≤ u := by
    dsimp [u]
    rw [← Real.exp_le_exp, Real.exp_log hXpos]
    exact hXbase
  have hu_pos : 0 < u := (Real.exp_pos 4).trans_le hu4
  have hl4 : 4 ≤ l := by
    dsimp [l]
    rw [← Real.exp_le_exp, Real.exp_log hu_pos]
    exact hu4
  have hl0 : 0 ≤ l := le_trans (by norm_num) hl4
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact Real.sqrt_nonneg _
  have hrsq : r ^ 2 = l := by
    dsimp [r]
    exact Real.sq_sqrt hl0
  have hr2 : 2 ≤ r := by
    nlinarith
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr2
  have hrne : r ≠ 0 := hrpos.ne'
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hTpos : 0 < T := by
    dsimp [T]
    exact Nat.ceil_pos.mpr (Real.exp_pos _)
  have hT : 1 ≤ T := hTpos
  have hXnat : 1 ≤ X := by
    have : 0 < X := by exact_mod_cast hXpos
    omega
  have huexp : Real.exp l = u := by
    dsimp [l]
    exact Real.exp_log hu_pos
  have hTlower : Real.exp (l / 2) ≤ (T : ℝ) := by
    dsimp [T]
    exact Nat.le_ceil _
  have hTupper : (T : ℝ) ≤ Real.exp (l / 2) + 1 := by
    dsimp [T]
    exact (Nat.ceil_lt_add_one (Real.exp_pos _).le).le
  have hr_le_exp_half : r ≤ Real.exp (l / 2) := by
    have hlin : r ≤ 1 + l / 2 := by
      nlinarith [sq_nonneg (r - 1)]
    exact hlin.trans (by simpa [add_comm] using Real.add_one_le_exp (l / 2))
  have hhalf_le_base : Real.exp (l / 2) ≤ u / r := by
    rw [le_div_iff₀ hrpos]
    calc
      Real.exp (l / 2) * r
          ≤ Real.exp (l / 2) * Real.exp (l / 2) :=
        mul_le_mul_of_nonneg_left hr_le_exp_half (Real.exp_pos _).le
      _ = Real.exp l := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ = u := huexp
  have htwo_le_base : (2 : ℝ) ≤ u / r := by
    have htwo : (2 : ℝ) ≤ Real.exp (l / 2) := by
      calc
        (2 : ℝ) ≤ 1 + l / 2 := by linarith
        _ ≤ Real.exp (l / 2) := by simpa [add_comm] using Real.add_one_le_exp (l / 2)
    exact htwo.trans hhalf_le_base
  have hsmall :
      ((T + 1 : ℕ) : ℝ) ≤ 2 * (u / r) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    calc
      (T : ℝ) + 1 ≤ Real.exp (l / 2) + 2 := by linarith
      _ ≤ u / r + u / r := add_le_add hhalf_le_base htwo_le_base
      _ = 2 * (u / r) := by ring
  have hul0 : 0 ≤ u * l := mul_nonneg hu_pos.le hl0
  have hYupper :
      ((shiuLogLogSmoothThreshold X : ℕ) : ℝ) ≤ u * l := by
    change ((⌊u * l⌋₊ : ℕ) : ℝ) ≤ u * l
    exact Nat.floor_le hul0
  have hu1 : (1 : ℝ) ≤ u := by
    have h5 : (5 : ℝ) ≤ Real.exp 4 := by
      nlinarith [Real.add_one_le_exp (4 : ℝ)]
    linarith
  have hul1 : (1 : ℝ) ≤ u * l := by
    have h4ul : (4 : ℝ) ≤ u * l := by
      calc
        (4 : ℝ) = 1 * 4 := by norm_num
        _ ≤ u * l := mul_le_mul hu1 hl4 (by norm_num) hu_pos.le
    linarith
  have hYplus :
      (((shiuLogLogSmoothThreshold X + 1 : ℕ) : ℝ)) ≤
        2 * (u * l) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hTpow :
      (T : ℝ) ^ (-δ) ≤ Real.exp (-2 * r) := by
    calc
      (T : ℝ) ^ (-δ)
          ≤ (Real.exp (l / 2)) ^ (-δ) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hTlower
          (neg_nonpos.mpr hδ.le)
      _ = Real.exp (-2 * r) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        congr 1
        dsimp [δ]
        field_simp [hrne]
        nlinarith [hrsq]
  have hr3le : r ^ 3 ≤ Real.exp (2 * r) := by
    have hexp :=
      Real.pow_div_factorial_le_exp
        (x := 2 * r) (show 0 ≤ 2 * r by positivity) 3
    calc
      r ^ 3 ≤ (2 * r) ^ 3 / (3 ! : ℕ) := by
        norm_num [Nat.factorial]
        have hr3non : 0 ≤ r ^ 3 := pow_nonneg hr0 _
        ring_nf
        nlinarith
      _ ≤ Real.exp (2 * r) := hexp
  have hr3decay : r ^ 3 * Real.exp (-2 * r) ≤ 1 := by
    calc
      r ^ 3 * Real.exp (-2 * r)
          ≤ Real.exp (2 * r) * Real.exp (-2 * r) :=
        mul_le_mul_of_nonneg_right hr3le (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add]
        norm_num
  have hdecay : l * Real.exp (-2 * r) ≤ 1 / r := by
    rw [le_div_iff₀ hrpos]
    calc
      (l * Real.exp (-2 * r)) * r
          = r ^ 3 * Real.exp (-2 * r) := by
        rw [← hrsq]
        ring
      _ ≤ 1 := hr3decay
  have hlarge :
      (((shiuLogLogSmoothThreshold X + 1 : ℕ) : ℝ)) *
          (T : ℝ) ^ (-δ) ≤
        2 * (u / r) := by
    calc
      (((shiuLogLogSmoothThreshold X + 1 : ℕ) : ℝ)) *
            (T : ℝ) ^ (-δ)
          ≤ (2 * (u * l)) * Real.exp (-2 * r) := by
        exact mul_le_mul hYplus hTpow
          (Real.rpow_nonneg (by positivity) _) (by positivity)
      _ = 2 * u * (l * Real.exp (-2 * r)) := by ring
      _ ≤ 2 * u * (1 / r) := by
        exact mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ = 2 * (u / r) := by
        field_simp [hrne]
  have hmass :
      (((T + 1 : ℕ) : ℝ) +
        (((shiuLogLogSmoothThreshold X + 1 : ℕ) : ℝ)) *
          (T : ℝ) ^ (-δ)) ≤
        4 * (u / r) := by
    linarith
  have hrank :=
    squarefreeSmoothCount_rankin_cutoff
      X (shiuLogLogSmoothThreshold X) T hXnat hT hδ
  calc
    (squarefreeSmoothCount X (shiuLogLogSmoothThreshold X) : ℝ)
        ≤ (X : ℝ) ^ δ *
          Real.exp
            (((T + 1 : ℕ) : ℝ) +
              (((shiuLogLogSmoothThreshold X + 1 : ℕ) : ℝ)) *
                (T : ℝ) ^ (-δ)) := hrank
    _ = Real.exp
          (δ * u +
            (((T + 1 : ℕ) : ℝ) +
              (((shiuLogLogSmoothThreshold X + 1 : ℕ) : ℝ)) *
                (T : ℝ) ^ (-δ))) := by
      rw [Real.rpow_def_of_pos hXpos, ← Real.exp_add]
      congr 1
      dsimp [u]
      ring
    _ ≤ Real.exp (8 * (u / r)) := by
      rw [Real.exp_le_exp]
      have hδu : δ * u = 4 * (u / r) := by
        dsimp [δ]
        field_simp [hrne]
      rw [hδu]
      linarith
    _ = Real.exp
          (8 * Real.log (X : ℝ) /
            Real.sqrt (Real.log (Real.log (X : ℝ)))) := by
      dsimp [u, l, r]
      ring


end M4B
end PaperB
