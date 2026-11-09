module

/-
Paper B M4B-CORE S8: Class III count.
Authorized surface: exact M4B0 ledger row S8 only.

The source Class-III mechanism is an overcount by a large squarefree smooth
prefix factor b.  S1 supplies the eventual number of such b, while the paid
M4A AP/divisibility counter supplies the count for each fixed b.
-/

public import PaperB.M4B.ShiuSmoothCount
public import PaperB.M4A.APDivCount

public section

open scoped BigOperators Topology
open Finset Nat Real Filter

noncomputable section

namespace PaperB
namespace M4B

/-- Smooth large prefix factors used in the S8 Class-III overcount.
The smoothness threshold is exactly the S1 scale attached to the ambient x. -/
@[expose] def classIIIFactors (x z k : ℕ) : Finset ℕ := by
  classical
  exact
    (squarefreeSmoothSet x (shiuLogLogSmoothThreshold x)).filter
      (fun b =>
        b ≤ z ∧ b.Coprime k ∧
          (z : ℝ) ^ (1 / 2 : ℝ) ≤ (b : ℝ))

/-- The source-faithful Class-III counting overcover: for every admissible
smooth prefix b, count progression points divisible by b. -/
@[expose] def classIIIOvercount (x y z k a : ℕ) : ℝ := by
  classical
  exact ∑ b ∈ classIIIFactors x z k,
    (PaperB.M4A.apDivCount x y k a b : ℝ)

theorem classIIIFactors_card_le_smoothCount (x z k : ℕ) :
    (classIIIFactors x z k).card ≤
      squarefreeSmoothCount x (shiuLogLogSmoothThreshold x) := by
  unfold classIIIFactors squarefreeSmoothCount
  apply Finset.card_le_card
  intro b hb
  exact (Finset.mem_filter.mp hb).1

/-- S1 at the ambient x scale, combined with x < z^160, gives the exact
quarter-power supply needed in Class III.  The enormous explicit onset is
deliberate: only existence of an absolute threshold is consumed downstream. -/
theorem smoothCount_loglog_le_quarter_of_pow :
    ∃ X0 : ℕ, ∀ x z : ℕ, X0 ≤ x → x < z ^ 160 →
      (squarefreeSmoothCount x (shiuLogLogSmoothThreshold x) : ℝ) ≤
        (z : ℝ) ^ (1 / 4 : ℝ) := by
  obtain ⟨X1, hX1⟩ := smoothCount_loglog_upper
  let X2 : ℕ := ⌈Real.exp (Real.exp ((5120 : ℝ) ^ 2))⌉₊
  refine ⟨max X1 X2, ?_⟩
  intro x z hx hxz
  have hx1 : X1 ≤ x := (Nat.le_max_left X1 X2).trans hx
  have hx2 : X2 ≤ x := (Nat.le_max_right X1 X2).trans hx
  have hbaseceil :
      Real.exp (Real.exp ((5120 : ℝ) ^ 2)) ≤ (X2 : ℕ) := by
    dsimp [X2]
    exact Nat.le_ceil _
  have hxbase :
      Real.exp (Real.exp ((5120 : ℝ) ^ 2)) ≤ (x : ℝ) := by
    calc
      Real.exp (Real.exp ((5120 : ℝ) ^ 2)) ≤ (X2 : ℕ) := hbaseceil
      _ ≤ (x : ℝ) := by exact_mod_cast hx2
  have hxpos : (0 : ℝ) < (x : ℝ) :=
    (Real.exp_pos _).trans_le hxbase
  have hlogx :
      Real.exp ((5120 : ℝ) ^ 2) ≤ Real.log (x : ℝ) := by
    rw [← Real.exp_le_exp, Real.exp_log hxpos]
    exact hxbase
  have hlogxpos : 0 < Real.log (x : ℝ) :=
    (Real.exp_pos _).trans_le hlogx
  have hll :
      (5120 : ℝ) ^ 2 ≤ Real.log (Real.log (x : ℝ)) := by
    rw [← Real.exp_le_exp, Real.exp_log hlogxpos]
    exact hlogx
  have hll0 : 0 ≤ Real.log (Real.log (x : ℝ)) :=
    le_trans (sq_nonneg (5120 : ℝ)) hll
  have hroot :
      (5120 : ℝ) ≤ Real.sqrt (Real.log (Real.log (x : ℝ))) := by
    have hs0 := Real.sqrt_nonneg (Real.log (Real.log (x : ℝ)))
    have hs2 := Real.sq_sqrt hll0
    nlinarith
  have hspos :
      0 < Real.sqrt (Real.log (Real.log (x : ℝ))) :=
    lt_of_lt_of_le (by norm_num) hroot
  have hE1 :
      8 * Real.log (x : ℝ) /
          Real.sqrt (Real.log (Real.log (x : ℝ))) ≤
        Real.log (x : ℝ) / 640 := by
    rw [div_le_iff₀ hspos]
    have hm :=
      mul_le_mul_of_nonneg_left hroot
        (div_nonneg hlogxpos.le (by norm_num : (0 : ℝ) ≤ 640))
    calc
      8 * Real.log (x : ℝ) =
          (Real.log (x : ℝ) / 640) * 5120 := by ring
      _ ≤ (Real.log (x : ℝ) / 640) *
          Real.sqrt (Real.log (Real.log (x : ℝ))) := hm
  have hzposNat : 0 < z := by
    by_contra hz
    have : z = 0 := Nat.eq_zero_of_not_pos hz
    subst z
    simp at hxz
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hzposNat
  have hxzR : (x : ℝ) < (z : ℝ) ^ 160 := by exact_mod_cast hxz
  have hlogxz :
      Real.log (x : ℝ) < 160 * Real.log (z : ℝ) := by
    rw [Real.log_lt_iff_lt_exp hxpos]
    calc
      (x : ℝ) < (z : ℝ) ^ 160 := hxzR
      _ = Real.exp (160 * Real.log (z : ℝ)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hzpos]
        congr 1
        ring
  have hE2 :
      Real.log (x : ℝ) / 640 ≤ Real.log (z : ℝ) / 4 := by
    linarith
  have hS1 := hX1 x hx1
  calc
    (squarefreeSmoothCount x (shiuLogLogSmoothThreshold x) : ℝ)
        ≤ Real.exp
          (8 * Real.log (x : ℝ) /
            Real.sqrt (Real.log (Real.log (x : ℝ)))) := hS1
    _ ≤ Real.exp (Real.log (z : ℝ) / 4) := by
      exact Real.exp_le_exp.mpr (hE1.trans hE2)
    _ = (z : ℝ) ^ (1 / 4 : ℝ) := by
      rw [Real.rpow_def_of_pos hzpos]
      congr 1
      ring

/-- The admissible S8 prefix-factor pool is eventually at most z^(1/4). -/
theorem classIIIFactors_card_quarter :
    ∃ X0 : ℕ, ∀ x z k : ℕ, X0 ≤ x → x < z ^ 160 →
      ((classIIIFactors x z k).card : ℝ) ≤
        (z : ℝ) ^ (1 / 4 : ℝ) := by
  obtain ⟨X0, hX0⟩ := smoothCount_loglog_le_quarter_of_pow
  refine ⟨X0, ?_⟩
  intro x z k hx hxz
  have hcardNat := classIIIFactors_card_le_smoothCount x z k
  have hcard :
      ((classIIIFactors x z k).card : ℝ) ≤
        (squarefreeSmoothCount x (shiuLogLogSmoothThreshold x) : ℝ) := by
    exact_mod_cast hcardNat
  exact hcard.trans (hX0 x z hx hxz)

/-- S8: Class III count.  This is the exact source mechanism needed later:
a smooth-factor overcount, with a fixed absolute constant, eventually bounded
by y/k*z^(-1/4) plus z. -/
theorem shiu_classIII_count :
    ∃ X0 : ℕ, ∀ x y z k a : ℕ,
      X0 ≤ x → y ≤ x → x < z ^ 160 → 0 < k →
      classIIIOvercount x y z k a ≤
        5 * (((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ) +
          (z : ℝ)) := by
  obtain ⟨X0, hcardQ⟩ := classIIIFactors_card_quarter
  refine ⟨X0, ?_⟩
  intro x y z k a hx hyx hxz hk
  classical
  let B := classIIIFactors x z k
  let Zq : ℝ := (z : ℝ) ^ (1 / 4 : ℝ)
  let Zh : ℝ := (z : ℝ) ^ (1 / 2 : ℝ)
  have hzposNat : 0 < z := by
    by_contra hz
    have : z = 0 := Nat.eq_zero_of_not_pos hz
    subst z
    simp at hxz
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hzposNat
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hZhpos : 0 < Zh := by
    dsimp [Zh]
    exact Real.rpow_pos_of_pos hzpos _
  have hBcard :
      (B.card : ℝ) ≤ Zq := by
    dsimp [B, Zq]
    exact hcardQ x z k hx hxz
  have hpoint :
      ∀ b ∈ B,
        (PaperB.M4A.apDivCount x y k a b : ℝ) ≤
          (y : ℝ) / ((k : ℝ) * Zh) + 4 := by
    intro b hb
    have hbF := Finset.mem_filter.mp hb
    have hbSmooth := Finset.mem_filter.mp hbF.1
    have hbI := Finset.mem_Icc.mp hbSmooth.1
    have hbpos : 0 < b := by omega
    have hcop : b.Coprime k := hbF.2.2.1
    have hcop' : k.Coprime b := hcop.symm
    obtain ⟨C, hC, hEq⟩ :=
      PaperB.M4A.apDivCount_realApprox x y k a b
        hyx hk hbpos hcop'
    have hCup : C ≤ 4 := (le_abs_self C).trans hC
    have hbLarge : Zh ≤ (b : ℝ) := by
      simpa [B, Zh] using hbF.2.2.2
    have hden :
        (k : ℝ) * Zh ≤ (k : ℝ) * (b : ℝ) :=
      mul_le_mul_of_nonneg_left hbLarge hkR.le
    have hfrac :
        (y : ℝ) / ((k : ℝ) * (b : ℝ)) ≤
          (y : ℝ) / ((k : ℝ) * Zh) := by
      exact div_le_div_of_nonneg_left
        (by positivity) (mul_pos hkR hZhpos) hden
    calc
      (PaperB.M4A.apDivCount x y k a b : ℝ) =
          (y : ℝ) / ((k : ℝ) * (b : ℝ)) + C := hEq
      _ ≤ (y : ℝ) / ((k : ℝ) * (b : ℝ)) + 4 := by linarith
      _ ≤ (y : ℝ) / ((k : ℝ) * Zh) + 4 := by
        exact add_le_add hfrac le_rfl
  have hQnonneg :
      0 ≤ (y : ℝ) / ((k : ℝ) * Zh) + 4 := by positivity
  have hsum :
      classIIIOvercount x y z k a ≤
        Zq * ((y : ℝ) / ((k : ℝ) * Zh) + 4) := by
    unfold classIIIOvercount
    change (∑ b ∈ B, (PaperB.M4A.apDivCount x y k a b : ℝ)) ≤ _
    calc
      (∑ b ∈ B, (PaperB.M4A.apDivCount x y k a b : ℝ))
          ≤ ∑ _b ∈ B, ((y : ℝ) / ((k : ℝ) * Zh) + 4) :=
        Finset.sum_le_sum fun b hb => hpoint b hb
      _ = (B.card : ℝ) * ((y : ℝ) / ((k : ℝ) * Zh) + 4) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Zq * ((y : ℝ) / ((k : ℝ) * Zh) + 4) :=
        mul_le_mul_of_nonneg_right hBcard hQnonneg
  have hratio :
      Zq / Zh = (z : ℝ) ^ (-1 / 4 : ℝ) := by
    dsimp [Zq, Zh]
    rw [← Real.rpow_sub hzpos]
    congr 1
    ring
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hzposNat
  have hZqz : Zq ≤ (z : ℝ) := by
    dsimp [Zq]
    exact Real.rpow_le_self_of_one_le hz1 (by norm_num)
  have hrewrite :
      Zq * ((y : ℝ) / ((k : ℝ) * Zh) + 4) =
        ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ) +
          4 * Zq := by
    rw [← hratio]
    field_simp [ne_of_gt hkR, ne_of_gt hZhpos]
  calc
    classIIIOvercount x y z k a
        ≤ Zq * ((y : ℝ) / ((k : ℝ) * Zh) + 4) := hsum
    _ = ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ) +
          4 * Zq := hrewrite
    _ ≤ ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ) +
          4 * (z : ℝ) := by
      gcongr
    _ ≤ 5 * (((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ) +
          (z : ℝ)) := by
      have ht :
          0 ≤ ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ) := by
        positivity
      have hz0 : (0 : ℝ) ≤ (z : ℝ) := by positivity
      nlinarith

end M4B
end PaperB
