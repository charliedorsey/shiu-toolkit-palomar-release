module

public import PaperB.M4A.SelectivePrimeProduct
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Basic.Real.Basic

public section

set_option autoImplicit false

open Finset Nat

namespace PaperB
namespace M4A

/-- Number of points in the short interval `(x-y,x]` which lie in the
reduced progression `a mod k` and are divisible by `d`. -/
@[expose] def apDivCount (x y k a d : ℕ) : ℕ :=
  ((Finset.Ioc (x - y) x).filter
    (fun n => n ≡ a [MOD k] ∧ d ∣ n)).card

private theorem natDivRealApprox
    (a b : ℕ) (hb : 0 < b) :
    ∃ C : ℝ, abs C ≤ 1 ∧
      ((a / b : ℕ) : ℝ) = (a : ℝ) / (b : ℝ) + C := by
  let C : ℝ := -((a % b : ℕ) : ℝ) / (b : ℝ)
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hmod : a % b < b := Nat.mod_lt a hb
  have hmodR : ((a % b : ℕ) : ℝ) < (b : ℝ) := by exact_mod_cast hmod
  have hCnonneg : 0 ≤ ((a % b : ℕ) : ℝ) / (b : ℝ) := by positivity
  have hClt : ((a % b : ℕ) : ℝ) / (b : ℝ) < 1 := by
    exact (div_lt_one hbR).2 hmodR
  have hdiv := Nat.mod_add_div a b
  have hdivR :
      ((a % b : ℕ) : ℝ) + (b : ℝ) * ((a / b : ℕ) : ℝ) = (a : ℝ) := by
    exact_mod_cast hdiv
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    rw [neg_div, abs_neg, abs_of_nonneg hCnonneg]
    exact le_of_lt hClt
  · dsimp [C]
    field_simp [ne_of_gt hbR]
    nlinarith

/-- A prefix residue-class count differs from its density prediction by at
most two.  The loose constant is deliberate: M4A only needs an absolute
bounded remainder before the Selberg double sum. -/
private theorem prefixModEqApprox
    (b r v : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, abs C ≤ 2 ∧
      ((b.count (fun n => n ≡ v [MOD r]) : ℕ) : ℝ) =
        (b : ℝ) / (r : ℝ) + C := by
  obtain ⟨C, hC, hdiv⟩ := natDivRealApprox b r hr
  by_cases h : v % r < b % r
  · refine ⟨C + 1, ?_, ?_⟩
    · have hadd := abs_add_le C (1 : ℝ)
      norm_num at hadd
      linarith
    · rw [Nat.count_modEq_card b hr v, if_pos h]
      push_cast
      rw [hdiv]
      ring
  · refine ⟨C, hC.trans (by norm_num), ?_⟩
    rw [Nat.count_modEq_card b hr v, if_neg h]
    push_cast
    simpa using hdiv

private theorem prefixModEq_mono
    {A B r v : ℕ} (hAB : A ≤ B) :
    A.count (fun n => n ≡ v [MOD r]) ≤
      B.count (fun n => n ≡ v [MOD r]) := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨lt_of_lt_of_le hn.1 hAB, hn.2⟩

private theorem IocModEqCard_eq_prefix_sub
    (A B r v : ℕ) (hAB : A ≤ B) :
    ((Finset.Ioc A B).filter (fun n => n ≡ v [MOD r])).card =
      (B + 1).count (fun n => n ≡ v [MOD r]) -
        (A + 1).count (fun n => n ≡ v [MOD r]) := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  let big :=
    (Finset.range (B + 1)).filter (fun n => n ≡ v [MOD r])
  let small :=
    (Finset.range (A + 1)).filter (fun n => n ≡ v [MOD r])
  have hsmall : small ⊆ big := by
    intro n hn
    dsimp [small, big] at hn ⊢
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    exact ⟨by omega, hn.2⟩
  have hset :
      (Finset.Ioc A B).filter (fun n => n ≡ v [MOD r]) =
        big \ small := by
    ext n
    dsimp [small, big]
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff,
      Finset.mem_range]
    constructor
    · intro h
      refine ⟨⟨by omega, h.2⟩, ?_⟩
      intro hs
      omega
    · intro h
      have hnA : A < n := by
        by_contra hnA
        apply h.2
        exact ⟨by omega, h.1.2⟩
      exact ⟨⟨hnA, Nat.lt_succ_iff.mp h.1.1⟩, h.1.2⟩
  rw [hset, Finset.card_sdiff_of_subset hsmall]

/-- Uniform absolute remainder for one residue class in a natural interval. -/
theorem IocModEqCard_realApprox
    (A B r v : ℕ) (hAB : A ≤ B) (hr : 0 < r) :
    ∃ C : ℝ, abs C ≤ 4 ∧
      (((Finset.Ioc A B).filter
        (fun n => n ≡ v [MOD r])).card : ℝ) =
        ((B - A : ℕ) : ℝ) / (r : ℝ) + C := by
  obtain ⟨CB, hCB, hB⟩ := prefixModEqApprox (B + 1) r v hr
  obtain ⟨CA, hCA, hA⟩ := prefixModEqApprox (A + 1) r v hr
  have hmono :
      (A + 1).count (fun n => n ≡ v [MOD r]) ≤
        (B + 1).count (fun n => n ≡ v [MOD r]) :=
    prefixModEq_mono (Nat.add_le_add_right hAB 1)
  refine ⟨CB - CA, ?_, ?_⟩
  · have hsub := abs_sub CB CA
    linarith
  · rw [IocModEqCard_eq_prefix_sub A B r v hAB, Nat.cast_sub hmono]
    rw [hB, hA]
    push_cast
    rw [Nat.cast_sub hAB]
    ring

/-- CRT residue joining `n = a (mod k)` with `d | n`. -/
def apDivResidue (k a d : ℕ) (hkd : k.Coprime d) : ℕ :=
  Nat.chineseRemainder hkd a 0

theorem apDivResidue_spec
    (k a d : ℕ) (hkd : k.Coprime d) :
    apDivResidue k a d hkd ≡ a [MOD k] ∧
      d ∣ apDivResidue k a d hkd := by
  unfold apDivResidue
  refine ⟨(Nat.chineseRemainder hkd a 0).prop.1, ?_⟩
  exact Nat.modEq_zero_iff_dvd.mp
    (Nat.chineseRemainder hkd a 0).prop.2

theorem apDivCondition_iff_crtResidue
    {n k a d : ℕ} (hkd : k.Coprime d) :
    (n ≡ a [MOD k] ∧ d ∣ n) ↔
      n ≡ apDivResidue k a d hkd [MOD k * d] := by
  let r := apDivResidue k a d hkd
  have hr := apDivResidue_spec k a d hkd
  constructor
  · intro h
    apply Nat.chineseRemainder_modEq_unique hkd
    · exact h.1
    · exact Nat.modEq_zero_iff_dvd.mpr h.2
  · intro h
    have hp := (Nat.modEq_and_modEq_iff_modEq_mul hkd).mpr h
    refine ⟨hp.1.trans hr.1, ?_⟩
    exact Nat.modEq_zero_iff_dvd.mp (hp.2.trans
      (Nat.modEq_zero_iff_dvd.mpr hr.2))

theorem apDivCount_eq_crtCount
    (x y k a d : ℕ) (hkd : k.Coprime d) :
    apDivCount x y k a d =
      ((Finset.Ioc (x - y) x).filter
        (fun n => n ≡ apDivResidue k a d hkd [MOD k * d])).card := by
  unfold apDivCount
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  exact and_congr_right (fun _ => apDivCondition_iff_crtResidue hkd)

/-- The AP-plus-divisibility count required by the selective Selberg sieve.
The remainder is an absolute constant, independent of all six parameters. -/
theorem apDivCount_realApprox
    (x y k a d : ℕ)
    (hyx : y ≤ x) (hk : 0 < k) (hd : 0 < d)
    (hkd : k.Coprime d) :
    ∃ C : ℝ, abs C ≤ 4 ∧
      (apDivCount x y k a d : ℝ) =
        (y : ℝ) / ((k : ℝ) * (d : ℝ)) + C := by
  have hAB : x - y ≤ x := Nat.sub_le x y
  have hmod : 0 < k * d := Nat.mul_pos hk hd
  obtain ⟨C, hC, hEq⟩ :=
    IocModEqCard_realApprox (x - y) x (k * d)
      (apDivResidue k a d hkd) hAB hmod
  refine ⟨C, hC, ?_⟩
  rw [apDivCount_eq_crtCount x y k a d hkd, hEq]
  have hxy : x - (x - y) = y := Nat.sub_sub_self hyx
  rw [hxy]
  push_cast
  ring

end M4A
end PaperB
