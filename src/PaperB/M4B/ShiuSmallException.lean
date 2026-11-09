module

/-
Paper B M4B-CORE S9: weighted small-exception bound.
Authorized surface: exact M4B0 ledger row S9 only.

The historical Class-II contribution is deleted on the squarefree-supported
route.  Thus the specialized II+III exceptional mass is exactly the Class-III
weighted overcount.  Only the fixed growth exponent 1/1280 is used.
-/

public import PaperB.M4B.ShiuClassII
public import PaperB.M4B.ShiuClassIII

public section

open scoped BigOperators
open Finset Nat Real
open ArithmeticFunction

noncomputable section

namespace PaperB
namespace M4B

/-- Weighted version of the S8 Class-III overcount.  Multiplicity in the outer
b-sum is intentional: this is the source overcover, not a disjoint partition. -/
@[expose] def classIIIWeightedOvercount
    (f : ArithmeticFunction ℝ) (x y z k a : ℕ) : ℝ := by
  classical
  exact ∑ b ∈ classIIIFactors x z k,
    ∑ n ∈ (Finset.Ioc (x - y) x).filter
      (fun n => n ≡ a [MOD k] ∧ b ∣ n), f n

/-- On the specialized squarefree route the historical Class-II mass is zero,
so the S9 small-exception overcount is exactly Class III. -/
@[expose] def smallExceptionWeightedOvercount
    (f : ArithmeticFunction ℝ) (x y z k a : ℕ) : ℝ :=
  classIIIWeightedOvercount f x y z k a

/-- The one fixed growth witness converts the S8 count into weighted mass. -/
theorem classIIIWeightedOvercount_le_growth
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    (x y z k a : ℕ) :
    classIIIWeightedOvercount f x y z k a ≤
      (A2 * (x : ℝ) ^ (1 / 1280 : ℝ)) *
        classIIIOvercount x y z k a := by
  classical
  let G : ℝ := A2 * (x : ℝ) ^ (1 / 1280 : ℝ)
  have hG0 : 0 ≤ G := by
    dsimp [G]
    exact mul_nonneg hf.A2_nonneg (Real.rpow_nonneg (by positivity) _)
  have hinner :
      ∀ b ∈ classIIIFactors x z k,
        (∑ n ∈ (Finset.Ioc (x - y) x).filter
            (fun n => n ≡ a [MOD k] ∧ b ∣ n), f n) ≤
          G * (PaperB.M4A.apDivCount x y k a b : ℝ) := by
    intro b hb
    let S : Finset ℕ :=
      (Finset.Ioc (x - y) x).filter
        (fun n => n ≡ a [MOD k] ∧ b ∣ n)
    have hpoint : ∀ n ∈ S, f n ≤ G := by
      intro n hn
      have hnF := Finset.mem_filter.mp hn
      have hnI := Finset.mem_Ioc.mp hnF.1
      have hnR : (n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hnI.2
      have hpow :
          (n : ℝ) ^ (1 / 1280 : ℝ) ≤
            (x : ℝ) ^ (1 / 1280 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hnR (by norm_num)
      exact (hf.growth n).trans
        (mul_le_mul_of_nonneg_left hpow hf.A2_nonneg)
    change (∑ n ∈ S, f n) ≤ _
    calc
      (∑ n ∈ S, f n) ≤ ∑ _n ∈ S, G :=
        Finset.sum_le_sum fun n hn => hpoint n hn
      _ = G * (S.card : ℝ) := by simp [mul_comm]
      _ = G * (PaperB.M4A.apDivCount x y k a b : ℝ) := by
        congr 1
  unfold classIIIWeightedOvercount classIIIOvercount
  change
    (∑ b ∈ classIIIFactors x z k,
      ∑ n ∈ (Finset.Ioc (x - y) x).filter
        (fun n => n ≡ a [MOD k] ∧ b ∣ n), f n) ≤
      G * ∑ b ∈ classIIIFactors x z k,
        (PaperB.M4A.apDivCount x y k a b : ℝ)
  calc
    (∑ b ∈ classIIIFactors x z k,
      ∑ n ∈ (Finset.Ioc (x - y) x).filter
        (fun n => n ≡ a [MOD k] ∧ b ∣ n), f n)
        ≤ ∑ b ∈ classIIIFactors x z k,
          G * (PaperB.M4A.apDivCount x y k a b : ℝ) :=
      Finset.sum_le_sum fun b hb => hinner b hb
    _ = G * ∑ b ∈ classIIIFactors x z k,
          (PaperB.M4A.apDivCount x y k a b : ℝ) := by
      rw [Finset.mul_sum]
    _ = (A2 * (x : ℝ) ^ (1 / 1280 : ℝ)) *
          ∑ b ∈ classIIIFactors x z k,
            (PaperB.M4A.apDivCount x y k a b : ℝ) := by
      rfl

/-- The source relation x < z^160 turns the fixed 1/1280 growth exponent into
exactly the z^(1/8) loss used in (5.6). -/
theorem growthScale_le_eighth_of_pow
    {x z : ℕ} (hxz : x < z ^ 160) :
    (x : ℝ) ^ (1 / 1280 : ℝ) ≤
      (z : ℝ) ^ (1 / 8 : ℝ) := by
  have hxle : x ≤ z ^ 160 := Nat.le_of_lt hxz
  have hxleR : (x : ℝ) ≤ ((z ^ 160 : ℕ) : ℝ) := by
    exact_mod_cast hxle
  have hpow :=
    Real.rpow_le_rpow (Nat.cast_nonneg x) hxleR
      (by norm_num : (0 : ℝ) ≤ 1 / 1280)
  calc
    (x : ℝ) ^ (1 / 1280 : ℝ)
        ≤ ((z ^ 160 : ℕ) : ℝ) ^ (1 / 1280 : ℝ) := hpow
    _ = ((z : ℝ) ^ 160) ^ (1 / 1280 : ℝ) := by
      norm_num
    _ = (z : ℝ) ^ (1 / 8 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg z)]
      congr 1
      norm_num

/-- S9: weighted II+III exceptional contribution on the specialized route.
Historical Class II contributes zero.  The final hypothesis is the elementary
source parameter absorption z <= (y/k) z^(-1/4), established later by the
fixed-quarter z=y^(1/40), k<y^(3/4) setup. -/
theorem shiu_small_exception_weight_bound
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2) :
    ∃ X0 : ℕ, ∀ x y z k a : ℕ,
      X0 ≤ x → y ≤ x → x < z ^ 160 → 0 < k →
      (z : ℝ) ≤
        ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ) →
      smallExceptionWeightedOvercount f x y z k a ≤
        (10 * A2) *
          (((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 8 : ℝ)) := by
  obtain ⟨X0, hIII⟩ := shiu_classIII_count
  refine ⟨X0, ?_⟩
  intro x y z k a hx hyx hxz hk hzabsorb
  have hzposNat : 0 < z := by
    by_contra hz
    have : z = 0 := Nat.eq_zero_of_not_pos hz
    subst z
    simp at hxz
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hzposNat
  have hcount0 : 0 ≤ classIIIOvercount x y z k a := by
    unfold classIIIOvercount
    positivity
  have hmass :=
    classIIIWeightedOvercount_le_growth hf x y z k a
  have hxscale := growthScale_le_eighth_of_pow hxz
  have hfactor :
      A2 * (x : ℝ) ^ (1 / 1280 : ℝ) ≤
        A2 * (z : ℝ) ^ (1 / 8 : ℝ) :=
    mul_le_mul_of_nonneg_left hxscale hf.A2_nonneg
  have hmass' :
      smallExceptionWeightedOvercount f x y z k a ≤
        (A2 * (z : ℝ) ^ (1 / 8 : ℝ)) *
          classIIIOvercount x y z k a := by
    unfold smallExceptionWeightedOvercount
    exact hmass.trans
      (mul_le_mul_of_nonneg_right hfactor hcount0)
  have hIIIbound := hIII x y z k a hx hyx hxz hk
  let T : ℝ :=
    ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ)
  let U : ℝ :=
    ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 8 : ℝ)
  have hT0 : 0 ≤ T := by
    dsimp [T]
    positivity
  have hz0 : (0 : ℝ) ≤ (z : ℝ) := by positivity
  have hsum : 5 * (T + (z : ℝ)) ≤ 10 * T := by
    dsimp [T]
    nlinarith
  have hfac0 :
      0 ≤ A2 * (z : ℝ) ^ (1 / 8 : ℝ) :=
    mul_nonneg hf.A2_nonneg (Real.rpow_nonneg hz0 _)
  have hpow :
      (z : ℝ) ^ (1 / 8 : ℝ) *
          (z : ℝ) ^ (-1 / 4 : ℝ) =
        (z : ℝ) ^ (-1 / 8 : ℝ) := by
    rw [← Real.rpow_add hzpos]
    congr 1
    ring
  have hscaleT :
      (z : ℝ) ^ (1 / 8 : ℝ) * T = U := by
    dsimp [T, U]
    calc
      (z : ℝ) ^ (1 / 8 : ℝ) *
          (((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ))
          =
        ((y : ℝ) / (k : ℝ)) *
          ((z : ℝ) ^ (1 / 8 : ℝ) *
            (z : ℝ) ^ (-1 / 4 : ℝ)) := by ring
      _ = ((y : ℝ) / (k : ℝ)) *
          (z : ℝ) ^ (-1 / 8 : ℝ) := by rw [hpow]
  calc
    smallExceptionWeightedOvercount f x y z k a
        ≤ (A2 * (z : ℝ) ^ (1 / 8 : ℝ)) *
            classIIIOvercount x y z k a := hmass'
    _ ≤ (A2 * (z : ℝ) ^ (1 / 8 : ℝ)) *
          (5 * (T + (z : ℝ))) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [T] using hIIIbound
      · exact hfac0
    _ ≤ (A2 * (z : ℝ) ^ (1 / 8 : ℝ)) * (10 * T) := by
      exact mul_le_mul_of_nonneg_left hsum hfac0
    _ = (10 * A2) *
          ((z : ℝ) ^ (1 / 8 : ℝ) * T) := by ring
    _ = (10 * A2) * U := by
      rw [hscaleT]
    _ = (10 * A2) *
          (((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 8 : ℝ)) := by
      rfl

end M4B
end PaperB

namespace PaperB.M4B

/-- Packaging-only uniform form of the paid S9 bound.  The threshold comes
from the unweighted Class-III count and is therefore independent of the
enveloped arithmetic function. -/
theorem shiu_small_exception_weight_bound_uniform
    (A1 A2 : ℝ) :
    ∃ X0 : ℕ, ∀ f : ArithmeticFunction ℝ,
      FixedQuarterEnvelope f A1 A2 →
      ∀ x y z k a : ℕ,
      X0 ≤ x → y ≤ x → x < z ^ 160 → 0 < k →
      (z : ℝ) ≤
        ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ) →
      smallExceptionWeightedOvercount f x y z k a ≤
        (10 * A2) *
          (((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 8 : ℝ)) := by
  obtain ⟨X0, hIII⟩ := shiu_classIII_count
  refine ⟨X0, ?_⟩
  intro f hf x y z k a hx hyx hxz hk hzabsorb
  have hzposNat : 0 < z := by
    by_contra hz
    have : z = 0 := Nat.eq_zero_of_not_pos hz
    subst z
    simp at hxz
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hzposNat
  have hcount0 : 0 ≤ classIIIOvercount x y z k a := by
    unfold classIIIOvercount
    positivity
  have hmass := classIIIWeightedOvercount_le_growth hf x y z k a
  have hxscale := growthScale_le_eighth_of_pow hxz
  have hfactor :
      A2 * (x : ℝ) ^ (1 / 1280 : ℝ) ≤
        A2 * (z : ℝ) ^ (1 / 8 : ℝ) :=
    mul_le_mul_of_nonneg_left hxscale hf.A2_nonneg
  have hmass' :
      smallExceptionWeightedOvercount f x y z k a ≤
        (A2 * (z : ℝ) ^ (1 / 8 : ℝ)) *
          classIIIOvercount x y z k a := by
    unfold smallExceptionWeightedOvercount
    exact hmass.trans (mul_le_mul_of_nonneg_right hfactor hcount0)
  have hIIIbound := hIII x y z k a hx hyx hxz hk
  let T : ℝ := ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ)
  let U : ℝ := ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 8 : ℝ)
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hz0 : (0 : ℝ) ≤ (z : ℝ) := by positivity
  have hsum : 5 * (T + (z : ℝ)) ≤ 10 * T := by
    dsimp [T]
    nlinarith
  have hfac0 : 0 ≤ A2 * (z : ℝ) ^ (1 / 8 : ℝ) :=
    mul_nonneg hf.A2_nonneg (Real.rpow_nonneg hz0 _)
  have hpow :
      (z : ℝ) ^ (1 / 8 : ℝ) * (z : ℝ) ^ (-1 / 4 : ℝ) =
        (z : ℝ) ^ (-1 / 8 : ℝ) := by
    rw [← Real.rpow_add hzpos]
    congr 1
    ring
  have hscaleT : (z : ℝ) ^ (1 / 8 : ℝ) * T = U := by
    dsimp [T, U]
    calc
      (z : ℝ) ^ (1 / 8 : ℝ) *
          (((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ)) =
        ((y : ℝ) / (k : ℝ)) *
          ((z : ℝ) ^ (1 / 8 : ℝ) * (z : ℝ) ^ (-1 / 4 : ℝ)) := by ring
      _ = ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 8 : ℝ) := by rw [hpow]
  calc
    smallExceptionWeightedOvercount f x y z k a
        ≤ (A2 * (z : ℝ) ^ (1 / 8 : ℝ)) *
            classIIIOvercount x y z k a := hmass'
    _ ≤ (A2 * (z : ℝ) ^ (1 / 8 : ℝ)) * (5 * (T + (z : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (by simpa [T] using hIIIbound) hfac0
    _ ≤ (A2 * (z : ℝ) ^ (1 / 8 : ℝ)) * (10 * T) :=
      mul_le_mul_of_nonneg_left hsum hfac0
    _ = (10 * A2) * ((z : ℝ) ^ (1 / 8 : ℝ) * T) := by ring
    _ = (10 * A2) * U := by rw [hscaleT]
    _ = _ := by rfl

#print axioms shiu_small_exception_weight_bound_uniform

end PaperB.M4B
