module

public import ShiuPublic.CorvethClassicalClassIII
public import ShiuPublic.PrimePowerEnvelope

public import PaperB.M4B.ShiuSmallException

public section

namespace PaperB.M4B
open scoped BigOperators
open Finset Nat Real
noncomputable section

@[expose] def corvethClassicalClassIIIWeightedOvercount
    (f : ArithmeticFunction ℝ) (x y z k a : ℕ) : ℝ := by
  classical
  exact ∑ b ∈ corvethClassicalClassIIIFactors x z k,
    ∑ n ∈ (Finset.Ioc (x - y) x).filter
      (fun n => n ≡ a [MOD k] ∧ b ∣ n), f n

theorem corveth_classIIIWeightedOvercount_le_growth
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : Shiu.ClassicalEnvelope f A) (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n →
      f n ≤ B * (n : ℝ) ^ (1 / 1280 : ℝ))
    (x y z k a : ℕ) :
    corvethClassicalClassIIIWeightedOvercount f x y z k a ≤
      (B * (x : ℝ) ^ (1 / 1280 : ℝ)) *
      corvethClassicalClassIIIOvercount x y z k a := by
  classical
  let G : ℝ := B * (x : ℝ) ^ (1 / 1280 : ℝ)
  have hG0 : 0 ≤ G := by
    dsimp [G]
    exact mul_nonneg hB (Real.rpow_nonneg (by positivity) _)
  have hinner :
      ∀ b ∈ corvethClassicalClassIIIFactors x z k,
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
      exact (hgrowth n (by omega)).trans
        (mul_le_mul_of_nonneg_left hpow hB)
    change (∑ n ∈ S, f n) ≤ _
    calc
      (∑ n ∈ S, f n) ≤ ∑ _n ∈ S, G :=
        Finset.sum_le_sum fun n hn => hpoint n hn
      _ = G * (S.card : ℝ) := by simp [mul_comm]
      _ = G * (PaperB.M4A.apDivCount x y k a b : ℝ) := by
        congr 1
  unfold corvethClassicalClassIIIWeightedOvercount corvethClassicalClassIIIOvercount
  change
    (∑ b ∈ corvethClassicalClassIIIFactors x z k,
      ∑ n ∈ (Finset.Ioc (x - y) x).filter
        (fun n => n ≡ a [MOD k] ∧ b ∣ n), f n) ≤
      G * ∑ b ∈ corvethClassicalClassIIIFactors x z k,
        (PaperB.M4A.apDivCount x y k a b : ℝ)
  calc
    (∑ b ∈ corvethClassicalClassIIIFactors x z k,
      ∑ n ∈ (Finset.Ioc (x - y) x).filter
        (fun n => n ≡ a [MOD k] ∧ b ∣ n), f n)
        ≤ ∑ b ∈ corvethClassicalClassIIIFactors x z k,
          G * (PaperB.M4A.apDivCount x y k a b : ℝ) :=
      Finset.sum_le_sum fun b hb => hinner b hb
    _ = G * ∑ b ∈ corvethClassicalClassIIIFactors x z k,
          (PaperB.M4A.apDivCount x y k a b : ℝ) := by
      rw [Finset.mul_sum]
    _ = (B * (x : ℝ) ^ (1 / 1280 : ℝ)) *
          ∑ b ∈ corvethClassicalClassIIIFactors x z k,
            (PaperB.M4A.apDivCount x y k a b : ℝ) := by
      rfl


theorem corveth_classical_classIII_weighted_of_card
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : Shiu.ClassicalEnvelope f A) (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n →
      f n ≤ B * (n : ℝ) ^ (1 / 1280 : ℝ))
    (x y z k a : ℕ)
    (hyx : y ≤ x) (hxz : x < z ^ 160) (hk : 0 < k)
    (hcard : ((corvethClassicalClassIIIFactors x z k).card : ℝ) ≤
      (z : ℝ) ^ (1 / 4 : ℝ))
    (hzabsorb : (z : ℝ) ≤
      ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ)) :
    corvethClassicalClassIIIWeightedOvercount f x y z k a ≤
      (10 * B) *
        (((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 8 : ℝ)) := by
  have hzposNat : 0 < z := by
    by_contra hz
    have : z = 0 := Nat.eq_zero_of_not_pos hz
    subst z
    simp at hxz
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hzposNat
  have hcount0 : 0 ≤ corvethClassicalClassIIIOvercount x y z k a := by
    unfold corvethClassicalClassIIIOvercount
    positivity
  have hmass :=
    corveth_classIIIWeightedOvercount_le_growth hf hB hgrowth x y z k a
  have hxscale := growthScale_le_eighth_of_pow hxz
  have hfactor :
      B * (x : ℝ) ^ (1 / 1280 : ℝ) ≤
        B * (z : ℝ) ^ (1 / 8 : ℝ) :=
    mul_le_mul_of_nonneg_left hxscale hB
  have hmass' :
      corvethClassicalClassIIIWeightedOvercount f x y z k a ≤
        (B * (z : ℝ) ^ (1 / 8 : ℝ)) *
          corvethClassicalClassIIIOvercount x y z k a := by
    exact hmass.trans
      (mul_le_mul_of_nonneg_right hfactor hcount0)
  have hIIIbound := corveth_classical_classIII_count_of_card x y z k a hyx hxz hk hcard
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
      0 ≤ B * (z : ℝ) ^ (1 / 8 : ℝ) :=
    mul_nonneg hB (Real.rpow_nonneg hz0 _)
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
    corvethClassicalClassIIIWeightedOvercount f x y z k a
        ≤ (B * (z : ℝ) ^ (1 / 8 : ℝ)) *
            corvethClassicalClassIIIOvercount x y z k a := hmass'
    _ ≤ (B * (z : ℝ) ^ (1 / 8 : ℝ)) *
          (5 * (T + (z : ℝ))) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [T] using hIIIbound
      · exact hfac0
    _ ≤ (B * (z : ℝ) ^ (1 / 8 : ℝ)) * (10 * T) := by
      exact mul_le_mul_of_nonneg_left hsum hfac0
    _ = (10 * B) *
          ((z : ℝ) ^ (1 / 8 : ℝ) * T) := by ring
    _ = (10 * B) * U := by
      rw [hscaleT]
    _ = (10 * B) *
          (((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 8 : ℝ)) := by
      rfl

#print axioms corveth_classIIIWeightedOvercount_le_growth
#print axioms corveth_classical_classIII_weighted_of_card
end
end PaperB.M4B
