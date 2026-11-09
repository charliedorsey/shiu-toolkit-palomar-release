module

public import ShiuPublic.VaelisSmoothDivisor
public import PaperB.M4B.ShiuClassIII

public section

namespace PaperB.M4B
open scoped BigOperators
open Finset Nat Real
noncomputable section

/-- Full-prime-power Class III prefix candidate, without a squarefree filter. -/
@[expose] def corvethClassicalClassIIIFactors (x z k : ℕ) : Finset ℕ := by
  classical
  exact (Shiu.boundedSmoothSet (Nat.primesLE (shiuLogLogSmoothThreshold x)) x).filter
    (fun b => b ≤ z ∧ b.Coprime k ∧
      (z : ℝ) ^ (1 / 2 : ℝ) ≤ (b : ℝ))

@[expose] def corvethClassicalClassIIIOvercount (x y z k a : ℕ) : ℝ := by
  classical
  exact ∑ b ∈ corvethClassicalClassIIIFactors x z k,
    (PaperB.M4A.apDivCount x y k a b : ℝ)

/-- Exact original AP/divisor overcount once the unrestricted smooth-prefix
cardinality estimate is supplied. Only that cardinality remains analytic. -/
theorem corveth_classical_classIII_count_of_card
    (x y z k a : ℕ)
    (hyx : y ≤ x) (hxz : x < z ^ 160) (hk : 0 < k)
    (hcard : ((corvethClassicalClassIIIFactors x z k).card : ℝ) ≤
      (z : ℝ) ^ (1 / 4 : ℝ)) :
    corvethClassicalClassIIIOvercount x y z k a ≤
      5 * (((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ) +
        (z : ℝ)) := by
  classical
  let B := corvethClassicalClassIIIFactors x z k
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
    exact hcard
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
      corvethClassicalClassIIIOvercount x y z k a ≤
        Zq * ((y : ℝ) / ((k : ℝ) * Zh) + 4) := by
    unfold corvethClassicalClassIIIOvercount
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
    corvethClassicalClassIIIOvercount x y z k a
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

#print axioms corveth_classical_classIII_count_of_card
end
end PaperB.M4B
