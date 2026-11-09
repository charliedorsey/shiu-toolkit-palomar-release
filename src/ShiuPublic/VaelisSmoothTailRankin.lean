module

public import ShiuPublic.VaelisOriginalSmoothEuler
public import ShiuPublic.RankinPowerGate

public section

namespace Shiu
open scoped BigOperators

/-- All multiplicities allowed: the original positive smooth integers
above a sharp Rankin threshold and below a finite height cap. -/
@[expose] def boundedSmoothTailSet (S : Finset ℕ) (T X : ℕ) : Finset ℕ :=
  (boundedSmoothSet S X).filter (fun n => T ≤ n)

/-- Source-neutral non-squarefree Rankin suppression with a sharp lower
threshold, retaining the same finite admissible smooth family. -/
theorem bounded_smooth_tail_rankin_le
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : ClassicalEnvelope f A) (S : Finset ℕ)
    (T X : ℕ) (hT : 1 ≤ T) (δ : ℝ) (hδ : 0 ≤ δ) :
    (∑ n ∈ boundedSmoothTailSet S T X, f n / (n : ℝ)) ≤
       (T : ℝ) ^ (-δ) *
       (∑ n ∈ boundedSmoothSet S X, f n / (n : ℝ) ^ (1-δ)) := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hT)
  have hpoint : ∀ n ∈ boundedSmoothTailSet S T X,
      f n / (n : ℝ) ≤
        (T : ℝ) ^ (-δ) * (f n / (n : ℝ) ^ (1-δ)) := by
    intro n hn
    have hnT : T ≤ n := (Finset.mem_filter.mp hn).2
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (hT.trans hnT))
    have hpow : (T : ℝ) ^ δ ≤ (n : ℝ) ^ δ := by
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnT) hδ
    have hF : (0 : ℝ) < (T : ℝ) ^ δ := Real.rpow_pos_of_pos hTpos _
    have hratio : (1 : ℝ) ≤ (T : ℝ) ^ (-δ) * (n : ℝ) ^ δ := by
      rw [Real.rpow_neg hTpos.le, inv_mul_eq_div]
      exact (le_div_iff₀ hF).2 (by simpa using hpow)
    have hscale : (1 : ℝ) / (n : ℝ) ≤
        (T : ℝ) ^ (-δ) / (n : ℝ) ^ (1-δ) := by
      rw [Real.rpow_sub hnpos, Real.rpow_one, div_div_eq_mul_div,
        div_le_div_iff_of_pos_right hnpos]
      simpa using hratio
    calc
      f n / (n : ℝ) = f n * ((1 : ℝ) / (n : ℝ)) := by ring
      _ ≤ f n * ((T : ℝ) ^ (-δ) / (n : ℝ) ^ (1-δ)) :=
        mul_le_mul_of_nonneg_left hscale (hf.nonnegative n)
      _ = (T : ℝ) ^ (-δ) * (f n / (n : ℝ) ^ (1-δ)) := by ring
  calc
    (∑ n ∈ boundedSmoothTailSet S T X, f n / (n : ℝ)) ≤
      ∑ n ∈ boundedSmoothTailSet S T X,
        (T : ℝ) ^ (-δ) * (f n / (n : ℝ) ^ (1-δ)) :=
        Finset.sum_le_sum hpoint
    _ ≤ ∑ n ∈ boundedSmoothSet S X,
        (T : ℝ) ^ (-δ) * (f n / (n : ℝ) ^ (1-δ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro n hn _
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (div_nonneg (hf.nonnegative _) (Real.rpow_nonneg (by positivity) _))
    _ = (T : ℝ) ^ (-δ) *
        (∑ n ∈ boundedSmoothSet S X, f n / (n : ℝ) ^ (1-δ)) := by
      rw [Finset.mul_sum]

#print axioms Shiu.bounded_smooth_tail_rankin_le
end Shiu
