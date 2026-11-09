module

public import ShiuPublic.PrimePowerEnvelope
public import PaperB.M4B.ShiuClassIV

public section

namespace Shiu
open ArithmeticFunction
open scoped BigOperators

/-- The prime-power envelope is bounded by A to the full multiplicity
count, with no squarefree-support hypothesis. -/
theorem classical_weight_le_pow_omega
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : ClassicalEnvelope f A)
    (d : ℕ) (hd : d ≠ 0) :
    f d ≤ A ^ (ArithmeticFunction.cardFactors d) := by
  have h := classical_factorization_weight_bound hf d hd
  have heq : d.factorization.prod (fun p m => A ^ m) =
      A ^ (ArithmeticFunction.cardFactors d) := by
    rw [cardFactors_eq_sum_factorization]
    change (∏ p ∈ d.factorization.support,
        A ^ (d.factorization p)) =
      A ^ (∑ p ∈ d.factorization.support, d.factorization p)
    exact Finset.prod_pow_eq_pow_sum _ _ _
  exact h.trans (le_of_eq heq)

/-- Reuses the *literal* Class IV rough size gate, now counting
prime factors with repetitions. -/
theorem classical_classIV_rough_value_le
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : ClassicalEnvelope f A)
    {d x z p r : ℕ}
    (hdpos : 0 < d) (hx : x < z ^ 160)
    (hdx : d ≤ x) (hr : 1 ≤ r)
    (hp : 0 < p) (hzpr : z < p ^ (r + 1))
    (hrough : PaperB.M4A.shiuRough d p) :
    f d ≤ (1 + A) ^ (320 * r) := by
  have hlen := PaperB.M4B.classIV_rough_primeFactorsList_length_lt
    hdpos hx hdx hr hp hzpr hrough
  have hcard : ArithmeticFunction.cardFactors d ≤ 320 * r := by
    rw [cardFactors_apply]
    omega
  calc
    f d ≤ A ^ (ArithmeticFunction.cardFactors d) := classical_weight_le_pow_omega hf d (by omega)
    _ ≤ (1 + A) ^ (ArithmeticFunction.cardFactors d) :=
      (pow_le_pow_left₀ hf.A_nonnegative (by linarith : A ≤ 1 + A)) _
    _ ≤ (1 + A) ^ (320 * r) :=
      pow_le_pow_right₀ (by linarith [hf.A_nonnegative]) hcard

/-- The second literal shell uses the cutoff w+1. -/
theorem classical_classIV_rough_value_le_succ
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : ClassicalEnvelope f A)
    {d x z w r : ℕ}
    (hdpos : 0 < d) (hx : x < z ^ 160)
    (hdx : d ≤ x) (hr : 1 ≤ r)
    (hzwr : z < (w + 1) ^ (r + 1))
    (hrough : PaperB.M4A.shiuRough d w) :
    f d ≤ (1 + A) ^ (320 * r) := by
  have hlen := PaperB.M4B.classIV_rough_primeFactorsList_length_lt_succ
    hdpos hx hdx hr hzwr hrough
  have hcard : ArithmeticFunction.cardFactors d ≤ 320 * r := by
    rw [cardFactors_apply]
    omega
  calc
    f d ≤ A ^ (ArithmeticFunction.cardFactors d) := classical_weight_le_pow_omega hf d (by omega)
    _ ≤ (1 + A) ^ (ArithmeticFunction.cardFactors d) :=
      (pow_le_pow_left₀ hf.A_nonnegative (by linarith : A ≤ 1 + A)) _
    _ ≤ (1 + A) ^ (320 * r) :=
      pow_le_pow_right₀ (by linarith [hf.A_nonnegative]) hcard

#print axioms Shiu.classical_weight_le_pow_omega
#print axioms Shiu.classical_classIV_rough_value_le
#print axioms Shiu.classical_classIV_rough_value_le_succ
end Shiu
