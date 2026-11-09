module

public import Shiu.Progressions
public import Orienne.UnrestrictedFixedQuarter

public import ChallengeDefs.Constant

public section

/-! Classical non-squarefree fixed-quarter theorem.
Threshold X0 precedes f. Extra uniform B n^(1/1280) is NOT removed. -/
namespace Shiu.API
open scoped BigOperators

-- Shared Mathlib-only source definition: ChallengeDefs.Constant.classicalConstant

theorem classical_quarter (A B : ℝ) :
    ∃ X0 : ℕ, ∀ f : ArithmeticFunction ℝ,
      Shiu.ClassicalEnvelope f A →
      0 ≤ B →
      (∀ n : ℕ, 1 ≤ n →
        f n ≤ B * (n : ℝ) ^ (1 / 1280 : ℝ)) →
      ∀ x y k a : ℕ,
        X0 ≤ x →
        (x : ℝ) ^ (1 / 4 : ℝ) < (y : ℝ) →
        y ≤ x →
        (k : ℝ) < (y : ℝ) ^ (3 / 4 : ℝ) →
        0 < a → a < k → a.Coprime k →
        progressionSum f x y k a ≤
          classicalConstant A B *
            ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
            Real.exp (primeMass f x k) := by
  obtain ⟨X0, h⟩ :=
    PaperB.M4B.orienne_unrestricted_shiu_fixed_quarter A B
  refine ⟨X0, ?_⟩
  intro f hf hB hgrowth x y k a hx hxy hyx hky ha0 hak hc
  rw [progressionSum_eq_source f x y k a hc]
  exact h f hf hB hgrowth x y k a
    hx hxy hyx hky ha0 hak hc

#print axioms classical_quarter
end Shiu.API
