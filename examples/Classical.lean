module

public import Shiu.Classical

public section

/-! Genuine classical API consumer: all source hypotheses are shown. -/
open scoped BigOperators
namespace Shiu.ConsumerExamples

example (A B : ℝ) :
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
        Shiu.API.progressionSum f x y k a ≤
          Shiu.API.classicalConstant A B *
            ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
            Real.exp (PaperB.M4B.primeMass f x k) := by
  exact Shiu.API.classical_quarter A B

end Shiu.ConsumerExamples
