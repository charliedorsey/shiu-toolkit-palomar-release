module

public import Shiu.ModulusOneFinal

public section

/-! External client: the unconditional k=1 statement, unchanged. -/
namespace Shiu.ConsumerExamples
open scoped BigOperators
open Shiu.API

example (A B : ℝ) :
    ∃ X0 : ℕ, ∀ f : ArithmeticFunction ℝ,
      Shiu.ClassicalEnvelope f A →
      0 ≤ B →
      (∀ n : ℕ, 1 ≤ n →
        f n ≤ B * (n : ℝ) ^ (1 / 1280 : ℝ)) →
      ∀ x y : ℕ,
        X0 ≤ x →
        (x : ℝ) ^ (1 / 4 : ℝ) < (y : ℝ) →
        y ≤ x →
        (∑ n ∈ Finset.Ioc (x-y) x, f n) ≤
          9 * classicalConstant A B *
            ((y : ℝ) / Real.log (x : ℝ)) *
            Real.exp (PaperB.M4B.primeMass f x 1) := by
  exact Shiu.API.classical_modulus_one_quarter A B

end Shiu.ConsumerExamples
