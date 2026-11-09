module

public import Shiu.ClassicalCorollaries

public section

/-!
Two real Tier-2 classical consumers; neither widens the source to
theta < 1/4, and the individual-f existential B is NOT uniform.
-/
namespace Shiu.ConsumerExamples
open scoped BigOperators

example (A : ℝ) (f : ArithmeticFunction ℝ)
    (hf : Shiu.ClassicalEnvelope f A) :
    ∃ B : ℝ, 0 < B ∧ ∃ X0 : ℕ,
      ∀ x y k a : ℕ,
        X0 ≤ x → (x : ℝ) ^ (1/4 : ℝ) < (y : ℝ) →
        y ≤ x → (k : ℝ) < (y : ℝ) ^ (3/4 : ℝ) →
        0 < a → a < k → a.Coprime k →
        Shiu.API.progressionSum f x y k a ≤
          Shiu.API.classicalConstant A B *
            ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
            Real.exp (PaperB.M4B.primeMass f x k) := by
  exact Shiu.API.classical_individual A f hf

example (A B : ℝ) :
    ∃ X0 : ℕ, ∀ theta : ℝ, (1/4 : ℝ) ≤ theta →
      ∀ f : ArithmeticFunction ℝ,
        Shiu.ClassicalEnvelope f A → 0 ≤ B →
        (∀ n : ℕ, 1 ≤ n →
          f n ≤ B * (n : ℝ) ^ (1/1280 : ℝ)) →
        ∀ x y k a : ℕ,
          X0 ≤ x → (x : ℝ) ^ theta < (y : ℝ) →
          y ≤ x → (k : ℝ) < (y : ℝ) ^ (3/4 : ℝ) →
          0 < a → a < k → a.Coprime k →
          Shiu.API.progressionSum f x y k a ≤
            Shiu.API.classicalConstant A B *
              ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
              Real.exp (PaperB.M4B.primeMass f x k) := by
  exact Shiu.API.classical_theta A B

end Shiu.ConsumerExamples
