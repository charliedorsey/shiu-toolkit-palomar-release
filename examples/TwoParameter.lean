module

public import Shiu.TwoParameter

public section

/-!
An independent import consumer of the **proved upper-right quadrant**
of the original Shiu two-parameter region. The threshold is uniform in
alpha, beta and f for fixed A and B.
-/

namespace Shiu.ConsumerExamples
open scoped BigOperators

example (A B : ℝ) :
    ∃ X0 : ℕ, ∀ alpha beta : ℝ,
      (1 / 4 : ℝ) ≤ alpha →
      alpha < (1 / 2 : ℝ) →
      (1 / 4 : ℝ) ≤ beta →
      beta < (1 / 2 : ℝ) →
      ∀ f : ArithmeticFunction ℝ,
        Shiu.ClassicalEnvelope f A →
        0 ≤ B →
        (∀ n : ℕ, 1 ≤ n →
          f n ≤ B * (n : ℝ) ^ (1 / 1280 : ℝ)) →
        ∀ x y k a : ℕ,
          X0 ≤ x →
          (x : ℝ) ^ beta < (y : ℝ) →
          y ≤ x →
          (k : ℝ) < (y : ℝ) ^ (1 - alpha) →
          0 < a → a < k → a.Coprime k →
          Shiu.API.progressionSum f x y k a ≤
            Shiu.API.classicalConstant A B *
              ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
              Real.exp (Shiu.API.primeMass f x k) :=
  Shiu.API.classical_two_parameter_quadrant A B

end Shiu.ConsumerExamples

/-! Concrete parameter choice: alpha=3/8 and beta=2/5, different
from the original fixed-quarter pair. No new growth hypotheses. -/

namespace Shiu.ConsumerExamples
open scoped BigOperators

example (A B : ℝ) :
    ∃ X0 : ℕ, ∀ f : ArithmeticFunction ℝ,
      Shiu.ClassicalEnvelope f A →
      0 ≤ B →
      (∀ n : ℕ, 1 ≤ n →
        f n ≤ B * (n : ℝ) ^ (1 / 1280 : ℝ)) →
      ∀ x y k a : ℕ,
        X0 ≤ x →
        (x : ℝ) ^ (2 / 5 : ℝ) < (y : ℝ) →
        y ≤ x →
        (k : ℝ) < (y : ℝ) ^ (1 - 3 / 8 : ℝ) →
        0 < a → a < k → a.Coprime k →
        Shiu.API.progressionSum f x y k a ≤
          Shiu.API.classicalConstant A B *
            ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
            Real.exp (Shiu.API.primeMass f x k) := by
  obtain ⟨X0, h⟩ := Shiu.API.classical_two_parameter_quadrant A B
  refine ⟨X0, ?_⟩
  intro f hf hB hgrowth x y k a hx hxy hyx hk ha hak hcop
  exact h (3 / 8 : ℝ) (2 / 5 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    f hf hB hgrowth x y k a hx hxy hyx hk ha hak hcop

end Shiu.ConsumerExamples
