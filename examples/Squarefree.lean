module

public import Shiu.Squarefree

public section

/-! Squarefree-supported theorem at theta >= 1/10. -/
open scoped BigOperators
namespace Shiu.ConsumerExamples

example (A B theta : ℝ) (htheta : (1 / 10 : ℝ) ≤ theta) :
    ∃ X0 : ℕ, ∀ f : ArithmeticFunction ℝ,
      Shiu.SquarefreeEnvelope f A B →
      ∀ x y k a : ℕ,
        X0 ≤ x →
        (x : ℝ) ^ theta < (y : ℝ) →
        y ≤ x →
        (k : ℝ) < (y : ℝ) ^ (3 / 4 : ℝ) →
        0 < a → a < k → a.Coprime k →
        (∑ n ∈ Finset.Ioc (x - y) x,
          if n ≡ a [MOD k] then f n else 0) ≤
          Shiu.API.squarefreeConstant A B *
            ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
            Real.exp
              (∑ p ∈ Nat.primesLE x with ¬ p ∣ k, f p / p) := by
  exact Shiu.API.squarefree_theta A B theta htheta

#check Shiu.API.squarefree_quarter
#check Shiu.API.squarefree_fifth
#check Shiu.API.squarefree_tenth
end Shiu.ConsumerExamples
