module

public import ShiuPublic.OneFifth
public import ShiuPublic.OneTenth
public import Shiu.Progressions

public section

/-! The squarefree-supported Shiu family. The non-squarefree classical theorem is separate. -/
namespace Shiu.API
open scoped BigOperators

noncomputable abbrev squarefreeConstant (A B : ℝ) : ℝ := Shiu.constant A B

/-- Source-preserving squarefree_quarter contract; no new weight hypotheses. -/
theorem squarefree_quarter (A B : ℝ) :
    ∃ X0 : ℕ, ∀ f : ArithmeticFunction ℝ,
      SquarefreeEnvelope f A B →
      ∀ x y k a : ℕ,
        X0 ≤ x →
        (x : ℝ) ^ (1 / 4 : ℝ) < (y : ℝ) →
        y ≤ x →
        (k : ℝ) < (y : ℝ) ^ (3 / 4 : ℝ) →
        0 < a → a < k → a.Coprime k →
        (∑ n ∈ Finset.Ioc (x - y) x,
          if n ≡ a [MOD k] then f n else 0) ≤
          squarefreeConstant A B *
            ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
            Real.exp
              (primeMass f x k) := by
  exact Shiu.progression_uniform A B

/-- Source-preserving squarefree_fifth contract; no new weight hypotheses. -/
theorem squarefree_fifth (A B : ℝ) :
    ∃ X0 : ℕ, ∀ f : ArithmeticFunction ℝ,
      SquarefreeEnvelope f A B →
      ∀ x y k a : ℕ,
        X0 ≤ x →
        (x : ℝ) ^ (1 / 5 : ℝ) < (y : ℝ) →
        y ≤ x →
        (k : ℝ) < (y : ℝ) ^ (3 / 4 : ℝ) →
        0 < a → a < k → a.Coprime k →
        (∑ n ∈ Finset.Ioc (x - y) x,
          if n ≡ a [MOD k] then f n else 0) ≤
          squarefreeConstant A B *
            ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
            Real.exp
              (primeMass f x k) := by
  exact Shiu.progression_one_fifth_uniform A B

/-- Source-preserving squarefree_tenth contract; no new weight hypotheses. -/
theorem squarefree_tenth (A B : ℝ) :
    ∃ X0 : ℕ, ∀ f : ArithmeticFunction ℝ,
      SquarefreeEnvelope f A B →
      ∀ x y k a : ℕ,
        X0 ≤ x →
        (x : ℝ) ^ (1 / 10 : ℝ) < (y : ℝ) →
        y ≤ x →
        (k : ℝ) < (y : ℝ) ^ (3 / 4 : ℝ) →
        0 < a → a < k → a.Coprime k →
        (∑ n ∈ Finset.Ioc (x - y) x,
          if n ≡ a [MOD k] then f n else 0) ≤
          squarefreeConstant A B *
            ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
            Real.exp
              (primeMass f x k) := by
  exact Shiu.progression_one_tenth_uniform A B

/-- Source-preserving squarefree_theta contract; no new weight hypotheses. -/
theorem squarefree_theta (A B theta : ℝ)
    (htheta : (1 / 10 : ℝ) ≤ theta) :
    ∃ X0 : ℕ, ∀ f : ArithmeticFunction ℝ,
      SquarefreeEnvelope f A B →
      ∀ x y k a : ℕ,
        X0 ≤ x →
        (x : ℝ) ^ theta < (y : ℝ) →
        y ≤ x →
        (k : ℝ) < (y : ℝ) ^ (3 / 4 : ℝ) →
        0 < a → a < k → a.Coprime k →
        (∑ n ∈ Finset.Ioc (x - y) x,
          if n ≡ a [MOD k] then f n else 0) ≤
          squarefreeConstant A B *
            ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
            Real.exp
              (primeMass f x k) := by
  exact Shiu.progression_theta_tenth_uniform A B theta htheta

#print axioms squarefree_quarter
#print axioms squarefree_fifth
#print axioms squarefree_tenth
#print axioms squarefree_theta
end Shiu.API
