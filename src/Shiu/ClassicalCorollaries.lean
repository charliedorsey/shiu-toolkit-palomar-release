module

public import Shiu.Classical

public section

/-!
# Selected Tier 2 consumers
A. Per-weight existential fixed power majorant (B and X0 follow f).
B. Classical theta >= 1/4 by monotonicity (threshold uniform in theta and f).
NO new non-squarefree theta < 1/4 theorem.
-/
namespace Shiu.API
open scoped BigOperators

/-- For each *individual* classical weight, obtain B and its threshold.
The quantifier order is ∀ f, ∃ B, ∃ X0, not ∃B∃X0∀f. -/
theorem classical_individual (A : ℝ)
    (f : ArithmeticFunction ℝ) (hf : Shiu.ClassicalEnvelope f A) :
    ∃ B : ℝ, 0 < B ∧ ∃ X0 : ℕ,
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
  obtain ⟨B, hB, hgrowth⟩ :=
    hf.growth (1 / 1280 : ℝ) (by norm_num)
  obtain ⟨X0, hX⟩ := classical_quarter A B
  exact ⟨B, hB, X0, fun x y k a hx hxy hyx hk ha hak hcop =>
    hX f hf hB.le hgrowth x y k a hx hxy hyx hk ha hak hcop⟩

/-- For theta ≥ 1/4, the original classical constant and
threshold are valid. The threshold is independent of theta and f. -/
theorem classical_theta (A B : ℝ) :
    ∃ X0 : ℕ, ∀ theta : ℝ,
      (1 / 4 : ℝ) ≤ theta →
      ∀ f : ArithmeticFunction ℝ,
        Shiu.ClassicalEnvelope f A →
        0 ≤ B →
        (∀ n : ℕ, 1 ≤ n →
          f n ≤ B * (n : ℝ) ^ (1 / 1280 : ℝ)) →
        ∀ x y k a : ℕ,
          X0 ≤ x →
          (x : ℝ) ^ theta < (y : ℝ) →
          y ≤ x →
          (k : ℝ) < (y : ℝ) ^ (3 / 4 : ℝ) →
          0 < a → a < k → a.Coprime k →
          progressionSum f x y k a ≤
            classicalConstant A B *
              ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
              Real.exp (primeMass f x k) := by
  obtain ⟨X0, hX⟩ := classical_quarter A B
  refine ⟨max X0 1, ?_⟩
  intro theta htheta f hf hB hgrowth x y k a hx hxy hyx hk ha hak hcop
  have hxX0 : X0 ≤ x := (le_max_left X0 1).trans hx
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast ((le_max_right X0 1).trans hx)
  have hpow : (x : ℝ) ^ (1 / 4 : ℝ) ≤ (x : ℝ) ^ theta :=
    Real.rpow_le_rpow_of_exponent_le hx1 htheta
  exact hX f hf hB hgrowth x y k a hxX0
    (lt_of_le_of_lt hpow hxy) hyx hk ha hak hcop

#print axioms classical_individual
#print axioms classical_theta
end Shiu.API
