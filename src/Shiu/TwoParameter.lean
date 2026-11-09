module

public import Shiu.ClassicalCorollaries

public section

/-!
# Two-parameter monotonicity consequence of classical fixed-quarter Shiu

Within Shiu's original 0 < alpha,beta < 1/2 domain this pays precisely
the quadrant alpha,beta >= 1/4. It does not prove smaller alpha or beta,
and retains the quantitative fixed-B growth hypothesis and Nat endpoints.
No new analytic estimate is introduced.
-/

namespace Shiu.API

open scoped BigOperators

/-- Uniform fixed-(A,B) Shiu bound for the upper-right quadrant of the
original (alpha,beta) region. X0 is independent of alpha, beta, and f.
The original source theorem allows all 0 < alpha,beta < 1/2; this result
does not cover alpha < 1/4 or beta < 1/4. -/
theorem classical_two_parameter_quadrant (A B : ℝ) :
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
          progressionSum f x y k a ≤
            classicalConstant A B *
              ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
              Real.exp (primeMass f x k) := by
  obtain ⟨X0, hX⟩ := classical_theta A B
  refine ⟨max X0 1, ?_⟩
  intro alpha beta halpha _ hbeta _ f hf hB hgrowth
    x y k a hx hxy hyx hk ha hak hcop
  have hxX0 : X0 ≤ x := (le_max_left X0 1).trans hx
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast ((le_max_right X0 1).trans hx)
  have hbeta0 : (0 : ℝ) ≤ beta := by linarith
  have hy1 : (1 : ℝ) ≤ (y : ℝ) :=
    (Real.one_le_rpow hx1 hbeta0).trans hxy.le
  have hmod : (y : ℝ) ^ (1 - alpha) ≤
      (y : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
  exact hX beta hbeta f hf hB hgrowth x y k a
    hxX0 hxy hyx (lt_of_lt_of_le hk hmod) ha hak hcop

#print axioms classical_two_parameter_quadrant

end Shiu.API
