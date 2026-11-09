module

public import Mathlib
public import ChallengeDefs.Envelope
public import ChallengeDefs.Progressions
public import ChallengeDefs.Constant

public section

/-!
# SHIU exact three-theorem Challenge
The only transitive sources are Mathlib and the nine audited
ChallengeDefs files consisting solely of copied definitions.
No substantive SHIU theorem or proof module is imported here.
The deliberate sorry proofs occur only in this Challenge.
-/

namespace Shiu.API

open scoped BigOperators

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
  sorry

theorem classical_modulus_one_quarter (A B : ℝ) :
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
  sorry

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
  sorry

end Shiu.API
