module

public import ShiuPublic.FixedQuarter
public import ShiuPublic.OneFifthExperiment

public section

/-! Uniform fifth-power range squarefree Shiu inequality, with a
public interface independent of the originating proof's naming. -/

namespace Shiu
open scoped BigOperators
open ArithmeticFunction

/-- Widened short-interval exponent: x^(1/5)<y<=x, with the same
original-modulus range k<y^(3/4). All weight parameters explicit. -/
theorem progression_one_fifth_uniform (A B : ℝ) :
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
          constant A B *
            ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
            Real.exp
              (∑ p ∈ Nat.primesLE x with ¬ p ∣ k, f p / p) := by
  obtain ⟨X0, h⟩ :=
    PaperB.M4B.shiuFixedFifth_progression_uniform A B
  refine ⟨X0, ?_⟩
  intro f hf x y k a hx hxy hyx hk ha hak hcop
  exact h f (⟨hf.multiplicative, hf.nonnegative, hf.squarefree, hf.prime_values, hf.primeBound_nonneg, hf.growthBound_nonneg, hf.growth⟩) x y k a hx hxy hyx hk ha hak hcop

/-- Parameterized squarefree Shiu for all theta >= 1/5.
The threshold is independent of theta, since x>=1. -/
theorem progression_theta_uniform (A B theta : ℝ)
    (htheta : (1 / 5 : ℝ) ≤ theta) :
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
          constant A B *
            ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
            Real.exp
              (∑ p ∈ Nat.primesLE x with ¬ p ∣ k, f p / p) := by
  obtain ⟨X0, h⟩ := progression_one_fifth_uniform A B
  refine ⟨max X0 1, ?_⟩
  intro f hf x y k a hx hxy hyx hk ha hak hcop
  have hx1 : (1 : ℝ) ≤ x := by
    exact_mod_cast (le_trans (le_max_right X0 1) hx)
  have hpow : (x : ℝ) ^ (1 / 5 : ℝ) ≤ (x : ℝ) ^ theta :=
    Real.rpow_le_rpow_of_exponent_le hx1 htheta
  exact h f hf x y k a (le_trans (le_max_left X0 1) hx)
    (lt_of_le_of_lt hpow hxy) hyx hk ha hak hcop

#print axioms Shiu.progression_theta_uniform
#print axioms Shiu.progression_one_fifth_uniform
end Shiu
