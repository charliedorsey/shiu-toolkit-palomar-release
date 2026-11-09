module

public import PaperB.M4B.ShiuProgression

public section

/-! Portable, source-neutral public contract for the independently replayed
squarefree-supported fixed-quarter Shiu estimate. The implementation still
imports the original M4B supplier; no claim of a standalone dependency graph.
-/

namespace Shiu
open scoped BigOperators
open ArithmeticFunction

/-- Precisely the verified weight class, with all constants public. -/
structure SquarefreeEnvelope (f : ArithmeticFunction ℝ)
    (primeBound growthBound : ℝ) : Prop where
  multiplicative : f.IsMultiplicative
  nonnegative : ∀ n : ℕ, 0 ≤ f n
  squarefree : ∀ n : ℕ, ¬ Squarefree n → f n = 0
  prime_values : ∀ p : ℕ, p.Prime → f p ≤ primeBound
  primeBound_nonneg : 0 ≤ primeBound
  growthBound_nonneg : 0 ≤ growthBound
  growth : ∀ n : ℕ, f n ≤ growthBound * (n : ℝ) ^ (1 / 1280 : ℝ)

/-- Explicit constant, independent of the summation parameters. -/
@[expose] noncomputable def constant (A B : ℝ) : ℝ :=
  PaperB.M4B.shiuFixedQuarterAssembleConstant A B

private theorem toSupplier {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : SquarefreeEnvelope f A B) :
    PaperB.M4B.FixedQuarterEnvelope f A B := by
  exact ⟨hf.multiplicative, hf.nonnegative, hf.squarefree,
    hf.prime_values, hf.primeBound_nonneg, hf.growthBound_nonneg,
    hf.growth⟩

/-- Uniform fixed-quarter arithmetic-progression Shiu inequality. This is
squarefree-supported, not the unrestricted prime-power theorem. -/
theorem progression_uniform (A B : ℝ) :
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
          constant A B *
            ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
            Real.exp
              (∑ p ∈ Nat.primesLE x with ¬ p ∣ k, f p / p) := by
  obtain ⟨X0, h⟩ := PaperB.M4B.shiuFixedQuarter_progression_uniform A B
  refine ⟨X0, ?_⟩
  intro f hf x y k a hx hxy hyx hk ha hak hcop
  exact h f (toSupplier hf) x y k a hx hxy hyx hk ha hak hcop

#print axioms Shiu.progression_uniform
end Shiu
