module

public import Shiu.Classical

public section

/-! A real classical-envelope instance: the constant-one arithmetic weight on
positive integers, represented by the Mathlib zeta arithmetic function.
This file is an API consumer, not part of the frozen proof source. -/

open ArithmeticFunction
open scoped BigOperators

namespace Shiu.ConsumerExamples

private def unitWeight : ArithmeticFunction ℝ :=
  ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)

private lemma unitWeight_apply (n : ℕ) (hn : n ≠ 0) :
    unitWeight n = 1 := by
  simp [unitWeight, ArithmeticFunction.zeta_apply_ne hn]

private theorem unitWeight_classical :
    Shiu.ClassicalEnvelope unitWeight 1 := by
  refine ⟨?_, ?_, by norm_num, ?_, ?_⟩
  · exact ArithmeticFunction.isMultiplicative_zeta.natCast
  · intro n
    by_cases hn : n = 0
    · simp [unitWeight, hn]
    · simp [unitWeight, ArithmeticFunction.zeta_apply_ne hn]
  · intro p m hp hm
    have hp0 : p ^ m ≠ 0 := pow_ne_zero m hp.ne_zero
    simp [unitWeight_apply _ hp0]
  · intro ε hε
    refine ⟨1, by norm_num, ?_⟩
    intro n hn
    have hn0 : n ≠ 0 := by omega
    rw [unitWeight_apply n hn0]
    have hr : (1 : ℝ) ≤ (n : ℝ) ^ ε :=
      Real.one_le_rpow (by exact_mod_cast hn) hε.le
    simpa using hr

private lemma unitWeight_growth (n : ℕ) (hn : 1 ≤ n) :
    unitWeight n ≤ (1 : ℝ) * (n : ℝ) ^ (1 / 1280 : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  rw [unitWeight_apply n hn0]
  simpa using (Real.one_le_rpow (by exact_mod_cast hn)
    (by norm_num : (0 : ℝ) ≤ 1 / 1280))

/-- A full theorem consumer for a concrete multiplicative function.
The value at 0 is 0 and the value at each positive integer is 1. -/
example : ∃ X0 : ℕ, ∀ x y k a : ℕ,
    X0 ≤ x →
    (x : ℝ) ^ (1/4 : ℝ) < (y : ℝ) →
    y ≤ x → (k : ℝ) < (y : ℝ) ^ (3/4 : ℝ) →
    0 < a → a < k → a.Coprime k →
    Shiu.API.progressionSum unitWeight x y k a ≤
      Shiu.API.classicalConstant 1 1 *
        ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
          Real.exp (PaperB.M4B.primeMass unitWeight x k) := by
  obtain ⟨X0, h⟩ := Shiu.API.classical_quarter 1 1
  refine ⟨X0, ?_⟩
  intro x y k a hx hxy hyx hk ha hak hcop
  exact h unitWeight unitWeight_classical (by norm_num)
    unitWeight_growth x y k a hx hxy hyx hk ha hak hcop

end Shiu.ConsumerExamples
