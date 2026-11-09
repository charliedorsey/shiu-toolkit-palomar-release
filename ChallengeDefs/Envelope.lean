module

public import Mathlib

public section

namespace Shiu

open scoped BigOperators
open ArithmeticFunction

structure ClassicalEnvelope (f : ArithmeticFunction ℝ) (A : ℝ) : Prop where
  multiplicative : f.IsMultiplicative
  nonnegative : ∀ n : ℕ, 0 ≤ f n
  A_nonnegative : 0 ≤ A
  prime_power : ∀ p m : ℕ, p.Prime → 1 ≤ m → f (p ^ m) ≤ A ^ m
  growth : ∀ ε : ℝ, 0 < ε →
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 1 ≤ n → f n ≤ B * (n : ℝ) ^ ε

end Shiu
