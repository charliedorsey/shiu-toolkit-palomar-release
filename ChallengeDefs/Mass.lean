module

public import Mathlib

public section

namespace PaperB.M4B

open scoped BigOperators

@[expose] noncomputable def primeMass (f : ArithmeticFunction ℝ) (X k : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE X with ¬ p ∣ k, f p / p

end PaperB.M4B
