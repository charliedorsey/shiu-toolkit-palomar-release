module

public import ChallengeDefs.Mass

public section

namespace Shiu.API

open scoped BigOperators

noncomputable abbrev primeMass (f : ArithmeticFunction ℝ)
    (x k : ℕ) : ℝ := PaperB.M4B.primeMass f x k

@[expose] def progressionSum (f : ArithmeticFunction ℝ) (x y k a : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc (x-y) x, if n ≡ a [MOD k] then f n else 0

end Shiu.API
