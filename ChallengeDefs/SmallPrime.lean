module

public import Mathlib

public section

namespace Shiu

open scoped BigOperators
open ArithmeticFunction

@[expose] noncomputable def smallPrimeConstant (Q : ℕ) (B : ℝ) : ℝ :=
  ∏ q ∈ Nat.primesLE Q,
    (1 + B / (1 - (q : ℝ) ^ (-(1/2 : ℝ))))

end Shiu
