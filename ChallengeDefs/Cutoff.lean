module

public import Mathlib

public section

namespace Shiu

open scoped BigOperators
open ArithmeticFunction

@[expose] noncomputable def fixedPrimePowerCutoff (A D : ℝ) : ℕ :=
  max 5 ⌈2 * A * Real.exp D⌉₊

end Shiu
