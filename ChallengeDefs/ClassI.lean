module

public import ChallengeDefs.SmallPrime
public import ChallengeDefs.Cutoff

public section

namespace PaperB.M4B

open scoped BigOperators

@[expose] noncomputable def corvethClassicalClassIConstant (A B : ℝ) : ℝ :=
  (4 * (1 + A) ^ 320) *
    Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A 1) B *
      Real.exp (((4 * A * Real.log 4) / Real.log 2) * Real.exp 1 +
        2 * A ^ 2 * Real.exp 2)

end PaperB.M4B
