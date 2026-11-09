module

public import ChallengeDefs.SmallPrime
public import ChallengeDefs.Cutoff
public import ChallengeDefs.Rankin

public section

namespace PaperB.M4B

open scoped BigOperators

@[expose] noncomputable def classicalShiuClassIVConstant (A B : ℝ) : ℝ :=
  96 * Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A (classicalClassIVRankinD A)) B *
    Real.exp (2*A^2*Real.exp (2*classicalClassIVRankinD A) + classicalClassIVRankinH A)

end PaperB.M4B
