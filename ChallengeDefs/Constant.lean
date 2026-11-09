module

public import ChallengeDefs.ClassI
public import ChallengeDefs.ClassIV

public section

namespace Shiu.API

open scoped BigOperators

@[expose] noncomputable def classicalConstant (A B : ℝ) : ℝ :=
  961 * PaperB.M4B.corvethClassicalClassIConstant A B +
  161 * PaperB.M4B.classicalShiuClassIVConstant A B + 56330 * B

end Shiu.API
