module

public import Mathlib

public section

namespace PaperB.M4B

open scoped BigOperators

@[expose] noncomputable def classicalClassIVRankinD (A : ℝ) : ℝ :=
  960 * Real.log (1 + A) + 24

@[expose] noncomputable def classicalClassIVRankinH (A : ℝ) : ℝ :=
  ((4 * A * Real.log 4) / Real.log 2) *
    Real.exp (classicalClassIVRankinD A)

end PaperB.M4B
