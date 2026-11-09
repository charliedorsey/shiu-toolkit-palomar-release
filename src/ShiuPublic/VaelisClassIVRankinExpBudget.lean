module

public import ShiuPublic.VaelisClassIVStrongEndpoints

public section

namespace PaperB.M4B
open scoped BigOperators

/-- The full non-squarefree Rankin exponential is reduced to one source
shell scalar budget; no squarefree hypothesis or missing Euler factor. -/
theorem classical_rankin_exponential_budget
    (T δ M C F R : ℝ) (hT : 0 < T)
    (hbudget : C - δ * Real.log T ≤ -R) :
    T ^ (-δ) * Real.exp (M + C + F) ≤
      Real.exp (M + F - R) := by
  have heq :
      T ^ (-δ) * Real.exp (M + C + F) =
        Real.exp (M + F + (C - δ * Real.log T)) := by
    rw [Real.rpow_def_of_pos hT, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  apply Real.exp_le_exp.mpr
  linarith

#print axioms classical_rankin_exponential_budget
end PaperB.M4B
