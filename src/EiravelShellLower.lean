module

public import PaperB.M4B.ShiuClassIV

public section

namespace PaperB.M4B

/-- The shell roughness cutoff stays strictly below the crossing base
prime, using only the correct naturalized r-shell endpoint. -/
theorem eiravel_classIV_shell_lower_lt_crossing_base
    (z p r : ℕ) (hr : 0 < r)
    (hp : p.Prime) (hzp : z < p ^ (r + 1)) :
    classIVShellLower z r < p := by
  unfold classIVShellLower
  exact (Nat.nthRoot_lt_iff (by omega : r + 1 ≠ 0)).mpr hzp

#print axioms eiravel_classIV_shell_lower_lt_crossing_base
end PaperB.M4B
