module

public import ShiuPublic.CorvethClassicalPrefixCore
public import PaperB.M4B.ShiuClassIVShell

public section

namespace PaperB.M4B

/-- Unrestricted shell endpoints for the CROSSING BASE PRIME (not its
full-power atom). No squarefree hypothesis. -/
theorem eiravel_classical_base_shell_endpoints
    (x z p : ℕ) (hp : p.Prime)
    (hpSqrt : p ≤ Nat.sqrt z)
    (hL2 : 2 ≤ shiuLogLogSmoothThreshold x)
    (hLp : shiuLogLogSmoothThreshold x < p) :
    let r := Nat.log p z
    2 ≤ r ∧ r ≤ shiuClassIVR0 x z ∧
      p ^ r ≤ z ∧ z < p ^ (r+1) := by
  intro r
  have hp2z : p ^ 2 ≤ z :=
    (Nat.pow_le_pow_left hpSqrt 2).trans (Nat.sqrt_le' z)
  have hr2 : 2 ≤ r := by
    dsimp [r]
    exact Nat.le_log_of_pow_le hp.one_lt hp2z
  have hz0 : z ≠ 0 := by
    intro h
    have hpp : 0 < p := hp.pos
    subst z
    nlinarith [sq_nonneg (p : ℝ)]
  have hr0 : r ≤ shiuClassIVR0 x z := by
    dsimp [r, shiuClassIVR0]
    exact Nat.log_anti_left (by omega) (Nat.le_of_lt hLp)
  refine ⟨hr2, hr0, ?_, ?_⟩
  · exact Nat.pow_log_le_self p hz0
  · exact Nat.lt_pow_succ_log_self hp.one_lt z

#print axioms eiravel_classical_base_shell_endpoints
end PaperB.M4B
