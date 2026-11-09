module

public import ShiuPublic.VaelisClassIVPrefixNonSquarefree
public import PaperB.M4B.ShiuClassIV

public section

namespace PaperB.M4B

/-- Upgrade actual unrestricted prefix membership from the first crossing
base p to the larger upper ceiling of its r-shell. No squarefree input. -/
theorem eiravel_classical_prefix_shell_ceiling
    (z k p r b : ℕ)
    (hr : 0 < r) (hpower : p ^ r ≤ z)
    (hb : b ∈ Shiu.classicalClassIVPrefixSet z k p) :
    b ∈ Shiu.classicalClassIVPrefixSet z k
      (classIVShellUpper z r) := by
  have hpup : p ≤ classIVShellUpper z r := by
    unfold classIVShellUpper
    exact (Nat.le_nthRoot_iff (by omega)).mpr hpower
  unfold Shiu.classicalClassIVPrefixSet at hb ⊢
  obtain ⟨hinterval, hcop, hprimeLe⟩ := Finset.mem_filter.mp hb
  apply Finset.mem_filter.mpr
  exact ⟨hinterval, hcop, fun q hq => (hprimeLe q hq).trans hpup⟩

#print axioms eiravel_classical_prefix_shell_ceiling
end PaperB.M4B
