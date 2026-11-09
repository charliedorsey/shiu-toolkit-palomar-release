module

public import ShiuPublic.VaelisPrimePowerPrefix
public import ShiuPublic.VaelisPrimePowerCoprimeList
public import Mathlib.Data.Nat.GCD.BigOperators

public section

namespace PaperB.M4B

/-- The actual prime-power prefix is coprime to its suffix, unlike the
naive repeated-prime list split. No squarefree assumption. -/
theorem classical_primePower_prefix_coprime
    (n z : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z) :
    (classical_primePower_prefix_split n z hn hz).small.prod.Coprime
      (classical_primePower_prefix_split n z hn hz).large.prod := by
  let S := classical_primePower_prefix_split n z hn hz
  have hpw : (S.small ++ S.large).Pairwise Nat.Coprime := by
    rw [S.concat]
    exact classical_primePowerAtomsSorted_pairwise_coprime n
  have hcross := (List.pairwise_append.mp hpw).2.2
  change S.small.prod.Coprime S.large.prod
  apply Nat.coprime_list_prod_left_iff.mpr
  intro p hp
  apply Nat.coprime_list_prod_right_iff.mpr
  intro q hq
  exact hcross p hp q hq

#print axioms classical_primePower_prefix_coprime
end PaperB.M4B
