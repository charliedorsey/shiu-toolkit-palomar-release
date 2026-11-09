module

public import ShiuPublic.VaelisPrimePowerBlocks
public import Mathlib.Data.Finset.Sort

public section

namespace PaperB.M4B

/-- Sorted distinct prime-power blocks, retaining all multiplicities. -/
@[expose] noncomputable def classicalPrimePowerAtomsSorted (n : ℕ) : List ℕ :=
  (n.primeFactors.sort (· ≤ ·)).map (fun p => p ^ n.factorization p)

theorem classical_primePowerAtomsSorted_prod (n : ℕ) (hn : n ≠ 0) :
    (classicalPrimePowerAtomsSorted n).prod = n := by
  have hperm : (classicalPrimePowerAtomsSorted n).Perm (classicalPrimePowerAtoms n) := by
    exact (Finset.sort_perm_toList n.primeFactors (· ≤ ·)).map (fun p => p ^ n.factorization p)
  exact hperm.prod_eq.trans (classical_primePowerAtoms_prod n hn)

#print axioms classical_primePowerAtomsSorted_prod
end PaperB.M4B
