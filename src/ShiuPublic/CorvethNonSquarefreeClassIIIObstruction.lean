module

public import ShiuPublic.CorvethClassicalPrefixCore
public import PaperB.M4B.ShiuClassIII

public section

namespace PaperB.M4B

/-- A full prime-power source prefix need not satisfy the old squarefree
Class III support. This is the actual proof-consumer mismatch. -/
theorem corveth_four_not_classIII (x k : ℕ) :
    4 ∉ classIIIFactors x 4 k := by
  intro h
  have hs : Squarefree (4 : ℕ) := by
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.1
  exact (Nat.squarefree_iff_prime_squarefree.mp hs 2 (by norm_num)) (by norm_num)

#print axioms corveth_four_not_classIII
end PaperB.M4B
