module

public import ShiuPublic.VaelisPrimePowerDistinctCoprime

public section

namespace PaperB.M4B

/-- Prefix split on entire prime-power atoms, never between copies of a prime. -/
structure ClassicalPrimePowerPrefixSplit (n z : ℕ) where
  small : List ℕ
  large : List ℕ
  concat : small ++ large = classicalPrimePowerAtomsSorted n
  factorization : n = small.prod * large.prod
  small_prod_le : small.prod ≤ z
  crossing : large = [] ∨ ∃ q qs, large = q :: qs ∧ z < small.prod * q

/-- The exact non-squarefree source factorization at the prime-power level. -/
noncomputable def classical_primePower_prefix_split
    (n z : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z) :
    ClassicalPrimePowerPrefixSplit n z := by
  let atoms := classicalPrimePowerAtomsSorted n
  let small := (prefixSplit z atoms).1
  let large := (prefixSplit z atoms).2
  have hpos : ∀ u ∈ atoms, 0 < u := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
    have hmem : p ∈ n.primeFactors := by
      have hp' : p ∈ n.primeFactors.sort (· ≤ ·) := hp
      simpa using (Finset.mem_sort (· ≤ ·)).mp hp'
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hmem
    exact pow_pos hprime.pos _
  have hconcat : small ++ large = atoms := by
    exact prefixSplit_append z atoms
  have hfactor : n = small.prod * large.prod := by
    have heq := congrArg List.prod hconcat
    rw [List.prod_append, classical_primePowerAtomsSorted_prod n hn] at heq
    exact heq.symm
  exact {
    small := small
    large := large
    concat := hconcat
    factorization := hfactor
    small_prod_le := prefixSplit_left_prod_le z atoms hz hpos
    crossing := prefixSplit_cross z atoms hpos
  }

#check classical_primePower_prefix_split
end PaperB.M4B
