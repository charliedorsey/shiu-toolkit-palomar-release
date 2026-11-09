module

public import PaperB.M4B.ShiuSplit

public section

namespace PaperB.M4B

/-- Exact multiplicity-preserving source prime-factor-list prefix; no
squarefree assumption and deliberately no false coprimality assertion. -/
structure ClassicalPrefixSplit (n z : ℕ) where
  small : List ℕ
  large : List ℕ
  concat : small ++ large = n.primeFactorsList
  factorization : n = small.prod * large.prod
  small_prod_le : small.prod ≤ z
  crossing : large = [] ∨
    ∃ q qs, large = q :: qs ∧ z < small.prod * q

def classical_prefix_factorization_split
    (n z : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z) :
    ClassicalPrefixSplit n z := by
  let small := (prefixSplit z n.primeFactorsList).1
  let large := (prefixSplit z n.primeFactorsList).2
  have hpos : ∀ p ∈ n.primeFactorsList, 0 < p :=
    fun p hp => Nat.pos_of_mem_primeFactorsList hp
  have hconcat : small ++ large = n.primeFactorsList := by
    exact prefixSplit_append z n.primeFactorsList
  have hfactor : n = small.prod * large.prod := by
    have h := congrArg List.prod hconcat
    rw [List.prod_append, Nat.prod_primeFactorsList hn] at h
    exact h.symm
  exact {
    small := small
    large := large
    concat := hconcat
    factorization := hfactor
    small_prod_le := prefixSplit_left_prod_le z n.primeFactorsList hz hpos
    crossing := prefixSplit_cross z n.primeFactorsList hpos
  }

#check classical_prefix_factorization_split
end PaperB.M4B
