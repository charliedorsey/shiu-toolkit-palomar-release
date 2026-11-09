module

public import ShiuPublic.VaelisPrimePowerPrefix

public section

namespace PaperB.M4B

/-- Base-list prefix whose mapped full-power atoms are exactly S.small. -/
theorem kestrelle_primePower_small_eq_base_take
    (n z : Nat) (hn : n ≠ 0) (hz : 1 ≤ z) :
    (classical_primePower_prefix_split n z hn hz).small =
      ((n.primeFactors.sort (· ≤ ·)).take
        (classical_primePower_prefix_split n z hn hz).small.length).map
          (fun p => p ^ n.factorization p) := by
  let S := classical_primePower_prefix_split n z hn hz
  have h := congrArg (List.take S.small.length) S.concat
  simp only [List.take_append_of_le_length (Nat.le_refl _),
    List.take_length] at h
  simpa [classicalPrimePowerAtomsSorted, List.map_take] using h

/-- Base-list suffix whose mapped full-power atoms are exactly S.large. -/
theorem kestrelle_primePower_large_eq_base_drop
    (n z : Nat) (hn : n ≠ 0) (hz : 1 ≤ z) :
    (classical_primePower_prefix_split n z hn hz).large =
      ((n.primeFactors.sort (· ≤ ·)).drop
        (classical_primePower_prefix_split n z hn hz).small.length).map
          (fun p => p ^ n.factorization p) := by
  let S := classical_primePower_prefix_split n z hn hz
  have h := congrArg (List.drop S.small.length) S.concat
  simp at h
  simpa [classicalPrimePowerAtomsSorted, List.map_drop] using h

/-- The original full-power prefix/suffix inherits STRICT BASE-PRIME ORDER.
The blocks themselves need not be numerically ordered. -/
theorem kestrelle_primePower_base_order
    (n z : Nat) (hn : n ≠ 0) (hz : 1 ≤ z) :
    let j := (classical_primePower_prefix_split n z hn hz).small.length
    ∀ p ∈ (n.primeFactors.sort (· ≤ ·)).take j,
      ∀ q ∈ (n.primeFactors.sort (· ≤ ·)).drop j, p < q := by
  intro j p hp q hq
  let L := n.primeFactors.sort (· ≤ ·)
  have hsort : L.SortedLT := Finset.sortedLT_sort n.primeFactors
  have hpair := hsort.pairwise
  have hsplit : (L.take j) ++ (L.drop j) = L := List.take_append_drop j L
  rw [← hsplit] at hpair
  exact (List.pairwise_append.mp hpair).2.2 p hp q hq

#print axioms kestrelle_primePower_base_order
#print axioms kestrelle_primePower_small_eq_base_take
#print axioms kestrelle_primePower_large_eq_base_drop
end PaperB.M4B
