module

public import ShiuPublic.VaelisPrimePowerDistinctCoprime

public section

namespace PaperB.M4B

/-- Any two distinct atoms in the actual sorted distinct-prime list are
coprime even when the original integer has repeated factors. -/
theorem classical_primePowerAtomsSorted_pairwise_coprime (n : ℕ) :
    (classicalPrimePowerAtomsSorted n).Pairwise Nat.Coprime := by
  classical
  let l := n.primeFactors.sort (· ≤ ·)
  have hmem : ∀ p ∈ l, p ∈ n.primeFactors := by
    intro p hp
    exact (Finset.mem_sort (· ≤ ·)).mp hp
  have hnodup : l.Nodup := Finset.sort_nodup n.primeFactors (· ≤ ·)
  have hpair (L : List ℕ)
      (hL : ∀ p ∈ L, p ∈ n.primeFactors) (hnd : L.Nodup) :
      L.Pairwise (fun p q => (p ^ n.factorization p).Coprime (q ^ n.factorization q)) := by
    induction L with
    | nil => simp
    | cons p ps ih =>
      have hp : p ∈ n.primeFactors := hL p (by simp)
      have htail : ∀ q ∈ ps, q ∈ n.primeFactors := by
        intro q hq
        exact hL q (by simp [hq])
      have hnot : p ∉ ps := (List.nodup_cons.mp hnd).1
      have htailnd : ps.Nodup := (List.nodup_cons.mp hnd).2
      apply List.pairwise_cons.mpr
      constructor
      · intro q hq
        have hpq : p ≠ q := by
          intro he
          exact hnot (he ▸ hq)
        exact classical_prime_power_atoms_coprime n p q hp (htail q hq) hpq
      · exact ih htail htailnd
  change (l.map (fun p => p ^ n.factorization p)).Pairwise Nat.Coprime
  exact (hpair l hmem hnodup).map (fun p => p ^ n.factorization p) (fun p q hpq => hpq)

#print axioms classical_primePowerAtomsSorted_pairwise_coprime
end PaperB.M4B
