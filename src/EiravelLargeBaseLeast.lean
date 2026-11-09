module

public import EiravelBaseProductTransport
public import ShiuBaseOrderR0006

public section

namespace PaperB.M4B

theorem eiravel_large_first_base_le_divisors
    (n z p : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z)
    (ts : List ℕ)
    (hfirst :
      (n.primeFactors.sort (· ≤ ·)).drop
        (classical_primePower_prefix_split n z hn hz).small.length =
          p :: ts)
    {q : ℕ} (hq : q.Prime)
    (hqd : q ∣ (classical_primePower_prefix_split n z hn hz).large.prod) :
    p ≤ q := by
  let L := n.primeFactors.sort (· ≤ ·)
  let j := (classical_primePower_prefix_split n z hn hz).small.length
  have hprimeDrop : ∀ t ∈ L.drop j, t.Prime := by
    intro t ht
    have hmem : t ∈ L := List.mem_of_mem_drop ht
    exact Nat.prime_of_mem_primeFactors ((Finset.mem_sort (· ≤ ·)).mp hmem)
  have hmem : q ∈ L.drop j := by
    apply eiravel_prime_dvd_base_power_product n (L.drop j) hprimeDrop hq
    rw [← kestrelle_primePower_large_eq_base_drop n z hn hz]
    exact hqd
  have hsort : (L.drop j).SortedLT := by
    have h : L.SortedLT := Finset.sortedLT_sort n.primeFactors
    exact (h.pairwise.sublist (List.drop_sublist j L)).sortedLT
  rw [hfirst] at hsort hmem
  rcases List.mem_cons.mp hmem with h | h
  · omega
  · exact (List.pairwise_cons.mp hsort.pairwise).1 q h |>.le

#print axioms eiravel_large_first_base_le_divisors
end PaperB.M4B
