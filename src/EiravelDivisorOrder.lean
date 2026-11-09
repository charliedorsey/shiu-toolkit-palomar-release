module

public import ShiuBaseOrderR0006
public import EiravelBaseProductTransport

public section

namespace PaperB.M4B

/-- Actual unrestricted source: prime divisors of the small product precede
prime divisors of the large product in BASE order. -/
theorem eiravel_classical_primePower_prefix_divisor_order
    (n z : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpd : p ∣ (classical_primePower_prefix_split n z hn hz).small.prod)
    (hqd : q ∣ (classical_primePower_prefix_split n z hn hz).large.prod) :
    p < q := by
  let S := classical_primePower_prefix_split n z hn hz
  let L := n.primeFactors.sort (· ≤ ·)
  let j := S.small.length
  have hbase : ∀ t ∈ L, t.Prime := by
    intro t ht
    exact Nat.prime_of_mem_primeFactors
      ((Finset.mem_sort (· ≤ ·)).mp ht)
  have hsmall : p ∈ L.take j := by
    have hprimeTake : ∀ t ∈ L.take j, t.Prime := by
      intro t ht
      exact hbase t (List.mem_of_mem_take ht)
    apply eiravel_prime_dvd_base_power_product n (L.take j) hprimeTake hp
    rw [← kestrelle_primePower_small_eq_base_take n z hn hz]
    exact hpd
  have hlarge : q ∈ L.drop j := by
    have hprimeDrop : ∀ t ∈ L.drop j, t.Prime := by
      intro t ht
      exact hbase t (List.mem_of_mem_drop ht)
    apply eiravel_prime_dvd_base_power_product n (L.drop j) hprimeDrop hq
    rw [← kestrelle_primePower_large_eq_base_drop n z hn hz]
    exact hqd
  exact kestrelle_primePower_base_order n z hn hz p hsmall q hlarge

#print axioms eiravel_classical_primePower_prefix_divisor_order

end PaperB.M4B
