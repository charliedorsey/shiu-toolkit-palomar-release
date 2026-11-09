module

public import ShiuPublic.VaelisClassIVPrefixNonSquarefree
public import ShiuPublic.VaelisPrimePowerPrefix

public section

namespace PaperB.M4B

/-- The unrestricted Class IV prefix membership adapter.  The only
remaining ordering input is the base-prime divisor-order theorem from the
actual physical prefix split. No squarefree hypothesis is introduced. -/
theorem eiravel_classical_classIV_prefix_of_divisor_order
    (n z k p : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z)
    (hlo : Nat.sqrt z ≤
      (classical_primePower_prefix_split n z hn hz).small.prod)
    (hcop : n.Coprime k)
    (hp : p.Prime)
    (hpd : p ∣ (classical_primePower_prefix_split n z hn hz).large.prod)
    (horder : ∀ q : ℕ, q.Prime →
       q ∣ (classical_primePower_prefix_split n z hn hz).small.prod →
       q < p) :
    (classical_primePower_prefix_split n z hn hz).small.prod ∈
      Shiu.classicalClassIVPrefixSet z k p := by
  let S := classical_primePower_prefix_split n z hn hz
  have hsmallDiv : S.small.prod ∣ n := by
    refine ⟨S.large.prod, ?_⟩
    exact S.factorization
  have hcopSmall : S.small.prod.Coprime k :=
    hcop.coprime_dvd_left hsmallDiv
  unfold Shiu.classicalClassIVPrefixSet
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_Icc.mpr ⟨hlo, S.small_prod_le⟩
  constructor
  · exact hcopSmall
  · intro q hq
    have hqprime := Nat.prime_of_mem_primeFactors hq
    have hqdiv := Nat.dvd_of_mem_primeFactors hq
    exact (horder q hqprime hqdiv).le

#print axioms eiravel_classical_classIV_prefix_of_divisor_order

end PaperB.M4B
