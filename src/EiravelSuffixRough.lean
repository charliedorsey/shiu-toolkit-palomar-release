module

public import PaperB.M4A.ShiuLemma2
public import ShiuPublic.VaelisPrimePowerPrefix

public section

namespace PaperB.M4B

/-- Suffix roughness follows from base-prime lower bounds. The source
prime-power atom ordering is not replaced by numerical ordering. -/
theorem eiravel_large_prod_rough_of_prime_lower
    (n z : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z)
    (w : ℕ)
    (hordered : ∀ q : ℕ, q.Prime →
      q ∣ (classical_primePower_prefix_split n z hn hz).large.prod →
      w < q) :
    PaperB.M4A.shiuRough
      (classical_primePower_prefix_split n z hn hz).large.prod w := by
  apply (PaperB.M4A.allSmallPrimesAvoid_iff_shiuRough).mp
  intro q hq hqw hqd
  have hgt := hordered q hq hqd
  omega

#print axioms eiravel_large_prod_rough_of_prime_lower
end PaperB.M4B
