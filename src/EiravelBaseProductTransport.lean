module

public import ShiuPublic.VaelisPrimePowerPrefix
public import Mathlib.Data.List.Prime

public section

namespace PaperB.M4B

/-- Any prime divisor of a product of full prime-power atoms is a base
prime from the corresponding list. No ordering of numerical atoms. -/
theorem eiravel_prime_dvd_base_power_product
    (n : ℕ) (L : List ℕ)
    (hprime : ∀ p ∈ L, p.Prime)
    {q : ℕ} (hq : q.Prime)
    (hd : q ∣ (L.map (fun p => p ^ n.factorization p)).prod) :
    q ∈ L := by
  obtain ⟨t, ht, hqt⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  obtain ⟨p, hp, htp⟩ := List.mem_map.mp ht
  subst t
  have hqp : q ∣ p := hq.dvd_of_dvd_pow hqt
  have hpeq : q = p :=
    (Nat.prime_dvd_prime_iff_eq hq (hprime p hp)).mp hqp
  exact hpeq ▸ hp

#print axioms eiravel_prime_dvd_base_power_product
end PaperB.M4B
