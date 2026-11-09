module

public import ShiuPublic.VaelisSortedPrimePowerBlocks

public section

namespace PaperB.M4B

/-- Two different physical primes retain coprimality after all repeated
factors are bundled into their full prime powers. -/
theorem classical_prime_power_atoms_coprime
    (n p q : ℕ)
    (hp : p ∈ n.primeFactors) (hq : q ∈ n.primeFactors)
    (hpq : p ≠ q) :
    (p ^ n.factorization p).Coprime (q ^ n.factorization q) := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hqq : q.Prime := Nat.prime_of_mem_primeFactors hq
  exact ((Nat.coprime_primes hpp hqq).2 hpq).pow _ _

#print axioms classical_prime_power_atoms_coprime
end PaperB.M4B
