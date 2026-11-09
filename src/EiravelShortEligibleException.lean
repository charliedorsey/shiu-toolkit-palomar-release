module

public import EiravelCrossingModulus
public import ShiuPublic.CorvethClassicalPrefixCore

public section

namespace PaperB.M4B

/-- The genuine short-prefix crossing lands in the SAME literal eligible
prime family and minimal whole-power divisor used by the paid AP theorem. -/
theorem eiravel_short_crossing_eligible_exception
    (n z k : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z)
    (hT : 0 < Nat.sqrt z)
    (hcop : n.Coprime k)
    (hshort : (classical_primePower_prefix_split n z hn hz).small.prod ≤ Nat.sqrt z)
    (p : ℕ) (hp : p ∈ n.primeFactors)
    (hpsqrt : p ≤ Nat.sqrt z)
    (hcross : ∃ ts : List ℕ,
      (classical_primePower_prefix_split n z hn hz).large =
        p ^ n.factorization p :: ts) :
    ∃ q ∈ (Nat.primesLE (Nat.sqrt z)).filter (fun q => ¬ q ∣ k),
      q ^ (Nat.log q (Nat.sqrt z) + 1) ∣ n := by
  classical
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hcopP : p.Coprime k :=
    hcop.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp)
  have hnot : ¬ p ∣ k := hpprime.coprime_iff_not_dvd.mp hcopP
  have hmem : p ∈
      (Nat.primesLE (Nat.sqrt z)).filter (fun q => ¬ q ∣ k) := by
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_primesLE.mpr ⟨hpsqrt, hpprime⟩, hnot⟩
  refine ⟨p, hmem, ?_⟩
  simpa only [eiravelCrossingModulus] using
    eiravel_physical_crossing_minimal_modulus
      n z hn hz hT hshort p hp hcross

#print axioms eiravel_short_crossing_eligible_exception

end PaperB.M4B
