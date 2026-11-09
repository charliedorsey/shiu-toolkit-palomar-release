module

public import ShiuPublic.CorvethHeavyPhysicalSquare

public section

namespace PaperB.M4B

/-- The minimal prime-power modulus strictly exceeding the square-root gate. -/
@[expose] def eiravelCrossingModulus (z p : ℕ) : ℕ :=
  p ^ (Nat.log p (Nat.sqrt z) + 1)

theorem eiravel_crossing_modulus_gt
    (z p : ℕ) (hp : p.Prime) :
    Nat.sqrt z < eiravelCrossingModulus z p := by
  unfold eiravelCrossingModulus
  exact Nat.lt_pow_succ_log_self hp.one_lt (Nat.sqrt z)

theorem eiravel_crossing_modulus_dvd_of_power
    (z p e n : ℕ) (hp : p.Prime)
    (hT : 0 < Nat.sqrt z) (hlarge : Nat.sqrt z < p ^ e)
    (hdiv : p ^ e ∣ n) :
    eiravelCrossingModulus z p ∣ n := by
  have hexp : Nat.log p (Nat.sqrt z) + 1 ≤ e := by
    exact Nat.succ_le_of_lt
      (Nat.log_lt_of_lt_pow hT.ne' hlarge)
  exact (pow_dvd_pow p hexp).trans hdiv

/-- Physical source crossing, without discarding its valuation to p^2. -/
theorem eiravel_physical_crossing_minimal_modulus
    (n z : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z)
    (hT : 0 < Nat.sqrt z)
    (hshort :
      (classical_primePower_prefix_split n z hn hz).small.prod ≤ Nat.sqrt z)
    (p : ℕ) (hp : p ∈ n.primeFactors)
    (hcross : ∃ ts,
      (classical_primePower_prefix_split n z hn hz).large =
        p ^ n.factorization p :: ts) :
    eiravelCrossingModulus z p ∣ n := by
  let S := classical_primePower_prefix_split n z hn hz
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  obtain ⟨ts, hts⟩ := hcross
  obtain ⟨t, us, hlarge, hheavy⟩ :=
    (corveth_primePower_crossing_heavy_or_empty n z hn hz hshort).resolve_left
      (by intro hempty; rw [hempty] at hts; simp at hts)
  have ht : t = p ^ n.factorization p := by
    rw [hts] at hlarge
    exact (List.cons.inj hlarge).1.symm
  have hbig : Nat.sqrt z < p ^ n.factorization p := ht ▸ hheavy
  have hmem : p ^ n.factorization p ∈ S.large := by
    rw [hts]; simp
  have hdiv : p ^ n.factorization p ∣ S.large.prod := List.dvd_prod hmem
  have hsource : p ^ n.factorization p ∣ n := by
    refine hdiv.trans ⟨S.small.prod, ?_⟩
    simpa only [Nat.mul_comm] using S.factorization
  exact eiravel_crossing_modulus_dvd_of_power
    z p (n.factorization p) n hprime hT hbig hsource

#print axioms eiravel_physical_crossing_minimal_modulus

#print axioms eiravel_crossing_modulus_gt
#print axioms eiravel_crossing_modulus_dvd_of_power

end PaperB.M4B
