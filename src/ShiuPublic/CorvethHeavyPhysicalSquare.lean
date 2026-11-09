module

public import ShiuPublic.CorvethHeavyPowerSquare

public section

namespace PaperB.M4B

/-- The exact crossed atom of the physical prime-power prefix is a
full valuation block of the original source. -/
theorem corveth_crossing_atom_source_square
    (n z : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z)
    (bshort : (classical_primePower_prefix_split n z hn hz).small.prod ≤ Nat.sqrt z)
    (p : ℕ) (hp : p ∈ n.primeFactors)
    (hcross :
      ∃ ts, (classical_primePower_prefix_split n z hn hz).large =
        p ^ n.factorization p :: ts)
    (hbase : p ≤ Nat.sqrt z) :
    p ^ 2 ∣ n := by
  let S := classical_primePower_prefix_split n z hn hz
  obtain ⟨t, ts, hlarge, hheavy⟩ :=
    (corveth_primePower_crossing_heavy_or_empty n z hn hz bshort).resolve_left
      (by rintro hnil; obtain ⟨us, hus⟩ := hcross; rw [hnil] at hus; simp at hus)
  obtain ⟨us, hus⟩ := hcross
  have ht : t = p ^ n.factorization p := by
    rw [hus] at hlarge
    exact (List.cons.inj hlarge).1.symm
  have hpm : p.Prime := Nat.prime_of_mem_primeFactors hp
  have he : 0 < n.factorization p := hpm.factorization_pos_of_dvd hn
    (Nat.dvd_of_mem_primeFactors hp)
  have hblock : p ^ n.factorization p ∣ n := by
    have hmem : p ^ n.factorization p ∈ S.large := by
      rw [hus]; simp
    have hd : p ^ n.factorization p ∣ S.large.prod := List.dvd_prod hmem
    exact hd.trans (by
      refine ⟨S.small.prod, ?_⟩
      simpa only [Nat.mul_comm] using S.factorization)
  exact corveth_heavy_power_square_divisor n p (n.factorization p) z
    hpm he hblock hbase (ht ▸ hheavy)

#print axioms corveth_crossing_atom_source_square
end PaperB.M4B
