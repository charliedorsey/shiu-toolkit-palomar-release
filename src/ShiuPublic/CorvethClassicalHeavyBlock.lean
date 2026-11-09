module

public import ShiuPublic.VaelisPrimePowerWeightedSplit

public section

namespace PaperB.M4B

theorem corveth_heavy_block_of_short_prefix
    {b z t : ℕ}
    (hb : b ≤ Nat.sqrt z) (hc : z < b * t) :
    Nat.sqrt z < t := by
  by_contra h
  have ht : t ≤ Nat.sqrt z := by omega
  have hmul : b * t ≤ (Nat.sqrt z) ^ 2 := by
    calc
      b * t ≤ Nat.sqrt z * t := Nat.mul_le_mul_right t hb
      _ ≤ Nat.sqrt z * Nat.sqrt z :=
        Nat.mul_le_mul_left (Nat.sqrt z) ht
      _ = (Nat.sqrt z) ^ 2 := by ring
  exact (not_lt_of_ge (hmul.trans (Nat.sqrt_le' z))) hc

theorem corveth_primePower_crossing_heavy_or_empty
    (n z : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z)
    (hb : (classical_primePower_prefix_split n z hn hz).small.prod ≤ Nat.sqrt z) :
    (classical_primePower_prefix_split n z hn hz).large = [] ∨
      ∃ t ts, (classical_primePower_prefix_split n z hn hz).large = t :: ts ∧
        Nat.sqrt z < t := by
  let S := classical_primePower_prefix_split n z hn hz
  rcases S.crossing with hnil | ⟨t, ts, hlarge, hcross⟩
  · exact Or.inl hnil
  · exact Or.inr ⟨t, ts, hlarge,
      corveth_heavy_block_of_short_prefix hb hcross⟩

#print axioms corveth_heavy_block_of_short_prefix
#print axioms corveth_primePower_crossing_heavy_or_empty
end PaperB.M4B
