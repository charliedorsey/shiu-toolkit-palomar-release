module

public import ShiuPublic.CorvethClassicalHeavyBlock

public section

namespace PaperB.M4B

/-- A heavy whole-prime-power block whose base prime is not large must
contain a square. This isolates precisely the new repeated-prime case. -/
theorem corveth_heavy_power_exponent_two
    (p e z : ℕ) (hp : p.Prime)
    (he : 0 < e) (hbase : p ≤ Nat.sqrt z)
    (hheavy : Nat.sqrt z < p ^ e) :
    2 ≤ e := by
  by_contra h
  have heq : e = 1 := by omega
  subst e
  exact (not_lt_of_ge hbase) (by simpa using hheavy)

/-- Every heavy composite prime-power crossing gives a literal square
divisor of the original source integer, not just a heuristic rare family. -/
theorem corveth_heavy_power_square_divisor
    (n p e z : ℕ)
    (hp : p.Prime) (he : 0 < e)
    (hblock : p ^ e ∣ n)
    (hbase : p ≤ Nat.sqrt z)
    (hheavy : Nat.sqrt z < p ^ e) :
    p ^ 2 ∣ n := by
  have htwo := corveth_heavy_power_exponent_two p e z hp he hbase hheavy
  exact (pow_dvd_pow p htwo).trans hblock

#print axioms corveth_heavy_power_exponent_two
#print axioms corveth_heavy_power_square_divisor
end PaperB.M4B
