module

public import Mathlib

public section

namespace PaperB.M4B

/-- Convert the integer square-root split's strict long-prefix inequality
into the real lower cutoff used by the unrestricted Class III consumer. -/
theorem eiravel_nat_sqrt_lt_to_real_half
    (z b : ℕ) (hb : Nat.sqrt z < b) :
    (z : ℝ) ^ (1 / 2 : ℝ) ≤ (b : ℝ) := by
  have hnat : z ≤ b ^ 2 := by
    calc
      z ≤ (Nat.sqrt z + 1) ^ 2 :=
        (Nat.lt_succ_sqrt' z).le
      _ ≤ b ^ 2 :=
        Nat.pow_le_pow_left (by omega : Nat.sqrt z + 1 ≤ b) 2
  have hreal : (z : ℝ) ≤ (b : ℝ)^2 := by
    exact_mod_cast hnat
  rw [← Real.sqrt_eq_rpow]
  exact (Real.sqrt_le_iff).2 ⟨by positivity, hreal⟩

#print axioms eiravel_nat_sqrt_lt_to_real_half
end PaperB.M4B
