module

public import ShiuPublic.SmallPrimeProduct

public section

namespace Shiu
open scoped BigOperators

/-- A geometric factor with exponent 1-delta-1/4 is dominated by
the fixed exponent 1/2 whenever delta <= 1/4. -/
theorem small_prime_geometric_uniform
    (q : ℕ) (hq : 2 ≤ q) (B δ : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hquarter : δ ≤ 1/4) :
    B / (1 - (q : ℝ) ^ (-(1-δ-1/4))) ≤
      B / (1 - (q : ℝ) ^ (-(1/2 : ℝ))) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hqgt : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hexp : -(1-δ-1/4) ≤ -(1/2 : ℝ) := by linarith
  have hp := Real.rpow_le_rpow_of_exponent_le hq1 hexp
  have hneg : -(1/2 : ℝ) < 0 := by norm_num
  have hu : (q : ℝ) ^ (-(1/2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hqgt hneg
  have ht : (q : ℝ) ^ (-(1-δ-1/4)) < 1 := lt_of_le_of_lt hp hu
  have hpos : 0 < 1 - (q : ℝ) ^ (-(1/2 : ℝ)) := sub_pos.mpr hu
  have htpos : 0 < 1 - (q : ℝ) ^ (-(1-δ-1/4)) := sub_pos.mpr ht
  apply (div_le_div_iff₀ htpos hpos).mpr
  nlinarith

#print axioms Shiu.small_prime_geometric_uniform
end Shiu
