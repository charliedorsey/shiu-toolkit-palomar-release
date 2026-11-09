module

public import ShiuPublic.VaelisPrimePowerSplitCoprime
public import ShiuPublic.ClassIVRoughPower

public section
namespace PaperB.M4B

theorem classical_primePower_prefix_weight_factorization
    {f : ArithmeticFunction ℝ} {A : ℝ} (hf : Shiu.ClassicalEnvelope f A)
    (n z : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z) :
    f n = f (classical_primePower_prefix_split n z hn hz).small.prod *
      f (classical_primePower_prefix_split n z hn hz).large.prod := by
  let S := classical_primePower_prefix_split n z hn hz
  have hcop := classical_primePower_prefix_coprime n z hn hz
  calc
    f n = f (S.small.prod * S.large.prod) := congrArg f S.factorization
    _ = f S.small.prod * f S.large.prod :=
      hf.multiplicative.map_mul_of_coprime hcop.gcd_eq_one
#print axioms classical_primePower_prefix_weight_factorization
end PaperB.M4B
