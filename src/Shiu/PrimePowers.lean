module

public import ShiuPublic.VaelisPrimePowerWeightedSplit
public import ShiuPublic.PrimePowerEnvelope
public import ShiuPublic.LargePrimeEulerFactor

public section

/-! Entire prime-power blocks; no squarefree-support assumption. -/
namespace Shiu.API

noncomputable def primePowerPrefix
    (n z : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z) :
    PaperB.M4B.ClassicalPrimePowerPrefixSplit n z :=
  PaperB.M4B.classical_primePower_prefix_split n z hn hz

theorem primePowerPrefix_weight
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (n z : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z) :
    f n = f (primePowerPrefix n z hn hz).small.prod *
      f (primePowerPrefix n z hn hz).large.prod := by
  exact PaperB.M4B.classical_primePower_prefix_weight_factorization
    hf n z hn hz

theorem primePowerTail
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (p N : ℕ) (hp : p.Prime) (hpA : 2 * A ≤ (p : ℝ)) :
    (∑ j ∈ Finset.range N,
      f (p ^ (j + 2)) / (p : ℝ) ^ (j + 2)) ≤
        2 * (A / (p : ℝ)) ^ 2 :=
  Shiu.classical_prime_power_tail hf p N hp hpA

theorem primePowerEulerRankin
    (f : ℕ → ℝ) (A δ : ℝ) (p N : ℕ)
    (hA : 0 ≤ A) (hp : 0 < p) (hone : f 1 = 1)
    (hhalf : 2 * A ≤ (p : ℝ) ^ (1 - δ))
    (hpower : ∀ m : ℕ, 2 ≤ m → f (p ^ m) ≤ A ^ m) :
    (∑ j ∈ Finset.range (N+2),
      f (p ^ j) / (p : ℝ) ^ ((j : ℝ) * (1 - δ))) ≤
      1 + f p / (p : ℝ) ^ (1 - δ) +
        2 * (A / (p : ℝ) ^ (1 - δ)) ^ 2 :=
  Shiu.large_prime_euler_factor_at_rankin_scale
    f A δ p N hA hp hone hhalf hpower

#print axioms primePowerPrefix_weight
#print axioms primePowerTail
#print axioms primePowerEulerRankin
end Shiu.API
