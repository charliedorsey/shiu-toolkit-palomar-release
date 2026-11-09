module

public import ShiuPublic.VaelisPrimePowerWeightedSplit

public section

namespace PaperB.M4B

/-- Consumer-facing source package for unrestricted prime-power splitting.
It deliberately does not assert squarefreeness of either factor. -/
theorem corveth_classical_primePower_source_core
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A) (n z k : ℕ)
    (hn : n ≠ 0) (hz : 1 ≤ z) (hnk : n.Coprime k) :
    let S := classical_primePower_prefix_split n z hn hz
    n = S.small.prod * S.large.prod ∧
    S.small.prod ≤ z ∧
    S.small.prod.Coprime S.large.prod ∧
    S.small.prod.Coprime k ∧
    S.large.prod.Coprime k ∧
    f n = f S.small.prod * f S.large.prod := by
  dsimp
  let S := classical_primePower_prefix_split n z hn hz
  have hfac : n = S.small.prod * S.large.prod := S.factorization
  have hdivb : S.small.prod ∣ n := ⟨S.large.prod, hfac⟩
  have hdivd : S.large.prod ∣ n := by
    refine ⟨S.small.prod, ?_⟩
    simpa [Nat.mul_comm] using hfac
  refine ⟨hfac, S.small_prod_le, classical_primePower_prefix_coprime n z hn hz,
      hnk.coprime_dvd_left hdivb, hnk.coprime_dvd_left hdivd, ?_⟩
  exact classical_primePower_prefix_weight_factorization hf n z hn hz

#print axioms corveth_classical_primePower_source_core
end PaperB.M4B
