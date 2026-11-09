module

public import ShiuPublic.VaelisClassicalSmoothTailOriginal

public section

namespace Shiu
open scoped BigOperators

/-- Complete unrestricted ordinary smooth tail, with ALL prime powers,
original M4B eligible primes, sharp threshold, and uniform Rankin factor. -/
theorem classical_complete_smooth_tail_original_mass
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : ClassicalEnvelope f A) (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n → f n ≤ B * (n : ℝ)^(1/4 : ℝ))
    (T P k : ℕ) (hT : 1 ≤ T) (D : ℝ)
    (hD : 0 < D) (hP : Real.exp (4*D) ≤ (P : ℝ))
    (hδ : 0 ≤ D / Real.log (P : ℝ)) :
    (∑' n : ℕ,
      if n ∈ Nat.factoredNumbers ((Nat.primesLE P).filter (fun q => ¬ q ∣ k)) ∧ T ≤ n then
        f n / (n : ℝ) else 0) ≤
      (T : ℝ)^(-(D/Real.log (P : ℝ))) *
      (smallPrimeConstant (fixedPrimePowerCutoff A D) B *
        Real.exp (PaperB.M4B.primeMass f P k +
          PaperB.M4B.primeRankinCorrection f P k
            (D/Real.log (P : ℝ)) + 2*A^2*Real.exp (2*D))) := by
  classical
  let S : Finset ℕ := (Nat.primesLE P).filter (fun q => ¬ q ∣ k)
  let w : ℕ → ℝ := fun n => f n / (n : ℝ)
  let g : ℕ → ℝ := fun n => if n ∈ Nat.factoredNumbers S ∧ T ≤ n then w n else 0
  let C : ℝ := (T : ℝ)^(-(D/Real.log (P : ℝ))) *
      (smallPrimeConstant (fixedPrimePowerCutoff A D) B *
        Real.exp (PaperB.M4B.primeMass f P k +
          PaperB.M4B.primeRankinCorrection f P k
            (D/Real.log (P : ℝ)) + 2*A^2*Real.exp (2*D)))
  have hw : ∀ n, 0 ≤ w n := by
    intro n
    exact div_nonneg (hf.nonnegative n) (by positivity)
  have hg : ∀ n, 0 ≤ g n := by
    intro n
    by_cases hh : n ∈ Nat.factoredNumbers S ∧ T ≤ n
    · simpa [g, hh] using hw n
    · simp [g, hh]
  have hrange : ∀ N, (∑ n ∈ Finset.range N, g n) ≤ C := by
    intro N
    have hsub : (Finset.range N).filter (fun n => n ∈ Nat.factoredNumbers S ∧ T ≤ n) ⊆
        boundedSmoothTailSet S T (N+1) := by
      intro n hn
      obtain ⟨hnrange, ⟨hnfact, hnT⟩⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnzero, hprimes⟩ :=
        Nat.mem_factoredNumbers_iff_primeFactors_subset.mp hnfact
      have hnlt : n < N := Finset.mem_range.mp hnrange
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_Icc.mpr (by omega), hprimes⟩
      · exact hnT
    have hfinite :
        (∑ n ∈ (Finset.range N).filter (fun n => n ∈ Nat.factoredNumbers S ∧ T ≤ n), w n) ≤
          ∑ n ∈ boundedSmoothTailSet S T (N+1), w n := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n hn _ => hw n)
    have hsource := classical_bounded_smooth_tail_original_mass
      hf hB hgrowth T (N+1) P k hT (by omega) D hD hP hδ
    have hbound : (∑ n ∈ boundedSmoothTailSet S T (N+1), w n) ≤ C := by
      simpa only [S, w, C] using hsource
    calc
      (∑ n ∈ Finset.range N, g n) =
        ∑ n ∈ (Finset.range N).filter (fun n => n ∈ Nat.factoredNumbers S ∧ T ≤ n), w n := by
          simp only [g, Finset.sum_filter]
      _ ≤ ∑ n ∈ boundedSmoothTailSet S T (N+1), w n := hfinite
      _ ≤ C := hbound
  have htsum : (∑' n : ℕ, g n) ≤ C :=
    Real.tsum_le_of_sum_range_le hg hrange
  simpa only [g, S, w, C] using htsum

#print axioms Shiu.classical_complete_smooth_tail_original_mass
end Shiu
