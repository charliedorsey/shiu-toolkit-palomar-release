module

public import ShiuPublic.VaelisOriginalSmoothEuler

public section

namespace Shiu
open scoped BigOperators

/-- UNRESTRICTED non-squarefree P-smooth source sum, evaluated with the same
original M4B prime mass and Rankin correction used by Cendrel R0019.
Every ordinary integer multiplicity is retained; convergence is proved. -/
theorem classical_complete_smooth_original_mass
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : ClassicalEnvelope f A)
    (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n →
      f n ≤ B * (n : ℝ)^(1/4 : ℝ))
    (P k : ℕ) (D : ℝ)
    (hD : 0 < D)
    (hP : Real.exp (4*D) ≤ (P : ℝ)) :
    (∑' n : ℕ,
      if n ∈ Nat.factoredNumbers
          ((Nat.primesLE P).filter (fun q => ¬ q ∣ k)) then
        f n / (n : ℝ) ^ (1-D/Real.log (P : ℝ))
      else 0) ≤
      smallPrimeConstant (fixedPrimePowerCutoff A D) B *
      Real.exp (PaperB.M4B.primeMass f P k +
        PaperB.M4B.primeRankinCorrection f P k
          (D/Real.log (P:ℝ)) + 2*A^2*Real.exp (2*D)) := by
  classical
  let S : Finset ℕ := (Nat.primesLE P).filter (fun q => ¬ q ∣ k)
  let s : ℝ := 1-D/Real.log (P : ℝ)
  let w : ℕ → ℝ := fun n => f n / (n : ℝ) ^ s
  let g : ℕ → ℝ := fun n => if n ∈ Nat.factoredNumbers S then w n else 0
  let C : ℝ := smallPrimeConstant (fixedPrimePowerCutoff A D) B *
    Real.exp (PaperB.M4B.primeMass f P k +
      PaperB.M4B.primeRankinCorrection f P k
        (D/Real.log (P:ℝ)) + 2*A^2*Real.exp (2*D))
  have hw : ∀ n, 0 ≤ w n := by
    intro n
    exact div_nonneg (hf.nonnegative n) (Real.rpow_nonneg (by positivity) _)
  have hg : ∀ n, 0 ≤ g n := by
    intro n
    dsimp [g]
    by_cases hh : n ∈ Nat.factoredNumbers S
    · simpa [hh] using hw n
    · simp [hh]
  have hrange : ∀ N, (∑ n ∈ Finset.range N, g n) ≤ C := by
    intro N
    have hsub : (Finset.range N).filter (fun n => n ∈ Nat.factoredNumbers S) ⊆
        boundedSmoothSet S (N+1) := by
      intro n hn
      obtain ⟨hnrange, hnfact⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnzero, hprimes⟩ :=
        Nat.mem_factoredNumbers_iff_primeFactors_subset.mp hnfact
      have hnlt : n < N := Finset.mem_range.mp hnrange
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        constructor <;> omega
      · exact hprimes
    have hfinite :
        (∑ n ∈ (Finset.range N).filter (fun n => n ∈ Nat.factoredNumbers S), w n) ≤
          ∑ n ∈ boundedSmoothSet S (N+1), w n := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n hn _ => hw n)
    have hsource := classical_bounded_smooth_original_mass
      hf hB hgrowth (N+1) P k (by omega) D hD hP
    have hbound : (∑ n ∈ boundedSmoothSet S (N+1), w n) ≤ C := by
      simpa only [S, s, w, C] using hsource
    calc
      (∑ n ∈ Finset.range N, g n) =
        ∑ n ∈ (Finset.range N).filter (fun n => n ∈ Nat.factoredNumbers S), w n := by
          simp only [g, Finset.sum_filter]
      _ ≤ ∑ n ∈ boundedSmoothSet S (N+1), w n := hfinite
      _ ≤ C := hbound
  have htsum : (∑' n : ℕ, g n) ≤ C :=
    Real.tsum_le_of_sum_range_le hg hrange
  simpa only [g, S, s, w, C] using htsum

#print axioms Shiu.classical_complete_smooth_original_mass
end Shiu
