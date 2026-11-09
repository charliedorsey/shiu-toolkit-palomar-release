module

public import ShiuPublic.VaelisClassIVShellRankin

public section
namespace PaperB.M4B
open scoped BigOperators
theorem classical_primeMass_mono
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    {P Z k : ℕ} (hPZ : P ≤ Z) :
    primeMass f P k ≤ primeMass f Z k := by
  classical
  let S : Finset ℕ :=
    (Nat.primesLE P).filter (fun q => ¬ q ∣ k)
  let T : Finset ℕ :=
    (Nat.primesLE Z).filter (fun q => ¬ q ∣ k)
  have hsub : S ⊆ T := by
    intro q hq
    have hqF := Finset.mem_filter.mp hq
    have hqP := Nat.mem_primesLE.mp hqF.1
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_primesLE.mpr ⟨hqP.1.trans hPZ, hqP.2⟩, hqF.2⟩
  have hnonneg : ∀ q ∈ T, 0 ≤ f q / (q : ℝ) := by
    intro q hq
    exact div_nonneg (hf.nonnegative q) (by positivity)
  unfold primeMass
  change (∑ q ∈ S, f q / (q : ℝ)) ≤ ∑ q ∈ T, f q / (q : ℝ)
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun q hq _ => hnonneg q hq)
#print axioms classical_primeMass_mono
end PaperB.M4B
