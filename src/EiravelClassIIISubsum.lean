module

public import EiravelSourceWeightedAssembly
public import ShiuPublic.CorvethClassicalClassIIIWeighted

public section

namespace PaperB.M4B
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Unrestricted full-prime-power Class III restricted physical mass
injects into the exact Corveth weighted divisor overcount. -/
theorem eiravel_unrestricted_classIII_subsum_le
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (x y z k a : ℕ) :
    (∑ n ∈ (eiravelShiuPhysicalSet x y k a).filter
      (fun n => ∃ b ∈ corvethClassicalClassIIIFactors x z k, b ∣ n), f n) ≤
      corvethClassicalClassIIIWeightedOvercount f x y z k a := by
  classical
  let S := (eiravelShiuPhysicalSet x y k a).filter
    (fun n => ∃ b ∈ corvethClassicalClassIIIFactors x z k, b ∣ n)
  let T : Finset (Σ _b : ℕ, ℕ) :=
    (corvethClassicalClassIIIFactors x z k).sigma (fun b =>
      (Finset.Ioc (x-y) x).filter
        (fun n => n ≡ a [MOD k] ∧ b ∣ n))
  have hpay : ∀ n : {n // n ∈ S},
      ∃ b ∈ corvethClassicalClassIIIFactors x z k, b ∣ n.1 := by
    intro n
    exact (Finset.mem_filter.mp n.2).2
  let b : {n // n ∈ S} → ℕ := fun n =>
    Classical.choose (hpay n)
  let i : {n // n ∈ S} → (Σ _b : ℕ, ℕ) :=
    fun n => ⟨b n, n.1⟩
  have hspec : ∀ n : {n // n ∈ S},
      b n ∈ corvethClassicalClassIIIFactors x z k ∧
      n.1 ∈ (Finset.Ioc (x-y) x).filter
        (fun m => m ≡ a [MOD k] ∧ b n ∣ m) := by
    intro n
    have he := Classical.choose_spec (hpay n)
    have hs := (Finset.mem_filter.mp n.2).1
    have hp := (Finset.mem_filter.mp hs)
    exact ⟨he.1, Finset.mem_filter.mpr
      ⟨hp.1, hp.2.1, he.2⟩⟩
  have hi : Function.Injective i := by
    intro n m h
    apply Subtype.ext
    exact congrArg (fun t => t.2) h
  have himage : S.attach.image i ⊆ T := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨n, hn, rfl⟩
    rw [Finset.mem_sigma]
    exact hspec n
  calc
    (∑ n ∈ S, f n) = ∑ n ∈ S.attach, f n.1 := by
      simpa using
        (Finset.sum_attach (s := S) (f := fun n => f n)).symm
    _ = ∑ n ∈ S.attach, f (i n).2 := by rfl
    _ = ∑ t ∈ S.attach.image i, f t.2 := by
      symm
      exact Finset.sum_image hi.injOn
    _ ≤ ∑ t ∈ T, f t.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun t ht _ => hf.nonnegative t.2)
    _ = corvethClassicalClassIIIWeightedOvercount f x y z k a := by
      unfold corvethClassicalClassIIIWeightedOvercount
      dsimp [T]
      rw [Finset.sum_sigma]

#print axioms eiravel_unrestricted_classIII_subsum_le
end
end PaperB.M4B
