module

public import EiravelSourceWeightedAssembly
public import ShiuPublic.CorvethClassicalClassIFinal

public section

namespace PaperB.M4B
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Exact weighted reindexing of the unrestricted physical Class I subset
into the established classical Class I b,d overcount. -/
theorem eiravel_unrestricted_classI_subsum_le
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (x y z k a : ℕ) :
    (∑ n ∈ (eiravelShiuPhysicalSet x y k a).filter
        (corvethClassicalClassIPays f x y z k a), f n) ≤
      classIOvercount f x y z k a := by
  classical
  let S := (eiravelShiuPhysicalSet x y k a).filter
    (corvethClassicalClassIPays f x y z k a)
  let B := (Finset.Icc 1 z).filter (fun b => b.Coprime k)
  let T : Finset (Σ _b : ℕ, ℕ) :=
    B.sigma (fun b => classIInnerSet x y z k a b)
  have hpay : ∀ n : {n // n ∈ S},
      corvethClassicalClassIPays f x y z k a n.1 := by
    intro n
    exact (Finset.mem_filter.mp n.2).2
  let w : {n // n ∈ S} → ℕ × ℕ := fun n =>
    Classical.choose (hpay n)
  let i : {n // n ∈ S} → (Σ _b : ℕ, ℕ) :=
    fun n => ⟨(w n).1, (w n).2⟩
  have hspec : ∀ n : {n // n ∈ S},
      n.1 = (w n).1 * (w n).2 ∧
      f n.1 = f (w n).1 * f (w n).2 ∧
      (w n).1 ∈ B ∧
      (w n).2 ∈ classIInnerSet x y z k a (w n).1 := by
    intro n
    simpa [B, w] using Classical.choose_spec (hpay n)
  have hi : Function.Injective i := by
    intro n m h
    apply Subtype.ext
    have hw : w n = w m := by
      apply Prod.ext
      · exact congrArg Sigma.fst h
      · exact congrArg (fun t => t.2) h
    rw [(hspec n).1, (hspec m).1, hw]
  have himage : S.attach.image i ⊆ T := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨n, hn, rfl⟩
    rw [Finset.mem_sigma]
    exact ⟨(hspec n).2.2.1, (hspec n).2.2.2⟩
  calc
    (∑ n ∈ S, f n) = ∑ n ∈ S.attach, f n.1 := by
      simpa using
        (Finset.sum_attach (s := S) (f := fun n => f n)).symm
    _ = ∑ n ∈ S.attach,
        f (i n).1 * f (i n).2 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (hspec n).2.1
    _ = ∑ t ∈ S.attach.image i, f t.1 * f t.2 := by
      symm
      exact Finset.sum_image hi.injOn
    _ ≤ ∑ t ∈ T, f t.1 * f t.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun t ht _ =>
          mul_nonneg (hf.nonnegative t.1) (hf.nonnegative t.2))
    _ = classIOvercount f x y z k a := by
      unfold classIOvercount
      dsimp [T, B]
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]

#print axioms eiravel_unrestricted_classI_subsum_le
end
end PaperB.M4B
