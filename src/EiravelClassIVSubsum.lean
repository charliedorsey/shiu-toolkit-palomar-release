module

public import EiravelSourceWeightedAssembly
public import ShiuPublic.VaelisClassIVAllShell

public section

namespace PaperB.M4B
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Exact unrestricted physical Class IV mass is bounded by the
published non-squarefree shell overcount, preserving f(n)=f(b)f(d). -/
theorem eiravel_unrestricted_classIV_subsum_le
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (x y z k a : ℕ) :
    (∑ n ∈ (eiravelShiuPhysicalSet x y k a).filter
      (eiravelClassIVPays f x y z k a), f n) ≤
      classicalClassIVOvercount f x y z k a := by
  classical
  let S := (eiravelShiuPhysicalSet x y k a).filter
    (eiravelClassIVPays f x y z k a)
  let R := Finset.Icc 2 (shiuClassIVR0 x z)
  let T : Finset (Σ _r : ℕ, Σ _b : ℕ, ℕ) :=
    R.sigma (fun r =>
      (Shiu.classicalClassIVPrefixSet z k (classIVShellUpper z r)).sigma
        (fun b => classIVInnerSet x y k a b (classIVShellLower z r)))
  have hpay : ∀ n : {n // n ∈ S},
      ∃ r ∈ R, ∃ u : ℕ × ℕ,
        n.1 = u.1 * u.2 ∧
        f n.1 = f u.1 * f u.2 ∧
        u.1 ∈ Shiu.classicalClassIVPrefixSet z k (classIVShellUpper z r) ∧
        u.2 ∈ classIVInnerSet x y k a u.1 (classIVShellLower z r) := by
    intro n
    obtain ⟨r, hr, b, d, hb, hd, hfac, hw⟩ :=
      (Finset.mem_filter.mp n.2).2
    exact ⟨r, hr, (b,d), hfac, hw, hb, hd⟩
  let rch : {n // n ∈ S} → ℕ := fun n =>
    Classical.choose (hpay n)
  let uch : {n // n ∈ S} → ℕ × ℕ := fun n =>
    Classical.choose (Classical.choose_spec (hpay n)).2
  let i : {n // n ∈ S} → (Σ _r : ℕ, Σ _b : ℕ, ℕ) :=
    fun n => ⟨rch n, ⟨(uch n).1, (uch n).2⟩⟩
  have hspec : ∀ n : {n // n ∈ S},
      rch n ∈ R ∧
      n.1 = (uch n).1 * (uch n).2 ∧
      f n.1 = f (uch n).1 * f (uch n).2 ∧
      (uch n).1 ∈ Shiu.classicalClassIVPrefixSet z k
        (classIVShellUpper z (rch n)) ∧
      (uch n).2 ∈ classIVInnerSet x y k a (uch n).1
        (classIVShellLower z (rch n)) := by
    intro n
    have hr := Classical.choose_spec (hpay n)
    have hu := Classical.choose_spec hr.2
    simpa [R, rch, uch] using And.intro hr.1 hu
  have hi : Function.Injective i := by
    intro n m h
    apply Subtype.ext
    have hb : (uch n).1 = (uch m).1 :=
      congrArg (fun t => t.2.1) h
    have hd : (uch n).2 = (uch m).2 :=
      congrArg (fun t => t.2.2) h
    rw [(hspec n).2.1, (hspec m).2.1, hb, hd]
  have himage : S.attach.image i ⊆ T := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨n, hn, rfl⟩
    rw [Finset.mem_sigma, Finset.mem_sigma]
    exact ⟨(hspec n).1, (hspec n).2.2.2.1, (hspec n).2.2.2.2⟩
  calc
    (∑ n ∈ S, f n) = ∑ n ∈ S.attach, f n.1 := by
      simpa using
        (Finset.sum_attach (s := S) (f := fun n => f n)).symm
    _ = ∑ n ∈ S.attach,
        f (i n).2.1 * f (i n).2.2 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (hspec n).2.2.1
    _ = ∑ t ∈ S.attach.image i, f t.2.1 * f t.2.2 := by
      symm
      exact Finset.sum_image hi.injOn
    _ ≤ ∑ t ∈ T, f t.2.1 * f t.2.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun t ht _ =>
          mul_nonneg (hf.nonnegative t.2.1) (hf.nonnegative t.2.2))
    _ = classicalClassIVOvercount f x y z k a := by
      unfold classicalClassIVOvercount classicalClassIVShellOvercount
      dsimp [T, R]
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]

#print axioms eiravel_unrestricted_classIV_subsum_le
end
end PaperB.M4B
