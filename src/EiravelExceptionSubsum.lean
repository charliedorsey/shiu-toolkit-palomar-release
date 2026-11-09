module

public import EiravelSourceWeightedAssembly
public import EiravelGeneralPowerAP

public section

namespace PaperB.M4B
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The original physical exceptional points inject into the exact
complete-prime-power divisor AP overcount, retaining the sharp
progression, full modulus, residue and original weight. -/
theorem eiravel_unrestricted_exception_subsum_le
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (x y z k a : ℕ) :
    (∑ n ∈ (eiravelShiuPhysicalSet x y k a).filter
      (eiravelExceptionPays z k), f n) ≤
      eiravelPowerExceptionalMass f x y k a
        ((Nat.primesLE (Nat.sqrt z)).filter (fun p => ¬ p ∣ k))
        (fun p => p ^ (Nat.log p (Nat.sqrt z) + 1)) := by
  classical
  let P : Finset ℕ :=
    (Nat.primesLE (Nat.sqrt z)).filter (fun p => ¬ p ∣ k)
  let m : ℕ → ℕ := fun p => p ^ (Nat.log p (Nat.sqrt z) + 1)
  let S := (eiravelShiuPhysicalSet x y k a).filter
    (eiravelExceptionPays z k)
  let T : Finset (Σ _p : ℕ, ℕ) :=
    P.sigma (fun p => (Finset.Ioc (x-y) x).filter
      (fun n => n ≡ a [MOD k] ∧ m p ∣ n))
  have hpay : ∀ n : {n // n ∈ S}, ∃ p ∈ P, m p ∣ n.1 := by
    intro n
    simpa [P, m, eiravelExceptionPays] using
      (Finset.mem_filter.mp n.2).2
  let p : {n // n ∈ S} → ℕ := fun n => Classical.choose (hpay n)
  let i : {n // n ∈ S} → (Σ _p : ℕ, ℕ) :=
    fun n => ⟨p n, n.1⟩
  have hspec : ∀ n : {n // n ∈ S},
      p n ∈ P ∧
      n.1 ∈ (Finset.Ioc (x-y) x).filter
        (fun a0 => a0 ≡ a [MOD k] ∧ m (p n) ∣ a0) := by
    intro n
    have he := Classical.choose_spec (hpay n)
    have hs := (Finset.mem_filter.mp n.2).1
    have hp := (Finset.mem_filter.mp hs)
    exact ⟨he.1, Finset.mem_filter.mpr ⟨hp.1, hp.2.1, he.2⟩⟩
  have hi : Function.Injective i := by
    intro n n' h
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
    _ = eiravelPowerExceptionalMass f x y k a P m := by
      unfold eiravelPowerExceptionalMass
      dsimp [T]
      rw [Finset.sum_sigma]

#print axioms eiravel_unrestricted_exception_subsum_le
end
end PaperB.M4B
