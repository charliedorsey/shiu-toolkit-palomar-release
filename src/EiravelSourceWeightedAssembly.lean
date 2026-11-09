module

public import EiravelUnrestrictedFourWay
public import EiravelWeightedFourWayFinite

public section

namespace PaperB.M4B
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Literal unrestricted physical Shiu progression: sharp interval,
original residue, and the source coprimality gate. -/
@[expose] def eiravelShiuPhysicalSet (x y k a : ℕ) : Finset ℕ :=
  (Finset.Ioc (x-y) x).filter (fun n => n ≡ a [MOD k] ∧ n.Coprime k)

/-- The unrestricted physical Class IV paying predicate. -/
@[expose] def eiravelClassIVPays (f : ArithmeticFunction ℝ)
    (x y z k a n : ℕ) : Prop :=
  ∃ r ∈ Finset.Icc 2 (shiuClassIVR0 x z),
    ∃ b d : ℕ,
      b ∈ Shiu.classicalClassIVPrefixSet z k (classIVShellUpper z r) ∧
      d ∈ classIVInnerSet x y k a b (classIVShellLower z r) ∧
      n = b * d ∧ f n = f b * f d

/-- Actual short-crossing source exception, with the exact eligible
primes and minimal complete-power modulus. -/
@[expose] def eiravelExceptionPays (z k n : ℕ) : Prop :=
  ∃ p ∈ (Nat.primesLE (Nat.sqrt z)).filter (fun p => ¬ p ∣ k),
    p ^ (Nat.log p (Nat.sqrt z) + 1) ∣ n

/-- Kernel-checked four-way source cover, now expressed with predicates
independent of the source's internal proof witnesses. -/
theorem eiravel_shiu_physical_paid_cover
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (x y z k a : ℕ)
    (hz4 : 4 ≤ z)
    (hL2 : 2 ≤ shiuLogLogSmoothThreshold x) :
    ∀ n ∈ eiravelShiuPhysicalSet x y k a,
      corvethClassicalClassIPays f x y z k a n ∨
      (∃ b ∈ corvethClassicalClassIIIFactors x z k, b ∣ n) ∨
      eiravelClassIVPays f x y z k a n ∨
      eiravelExceptionPays z k n := by
  classical
  intro n hn
  have hnF := Finset.mem_filter.mp hn
  have hbase : n ∈ Finset.Ioc (x-y) x := hnF.1
  have ha : n ≡ a [MOD k] := hnF.2.1
  have hk : n.Coprime k := hnF.2.2
  rcases eiravel_unrestricted_shiu_physical_four_way hf
    x y z k a n hz4 hL2 hbase ha hk with
    hI | hIII | hIV | hExc
  · exact Or.inl hI
  · exact Or.inr (Or.inl hIII)
  · right; right; left
    obtain ⟨r, hr, hpref, hinner, hfact, hw⟩ := hIV
    unfold eiravelClassIVPays
    let S := classical_primePower_prefix_split n z
      (by have hlo := (Finset.mem_Ioc.mp hbase).1; omega) (by omega)
    exact ⟨r, hr, S.small.prod, S.large.prod,
      hpref, hinner, hfact, hw⟩
  · exact Or.inr (Or.inr (Or.inr hExc))

/-- Finite weighted assembly at the ORIGINAL source level. No unproved
analytic estimates are inserted; the four restricted source masses
must be compared to the four existing overcount definitions next. -/
theorem eiravel_shiu_weighted_four_way_source
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (x y z k a : ℕ) (hz4 : 4 ≤ z)
    (hL2 : 2 ≤ shiuLogLogSmoothThreshold x) :
    (∑ n ∈ eiravelShiuPhysicalSet x y k a, f n) ≤
      (∑ n ∈ (eiravelShiuPhysicalSet x y k a).filter
        (corvethClassicalClassIPays f x y z k a), f n) +
      (∑ n ∈ (eiravelShiuPhysicalSet x y k a).filter
        (fun n => ∃ b ∈ corvethClassicalClassIIIFactors x z k, b ∣ n), f n) +
      (∑ n ∈ (eiravelShiuPhysicalSet x y k a).filter
        (eiravelClassIVPays f x y z k a), f n) +
      (∑ n ∈ (eiravelShiuPhysicalSet x y k a).filter
        (eiravelExceptionPays z k), f n) := by
  classical
  exact eiravel_four_way_finite_weighted_cover
    (eiravelShiuPhysicalSet x y k a) (fun n => f n)
    (corvethClassicalClassIPays f x y z k a)
    (fun n => ∃ b ∈ corvethClassicalClassIIIFactors x z k, b ∣ n)
    (eiravelClassIVPays f x y z k a)
    (eiravelExceptionPays z k)
    (by intro n hn; exact hf.nonnegative n)
    (eiravel_shiu_physical_paid_cover hf x y z k a hz4 hL2)

#print axioms eiravel_shiu_physical_paid_cover
#print axioms eiravel_shiu_weighted_four_way_source
end PaperB.M4B
