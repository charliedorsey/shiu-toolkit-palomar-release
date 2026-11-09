module

public import EiravelClassISubsum
public import EiravelClassIIISubsum
public import EiravelClassIVSubsum
public import EiravelExceptionSubsum

public section

namespace PaperB.M4B
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The unrestricted physical weighted Shiu source is bounded by the
FOUR exact source overcount consumers, with complete prime-power
multiplicities and original progression. This theorem makes no analytic
assertion about absorption of the published endpoint terms. -/
theorem eiravel_unrestricted_shiu_four_overcounts
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (x y z k a : ℕ)
    (hz4 : 4 ≤ z)
    (hL2 : 2 ≤ shiuLogLogSmoothThreshold x) :
    (∑ n ∈ eiravelShiuPhysicalSet x y k a, f n) ≤
      classIOvercount f x y z k a +
      corvethClassicalClassIIIWeightedOvercount f x y z k a +
      classicalClassIVOvercount f x y z k a +
      eiravelPowerExceptionalMass f x y k a
        ((Nat.primesLE (Nat.sqrt z)).filter (fun p => ¬ p ∣ k))
        (fun p => p ^ (Nat.log p (Nat.sqrt z) + 1)) := by
  let M1 := ∑ n ∈ (eiravelShiuPhysicalSet x y k a).filter
    (corvethClassicalClassIPays f x y z k a), f n
  let M3 := ∑ n ∈ (eiravelShiuPhysicalSet x y k a).filter
    (fun n => ∃ b ∈ corvethClassicalClassIIIFactors x z k, b ∣ n), f n
  let M4 := ∑ n ∈ (eiravelShiuPhysicalSet x y k a).filter
    (eiravelClassIVPays f x y z k a), f n
  let ME := ∑ n ∈ (eiravelShiuPhysicalSet x y k a).filter
    (eiravelExceptionPays z k), f n
  have hcover : (∑ n ∈ eiravelShiuPhysicalSet x y k a, f n) ≤
      M1 + M3 + M4 + ME := by
    simpa only [M1, M3, M4, ME] using
      eiravel_shiu_weighted_four_way_source hf x y z k a hz4 hL2
  have h1 : M1 ≤ classIOvercount f x y z k a := by
    simpa only [M1] using eiravel_unrestricted_classI_subsum_le hf x y z k a
  have h3 : M3 ≤ corvethClassicalClassIIIWeightedOvercount f x y z k a := by
    simpa only [M3] using eiravel_unrestricted_classIII_subsum_le hf x y z k a
  have h4 : M4 ≤ classicalClassIVOvercount f x y z k a := by
    simpa only [M4] using eiravel_unrestricted_classIV_subsum_le hf x y z k a
  have he : ME ≤ eiravelPowerExceptionalMass f x y k a
      ((Nat.primesLE (Nat.sqrt z)).filter (fun p => ¬ p ∣ k))
      (fun p => p ^ (Nat.log p (Nat.sqrt z) + 1)) := by
    simpa only [ME] using eiravel_unrestricted_exception_subsum_le hf x y z k a
  exact hcover.trans (add_le_add (add_le_add (add_le_add h1 h3) h4) he)

#print axioms eiravel_unrestricted_shiu_four_overcounts
end
end PaperB.M4B
