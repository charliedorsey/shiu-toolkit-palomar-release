module

public import ShiuPublic.CorvethClassicalClassIII

public section

namespace PaperB.M4B

/-- Literal unrestricted Class III factor membership from a smooth
full-prime-power prefix. Prime powers are not discarded. -/
theorem eiravel_classIII_factor_of_smooth_prefix
    (x z k b : ℕ)
    (hb1 : 1 ≤ b) (hbx : b ≤ x) (hbz : b ≤ z)
    (hcop : b.Coprime k)
    (hbig : (z : ℝ) ^ (1 / 2 : ℝ) ≤ (b : ℝ))
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ b →
      p ≤ shiuLogLogSmoothThreshold x) :
    b ∈ corvethClassicalClassIIIFactors x z k := by
  classical
  unfold corvethClassicalClassIIIFactors Shiu.boundedSmoothSet
  simp only [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨⟨hb1, hbx⟩, ?_⟩, hbz, hcop, hbig⟩
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ b := Nat.dvd_of_mem_primeFactors hp
  exact Nat.mem_primesLE.mpr ⟨hsmooth p hpp hpd, hpp⟩

#print axioms eiravel_classIII_factor_of_smooth_prefix

end PaperB.M4B
