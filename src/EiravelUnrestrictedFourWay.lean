module

public import EiravelClassIBranches
public import EiravelActualFirstLargeBase
public import EiravelShortEligibleException
public import EiravelClassIIISmoothPhysical
public import EiravelNonsmoothClassIVWitness
public import EiravelSquareRootBridge

public section

namespace PaperB.M4B

/-- The literal four-way covering of the unrestricted weighted Shiu
progression, with full prime-power prefix atoms and no squarefree
hypothesis. Every branch lands in a source-exact paid consumer set.
Only the actual threshold L(x)≥2 and z≥4 are required for this
geometric covering theorem. -/
theorem eiravel_unrestricted_shiu_physical_four_way
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (x y z k a n : ℕ)
    (hz4 : 4 ≤ z)
    (hL2 : 2 ≤ shiuLogLogSmoothThreshold x)
    (hnI : n ∈ Finset.Ioc (x-y) x)
    (hna : n ≡ a [MOD k]) (hncop : n.Coprime k) :
    corvethClassicalClassIPays f x y z k a n ∨
    (∃ b ∈ corvethClassicalClassIIIFactors x z k, b ∣ n) ∨
    (∃ r ∈ Finset.Icc 2 (shiuClassIVR0 x z),
      let S := classical_primePower_prefix_split n z
        (by
          have hlow := (Finset.mem_Ioc.mp hnI).1
          omega) (by omega)
      S.small.prod ∈
        Shiu.classicalClassIVPrefixSet z k (classIVShellUpper z r) ∧
      S.large.prod ∈
        classIVInnerSet x y k a S.small.prod (classIVShellLower z r) ∧
      n = S.small.prod * S.large.prod ∧
      f n = f S.small.prod * f S.large.prod) ∨
    (∃ p ∈ (Nat.primesLE (Nat.sqrt z)).filter (fun p => ¬ p ∣ k),
      p ^ (Nat.log p (Nat.sqrt z) + 1) ∣ n) := by
  classical
  have hn0 : n ≠ 0 := by
    have hl := (Finset.mem_Ioc.mp hnI).1
    omega
  have hz : 1 ≤ z := by omega
  let S := classical_primePower_prefix_split n z hn0 hz
  have hcore := corveth_classical_primePower_source_core
    hf n z k hn0 hz hncop
  obtain ⟨hfac, hbz, _, hbck, _, _⟩ := hcore
  have hbpos : 1 ≤ S.small.prod := by
    have hprod : 0 < S.small.prod * S.large.prod := by
      rw [← hfac]
      exact Nat.pos_of_ne_zero hn0
    by_contra h
    have hh : S.small.prod = 0 := Nat.eq_zero_of_not_pos (by omega)
    simp [hh] at hprod
  by_cases hempty : S.large = []
  · left
    have hrough :=
      eiravel_actual_classI_rough_large_empty n z hn0 hz hempty
    exact corveth_classical_source_classI_of_rough
      hf hnI hna hncop hz hrough
  · obtain ⟨p, ts, hpMem, hfirst, hpower⟩ :=
      eiravel_actual_first_large_base n z hn0 hz hempty
    have hpd : p ∣ S.large.prod := by
      apply eiravel_first_large_base_dvd
        n z p hn0 hz hpMem (ts.map (fun q => q ^ n.factorization q))
      exact hpower
    by_cases hpBig : Nat.sqrt z < p
    · left
      have hrough := eiravel_actual_classI_rough_large_base
        n z p hn0 hz ts hfirst hpBig
      exact corveth_classical_source_classI_of_rough
        hf hnI hna hncop hz hrough
    · have hpSmall : p ≤ Nat.sqrt z := by omega
      by_cases hshort : S.small.prod ≤ Nat.sqrt z
      · right; right; right
        have hT : 0 < Nat.sqrt z := by
          have hh : 2 ≤ Nat.sqrt z :=
            Nat.le_sqrt'.mpr (by omega : 2 ^ 2 ≤ z)
          omega
        exact eiravel_short_crossing_eligible_exception
          n z k hn0 hz hT hncop hshort p hpMem hpSmall
          ⟨ts.map (fun q => q ^ n.factorization q), hpower⟩
      · have hlong : Nat.sqrt z < S.small.prod := by omega
        by_cases hsmooth :
          ∀ q : ℕ, q.Prime → q ∣ S.small.prod →
            q ≤ shiuLogLogSmoothThreshold x
        · right; left
          have hdvd : S.small.prod ∣ n := ⟨S.large.prod, hfac⟩
          have hdpos : 1 ≤ S.large.prod := by
            have hh : 0 < S.small.prod * S.large.prod := by
              rw [← hfac]
              exact Nat.pos_of_ne_zero hn0
            by_contra hh'
            have hzprod : S.large.prod = 0 :=
              Nat.eq_zero_of_not_pos (by omega)
            simp [hzprod] at hh
          have hb_le_n : S.small.prod ≤ n := by
            calc
              S.small.prod = S.small.prod * 1 := by simp
              _ ≤ S.small.prod * S.large.prod :=
                Nat.mul_le_mul_left _ hdpos
              _ = n := hfac.symm
          have hb_le_x : S.small.prod ≤ x :=
            hb_le_n.trans (Finset.mem_Ioc.mp hnI).2
          have hreal :
              (z : ℝ) ^ (1/2 : ℝ) ≤ (S.small.prod : ℝ) :=
            eiravel_nat_sqrt_lt_to_real_half z S.small.prod hlong
          exact ⟨S.small.prod,
            eiravel_classIII_factor_of_smooth_prefix x z k S.small.prod
              hbpos hb_le_x hbz hbck hreal hsmooth,
            hdvd⟩
        · right; right; left
          have hnonsmooth :
              ∃ q : ℕ, q.Prime ∧ q ∣ S.small.prod ∧
                shiuLogLogSmoothThreshold x < q := by
            push_neg at hsmooth
            exact hsmooth
          exact eiravel_nonsmooth_physical_classIV_witness
            hf n x y z k a p hn0 hz hnI hna hncop hL2
            hpMem hpSmall ⟨ts, hfirst⟩ hpd hlong hnonsmooth

#print axioms eiravel_unrestricted_shiu_physical_four_way

end PaperB.M4B
