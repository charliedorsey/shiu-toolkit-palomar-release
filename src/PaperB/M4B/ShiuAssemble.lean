module

/-
Paper B M4B-CORE S12: fixed-quarter final absorption.
Authorized surface: exact M4B0 ledger row S12 only.

This row consumes the paid S6, S9, and exact S11 public interfaces. It does
not reopen their proofs. The remaining hypotheses are precisely scalar
readiness facts supplied by the fixed-quarter z = y^(1/40) specialization
when S13 packages Theorem 1.
-/

public import PaperB.M4B.ShiuClassI
public import PaperB.M4B.ShiuSmallException
public import PaperB.M4B.ShiuClassIV

public section

open scoped BigOperators
open Finset Nat Real
open ArithmeticFunction

noncomputable section

namespace PaperB
namespace M4B

/-- The three paid source contributions entering Shiu's final absorption.
Historical Class II is already deleted inside the S9 term. -/
def shiuCoreOvercount
    (f : ArithmeticFunction ℝ) (x y z k a : ℕ) : ℝ :=
  classIOvercount f x y z k a +
    smallExceptionWeightedOvercount f x y z k a +
    classIVOvercount f x y z k a

/-- Fixed S12 constant. It depends only on the fixed envelope. -/
@[expose] def shiuFixedQuarterAssembleConstant (A1 A2 : ℝ) : ℝ :=
  961 * (4 * (1 + A1) ^ 320) +
    10 * A2 +
    161 * shiuClassIVConstant A1

private theorem primeMass_nonneg
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    (X k : ℕ) :
    0 ≤ primeMass f X k := by
  classical
  unfold primeMass
  apply Finset.sum_nonneg
  intro p hp
  exact div_nonneg (hf.nonneg p) (Nat.cast_nonneg p)

private theorem primeMass_mono
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    {Z X k : ℕ} (hZX : Z ≤ X) :
    primeMass f Z k ≤ primeMass f X k := by
  classical
  let PZ : Finset ℕ :=
    (Nat.primesLE Z).filter (fun p => ¬ p ∣ k)
  let PX : Finset ℕ :=
    (Nat.primesLE X).filter (fun p => ¬ p ∣ k)
  have hsub : PZ ⊆ PX := by
    intro p hp
    have hpF := Finset.mem_filter.mp hp
    have hpP := Nat.mem_primesLE.mp hpF.1
    rw [Finset.mem_filter, Nat.mem_primesLE]
    exact ⟨⟨hpP.1.trans hZX, hpP.2⟩, hpF.2⟩
  have hnonneg : ∀ p ∈ PX, 0 ≤ f p / (p : ℝ) := by
    intro p hp
    exact div_nonneg (hf.nonneg p) (by positivity)
  have hsum :
      (∑ p ∈ PZ, f p / (p : ℝ)) ≤
        ∑ p ∈ PX, f p / (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p hp _ => hnonneg p hp)
  simpa [primeMass, PZ, PX] using hsum


private theorem classIOvercount_nonneg
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    (x y z k a : ℕ) :
    0 ≤ classIOvercount f x y z k a := by
  unfold classIOvercount
  apply Finset.sum_nonneg
  intro b hb
  exact mul_nonneg (hf.nonneg b)
    (Finset.sum_nonneg fun d hd => hf.nonneg d)

private theorem smallExceptionWeightedOvercount_nonneg
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    (x y z k a : ℕ) :
    0 ≤ smallExceptionWeightedOvercount f x y z k a := by
  unfold smallExceptionWeightedOvercount classIIIWeightedOvercount
  apply Finset.sum_nonneg
  intro b hb
  exact Finset.sum_nonneg fun n hn => hf.nonneg n

private theorem classIVOvercount_nonneg
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    (x y z k a : ℕ) :
    0 ≤ classIVOvercount f x y z k a := by
  unfold classIVOvercount
  apply Finset.sum_nonneg
  intro r hr
  unfold classIVShellOvercount
  apply Finset.sum_nonneg
  intro b hb
  exact mul_nonneg (hf.nonneg b)
    (Finset.sum_nonneg fun d hd => hf.nonneg d)

/-- A progression point paid by the Class-I overcount. -/
private def classIPays
    (f : ArithmeticFunction ℝ) (x y z k a n : ℕ) : Prop :=
  ∃ u : ℕ × ℕ,
    n = u.1 * u.2 ∧
    f n = f u.1 * f u.2 ∧
    u.1 ∈ (Finset.Icc 1 z).filter (fun b => b.Coprime k) ∧
    u.2 ∈ classIInnerSet x y z k a u.1

/-- A progression point paid by the specialized Class-III overcount. -/
private def classIIIPays
    (x y z k a n : ℕ) : Prop :=
  ∃ b : ℕ,
    b ∈ classIIIFactors x z k ∧
    n ∈ (Finset.Ioc (x - y) x).filter
      (fun m => m ≡ a [MOD k] ∧ b ∣ m)

/-- A progression point paid by one of the exact S11 Class-IV shells. -/
private def classIVPays
    (f : ArithmeticFunction ℝ) (x y z k a n : ℕ) : Prop :=
  ∃ r : ℕ, r ∈ Finset.Icc 2 (shiuClassIVR0 x z) ∧
    ∃ u : ℕ × ℕ,
      n = u.1 * u.2 ∧
      f n = f u.1 * f u.2 ∧
      u.1 ∈ classIVPrefixSet z k (classIVShellUpper z r) ∧
      u.2 ∈ classIVInnerSet x y k a u.1 (classIVShellLower z r)


private noncomputable def classIProgSet
    (f : ArithmeticFunction ℝ) (x y z k a : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (x - y) x).filter (classIPays f x y z k a)

private noncomputable def classIIIProgSet
    (x y z k a : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (x - y) x).filter (classIIIPays x y z k a)

private noncomputable def classIVProgSet
    (f : ArithmeticFunction ℝ) (x y z k a : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (x - y) x).filter (classIVPays f x y z k a)

private noncomputable def classIPaidSet
    (f : ArithmeticFunction ℝ) (x y z k a : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (x - y) x).filter (classIPays f x y z k a)

private noncomputable def classIIIPaidSet
    (x y z k a : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (x - y) x).filter (classIIIPays x y z k a)

private noncomputable def classIVPaidSet
    (f : ArithmeticFunction ℝ) (x y z k a : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (x - y) x).filter (classIVPays f x y z k a)

private theorem mem_classIPaidSet
    {f : ArithmeticFunction ℝ} {x y z k a n : ℕ} :
    n ∈ classIPaidSet f x y z k a ↔
      n ∈ Finset.Ioc (x - y) x ∧ classIPays f x y z k a n := by
  classical
  simp [classIPaidSet]

private theorem mem_classIIIPaidSet
    {x y z k a n : ℕ} :
    n ∈ classIIIPaidSet x y z k a ↔
      n ∈ Finset.Ioc (x - y) x ∧ classIIIPays x y z k a n := by
  classical
  simp [classIIIPaidSet]

private theorem mem_classIVPaidSet
    {f : ArithmeticFunction ℝ} {x y z k a n : ℕ} :
    n ∈ classIVPaidSet f x y z k a ↔
      n ∈ Finset.Ioc (x - y) x ∧ classIVPays f x y z k a n := by
  classical
  simp [classIVPaidSet]

/-- Every squarefree supported progression point enters at least one paid
source overcount.  The predicates may overlap; overlap is harmless because
all weights are nonnegative. -/
private theorem progression_point_covered
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    {x y z k a n : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hz1 : 1 ≤ z)
    (hxz : x < z ^ 160)
    (hL2 : 2 ≤ shiuLogLogSmoothThreshold x)
    (hnI : n ∈ Finset.Ioc (x - y) x)
    (hna : n ≡ a [MOD k])
    (hsq : Squarefree n) :
    classIPays f x y z k a n ∨
      classIIIPays x y z k a n ∨
      classIVPays f x y z k a n := by
  classical
  obtain ⟨s, -⟩ := shiu_prefix_factorization_split n z hsq hz1
  let b : ℕ := s.small.prod
  let d : ℕ := s.large.prod
  have hfac : n = b * d := by
    simpa [b, d] using s.factorization
  have hn0 : n ≠ 0 := hsq.ne_zero
  have hbdpos : 0 < b * d := by
    rw [← hfac]
    exact Nat.pos_of_ne_zero hn0
  have hbpos : 0 < b :=
    pos_of_mul_pos_left hbdpos (Nat.zero_le d)
  have hdpos : 0 < d :=
    pos_of_mul_pos_right hbdpos (Nat.zero_le b)
  have hnx : n ≤ x := (Finset.mem_Ioc.mp hnI).2
  have hbdiv : b ∣ n := ⟨d, hfac⟩
  have hddiv : d ∣ n := by
    refine ⟨b, ?_⟩
    rw [hfac, Nat.mul_comm]
  have hbsq : Squarefree b := hsq.squarefree_of_dvd hbdiv
  have hncop : n.Coprime k := coprime_of_modEq_reduced hak hna
  have hbk : b.Coprime k := hncop.coprime_dvd_left hbdiv
  have hb1 : 1 ≤ b := by omega
  have hbz : b ≤ z := by simpa [b] using s.small_prod_le
  have hblex : b ≤ x :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hbdiv).trans hnx
  have hsmallPrime : ∀ p ∈ s.small, p.Prime := by
    intro p hp
    apply Nat.prime_of_mem_primeFactorsList
    rw [← s.concat]
    simp [hp]
  have hlargePrime : ∀ p ∈ s.large, p.Prime := by
    intro p hp
    apply Nat.prime_of_mem_primeFactorsList
    rw [← s.concat]
    simp [hp]
  have hpermB : List.Perm s.small b.primeFactorsList := by
    dsimp [b]
    exact Nat.primeFactorsList_unique rfl hsmallPrime
  have hpermD : List.Perm s.large d.primeFactorsList := by
    dsimp [d]
    exact Nat.primeFactorsList_unique rfl hlargePrime
  have hsortAll : (s.small ++ s.large).SortedLT := by
    rw [s.concat]
    exact
      (Nat.primeFactorsList_sorted n).sortedLT_of_nodup
        hsq.nodup_primeFactorsList
  have hsortLarge : s.large.SortedLT := by
    have hsub : s.large.Sublist (s.small ++ s.large) :=
      List.sublist_append_right s.small s.large
    exact (List.Pairwise.sublist hsub hsortAll.pairwise).sortedLT
  have hfmul : f n = f b * f d := by
    rw [hfac]
    exact hf.multiplicative.map_mul_of_coprime s.coprime.gcd_eq_one
  have hbdlo : x - y < b * d := by
    simpa [← hfac] using (Finset.mem_Ioc.mp hnI).1
  have hbdhi : b * d ≤ x := by simpa [← hfac] using hnx
  have hdScaled :
      d ∈ Finset.Ioc (scaledLower x y b) (scaledUpper x b) :=
    scaledInterval_mem hbpos hbdlo hbdhi
  have hnaBD : b * d ≡ a [MOD k] := by simpa [← hfac] using hna
  have hbI :
      b ∈ (Finset.Icc 1 z).filter (fun b => b.Coprime k) := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hb1, hbz⟩, hbk⟩

  have payI
      (hrough : PaperB.M4A.shiuRough d (Nat.sqrt z)) :
      classIPays f x y z k a n := by
    refine ⟨(b, d), hfac, hfmul, hbI, ?_⟩
    unfold classIInnerSet
    rw [Finset.mem_filter]
    exact ⟨hdScaled, hnaBD, hrough⟩

  rcases s.crossing with hlargeNil | ⟨q, qs, hlarge, hcross⟩
  · left
    apply payI
    have hd1 : d = 1 := by
      dsimp [d]
      rw [hlargeNil]
      rfl
    exact Or.inl hd1
  · have hqmem : q ∈ s.large := by rw [hlarge]; simp
    have hq_le_large : ∀ t ∈ s.large, q ≤ t := by
      intro t ht
      rw [hlarge] at ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact le_rfl
      · have hs : (q :: qs).SortedLT := by simpa [hlarge] using hsortLarge
        exact (List.pairwise_cons.mp hs.pairwise).1 t ht |>.le
    by_cases hqSqrt : q ≤ Nat.sqrt z
    · have hbgt : Nat.sqrt z < b := by
        by_contra h
        have hble : b ≤ Nat.sqrt z := by omega
        have hbq : b * q ≤ (Nat.sqrt z) ^ 2 := by
          calc
            b * q ≤ Nat.sqrt z * q := Nat.mul_le_mul_right q hble
            _ ≤ Nat.sqrt z * Nat.sqrt z :=
              Nat.mul_le_mul_left (Nat.sqrt z) hqSqrt
            _ = (Nat.sqrt z) ^ 2 := by ring
        exact (not_lt_of_ge (hbq.trans (Nat.sqrt_le' z))) hcross
      let L : ℕ := shiuLogLogSmoothThreshold x
      by_cases hsmooth : ∀ p ∈ s.small, p ≤ L
      · right; left
        have hbprimeSubset : b.primeFactors ⊆ Nat.primesLE L := by
          intro p hp
          have hpListB :
              p ∈ b.primeFactorsList :=
            Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp
          have hpSmall : p ∈ s.small := hpermB.mem_iff.mpr hpListB
          have hple : p ≤ L := hsmooth p hpSmall
          have hpprime : p.Prime :=
            Nat.prime_of_mem_primeFactorsList hpListB
          simpa [Nat.mem_primesLE, hpprime, hple]
        have hzbbNat : z < b ^ 2 := by
          have hqb : q < b := hqSqrt.trans_lt hbgt
          calc
            z < b * q := by simpa [b] using hcross
            _ < b * b := (Nat.mul_lt_mul_left hbpos).2 hqb
            _ = b ^ 2 := by ring
        have hzbbR : (z : ℝ) < (b : ℝ) ^ 2 := by exact_mod_cast hzbbNat
        have hsqrtb : Real.sqrt (z : ℝ) < (b : ℝ) := by
          have hs := Real.sqrt_lt_sqrt
            (by positivity : (0 : ℝ) ≤ z) hzbbR
          simpa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ b)] using hs
        have hbLarge : (z : ℝ) ^ (1 / 2 : ℝ) ≤ (b : ℝ) := by
          rw [← Real.sqrt_eq_rpow]
          exact hsqrtb.le
        have hbIII : b ∈ classIIIFactors x z k := by
          unfold classIIIFactors squarefreeSmoothSet
          rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨⟨hb1, hblex⟩, hbsq, hbprimeSubset⟩,
            hbz, hbk, hbLarge⟩
        refine ⟨b, hbIII, ?_⟩
        rw [Finset.mem_filter]
        exact ⟨hnI, hna, hbdiv⟩
      · right; right
        push_neg at hsmooth
        obtain ⟨p, hpSmall, hLp⟩ := hsmooth
        have hpq : p < q := s.ordered p hpSmall q hqmem
        have hLq : L < q := hLp.trans hpq
        obtain ⟨sh, -⟩ :=
          shiu_classIV_shell_decomposition
            hsq hnx hxz s hlarge hqSqrt
            (by simpa [L] using hL2)
            (by simpa [L] using hLq)
        have hbIV : b ∈ classIVPrefixSet z k
            (classIVShellUpper z sh.r) := by
          unfold classIVPrefixSet
          rw [Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨?_, hbz⟩, hbsq, hbk, ?_⟩
          · omega
          · intro t ht
            have htListB :
                t ∈ b.primeFactorsList :=
              Nat.mem_primeFactors_iff_mem_primeFactorsList.mp ht
            have htSmall : t ∈ s.small :=
              hpermB.mem_iff.mpr htListB
            unfold classIVShellUpper
            have hrpos : 0 < sh.r :=
              lt_of_lt_of_le (by decide : 0 < 2) sh.r_two_le
            apply (Nat.le_nthRoot_iff (Nat.ne_of_gt hrpos)).2
            exact Nat.le_of_lt (sh.small_pow_lt t htSmall)
        have hqsh : q = sh.p := by
          have hh : q :: qs = sh.p :: sh.ps := by
            calc
              q :: qs = s.large := hlarge.symm
              _ = sh.p :: sh.ps := sh.large_eq
          injection hh
        have hdrough :
            PaperB.M4A.shiuRough d
              (classIVShellLower z sh.r) := by
          have hwq : classIVShellLower z sh.r < q := by
            rw [hqsh]
            unfold classIVShellLower
            exact (Nat.nthRoot_lt_iff (by omega : sh.r + 1 ≠ 0)).2
              sh.z_lt_p_pow_succ
          apply PaperB.M4A.allSmallPrimesAvoid_iff_shiuRough.mp
          intro t htprime htw htd
          have htListD :
              t ∈ d.primeFactorsList :=
            (Nat.mem_primeFactorsList_iff_dvd
              (Nat.ne_of_gt hdpos) htprime).2 htd
          have htLarge : t ∈ s.large := hpermD.mem_iff.mpr htListD
          have hqt := hq_le_large t htLarge
          omega
        have hdIV : d ∈ classIVInnerSet x y k a b
            (classIVShellLower z sh.r) := by
          unfold classIVInnerSet
          rw [Finset.mem_filter]
          exact ⟨hdScaled, hnaBD, hdrough⟩
        refine ⟨sh.r, ?_, (b, d), hfac, hfmul, hbIV, hdIV⟩
        rw [Finset.mem_Icc]
        exact ⟨sh.r_two_le, sh.r_le_r0⟩
    · left
      apply payI
      have hqgt : Nat.sqrt z < q := by omega
      apply PaperB.M4A.allSmallPrimesAvoid_iff_shiuRough.mp
      intro t htprime htSqrt htd
      have htListD :
          t ∈ d.primeFactorsList :=
        (Nat.mem_primeFactorsList_iff_dvd
          (Nat.ne_of_gt hdpos) htprime).2 htd
      have htLarge : t ∈ s.large := hpermD.mem_iff.mpr htListD
      have hqt := hq_le_large t htLarge
      omega

private theorem classI_subsum_le
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    (x y z k a : ℕ) :
    (∑ n ∈ classIPaidSet f x y z k a, f n) ≤
      classIOvercount f x y z k a := by
  classical
  let S := classIPaidSet f x y z k a
  let B := (Finset.Icc 1 z).filter (fun b => b.Coprime k)
  let T : Finset (Σ _b : ℕ, ℕ) :=
    B.sigma (fun b => classIInnerSet x y z k a b)
  have hpay : ∀ n : {n // n ∈ S}, classIPays f x y z k a n.1 := by
    intro n
    exact (mem_classIPaidSet.mp (by simpa [S] using n.2)).2
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
    simpa [B, w] using (Classical.choose_spec (hpay n))
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
    (∑ n ∈ classIPaidSet f x y z k a, f n)
        = ∑ n ∈ S.attach, f n.1 := by
          simpa [S] using
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
        (fun t ht _ => mul_nonneg (hf.nonneg t.1) (hf.nonneg t.2))
    _ = classIOvercount f x y z k a := by
      unfold classIOvercount
      dsimp [T, B]
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]

private theorem classIII_subsum_le
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    (x y z k a : ℕ) :
    (∑ n ∈ classIIIPaidSet x y z k a, f n) ≤
      smallExceptionWeightedOvercount f x y z k a := by
  classical
  let S := classIIIPaidSet x y z k a
  let T : Finset (Σ _b : ℕ, ℕ) :=
    (classIIIFactors x z k).sigma (fun b =>
      (Finset.Ioc (x - y) x).filter
        (fun n => n ≡ a [MOD k] ∧ b ∣ n))
  have hpay : ∀ n : {n // n ∈ S}, classIIIPays x y z k a n.1 := by
    intro n
    exact (mem_classIIIPaidSet.mp (by simpa [S] using n.2)).2
  let b : {n // n ∈ S} → ℕ := fun n =>
    Classical.choose (hpay n)
  let i : {n // n ∈ S} → (Σ _b : ℕ, ℕ) :=
    fun n => ⟨b n, n.1⟩
  have hspec : ∀ n : {n // n ∈ S},
      b n ∈ classIIIFactors x z k ∧
      n.1 ∈ (Finset.Ioc (x - y) x).filter
        (fun m => m ≡ a [MOD k] ∧ b n ∣ m) := by
    intro n
    simpa [b] using (Classical.choose_spec (hpay n))
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
    (∑ n ∈ classIIIPaidSet x y z k a, f n)
        = ∑ n ∈ S.attach, f n.1 := by
          simpa [S] using
            (Finset.sum_attach (s := S) (f := fun n => f n)).symm
    _ = ∑ n ∈ S.attach, f (i n).2 := by rfl
    _ = ∑ t ∈ S.attach.image i, f t.2 := by
          symm
          exact Finset.sum_image hi.injOn
    _ ≤ ∑ t ∈ T, f t.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun t ht _ => hf.nonneg t.2)
    _ = smallExceptionWeightedOvercount f x y z k a := by
      unfold smallExceptionWeightedOvercount classIIIWeightedOvercount
      dsimp [T]
      rw [Finset.sum_sigma]

private theorem classIV_subsum_le
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    (x y z k a : ℕ) :
    (∑ n ∈ classIVPaidSet f x y z k a, f n) ≤
      classIVOvercount f x y z k a := by
  classical
  let S := classIVPaidSet f x y z k a
  let R := Finset.Icc 2 (shiuClassIVR0 x z)
  let T : Finset (Σ r : ℕ, Σ _b : ℕ, ℕ) :=
    R.sigma (fun r =>
      (classIVPrefixSet z k (classIVShellUpper z r)).sigma (fun b =>
        classIVInnerSet x y k a b (classIVShellLower z r)))
  have hpay : ∀ n : {n // n ∈ S}, classIVPays f x y z k a n.1 := by
    intro n
    exact (mem_classIVPaidSet.mp (by simpa [S] using n.2)).2
  let rch : {n // n ∈ S} → ℕ := fun n =>
    Classical.choose (hpay n)
  let uch : {n // n ∈ S} → ℕ × ℕ := fun n =>
    Classical.choose (Classical.choose_spec (hpay n)).2
  let i : {n // n ∈ S} → (Σ r : ℕ, Σ _b : ℕ, ℕ) :=
    fun n => ⟨rch n, ⟨(uch n).1, (uch n).2⟩⟩
  have hspec : ∀ n : {n // n ∈ S},
      rch n ∈ R ∧
      n.1 = (uch n).1 * (uch n).2 ∧
      f n.1 = f (uch n).1 * f (uch n).2 ∧
      (uch n).1 ∈ classIVPrefixSet z k (classIVShellUpper z (rch n)) ∧
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
    (∑ n ∈ classIVPaidSet f x y z k a, f n)
        = ∑ n ∈ S.attach, f n.1 := by
          simpa [S] using
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
        (fun t ht _ => mul_nonneg (hf.nonneg t.2.1) (hf.nonneg t.2.2))
    _ = classIVOvercount f x y z k a := by
      unfold classIVOvercount classIVShellOvercount
      dsimp [T, R]
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]

/-- Finite source partition bridge.  The three source predicates are allowed
to overlap, so coverage plus nonnegativity is enough; the three injection
lemmas above prevent any source term from being duplicated inside an
individual paid overcount. -/
private theorem progressionSum_le_shiuCoreOvercount
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    {x y z k a : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hz1 : 1 ≤ z)
    (hxz : x < z ^ 160)
    (hL2 : 2 ≤ shiuLogLogSmoothThreshold x) :
    progressionSum f x y k a ≤ shiuCoreOvercount f x y z k a := by
  classical
  let U := Finset.Ioc (x - y) x
  have hpoint : ∀ n ∈ U,
      (if n ≡ a [MOD k] then f n else 0) ≤
        (if classIPays f x y z k a n then f n else 0) +
        (if classIIIPays x y z k a n then f n else 0) +
        (if classIVPays f x y z k a n then f n else 0) := by
    intro n hn
    by_cases hna : n ≡ a [MOD k]
    · simp only [hna, if_true]
      by_cases hsq : Squarefree n
      · have hc :=
          progression_point_covered hf ha0 haklt hak hyx hz1 hxz hL2 hn hna hsq
        rcases hc with hI | hIII | hIV
        · by_cases hIII' : classIIIPays x y z k a n
          · by_cases hIV' : classIVPays f x y z k a n
            · simp [hI, hIII', hIV', hf.nonneg n]
            · simp [hI, hIII', hIV', hf.nonneg n]
          · by_cases hIV' : classIVPays f x y z k a n
            · simp [hI, hIII', hIV', hf.nonneg n]
            · simp [hI, hIII', hIV', hf.nonneg n]
        · by_cases hI' : classIPays f x y z k a n
          · by_cases hIV' : classIVPays f x y z k a n
            · simp [hI', hIII, hIV', hf.nonneg n]
            · simp [hI', hIII, hIV', hf.nonneg n]
          · by_cases hIV' : classIVPays f x y z k a n
            · simp [hI', hIII, hIV', hf.nonneg n]
            · simp [hI', hIII, hIV', hf.nonneg n]
        · by_cases hI' : classIPays f x y z k a n
          · by_cases hIII' : classIIIPays x y z k a n
            · simp [hI', hIII', hIV, hf.nonneg n]
            · simp [hI', hIII', hIV, hf.nonneg n]
          · by_cases hIII' : classIIIPays x y z k a n
            · simp [hI', hIII', hIV, hf.nonneg n]
            · simp [hI', hIII', hIV, hf.nonneg n]
      · rw [hf.squarefree_support n hsq]
        by_cases hI' : classIPays f x y z k a n <;>
          by_cases hIII' : classIIIPays x y z k a n <;>
          by_cases hIV' : classIVPays f x y z k a n <;>
          simp [hI', hIII', hIV']
    · simp only [hna, if_false]
      have hI0 :
          0 ≤ if classIPays f x y z k a n then f n else 0 := by
        by_cases hI' : classIPays f x y z k a n
        · simp [hI', hf.nonneg n]
        · simp [hI']
      have hIII0 :
          0 ≤ if classIIIPays x y z k a n then f n else 0 := by
        by_cases hIII' : classIIIPays x y z k a n
        · simp [hIII', hf.nonneg n]
        · simp [hIII']
      have hIV0 :
          0 ≤ if classIVPays f x y z k a n then f n else 0 := by
        by_cases hIV' : classIVPays f x y z k a n
        · simp [hIV', hf.nonneg n]
        · simp [hIV']
      exact add_nonneg (add_nonneg hI0 hIII0) hIV0
  have hcover :
      progressionSum f x y k a ≤
        (∑ n ∈ classIPaidSet f x y z k a, f n) +
        (∑ n ∈ classIIIPaidSet x y z k a, f n) +
        (∑ n ∈ classIVPaidSet f x y z k a, f n) := by
    unfold progressionSum
    calc
      (∑ n ∈ U, if n ≡ a [MOD k] then f n else 0)
          ≤ ∑ n ∈ U,
            ((if classIPays f x y z k a n then f n else 0) +
             (if classIIIPays x y z k a n then f n else 0) +
             (if classIVPays f x y z k a n then f n else 0)) :=
        Finset.sum_le_sum hpoint
      _ =
        (∑ n ∈ classIPaidSet f x y z k a, f n) +
        (∑ n ∈ classIIIPaidSet x y z k a, f n) +
        (∑ n ∈ classIVPaidSet f x y z k a, f n) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          change
            (∑ n ∈ Finset.Ioc (x - y) x,
                if classIPays f x y z k a n then f n else 0) +
              (∑ n ∈ Finset.Ioc (x - y) x,
                if classIIIPays x y z k a n then f n else 0) +
              (∑ n ∈ Finset.Ioc (x - y) x,
                if classIVPays f x y z k a n then f n else 0) =
            (∑ n ∈ (Finset.Ioc (x - y) x).filter
                (classIPays f x y z k a), f n) +
              (∑ n ∈ (Finset.Ioc (x - y) x).filter
                (classIIIPays x y z k a), f n) +
              (∑ n ∈ (Finset.Ioc (x - y) x).filter
                (classIVPays f x y z k a), f n)
          rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  have hI := classI_subsum_le hf x y z k a
  have hIII := classIII_subsum_le hf x y z k a
  have hIV := classIV_subsum_le hf x y z k a
  unfold shiuCoreOvercount
  exact hcover.trans (_root_.add_le_add (_root_.add_le_add hI hIII) hIV)

set_option maxHeartbeats 1200000 in
/-- S12: source (5.3)+(5.6)+(5.8) final absorption.

The scalar readiness hypotheses are exactly the consequences later supplied
by the fixed-quarter choice z comparable to y^(1/40): the two logarithmic
comparisons, absorption of z^2 and the II/III error, and z <= x for enlarging
the nonnegative prime sum. No analytic theorem beyond the paid S6/S9/S11
interfaces is used here. -/
theorem shiu_fixed_quarter_assemble
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2) :
    ∃ X0 : ℕ, ∀ x y z k a : ℕ,
      X0 ≤ x →
      2 ≤ x →
      0 < a → a < k → a.Coprime k →
      y ≤ x → z ≤ y → k * z < y →
      2 ≤ Nat.sqrt z → x < z ^ 160 →
      4 ≤ shiuLogLogSmoothThreshold x →
      Real.exp (classIVRankinD A1) ≤
        (shiuLogLogSmoothThreshold x : ℝ) →
      (z : ℝ) ≤
        ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ) →
      Real.log (x : ℝ) ≤
        320 * Real.log (Nat.sqrt z : ℝ) →
      Real.log (x : ℝ) ≤
        160 * Real.log (z : ℝ) →
      (z : ℝ) ^ 2 ≤
        (y : ℝ) /
          ((k.totient : ℝ) * Real.log (x : ℝ)) →
      ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 8 : ℝ) ≤
        (y : ℝ) /
          ((k.totient : ℝ) * Real.log (x : ℝ)) →
      z ≤ x →
      progressionSum f x y k a ≤
        shiuFixedQuarterAssembleConstant A1 A2 *
          ((y : ℝ) /
            ((k.totient : ℝ) * Real.log (x : ℝ))) *
          Real.exp (primeMass f x k) := by
  obtain ⟨X0, hsmall⟩ := shiu_small_exception_weight_bound hf
  refine ⟨X0, ?_⟩
  intro x y z k a hx0 hx2 ha0 haklt hak hyx hzy hkz hzsqrt hxz
    hL4 hlarge hzabsorb hlogSqrt hlogZ hz2absorb hsmallabsorb hzx
  have hk : 0 < k := lt_trans ha0 haklt
  have hphi : 0 < (k.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 hk
  have hlogx : 0 < Real.log (x : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < x by omega)
  have hlogs : 0 < Real.log (Nat.sqrt z : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < Nat.sqrt z by omega)
  have hz2 : 2 ≤ z := by
    have hsle : (Nat.sqrt z) ^ 2 ≤ z := Nat.sqrt_le' z
    nlinarith
  have hlogz : 0 < Real.log (z : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < z by omega)
  let Q : ℝ :=
    (y : ℝ) /
      ((k.totient : ℝ) * Real.log (x : ℝ))
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hfracI :
      (y : ℝ) /
          ((k.totient : ℝ) * Real.log (Nat.sqrt z : ℝ)) ≤
        320 * Q := by
    have hdenS :
        0 < (k.totient : ℝ) *
          Real.log (Nat.sqrt z : ℝ) := mul_pos hphi hlogs
    have hdenX :
        0 < (k.totient : ℝ) *
          Real.log (x : ℝ) := mul_pos hphi hlogx
    dsimp [Q]
    rw [show
      320 * ((y : ℝ) /
        ((k.totient : ℝ) * Real.log (x : ℝ))) =
      (320 * (y : ℝ)) /
        ((k.totient : ℝ) * Real.log (x : ℝ)) by ring]
    apply (div_le_div_iff₀ hdenS hdenX).2
    have hm :=
      mul_le_mul_of_nonneg_left hlogSqrt
        (mul_nonneg (Nat.cast_nonneg y) hphi.le)
    ring_nf at hm ⊢
    exact hm
  have hfracIV :
      (y : ℝ) /
          ((k.totient : ℝ) * Real.log (z : ℝ)) ≤
        160 * Q := by
    have hdenZ :
        0 < (k.totient : ℝ) *
          Real.log (z : ℝ) := mul_pos hphi hlogz
    have hdenX :
        0 < (k.totient : ℝ) *
          Real.log (x : ℝ) := mul_pos hphi hlogx
    dsimp [Q]
    rw [show
      160 * ((y : ℝ) /
        ((k.totient : ℝ) * Real.log (x : ℝ))) =
      (160 * (y : ℝ)) /
        ((k.totient : ℝ) * Real.log (x : ℝ)) by ring]
    apply (div_le_div_iff₀ hdenZ hdenX).2
    have hm :=
      mul_le_mul_of_nonneg_left hlogZ
        (mul_nonneg (Nat.cast_nonneg y) hphi.le)
    ring_nf at hm ⊢
    exact hm
  have hmassZX := primeMass_mono hf (k := k) hzx
  have hexpZX :
      Real.exp (primeMass f z k) ≤
        Real.exp (primeMass f x k) :=
    Real.exp_le_exp.mpr hmassZX
  have hexp1 :
      (1 : ℝ) ≤ Real.exp (primeMass f x k) := by
    rw [Real.one_le_exp_iff]
    exact primeMass_nonneg hf x k
  have hRI :
      (3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
          (z : ℝ) ^ 2 ≤
        961 * Q := by
    calc
      (3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
          (z : ℝ) ^ 2
          =
        3 * ((y : ℝ) /
          ((k.totient : ℝ) * Real.log (Nat.sqrt z))) +
          (z : ℝ) ^ 2 := by ring
      _ ≤ 3 * (320 * Q) + Q := by
        exact _root_.add_le_add
          (mul_le_mul_of_nonneg_left hfracI (by norm_num))
          (by simpa [Q] using hz2absorb)
      _ = 961 * Q := by ring
  have hRIV :
      (y : ℝ) /
          ((k.totient : ℝ) * Real.log (z : ℝ)) +
          (z : ℝ) ^ 2 ≤
        161 * Q := by
    calc
      (y : ℝ) /
          ((k.totient : ℝ) * Real.log (z : ℝ)) +
          (z : ℝ) ^ 2
          ≤ 160 * Q + Q := by
        exact _root_.add_le_add hfracIV
          (by simpa [Q] using hz2absorb)
      _ = 161 * Q := by ring
  have hI :=
    shiu_classI_bound hf ha0 haklt hak hyx hzy hkz hzsqrt hxz
  have hCI0 : 0 ≤ 4 * (1 + A1) ^ 320 := by
    positivity
  have hI' :
      classIOvercount f x y z k a ≤
        (961 * (4 * (1 + A1) ^ 320)) *
          Q * Real.exp (primeMass f x k) := by
    calc
      classIOvercount f x y z k a
          ≤ 4 * (1 + A1) ^ 320 *
            (((3 * (y : ℝ)) /
              ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
              (z : ℝ) ^ 2) *
              Real.exp (primeMass f z k)) := hI
      _ ≤ 4 * (1 + A1) ^ 320 *
            ((961 * Q) * Real.exp (primeMass f z k)) := by
        gcongr
      _ ≤ 4 * (1 + A1) ^ 320 *
            ((961 * Q) * Real.exp (primeMass f x k)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexpZX
            (mul_nonneg (by norm_num) hQ0))
          hCI0
      _ =
        (961 * (4 * (1 + A1) ^ 320)) *
          Q * Real.exp (primeMass f x k) := by ring
  have hE :=
    hsmall x y z k a hx0 hyx hxz hk hzabsorb
  have hE' :
      smallExceptionWeightedOvercount f x y z k a ≤
        (10 * A2) * Q * Real.exp (primeMass f x k) := by
    calc
      smallExceptionWeightedOvercount f x y z k a
          ≤ (10 * A2) *
            (((y : ℝ) / (k : ℝ)) *
              (z : ℝ) ^ (-1 / 8 : ℝ)) := hE
      _ ≤ (10 * A2) * Q := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [Q] using hsmallabsorb)
          (mul_nonneg (by norm_num) hf.A2_nonneg)
      _ ≤ (10 * A2) * Q *
          Real.exp (primeMass f x k) := by
        have hfac : 0 ≤ (10 * A2) * Q :=
          mul_nonneg (mul_nonneg (by norm_num) hf.A2_nonneg) hQ0
        calc
          (10 * A2) * Q = (10 * A2) * Q * 1 := by ring
          _ ≤ (10 * A2) * Q * Real.exp (primeMass f x k) :=
            mul_le_mul_of_nonneg_left hexp1 hfac
  have hIV :=
    shiu_classIV_bound hf ha0 haklt hak hyx hzy hkz hz2 hxz
      hL4 hlarge
  have hCIV0 : 0 ≤ shiuClassIVConstant A1 := by
    unfold shiuClassIVConstant
    positivity
  have hIV' :
      classIVOvercount f x y z k a ≤
        (161 * shiuClassIVConstant A1) *
          Q * Real.exp (primeMass f x k) := by
    calc
      classIVOvercount f x y z k a
          ≤ shiuClassIVConstant A1 *
            ((((y : ℝ)) /
              ((k.totient : ℝ) * Real.log (z : ℝ)) +
              (z : ℝ) ^ 2) *
              Real.exp (primeMass f z k)) := hIV
      _ ≤ shiuClassIVConstant A1 *
            ((161 * Q) * Real.exp (primeMass f z k)) := by
        gcongr
      _ ≤ shiuClassIVConstant A1 *
            ((161 * Q) * Real.exp (primeMass f x k)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexpZX
            (mul_nonneg (by norm_num) hQ0))
          hCIV0
      _ =
        (161 * shiuClassIVConstant A1) *
          Q * Real.exp (primeMass f x k) := by ring
  have hz1 : 1 ≤ z := by omega
  have hL2 : 2 ≤ shiuLogLogSmoothThreshold x := by omega
  have hpartition :=
    progressionSum_le_shiuCoreOvercount
      hf ha0 haklt hak hyx hz1 hxz hL2
  calc
    progressionSum f x y k a
        ≤ shiuCoreOvercount f x y z k a := hpartition
    _ =
      classIOvercount f x y z k a +
        smallExceptionWeightedOvercount f x y z k a +
        classIVOvercount f x y z k a := rfl
    _ ≤
      (961 * (4 * (1 + A1) ^ 320)) *
          Q * Real.exp (primeMass f x k) +
        (10 * A2) * Q * Real.exp (primeMass f x k) +
        (161 * shiuClassIVConstant A1) *
          Q * Real.exp (primeMass f x k) :=
      _root_.add_le_add (_root_.add_le_add hI' hE') hIV'
    _ =
      shiuFixedQuarterAssembleConstant A1 A2 *
        Q * Real.exp (primeMass f x k) := by
      dsimp [shiuFixedQuarterAssembleConstant]
      ring
    _ =
      shiuFixedQuarterAssembleConstant A1 A2 *
        ((y : ℝ) /
          ((k.totient : ℝ) * Real.log (x : ℝ))) *
        Real.exp (primeMass f x k) := by rfl

end M4B
end PaperB

namespace PaperB.M4B

set_option maxHeartbeats 1800000 in
/-- Packaging-only uniform form of the paid fixed-quarter assembly.  The
threshold is independent of the enveloped arithmetic function; all analytic
content is the existing S6/S9/S11 proof. -/
theorem shiu_fixed_quarter_assemble_uniform
    (A1 A2 : ℝ) :
    ∃ X0 : ℕ, ∀ f : ArithmeticFunction ℝ,
      FixedQuarterEnvelope f A1 A2 →
      ∀ x y z k a : ℕ,
      X0 ≤ x →
      2 ≤ x →
      0 < a → a < k → a.Coprime k →
      y ≤ x → z ≤ y → k * z < y →
      2 ≤ Nat.sqrt z → x < z ^ 160 →
      4 ≤ shiuLogLogSmoothThreshold x →
      Real.exp (classIVRankinD A1) ≤
        (shiuLogLogSmoothThreshold x : ℝ) →
      (z : ℝ) ≤
        ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ) →
      Real.log (x : ℝ) ≤
        320 * Real.log (Nat.sqrt z : ℝ) →
      Real.log (x : ℝ) ≤
        160 * Real.log (z : ℝ) →
      (z : ℝ) ^ 2 ≤
        (y : ℝ) /
          ((k.totient : ℝ) * Real.log (x : ℝ)) →
      ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 8 : ℝ) ≤
        (y : ℝ) /
          ((k.totient : ℝ) * Real.log (x : ℝ)) →
      z ≤ x →
      progressionSum f x y k a ≤
        shiuFixedQuarterAssembleConstant A1 A2 *
          ((y : ℝ) /
            ((k.totient : ℝ) * Real.log (x : ℝ))) *
          Real.exp (primeMass f x k) := by
  obtain ⟨X0, hsmall⟩ := shiu_small_exception_weight_bound_uniform A1 A2
  refine ⟨X0, ?_⟩
  intro f hf x y z k a hx0 hx2 ha0 haklt hak hyx hzy hkz hzsqrt hxz
    hL4 hlarge hzabsorb hlogSqrt hlogZ hz2absorb hsmallabsorb hzx
  have hk : 0 < k := lt_trans ha0 haklt
  have hphi : 0 < (k.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 hk
  have hlogx : 0 < Real.log (x : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < x by omega)
  have hlogs : 0 < Real.log (Nat.sqrt z : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < Nat.sqrt z by omega)
  have hz2 : 2 ≤ z := by
    have hsle : (Nat.sqrt z) ^ 2 ≤ z := Nat.sqrt_le' z
    nlinarith
  have hlogz : 0 < Real.log (z : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < z by omega)
  let Q : ℝ :=
    (y : ℝ) /
      ((k.totient : ℝ) * Real.log (x : ℝ))
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hfracI :
      (y : ℝ) /
          ((k.totient : ℝ) * Real.log (Nat.sqrt z : ℝ)) ≤
        320 * Q := by
    have hdenS :
        0 < (k.totient : ℝ) *
          Real.log (Nat.sqrt z : ℝ) := mul_pos hphi hlogs
    have hdenX :
        0 < (k.totient : ℝ) *
          Real.log (x : ℝ) := mul_pos hphi hlogx
    dsimp [Q]
    rw [show
      320 * ((y : ℝ) /
        ((k.totient : ℝ) * Real.log (x : ℝ))) =
      (320 * (y : ℝ)) /
        ((k.totient : ℝ) * Real.log (x : ℝ)) by ring]
    apply (div_le_div_iff₀ hdenS hdenX).2
    have hm :=
      mul_le_mul_of_nonneg_left hlogSqrt
        (mul_nonneg (Nat.cast_nonneg y) hphi.le)
    ring_nf at hm ⊢
    exact hm
  have hfracIV :
      (y : ℝ) /
          ((k.totient : ℝ) * Real.log (z : ℝ)) ≤
        160 * Q := by
    have hdenZ :
        0 < (k.totient : ℝ) *
          Real.log (z : ℝ) := mul_pos hphi hlogz
    have hdenX :
        0 < (k.totient : ℝ) *
          Real.log (x : ℝ) := mul_pos hphi hlogx
    dsimp [Q]
    rw [show
      160 * ((y : ℝ) /
        ((k.totient : ℝ) * Real.log (x : ℝ))) =
      (160 * (y : ℝ)) /
        ((k.totient : ℝ) * Real.log (x : ℝ)) by ring]
    apply (div_le_div_iff₀ hdenZ hdenX).2
    have hm :=
      mul_le_mul_of_nonneg_left hlogZ
        (mul_nonneg (Nat.cast_nonneg y) hphi.le)
    ring_nf at hm ⊢
    exact hm
  have hmassZX := primeMass_mono hf (k := k) hzx
  have hexpZX :
      Real.exp (primeMass f z k) ≤
        Real.exp (primeMass f x k) :=
    Real.exp_le_exp.mpr hmassZX
  have hexp1 :
      (1 : ℝ) ≤ Real.exp (primeMass f x k) := by
    rw [Real.one_le_exp_iff]
    exact primeMass_nonneg hf x k
  have hRI :
      (3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
          (z : ℝ) ^ 2 ≤
        961 * Q := by
    calc
      (3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
          (z : ℝ) ^ 2
          =
        3 * ((y : ℝ) /
          ((k.totient : ℝ) * Real.log (Nat.sqrt z))) +
          (z : ℝ) ^ 2 := by ring
      _ ≤ 3 * (320 * Q) + Q := by
        exact _root_.add_le_add
          (mul_le_mul_of_nonneg_left hfracI (by norm_num))
          (by simpa [Q] using hz2absorb)
      _ = 961 * Q := by ring
  have hRIV :
      (y : ℝ) /
          ((k.totient : ℝ) * Real.log (z : ℝ)) +
          (z : ℝ) ^ 2 ≤
        161 * Q := by
    calc
      (y : ℝ) /
          ((k.totient : ℝ) * Real.log (z : ℝ)) +
          (z : ℝ) ^ 2
          ≤ 160 * Q + Q := by
        exact _root_.add_le_add hfracIV
          (by simpa [Q] using hz2absorb)
      _ = 161 * Q := by ring
  have hI :=
    shiu_classI_bound hf ha0 haklt hak hyx hzy hkz hzsqrt hxz
  have hCI0 : 0 ≤ 4 * (1 + A1) ^ 320 := by
    positivity
  have hI' :
      classIOvercount f x y z k a ≤
        (961 * (4 * (1 + A1) ^ 320)) *
          Q * Real.exp (primeMass f x k) := by
    calc
      classIOvercount f x y z k a
          ≤ 4 * (1 + A1) ^ 320 *
            (((3 * (y : ℝ)) /
              ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
              (z : ℝ) ^ 2) *
              Real.exp (primeMass f z k)) := hI
      _ ≤ 4 * (1 + A1) ^ 320 *
            ((961 * Q) * Real.exp (primeMass f z k)) := by
        gcongr
      _ ≤ 4 * (1 + A1) ^ 320 *
            ((961 * Q) * Real.exp (primeMass f x k)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexpZX
            (mul_nonneg (by norm_num) hQ0))
          hCI0
      _ =
        (961 * (4 * (1 + A1) ^ 320)) *
          Q * Real.exp (primeMass f x k) := by ring
  have hE :=
    hsmall f hf x y z k a hx0 hyx hxz hk hzabsorb
  have hE' :
      smallExceptionWeightedOvercount f x y z k a ≤
        (10 * A2) * Q * Real.exp (primeMass f x k) := by
    calc
      smallExceptionWeightedOvercount f x y z k a
          ≤ (10 * A2) *
            (((y : ℝ) / (k : ℝ)) *
              (z : ℝ) ^ (-1 / 8 : ℝ)) := hE
      _ ≤ (10 * A2) * Q := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [Q] using hsmallabsorb)
          (mul_nonneg (by norm_num) hf.A2_nonneg)
      _ ≤ (10 * A2) * Q *
          Real.exp (primeMass f x k) := by
        have hfac : 0 ≤ (10 * A2) * Q :=
          mul_nonneg (mul_nonneg (by norm_num) hf.A2_nonneg) hQ0
        calc
          (10 * A2) * Q = (10 * A2) * Q * 1 := by ring
          _ ≤ (10 * A2) * Q * Real.exp (primeMass f x k) :=
            mul_le_mul_of_nonneg_left hexp1 hfac
  have hIV :=
    shiu_classIV_bound hf ha0 haklt hak hyx hzy hkz hz2 hxz
      hL4 hlarge
  have hCIV0 : 0 ≤ shiuClassIVConstant A1 := by
    unfold shiuClassIVConstant
    positivity
  have hIV' :
      classIVOvercount f x y z k a ≤
        (161 * shiuClassIVConstant A1) *
          Q * Real.exp (primeMass f x k) := by
    calc
      classIVOvercount f x y z k a
          ≤ shiuClassIVConstant A1 *
            ((((y : ℝ)) /
              ((k.totient : ℝ) * Real.log (z : ℝ)) +
              (z : ℝ) ^ 2) *
              Real.exp (primeMass f z k)) := hIV
      _ ≤ shiuClassIVConstant A1 *
            ((161 * Q) * Real.exp (primeMass f z k)) := by
        gcongr
      _ ≤ shiuClassIVConstant A1 *
            ((161 * Q) * Real.exp (primeMass f x k)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexpZX
            (mul_nonneg (by norm_num) hQ0))
          hCIV0
      _ =
        (161 * shiuClassIVConstant A1) *
          Q * Real.exp (primeMass f x k) := by ring
  have hz1 : 1 ≤ z := by omega
  have hL2 : 2 ≤ shiuLogLogSmoothThreshold x := by omega
  have hpartition :=
    progressionSum_le_shiuCoreOvercount
      hf ha0 haklt hak hyx hz1 hxz hL2
  calc
    progressionSum f x y k a
        ≤ shiuCoreOvercount f x y z k a := hpartition
    _ =
      classIOvercount f x y z k a +
        smallExceptionWeightedOvercount f x y z k a +
        classIVOvercount f x y z k a := rfl
    _ ≤
      (961 * (4 * (1 + A1) ^ 320)) *
          Q * Real.exp (primeMass f x k) +
        (10 * A2) * Q * Real.exp (primeMass f x k) +
        (161 * shiuClassIVConstant A1) *
          Q * Real.exp (primeMass f x k) :=
      _root_.add_le_add (_root_.add_le_add hI' hE') hIV'
    _ =
      shiuFixedQuarterAssembleConstant A1 A2 *
        Q * Real.exp (primeMass f x k) := by
      dsimp [shiuFixedQuarterAssembleConstant]
      ring
    _ =
      shiuFixedQuarterAssembleConstant A1 A2 *
        ((y : ℝ) /
          ((k.totient : ℝ) * Real.log (x : ℝ))) *
        Real.exp (primeMass f x k) := by rfl

#print axioms shiu_fixed_quarter_assemble_uniform

end PaperB.M4B
