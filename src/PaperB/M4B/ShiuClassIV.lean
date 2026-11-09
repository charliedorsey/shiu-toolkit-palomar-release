module

/-
Paper B M4B-CORE S11 finite Class-IV assembly organs.
Authorized surface: exact M4B0 ledger row S11 only.

This file contains only finite bridges from the S10 shell package to the
paid S3 smooth-tail engine and paid C5 rough progression estimate.
-/

public import PaperB.M4B.ShiuClassIVShell
public import PaperB.M4B.ShiuSmoothTail
public import PaperB.M4B.ShiuScaledAP
public import PaperB.M4A.ShiuLemma2
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
public import Mathlib.Analysis.SpecificLimits.Basic

public section

open scoped BigOperators
open Finset Nat Real
open ArithmeticFunction

noncomputable section

namespace PaperB
namespace M4B

/-- Source Class-IV factor-count budget. -/
theorem classIV_rough_primeFactorsList_length_lt
    {d x z p r : ℕ}
    (hdpos : 0 < d)
    (hx : x < z ^ 160)
    (hdx : d ≤ x)
    (hr : 1 ≤ r)
    (hp : 0 < p)
    (hzpr : z < p ^ (r + 1))
    (hrough : PaperB.M4A.shiuRough d p) :
    d.primeFactorsList.length < 320 * r := by
  rcases hrough with rfl | hmin
  · simp
    omega
  have hd0 : d ≠ 0 := Nat.ne_of_gt hdpos
  have hprod : p ^ d.primeFactorsList.length ≤ d := by
    calc
      p ^ d.primeFactorsList.length ≤ d.primeFactorsList.prod :=
        List.pow_length_le_prod d.primeFactorsList p (fun q hq => by
          have hqprime : q.Prime := Nat.prime_of_mem_primeFactorsList hq
          have hqd : q ∣ d := Nat.dvd_of_mem_primeFactorsList hq
          have hminle : d.minFac ≤ q :=
            Nat.minFac_le_of_dvd hqprime.two_le hqd
          omega)
      _ = d := Nat.prod_primeFactorsList hd0
  by_contra hlen
  have hlen' : 320 * r ≤ d.primeFactorsList.length := by omega
  have hpmono :
      p ^ (320 * r) ≤ p ^ d.primeFactorsList.length :=
    Nat.pow_le_pow_right hp hlen'
  have hzpow :
      z ^ 160 < p ^ (320 * r) := by
    calc
      z ^ 160 < (p ^ (r + 1)) ^ 160 :=
        Nat.pow_lt_pow_left hzpr (by norm_num)
      _ = p ^ ((r + 1) * 160) := by rw [← pow_mul]
      _ ≤ p ^ (320 * r) := by
        apply Nat.pow_le_pow_right hp
        omega
  have hxd : x < d :=
    hx.trans (hzpow.trans_le (hpmono.trans hprod))
  exact (not_lt_of_ge hdx) hxd

/-- Fixed-envelope Class-IV pointwise weight budget. -/
theorem fixedQuarter_classIV_rough_value_le
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    {d x z p r : ℕ}
    (hdpos : 0 < d)
    (hx : x < z ^ 160)
    (hdx : d ≤ x)
    (hr : 1 ≤ r)
    (hp : 0 < p)
    (hzpr : z < p ^ (r + 1))
    (hrough : PaperB.M4A.shiuRough d p) :
    f d ≤ (1 + A1) ^ (320 * r) := by
  by_cases hs : Squarefree d
  · have hlen :=
      classIV_rough_primeFactorsList_length_lt
        hdpos hx hdx hr hp hzpr hrough
    have hcard : d.primeFactors.card ≤ 320 * r := by
      calc
        d.primeFactors.card
            ≤ d.primeFactorsList.length := by
          change d.primeFactorsList.toFinset.card ≤ d.primeFactorsList.length
          exact List.toFinset_card_le (l := d.primeFactorsList)
        _ ≤ 320 * r := Nat.le_of_lt hlen
    have hprod :
        (∏ q ∈ d.primeFactors, f q) ≤
          ∏ _q ∈ d.primeFactors, (1 + A1) := by
      refine Finset.prod_le_prod₀ (fun q hq => hf.nonneg q) ?_
      intro q hq
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hqle := hf.prime_le q hqprime
      linarith [hf.A1_nonneg]
    calc
      f d = ∏ q ∈ d.primeFactors, f q :=
        (hf.multiplicative.prod_primeFactors hs).symm
      _ ≤ ∏ _q ∈ d.primeFactors, (1 + A1) := hprod
      _ = (1 + A1) ^ d.primeFactors.card := by simp
      _ ≤ (1 + A1) ^ (320 * r) := by
        exact pow_le_pow_right₀ (by linarith [hf.A1_nonneg]) hcard
  · rw [hf.squarefree_support d hs]
    exact pow_nonneg (by linarith [hf.A1_nonneg]) _

/-- Class-IV admissible large prefix factors for a fixed shell ceiling p. -/
@[expose] def classIVPrefixSet (z k p : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc (Nat.sqrt z) z).filter
    (fun b =>
      Squarefree b ∧ b.Coprime k ∧
        ∀ q ∈ b.primeFactors, q ≤ p)

/-- The Class-IV prefix harmonic weight is a sub-sum of the paid S3 object. -/
theorem classIV_prefix_harmonic_le_smoothTail
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    (z k p : ℕ) :
    (∑ b ∈ classIVPrefixSet z k p, f b / (b : ℝ)) ≤
      squarefreeSmoothTailMass f (Nat.sqrt z) p k := by
  classical
  let B : Finset ℕ := classIVPrefixSet z k p
  let P : Finset ℕ :=
    (Nat.primesLE p).filter (fun q => ¬ q ∣ k)
  let w : Finset ℕ → ℝ :=
    fun t => ∏ q ∈ t, f q / (q : ℝ)
  have hweight :
      ∀ b ∈ B, f b / (b : ℝ) = w b.primeFactors := by
    intro b hb
    have hbF := Finset.mem_filter.mp hb
    have hs : Squarefree b := hbF.2.1
    unfold w
    rw [Finset.prod_div_distrib, hf.multiplicative.prod_primeFactors hs]
    have hprod := Nat.prod_primeFactors_of_squarefree hs
    rw [← Nat.cast_prod, hprod]
  have hinj :
      ∀ ⦃b₁⦄, b₁ ∈ B → ∀ ⦃b₂⦄, b₂ ∈ B →
        b₁.primeFactors = b₂.primeFactors → b₁ = b₂ := by
    intro b₁ hb₁ b₂ hb₂ heq
    have hs₁ : Squarefree b₁ := (Finset.mem_filter.mp hb₁).2.1
    have hs₂ : Squarefree b₂ := (Finset.mem_filter.mp hb₂).2.1
    calc
      b₁ = ∏ q ∈ b₁.primeFactors, q :=
        (Nat.prod_primeFactors_of_squarefree hs₁).symm
      _ = ∏ q ∈ b₂.primeFactors, q := by rw [heq]
      _ = b₂ := Nat.prod_primeFactors_of_squarefree hs₂
  have hsubset :
      B.image Nat.primeFactors ⊆
        P.powerset.filter (fun t => Nat.sqrt z ≤ t.prod id) := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨b, hbB, rfl⟩
    have hbF := Finset.mem_filter.mp hbB
    have hbI := Finset.mem_Icc.mp hbF.1
    have hs : Squarefree b := hbF.2.1
    have hcop : b.Coprime k := hbF.2.2.1
    have hprimeLe : ∀ q ∈ b.primeFactors, q ≤ p := hbF.2.2.2
    rw [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro q hq
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hqd : q ∣ b := Nat.dvd_of_mem_primeFactors hq
      have hqnot : ¬ q ∣ k := by
        intro hqk
        have hqone : q ∣ 1 := by
          rw [← hcop.gcd_eq_one]
          exact Nat.dvd_gcd hqd hqk
        exact hqprime.not_dvd_one hqone
      simp [P, Nat.mem_primesLE, hqprime, hprimeLe q hq, hqnot]
    · have hprod := Nat.prod_primeFactors_of_squarefree hs
      simpa [hprod] using hbI.1
  have hw_nonneg :
      ∀ t ∈ P.powerset, 0 ≤ w t := by
    intro t ht
    unfold w
    exact Finset.prod_nonneg fun q hq =>
      div_nonneg (hf.nonneg q) (by positivity)
  unfold squarefreeSmoothTailMass
  change
    (∑ b ∈ B, f b / (b : ℝ)) ≤
      ∑ t ∈ P.powerset with Nat.sqrt z ≤ t.prod id, w t
  calc
    (∑ b ∈ B, f b / (b : ℝ))
        = ∑ b ∈ B, w b.primeFactors := by
      apply Finset.sum_congr rfl
      intro b hb
      exact hweight b hb
    _ = ∑ t ∈ B.image Nat.primeFactors, w t := by
      symm
      exact Finset.sum_image hinj
    _ ≤ ∑ t ∈ P.powerset with Nat.sqrt z ≤ t.prod id, w t :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun t ht _ =>
          hw_nonneg t (Finset.mem_filter.mp ht).1)


/-- Fixed-b Class-IV shell inner set at a generic roughness cutoff w.
The shell-specific choice of w is deliberately kept outside this C5 adapter. -/
@[expose] def classIVInnerSet (x y k a b w : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (scaledLower x y b) (scaledUpper x b)).filter
    (fun d => b * d ≡ a [MOD k] ∧ PaperB.M4A.shiuRough d w)

/-- Paid-C5 shellwise count for a fixed extracted factor b.
This is the exact finite/progression adapter reused by S11. -/
theorem shiu_classIV_inner_count_bound
    {x y k a b w : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hbpos : 0 < b) (hbk : b.Coprime k)
    (hkb : k * b < y) (hw : 2 ≤ w) :
    ((classIVInnerSet x y k a b w).card : ℝ) ≤
      4 * (((scaledCoverLength x y b : ℕ) : ℝ) /
        ((k.totient : ℝ) * Real.log w) + (w : ℝ) ^ 2) := by
  classical
  obtain ⟨a', ha'0, ha'lt, ha'cop, hres⟩ :=
    scaledResidue_fixed ha0 haklt hak hbk
  have hcover :
      scaledCoverLength x y b ≤ scaledCoverUpper x b := by
    have hlow := scaledLower_le_upper x y b
    unfold scaledCoverLength scaledCoverUpper scaledLength
    omega
  have hklen :
      k < scaledCoverLength x y b :=
    modulus_lt_scaledCoverLength hbpos hyx hkb
  have hphi :=
    PaperB.M4A.shiuLemma2
      (scaledCoverUpper x b) (scaledCoverLength x y b)
      w k a'
      ha'0 ha'lt ha'cop hklen hcover hw
  let S : Finset ℕ := classIVInnerSet x y k a b w
  let T : Finset ℕ :=
    Finset.Ioc
      (scaledCoverUpper x b - scaledCoverLength x y b)
      (scaledCoverUpper x b)
  have hsubset : S ⊆ T := by
    intro d hd
    have hdF := Finset.mem_filter.mp hd
    have hdI := Finset.mem_Ioc.mp hdF.1
    rw [Finset.mem_Ioc, scaledCover_lower_eq]
    constructor
    · exact hdI.1
    · simpa [scaledCoverUpper] using
        hdI.2.trans (Nat.le_succ (scaledUpper x b))
  have hcount :
      ((S.card : ℕ) : ℝ) ≤
        PaperB.M4A.shiuPhi
          (scaledCoverUpper x b) (scaledCoverLength x y b)
          w k a' := by
    unfold PaperB.M4A.shiuPhi
    calc
      ((S.card : ℕ) : ℝ) = ∑ d ∈ S, (1 : ℝ) := by simp
      _ = ∑ d ∈ S,
          if d ≡ a' [MOD k] ∧ PaperB.M4A.shiuRough d w
          then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro d hd
            have hdF := Finset.mem_filter.mp hd
            have hdres : d ≡ a' [MOD k] := (hres d).mp hdF.2.1
            simp [hdres, hdF.2.2]
      _ ≤ ∑ d ∈ T,
          if d ≡ a' [MOD k] ∧ PaperB.M4A.shiuRough d w
          then (1 : ℝ) else 0 := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
            intro d hdT hdnot
            split <;> positivity
  exact hcount.trans hphi


/-- Naturalized source factor-count budget at the strict C5 cutoff w:
w-roughness means every prime factor is at least w+1, while the shell
lower inequality is recorded as z < (w+1)^(r+1). -/
theorem classIV_rough_primeFactorsList_length_lt_succ
    {d x z w r : ℕ}
    (hdpos : 0 < d)
    (hx : x < z ^ 160)
    (hdx : d ≤ x)
    (hr : 1 ≤ r)
    (hzwr : z < (w + 1) ^ (r + 1))
    (hrough : PaperB.M4A.shiuRough d w) :
    d.primeFactorsList.length < 320 * r := by
  rcases hrough with rfl | hmin
  · simp
    omega
  have hd0 : d ≠ 0 := Nat.ne_of_gt hdpos
  have hp : 0 < w + 1 := by omega
  have hprod : (w + 1) ^ d.primeFactorsList.length ≤ d := by
    calc
      (w + 1) ^ d.primeFactorsList.length ≤ d.primeFactorsList.prod :=
        List.pow_length_le_prod d.primeFactorsList (w + 1) (fun q hq => by
          have hqprime : q.Prime := Nat.prime_of_mem_primeFactorsList hq
          have hqd : q ∣ d := Nat.dvd_of_mem_primeFactorsList hq
          have hminle : d.minFac ≤ q :=
            Nat.minFac_le_of_dvd hqprime.two_le hqd
          omega)
      _ = d := Nat.prod_primeFactorsList hd0
  by_contra hlen
  have hlen' : 320 * r ≤ d.primeFactorsList.length := by omega
  have hpmono :
      (w + 1) ^ (320 * r) ≤ (w + 1) ^ d.primeFactorsList.length :=
    Nat.pow_le_pow_right hp hlen'
  have hzpow :
      z ^ 160 < (w + 1) ^ (320 * r) := by
    calc
      z ^ 160 < ((w + 1) ^ (r + 1)) ^ 160 :=
        Nat.pow_lt_pow_left hzwr (by norm_num)
      _ = (w + 1) ^ ((r + 1) * 160) := by rw [← pow_mul]
      _ ≤ (w + 1) ^ (320 * r) := by
        apply Nat.pow_le_pow_right hp
        omega
  have hxd : x < d :=
    hx.trans (hzpow.trans_le (hpmono.trans hprod))
  exact (not_lt_of_ge hdx) hxd

/-- Fixed-envelope weight budget at the naturalized strict shell cutoff. -/
theorem fixedQuarter_classIV_rough_value_le_succ
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    {d x z w r : ℕ}
    (hdpos : 0 < d)
    (hx : x < z ^ 160)
    (hdx : d ≤ x)
    (hr : 1 ≤ r)
    (hzwr : z < (w + 1) ^ (r + 1))
    (hrough : PaperB.M4A.shiuRough d w) :
    f d ≤ (1 + A1) ^ (320 * r) := by
  by_cases hs : Squarefree d
  · have hlen :=
      classIV_rough_primeFactorsList_length_lt_succ
        hdpos hx hdx hr hzwr hrough
    have hcard : d.primeFactors.card ≤ 320 * r := by
      calc
        d.primeFactors.card
            ≤ d.primeFactorsList.length := by
          change d.primeFactorsList.toFinset.card ≤ d.primeFactorsList.length
          exact List.toFinset_card_le (l := d.primeFactorsList)
        _ ≤ 320 * r := Nat.le_of_lt hlen
    have hprod :
        (∏ q ∈ d.primeFactors, f q) ≤
          ∏ _q ∈ d.primeFactors, (1 + A1) := by
      refine Finset.prod_le_prod₀ (fun q hq => hf.nonneg q) ?_
      intro q hq
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hqle := hf.prime_le q hqprime
      linarith [hf.A1_nonneg]
    calc
      f d = ∏ q ∈ d.primeFactors, f q :=
        (hf.multiplicative.prod_primeFactors hs).symm
      _ ≤ ∏ _q ∈ d.primeFactors, (1 + A1) := hprod
      _ = (1 + A1) ^ d.primeFactors.card := by simp
      _ ≤ (1 + A1) ^ (320 * r) := by
        exact pow_le_pow_right₀ (by linarith [hf.A1_nonneg]) hcard
  · rw [hf.squarefree_support d hs]
    exact pow_nonneg (by linarith [hf.A1_nonneg]) _

/-- S11 fixed-b weighted shell estimate: C5 supplies the rough progression
count, while the shell factor-count budget supplies the pointwise f-weight. -/
theorem shiu_classIV_inner_weight_bound
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    {x y z k a b w r : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hbpos : 0 < b) (hbk : b.Coprime k)
    (hkb : k * b < y) (hw : 2 ≤ w)
    (hx : x < z ^ 160) (hr : 1 ≤ r)
    (hzwr : z < (w + 1) ^ (r + 1)) :
    (∑ d ∈ classIVInnerSet x y k a b w, f d) ≤
      (1 + A1) ^ (320 * r) *
        (4 * (((scaledCoverLength x y b : ℕ) : ℝ) /
          ((k.totient : ℝ) * Real.log w) + (w : ℝ) ^ 2)) := by
  classical
  let S : Finset ℕ := classIVInnerSet x y k a b w
  have hcount :=
    shiu_classIV_inner_count_bound
      ha0 haklt hak hyx hbpos hbk hkb hw
  have hC : 0 ≤ (1 + A1) ^ (320 * r) :=
    pow_nonneg (by linarith [hf.A1_nonneg]) _
  have hpoint :
      ∀ d ∈ S, f d ≤ (1 + A1) ^ (320 * r) := by
    intro d hd
    have hdF := Finset.mem_filter.mp hd
    have hdI := Finset.mem_Ioc.mp hdF.1
    have hdpos : 0 < d := by omega
    have hdupper : d ≤ x / b := by
      simpa [scaledUpper] using hdI.2
    have hdle : d ≤ x :=
      hdupper.trans (Nat.div_le_self x b)
    exact
      fixedQuarter_classIV_rough_value_le_succ
        hf hdpos hx hdle hr hzwr hdF.2.2
  change (∑ d ∈ S, f d) ≤ _
  calc
    (∑ d ∈ S, f d)
        ≤ ∑ _d ∈ S, (1 + A1) ^ (320 * r) :=
      Finset.sum_le_sum fun d hd => hpoint d hd
    _ = (1 + A1) ^ (320 * r) * (S.card : ℝ) := by
      simp [mul_comm]
    _ ≤ (1 + A1) ^ (320 * r) *
        (4 * (((scaledCoverLength x y b : ℕ) : ℝ) /
          ((k.totient : ℝ) * Real.log w) + (w : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hcount hC


/-- Scalar factorization for the S11 outer b-sum.  The one-unit scaled
interval over-cover costs a factor 3, while w^2*b is absorbed by z^2. -/
theorem classIV_scaled_weight_bound
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    {x y z k b w : ℕ}
    (hyx : y ≤ x) (hb1 : 1 ≤ b) (hbz : b ≤ z) (hzy : z ≤ y)
    (hk : 0 < k) (hw : 2 ≤ w) (hwsq : w ^ 2 ≤ z) :
    f b * (((scaledCoverLength x y b : ℕ) : ℝ) /
        ((k.totient : ℝ) * Real.log w) + (w : ℝ) ^ 2) ≤
      (f b / (b : ℝ)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) := by
  have hbpos : 0 < b := by omega
  have hfb : 0 ≤ f b := hf.nonneg b
  have hq : 0 ≤ f b / (b : ℝ) := div_nonneg hfb (by positivity)
  have hkpos : 0 < k.totient := Nat.totient_pos.2 hk
  have hlog : 0 < Real.log (w : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < w by omega)
  have hden :
      0 < (k.totient : ℝ) * Real.log w := by
    positivity
  have hLnat := scaledCoverLength_le (x := x) (y := y) (b := b) hyx
  have hLreal :
      ((scaledCoverLength x y b : ℕ) : ℝ) ≤
        (y : ℝ) / (b : ℝ) + 2 := by
    calc
      ((scaledCoverLength x y b : ℕ) : ℝ)
          ≤ ((y / b + 2 : ℕ) : ℝ) := by exact_mod_cast hLnat
      _ = ((y / b : ℕ) : ℝ) + 2 := by norm_num
      _ ≤ (y : ℝ) / (b : ℝ) + 2 := by
        gcongr
        exact Nat.cast_div_le
  have hbY : (b : ℝ) ≤ y := by
    exact_mod_cast hbz.trans hzy
  have hbne : (b : ℝ) ≠ 0 := by positivity
  have hfb_eq :
      f b = (b : ℝ) * (f b / (b : ℝ)) := by
    calc
      f b = (f b / (b : ℝ)) * (b : ℝ) :=
        (div_mul_cancel₀ _ hbne).symm
      _ = (b : ℝ) * (f b / (b : ℝ)) := by ring
  have hfL :
      f b * ((scaledCoverLength x y b : ℕ) : ℝ) ≤
        3 * (y : ℝ) * (f b / (b : ℝ)) := by
    calc
      f b * ((scaledCoverLength x y b : ℕ) : ℝ)
          ≤ f b * ((y : ℝ) / (b : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hLreal hfb
      _ = (y : ℝ) * (f b / (b : ℝ)) +
            2 * ((b : ℝ) * (f b / (b : ℝ))) := by
          rw [hfb_eq]
          field_simp
      _ ≤ (y : ℝ) * (f b / (b : ℝ)) +
            2 * ((y : ℝ) * (f b / (b : ℝ))) := by
          gcongr
      _ = 3 * (y : ℝ) * (f b / (b : ℝ)) := by ring
  have hwbNat :
      w ^ 2 * b ≤ z ^ 2 := by
    calc
      w ^ 2 * b ≤ z * b := Nat.mul_le_mul_right b hwsq
      _ ≤ z * z := Nat.mul_le_mul_left z hbz
      _ = z ^ 2 := by ring
  have hwb :
      (w : ℝ) ^ 2 * (b : ℝ) ≤ (z : ℝ) ^ 2 := by
    exact_mod_cast hwbNat
  have hfR :
      f b * (w : ℝ) ^ 2 ≤
        (z : ℝ) ^ 2 * (f b / (b : ℝ)) := by
    calc
      f b * (w : ℝ) ^ 2
          = ((b : ℝ) * (f b / (b : ℝ))) * (w : ℝ) ^ 2 :=
        congrArg (fun t : ℝ => t * (w : ℝ) ^ 2) hfb_eq
      _ = ((w : ℝ) ^ 2 * (b : ℝ)) *
              (f b / (b : ℝ)) := by ring
      _ ≤ (z : ℝ) ^ 2 * (f b / (b : ℝ)) :=
        mul_le_mul_of_nonneg_right hwb hq
  calc
    f b * (((scaledCoverLength x y b : ℕ) : ℝ) /
          ((k.totient : ℝ) * Real.log w) + (w : ℝ) ^ 2)
        =
      (f b * ((scaledCoverLength x y b : ℕ) : ℝ)) /
          ((k.totient : ℝ) * Real.log w) +
        f b * (w : ℝ) ^ 2 := by ring
    _ ≤
      (3 * (y : ℝ) * (f b / (b : ℝ))) /
          ((k.totient : ℝ) * Real.log w) +
        (z : ℝ) ^ 2 * (f b / (b : ℝ)) := by
      gcongr
    _ =
      (f b / (b : ℝ)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) := by ring

/-- Raw shell overcount before the S3 Rankin suppression is inserted. -/
@[expose] def classIVShellOvercount
    (f : ArithmeticFunction ℝ)
    (x y z k a p w : ℕ) : ℝ := by
  classical
  exact ∑ b ∈ classIVPrefixSet z k p,
    f b * ∑ d ∈ classIVInnerSet x y k a b w, f d

/-- S11 raw shell assembly: paid C5 is applied at fixed b, then the b-harmonic
sum is injected into the paid S3 squarefree smooth-tail object. -/
theorem shiu_classIV_shell_bound_raw
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    {x y z k a p w r : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hzy : z ≤ y) (hk : 0 < k)
    (hzsqrt : 1 ≤ Nat.sqrt z)
    (hw : 2 ≤ w) (hwsq : w ^ 2 ≤ z)
    (hx : x < z ^ 160) (hr : 1 ≤ r)
    (hzwr : z < (w + 1) ^ (r + 1))
    (hkb : ∀ b ∈ classIVPrefixSet z k p, k * b < y) :
    classIVShellOvercount f x y z k a p w ≤
      (4 * (1 + A1) ^ (320 * r)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) *
        squarefreeSmoothTailMass f (Nat.sqrt z) p k := by
  classical
  let B : Finset ℕ := classIVPrefixSet z k p
  let C : ℝ := (1 + A1) ^ (320 * r)
  let G : ℝ :=
    (3 * (y : ℝ)) /
      ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact pow_nonneg (by linarith [hf.A1_nonneg]) _
  have hlog : 0 < Real.log (w : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < w by omega)
  have hkpos : 0 < k.totient := Nat.totient_pos.2 hk
  have hG0 : 0 ≤ G := by
    dsimp [G]
    positivity
  have hpoint :
      ∀ b ∈ B,
        f b * (∑ d ∈ classIVInnerSet x y k a b w, f d) ≤
          (4 * C * G) * (f b / (b : ℝ)) := by
    intro b hb
    have hbF := Finset.mem_filter.mp hb
    have hbI := Finset.mem_Icc.mp hbF.1
    have hb1 : 1 ≤ b := hzsqrt.trans hbI.1
    have hbpos : 0 < b := by omega
    have hbz : b ≤ z := hbI.2
    have hbk : b.Coprime k := hbF.2.2.1
    have hinner :=
      shiu_classIV_inner_weight_bound
        hf ha0 haklt hak hyx hbpos hbk (hkb b hb)
          hw hx hr hzwr
    have hscaled :=
      classIV_scaled_weight_bound
        hf hyx hb1 hbz hzy hk hw hwsq
    have hfb : 0 ≤ f b := hf.nonneg b
    have h4C : 0 ≤ 4 * C := by positivity
    calc
      f b * (∑ d ∈ classIVInnerSet x y k a b w, f d)
          ≤ f b *
              (C * (4 * (((scaledCoverLength x y b : ℕ) : ℝ) /
                ((k.totient : ℝ) * Real.log w) + (w : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left hinner hfb
      _ = (4 * C) *
          (f b * (((scaledCoverLength x y b : ℕ) : ℝ) /
            ((k.totient : ℝ) * Real.log w) + (w : ℝ) ^ 2)) := by
        ring
      _ ≤ (4 * C) *
          ((f b / (b : ℝ)) * G) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [G] using hscaled) h4C
      _ = (4 * C * G) * (f b / (b : ℝ)) := by ring
  have hpref :=
    classIV_prefix_harmonic_le_smoothTail hf z k p
  have hfac : 0 ≤ 4 * C * G := by positivity
  unfold classIVShellOvercount
  change
    (∑ b ∈ B,
      f b * ∑ d ∈ classIVInnerSet x y k a b w, f d) ≤ _
  calc
    (∑ b ∈ B,
      f b * ∑ d ∈ classIVInnerSet x y k a b w, f d)
        ≤ ∑ b ∈ B, (4 * C * G) * (f b / (b : ℝ)) :=
      Finset.sum_le_sum fun b hb => hpoint b hb
    _ = (4 * C * G) * ∑ b ∈ B, f b / (b : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ (4 * C * G) *
        squarefreeSmoothTailMass f (Nat.sqrt z) p k :=
      mul_le_mul_of_nonneg_left
        (by simpa [B] using hpref) hfac
    _ =
      (4 * (1 + A1) ^ (320 * r)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) *
        squarefreeSmoothTailMass f (Nat.sqrt z) p k := by
      rfl


/-- Prime mass is monotone in its prime ceiling for the nonnegative CORE
envelope. -/
private theorem primeMass_mono
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
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
    exact div_nonneg (hf.nonneg q) (by positivity)
  unfold primeMass
  change (∑ q ∈ S, f q / (q : ℝ)) ≤ ∑ q ∈ T, f q / (q : ℝ)
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun q hq _ => hnonneg q hq)

/-- S11 shell estimate after inserting the paid S3 Rankin suppression.
The scalar Rankin budget is deliberately explicit here; the shell-parameter
organ discharges it separately. -/
theorem shiu_classIV_shell_bound_of_rankin_budget
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    {x y z k a p w r : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hzy : z ≤ y) (hk : 0 < k)
    (hzsqrt : 1 ≤ Nat.sqrt z)
    (hw : 2 ≤ w) (hwsq : w ^ 2 ≤ z)
    (hx : x < z ^ 160) (hr : 1 ≤ r)
    (hzwr : z < (w + 1) ^ (r + 1))
    (hpz : p ≤ z)
    (hkb : ∀ b ∈ classIVPrefixSet z k p, k * b < y)
    {ε R : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hbudget :
      primeRankinCorrection f p k ε -
          ε * Real.log ((Nat.sqrt z : ℕ) : ℝ) ≤ -R) :
    classIVShellOvercount f x y z k a p w ≤
      (4 * (1 + A1) ^ (320 * r)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) *
        Real.exp (primeMass f z k - R) := by
  have hraw :=
    shiu_classIV_shell_bound_raw
      hf ha0 haklt hak hyx hzy hk hzsqrt hw hwsq hx hr hzwr hkb
  have hs3 :=
    squarefree_smoothTail_rankin_of_budget
      hf (Nat.sqrt z) p k hzsqrt hε0 hε1 hbudget
  have hpm := primeMass_mono hf (k := k) hpz
  have hexp :
      Real.exp (primeMass f p k - R) ≤
        Real.exp (primeMass f z k - R) :=
    Real.exp_le_exp.mpr (sub_le_sub_right hpm R)
  have hfac0 :
      0 ≤
        (4 * (1 + A1) ^ (320 * r)) *
          ((3 * (y : ℝ)) /
            ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) := by
    have hlog : 0 < Real.log (w : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < w by omega)
    have hkpos : 0 < k.totient := Nat.totient_pos.2 hk
    have hpow0 : 0 ≤ (1 + A1) ^ (320 * r) :=
      pow_nonneg (by linarith [hf.A1_nonneg]) _
    have hden0 :
        0 ≤ (k.totient : ℝ) * Real.log w := by
      positivity
    have hmain0 :
        0 ≤ (3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) := by
      exact div_nonneg (by positivity) hden0
    exact mul_nonneg
      (mul_nonneg (by norm_num) hpow0)
      (add_nonneg hmain0 (sq_nonneg (z : ℝ)))
  calc
    classIVShellOvercount f x y z k a p w
        ≤
      (4 * (1 + A1) ^ (320 * r)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) *
        squarefreeSmoothTailMass f (Nat.sqrt z) p k := hraw
    _ ≤
      (4 * (1 + A1) ^ (320 * r)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) *
        Real.exp (primeMass f p k - R) :=
      mul_le_mul_of_nonneg_left hs3 hfac0
    _ ≤
      (4 * (1 + A1) ^ (320 * r)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) *
        Real.exp (primeMass f z k - R) :=
      mul_le_mul_of_nonneg_left hexp hfac0


/-- Finite geometric estimate for the live dyadic S3 Rankin correction.
This is the pre-authorized S11 scalar micro-lemma; it introduces no new
analytic input. -/
private theorem shell_geometric_rankin_bound
    {P : ℕ} {ε : ℝ}
    (hP : 2 ≤ P) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ε * (∑ j ∈ Finset.range (Nat.log 2 P + 1),
      (((2 ^ j : ℕ) : ℝ)) ^ ε) ≤
      (2 / Real.log 2) * (P : ℝ) ^ ε := by
  let q : ℝ := (2 : ℝ) ^ ε
  let M : ℕ := Nat.log 2 P
  have hq1 : 1 < q := by
    dsimp [q]
    exact Real.one_lt_rpow (by norm_num) hε0
  have hq0 : 0 ≤ q := hq1.le.trans' (by norm_num)
  have hq2 : q ≤ 2 := by
    dsimp [q]
    calc
      (2 : ℝ) ^ ε ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1
      _ = 2 := by simp
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterm : ∀ j : ℕ,
      (((2 ^ j : ℕ) : ℝ)) ^ ε = q ^ j := by
    intro j
    dsimp [q]
    rw [Nat.cast_pow, Nat.cast_ofNat]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [mul_comm]
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.rpow_natCast]
  have hden : ε * Real.log 2 ≤ q - 1 := by
    have h := Real.add_one_le_exp (ε * Real.log 2)
    have hqexp : q = Real.exp (ε * Real.log 2) := by
      dsimp [q]
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    rw [← hqexp] at h
    linarith
  have hden0 : 0 < q - 1 := sub_pos.mpr hq1
  have hfrac : ε / (q - 1) ≤ 1 / Real.log 2 := by
    apply (div_le_iff₀ hden0).2
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hlog2]
    simpa [mul_comm] using hden
  have hMpowNat : 2 ^ M ≤ P := by
    dsimp [M]
    exact Nat.pow_log_le_self 2 (by omega)
  have hMpowReal : (((2 ^ M : ℕ) : ℝ)) ≤ (P : ℝ) := by
    exact_mod_cast hMpowNat
  have hqM : q ^ M ≤ (P : ℝ) ^ ε := by
    rw [← hterm M]
    exact Real.rpow_le_rpow (by positivity) hMpowReal hε0.le
  have hgeom :
      (∑ j ∈ Finset.range (M + 1), q ^ j) =
        (q ^ (M + 1) - 1) / (q - 1) :=
    geom_sum_eq hq1.ne' (M + 1)
  have hnum0 : 0 ≤ q ^ (M + 1) - 1 := by
    exact sub_nonneg.mpr (one_le_pow₀ hq1.le)
  have hnumle : q ^ (M + 1) - 1 ≤ q ^ (M + 1) := by linarith
  have hpowSucc : q ^ (M + 1) ≤ 2 * q ^ M := by
    rw [pow_succ]
    nlinarith [pow_nonneg hq0 M]
  change
    ε * (∑ j ∈ Finset.range (M + 1),
      (((2 ^ j : ℕ) : ℝ)) ^ ε) ≤ _
  calc
    ε * (∑ j ∈ Finset.range (M + 1),
        (((2 ^ j : ℕ) : ℝ)) ^ ε)
        = ε * (∑ j ∈ Finset.range (M + 1), q ^ j) := by
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          exact hterm j
    _ = ε * ((q ^ (M + 1) - 1) / (q - 1)) := by rw [hgeom]
    _ = (ε / (q - 1)) * (q ^ (M + 1) - 1) := by ring
    _ ≤ (1 / Real.log 2) * (q ^ (M + 1) - 1) :=
      mul_le_mul_of_nonneg_right hfrac hnum0
    _ ≤ (1 / Real.log 2) * q ^ (M + 1) :=
      mul_le_mul_of_nonneg_left hnumle (by positivity)
    _ ≤ (1 / Real.log 2) * (2 * q ^ M) :=
      mul_le_mul_of_nonneg_left hpowSucc (by positivity)
    _ = (2 / Real.log 2) * q ^ M := by ring
    _ ≤ (2 / Real.log 2) * (P : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_left hqM (by positivity)


/-- The paid dyadic S3 correction is uniformly bounded by a fixed
multiple of the endpoint rpow. -/
private theorem primeRankinCorrection_le_endpoint_rpow
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    {P k : ℕ} {ε : ℝ}
    (hP : 2 ≤ P) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    primeRankinCorrection f P k ε ≤
      ((4 * A1 * Real.log 4) / Real.log 2) * (P : ℝ) ^ ε := by
  have hdy :=
    primeRankinCorrection_le_dyadic hf P k hε0.le hε1
  have hgeom := shell_geometric_rankin_bound hP hε0 hε1
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ 2 * A1 * Real.log 4 := by
    exact mul_nonneg (mul_nonneg (by norm_num) hf.A1_nonneg) hlog4
  calc
    primeRankinCorrection f P k ε
        ≤ (A1 * ε) *
          (2 * Real.log 4 *
            ∑ j ∈ Finset.range (Nat.log 2 P + 1),
              (((2 ^ j : ℕ) : ℝ)) ^ ε) := hdy
    _ = (2 * A1 * Real.log 4) *
          (ε * ∑ j ∈ Finset.range (Nat.log 2 P + 1),
            (((2 ^ j : ℕ) : ℝ)) ^ ε) := by ring
    _ ≤ (2 * A1 * Real.log 4) *
          ((2 / Real.log 2) * (P : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left hgeom hA
    _ = ((4 * A1 * Real.log 4) / Real.log 2) *
          (P : ℝ) ^ ε := by ring


def classIVRankinD (A1 : ℝ) : ℝ :=
  960 * Real.log (1 + A1) + 24

private def classIVRankinH (A1 : ℝ) : ℝ :=
  ((4 * A1 * Real.log 4) / Real.log 2) *
    Real.exp (classIVRankinD A1)

/-- Endpoint form of the Class-IV Rankin budget. The fixed-envelope weight
loss is cancelled by the square-root tail, leaving an additional exp(-8r)
shell decay and only an A1-dependent scalar. -/
private theorem classIV_rankin_budget_of_endpoints
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    {z p k r : ℕ}
    (hr : 2 ≤ r) (hp : 2 ≤ p) (hpr : p ^ r ≤ z)
    (hzsqrt : 1 ≤ Nat.sqrt z)
    (hlarge : Real.exp (classIVRankinD A1) ≤ (p : ℝ)) :
    ∃ ε : ℝ,
      0 ≤ ε ∧ ε ≤ 1 ∧
      primeRankinCorrection f p k ε -
          ε * Real.log ((Nat.sqrt z : ℕ) : ℝ) ≤
        -(320 * (r : ℝ) * Real.log (1 + A1) +
            8 * (r : ℝ) - classIVRankinH A1) := by
  let D : ℝ := classIVRankinD A1
  let H : ℝ := classIVRankinH A1
  let ε : ℝ := D / Real.log (p : ℝ)
  have hbase : (1 : ℝ) ≤ 1 + A1 := by
    linarith [hf.A1_nonneg]
  have hlogbase : 0 ≤ Real.log (1 + A1) :=
    Real.log_nonneg hbase
  have hD : 0 < D := by
    dsimp [D, classIVRankinD]
    nlinarith
  have hpR : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_two hp)
  have hp1R : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le one_lt_two hp)
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos hp1R
  have hε0 : 0 < ε := by
    dsimp [ε]
    positivity
  have hDle : D ≤ Real.log (p : ℝ) := by
    have hlog :=
      Real.log_le_log (Real.exp_pos D) hlarge
    simpa [Real.log_exp] using hlog
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    exact (div_le_one hlogp).2 hDle
  have hpε : (p : ℝ) ^ ε = Real.exp D := by
    rw [Real.rpow_def_of_pos hpR]
    congr 1
    dsimp [ε]
    field_simp [hlogp.ne']
  have hcorr0 :=
    primeRankinCorrection_le_endpoint_rpow
      (k := k) hf hp hε0 hε1
  have hcorr :
      primeRankinCorrection f p k ε ≤ H := by
    dsimp [H, classIVRankinH]
    rw [hpε] at hcorr0
    exact hcorr0
  let m : ℕ := r / 2
  have hm3Nat : r ≤ 3 * m := by
    dsimp [m]
    omega
  have h2m : 2 * m ≤ r := by
    dsimp [m]
    omega
  have hpmono : p ^ (2 * m) ≤ p ^ r :=
    Nat.pow_le_pow_right (by omega) h2m
  have hpmsq : (p ^ m) ^ 2 ≤ z := by
    calc
      (p ^ m) ^ 2 = p ^ (2 * m) := by
        rw [← pow_mul]
        congr 1
        omega
      _ ≤ p ^ r := hpmono
      _ ≤ z := hpr
  have hpmroot : p ^ m ≤ Nat.sqrt z := by
    rw [Nat.le_sqrt']
    exact hpmsq
  have hrootR : (0 : ℝ) < ((Nat.sqrt z : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hzsqrt)
  have hlogpm :
      Real.log (((p ^ m : ℕ) : ℝ)) ≤
        Real.log ((Nat.sqrt z : ℕ) : ℝ) := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpmroot)
  have hlogpm_eq :
      Real.log (((p ^ m : ℕ) : ℝ)) =
        (m : ℝ) * Real.log (p : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  have hm3 : (r : ℝ) / 3 ≤ (m : ℝ) := by
    have hm3R : (r : ℝ) ≤ 3 * (m : ℝ) := by
      exact_mod_cast hm3Nat
    linarith
  have hDscale :
      D * (r : ℝ) / 3 ≤
        ε * Real.log ((Nat.sqrt z : ℕ) : ℝ) := by
    calc
      D * (r : ℝ) / 3 ≤ D * (m : ℝ) := by
        have hm := mul_le_mul_of_nonneg_left hm3 hD.le
        nlinarith
      _ = ε * ((m : ℝ) * Real.log (p : ℝ)) := by
        dsimp [ε]
        field_simp [hlogp.ne']
      _ = ε * Real.log (((p ^ m : ℕ) : ℝ)) := by
        rw [hlogpm_eq]
      _ ≤ ε * Real.log ((Nat.sqrt z : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlogpm hε0.le
  have hcancel :
      320 * (r : ℝ) * Real.log (1 + A1) +
          8 * (r : ℝ) ≤
        ε * Real.log ((Nat.sqrt z : ℕ) : ℝ) := by
    calc
      320 * (r : ℝ) * Real.log (1 + A1) +
          8 * (r : ℝ)
          = D * (r : ℝ) / 3 := by
            dsimp [D, classIVRankinD]
            ring
      _ ≤ ε * Real.log ((Nat.sqrt z : ℕ) : ℝ) := hDscale
  refine ⟨ε, hε0.le, hε1, ?_⟩
  change primeRankinCorrection f p k ε -
      ε * Real.log ((Nat.sqrt z : ℕ) : ℝ) ≤
    -(320 * (r : ℝ) * Real.log (1 + A1) +
        8 * (r : ℝ) - H)
  linarith


/-- Naturalized upper endpoint of the source Class-IV r-shell. -/
@[expose] def classIVShellUpper (z r : ℕ) : ℕ :=
  Nat.nthRoot r z

/-- Naturalized lower roughness cutoff of the source Class-IV r-shell. -/
@[expose] def classIVShellLower (z r : ℕ) : ℕ :=
  Nat.nthRoot (r + 1) z

/-- Source-faithful one-shell-per-r Class-IV overcount. -/
@[expose] def classIVOvercount
    (f : ArithmeticFunction ℝ) (x y z k a : ℕ) : ℝ := by
  classical
  exact ∑ r ∈ Finset.Icc 2 (shiuClassIVR0 x z),
    classIVShellOvercount f x y z k a
      (classIVShellUpper z r) (classIVShellLower z r)

private theorem classIV_shell_endpoints
    {A1 : ℝ} {x z r : ℕ}
    (hz2 : 2 ≤ z)
    (hL4 : 4 ≤ shiuLogLogSmoothThreshold x)
    (hlarge :
      Real.exp (classIVRankinD A1) ≤
        (shiuLogLogSmoothThreshold x : ℝ))
    (hr : r ∈ Finset.Icc 2 (shiuClassIVR0 x z)) :
    let p := classIVShellUpper z r
    let w := classIVShellLower z r
    2 ≤ p ∧ p ^ r ≤ z ∧ p ≤ z ∧
    Real.exp (classIVRankinD A1) ≤ (p : ℝ) ∧
    2 ≤ w ∧ w ^ 2 ≤ z ∧ z < (w + 1) ^ (r + 1) := by
  let L : ℕ := shiuLogLogSmoothThreshold x
  let r0 : ℕ := shiuClassIVR0 x z
  let p : ℕ := classIVShellUpper z r
  let w : ℕ := classIVShellLower z r
  have hrI := Finset.mem_Icc.mp hr
  have hr2 : 2 ≤ r := hrI.1
  have hrr0 : r ≤ r0 := hrI.2
  have hz0 : z ≠ 0 := by omega
  have hLpos : 0 < L := by
    dsimp [L]
    omega
  have hLpow0 : L ^ r0 ≤ z := by
    dsimp [r0, shiuClassIVR0]
    exact Nat.pow_log_le_self L hz0
  have hLpow : L ^ r ≤ z := by
    exact (Nat.pow_le_pow_right hLpos hrr0).trans hLpow0
  have hLp : L ≤ p := by
    dsimp [p, classIVShellUpper]
    exact (Nat.le_nthRoot_iff (by omega)).2 hLpow
  have hp2 : 2 ≤ p := by
    dsimp [L] at hLp
    omega
  have hpr : p ^ r ≤ z := by
    dsimp [p, classIVShellUpper]
    exact Nat.pow_nthRoot_le (Or.inl (by omega))
  have hpz : p ≤ z := by
    exact (Nat.le_self_pow (by omega) p).trans hpr
  have hlargeP :
      Real.exp (classIVRankinD A1) ≤ (p : ℝ) := by
    have hLpR : (L : ℝ) ≤ (p : ℝ) := by exact_mod_cast hLp
    simpa [L] using hlarge.trans hLpR
  have htwoexp : 2 ^ (r + 1) ≤ z := by
    have he : r + 1 ≤ 2 * r := by omega
    have h24 : 2 ^ (r + 1) ≤ 2 ^ (2 * r) :=
      Nat.pow_le_pow_right (by omega) he
    have hpow4 : 2 ^ (2 * r) = 4 ^ r := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    have h4L : 4 ^ r ≤ L ^ r :=
      Nat.pow_le_pow_left (by simpa [L] using hL4) r
    calc
      2 ^ (r + 1) ≤ 2 ^ (2 * r) := h24
      _ = 4 ^ r := hpow4
      _ ≤ L ^ r := h4L
      _ ≤ z := hLpow
  have hw2 : 2 ≤ w := by
    dsimp [w, classIVShellLower]
    exact (Nat.le_nthRoot_iff (by omega)).2 htwoexp
  have hwpow : w ^ (r + 1) ≤ z := by
    dsimp [w, classIVShellLower]
    exact Nat.pow_nthRoot_le (Or.inl (by omega))
  have hwsq : w ^ 2 ≤ z := by
    have hpowmono : w ^ 2 ≤ w ^ (r + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact hpowmono.trans hwpow
  have hzwr : z < (w + 1) ^ (r + 1) := by
    dsimp [w, classIVShellLower]
    exact (Nat.nthRoot_lt_iff (by omega)).1
      (Nat.lt_succ_self (Nat.nthRoot (r + 1) z))
  exact ⟨hp2, hpr, hpz, hlargeP, hw2, hwsq, hzwr⟩

private theorem classIV_log_shell_compare
    {z w r : ℕ}
    (hz2 : 2 ≤ z) (hw2 : 2 ≤ w)
    (hzwr : z < (w + 1) ^ (r + 1)) :
    Real.log (z : ℝ) ≤
      2 * ((r + 1 : ℕ) : ℝ) * Real.log (w : ℝ) := by
  have hzpos : (0 : ℝ) < (z : ℝ) := by positivity
  have hzwR :
      (z : ℝ) < (((w + 1) ^ (r + 1) : ℕ) : ℝ) := by
    exact_mod_cast hzwr
  have hlog1 :
      Real.log (z : ℝ) <
        Real.log ((((w + 1) ^ (r + 1) : ℕ) : ℝ)) :=
    Real.log_lt_log hzpos hzwR
  have hlog1' :
      Real.log (z : ℝ) <
        (((r + 1 : ℕ) : ℝ)) * Real.log ((w + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_pow, Real.log_pow] using hlog1
  have hwpowNat : w + 1 ≤ w ^ 2 := by
    nlinarith
  have hwpowR :
      ((w + 1 : ℕ) : ℝ) ≤ ((w ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hwpowNat
  have hlog2 :
      Real.log ((w + 1 : ℕ) : ℝ) ≤
        Real.log ((w ^ 2 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) hwpowR
  have hlog2' :
      Real.log ((w + 1 : ℕ) : ℝ) ≤
        2 * Real.log (w : ℝ) := by
    simpa [Nat.cast_pow, Real.log_pow] using hlog2
  have hm :=
    mul_le_mul_of_nonneg_left hlog2'
      (by positivity : 0 ≤ (((r + 1 : ℕ) : ℝ)))
  nlinarith

private theorem classIV_decay_weight_le
    {r : ℕ} (hr : 2 ≤ r) :
    (((r + 1 : ℕ) : ℝ)) *
        Real.exp (-8 * (r : ℝ)) ≤
      2 * ((1 / 2 : ℝ) ^ r) := by
  have h4exp : (4 : ℝ) ≤ Real.exp 8 := by
    nlinarith [Real.add_one_le_exp (8 : ℝ)]
  have hexp8 : Real.exp (-8 : ℝ) ≤ (1 / 4 : ℝ) := by
    rw [Real.exp_neg]
    have hi :=
      (inv_le_inv₀ (Real.exp_pos (8 : ℝ))
        (by norm_num : (0 : ℝ) < 4)).2 h4exp
    norm_num at hi ⊢
    exact hi
  have hdec :
      Real.exp (-8 * (r : ℝ)) ≤ (1 / 4 : ℝ) ^ r := by
    rw [show -8 * (r : ℝ) = (r : ℝ) * (-8 : ℝ) by ring,
      Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hexp8 r
  have hsuccNat : r + 1 ≤ 2 ^ (r + 1) :=
    Nat.le_of_lt (r + 1).lt_two_pow_self
  have hsucc : (((r + 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (r + 1) := by
    exact_mod_cast hsuccNat
  calc
    (((r + 1 : ℕ) : ℝ)) * Real.exp (-8 * (r : ℝ))
        ≤ (2 : ℝ) ^ (r + 1) * (1 / 4 : ℝ) ^ r :=
      mul_le_mul hsucc hdec (by positivity) (by positivity)
    _ = 2 * ((1 / 2 : ℝ) ^ r) := by
      rw [pow_succ]
      calc
        (2 : ℝ) ^ r * 2 * (1 / 4 : ℝ) ^ r
            = 2 * ((2 : ℝ) ^ r * (1 / 4 : ℝ) ^ r) := by ring
        _ = 2 * (((2 : ℝ) * (1 / 4 : ℝ)) ^ r) := by
          rw [mul_pow]
        _ = 2 * ((1 / 2 : ℝ) ^ r) := by norm_num

private theorem classIV_decay_sum_le_four (R : ℕ) :
    (∑ r ∈ Finset.Icc 2 R,
      (((r + 1 : ℕ) : ℝ)) * Real.exp (-8 * (r : ℝ))) ≤ 4 := by
  have hpoint :
      ∀ r ∈ Finset.Icc 2 R,
        (((r + 1 : ℕ) : ℝ)) * Real.exp (-8 * (r : ℝ)) ≤
          2 * ((1 / 2 : ℝ) ^ r) := by
    intro r hr
    exact classIV_decay_weight_le (Finset.mem_Icc.mp hr).1
  have hsub : Finset.Icc 2 R ⊆ Finset.range (R + 1) := by
    intro r hr
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.mem_Icc.mp hr).2
  calc
    (∑ r ∈ Finset.Icc 2 R,
        (((r + 1 : ℕ) : ℝ)) * Real.exp (-8 * (r : ℝ)))
        ≤ ∑ r ∈ Finset.Icc 2 R, 2 * ((1 / 2 : ℝ) ^ r) :=
      Finset.sum_le_sum fun r hr => hpoint r hr
    _ ≤ ∑ r ∈ Finset.range (R + 1), 2 * ((1 / 2 : ℝ) ^ r) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun r hr _ => by positivity)
    _ = 2 * ∑ r ∈ Finset.range (R + 1), ((1 / 2 : ℝ) ^ r) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * 2 := by
      exact mul_le_mul_of_nonneg_left
        (sum_geometric_two_le (R + 1)) (by norm_num)
    _ = 4 := by norm_num


/-- Fixed-envelope Class-IV constant exposed to the S12 consumer. -/
@[expose] def shiuClassIVConstant (A1 : ℝ) : ℝ :=
  96 * Real.exp
    ((((4 * A1 * Real.log 4) / Real.log 2) *
        Real.exp (960 * Real.log (1 + A1) + 24)))

private theorem classIV_shell_bound_final
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    {x y z k a r : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hzy : z ≤ y) (hkz : k * z < y)
    (hz2 : 2 ≤ z) (hx : x < z ^ 160)
    (hL4 : 4 ≤ shiuLogLogSmoothThreshold x)
    (hlarge :
      Real.exp (classIVRankinD A1) ≤
        (shiuLogLogSmoothThreshold x : ℝ))
    (hr : r ∈ Finset.Icc 2 (shiuClassIVR0 x z)) :
    classIVShellOvercount f x y z k a
        (classIVShellUpper z r) (classIVShellLower z r) ≤
      (24 * Real.exp (classIVRankinH A1)) *
        ((((r + 1 : ℕ) : ℝ)) * Real.exp (-8 * (r : ℝ))) *
        ((((y : ℝ)) /
            ((k.totient : ℝ) * Real.log (z : ℝ)) +
          (z : ℝ) ^ 2) *
          Real.exp (primeMass f z k)) := by
  let p := classIVShellUpper z r
  let w := classIVShellLower z r
  obtain ⟨hp2, hpr, hpz, hlargeP, hw2, hwsq, hzwr⟩ :=
    classIV_shell_endpoints
      (A1 := A1) (x := x) hz2 hL4 hlarge hr
  have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
  have hzsqrt : 1 ≤ Nat.sqrt z := by
    rw [Nat.le_sqrt]
    omega
  have hk : 0 < k := lt_trans ha0 haklt
  have hkb :
      ∀ b ∈ classIVPrefixSet z k p, k * b < y := by
    intro b hb
    have hbF := Finset.mem_filter.mp hb
    have hbI := Finset.mem_Icc.mp hbF.1
    exact (Nat.mul_le_mul_left k hbI.2).trans_lt hkz
  obtain ⟨ε, hε0, hε1, hbudget⟩ :=
    classIV_rankin_budget_of_endpoints
      hf hr2 hp2 hpr hzsqrt hlargeP
  let R : ℝ :=
    320 * (r : ℝ) * Real.log (1 + A1) +
      8 * (r : ℝ) - classIVRankinH A1
  have hshell :=
    shiu_classIV_shell_bound_of_rankin_budget
      hf ha0 haklt hak hyx hzy hk hzsqrt hw2 hwsq hx
        (by omega : 1 ≤ r) hzwr hpz hkb
        hε0 hε1 (R := R) (by simpa [R] using hbudget)
  have hbasepos : 0 < 1 + A1 := by
    linarith [hf.A1_nonneg]
  have hpowexp :
      (1 + A1) ^ (320 * r) =
        Real.exp (320 * (r : ℝ) * Real.log (1 + A1)) := by
    calc
      (1 + A1) ^ (320 * r)
          = Real.exp (Real.log (1 + A1)) ^ (320 * r) := by
            rw [Real.exp_log hbasepos]
      _ = Real.exp
          (((320 * r : ℕ) : ℝ) * Real.log (1 + A1)) := by
            rw [← Real.exp_nat_mul]
      _ = Real.exp (320 * (r : ℝ) * Real.log (1 + A1)) := by
            congr 1
            norm_num
  have hexpcancel :
      (1 + A1) ^ (320 * r) *
        Real.exp (primeMass f z k - R) =
      Real.exp (classIVRankinH A1) *
        Real.exp (-8 * (r : ℝ)) *
        Real.exp (primeMass f z k) := by
    rw [hpowexp, ← Real.exp_add]
    have hexp :
        320 * (r : ℝ) * Real.log (1 + A1) +
            (primeMass f z k - R) =
          classIVRankinH A1 + (-8 * (r : ℝ)) +
            primeMass f z k := by
      dsimp [R]
      ring
    rw [hexp, Real.exp_add, Real.exp_add]
  have hlogz : 0 < Real.log (z : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < z by omega)
  have hlogw : 0 < Real.log (w : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < w by omega)
  have hlogcmp :=
    classIV_log_shell_compare (z := z) (w := w) (r := r)
      hz2 hw2 hzwr
  have hinv :
      1 / Real.log (w : ℝ) ≤
        (2 * (((r + 1 : ℕ) : ℝ))) / Real.log (z : ℝ) := by
    apply (le_div_iff₀ hlogz).2
    have hratio :
        Real.log (z : ℝ) / Real.log (w : ℝ) ≤
          2 * (((r + 1 : ℕ) : ℝ)) :=
      (div_le_iff₀ hlogw).2 hlogcmp
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using hratio
  let A : ℝ :=
    (y : ℝ) /
      ((k.totient : ℝ) * Real.log (z : ℝ))
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hscaled :
      (y : ℝ) /
          ((k.totient : ℝ) * Real.log (w : ℝ)) ≤
        2 * (((r + 1 : ℕ) : ℝ)) * A := by
    have hphi : (0 : ℝ) ≤ (k.totient : ℝ) := by positivity
    calc
      (y : ℝ) /
          ((k.totient : ℝ) * Real.log (w : ℝ))
          =
        ((y : ℝ) / (k.totient : ℝ)) *
          (1 / Real.log (w : ℝ)) := by ring
      _ ≤ ((y : ℝ) / (k.totient : ℝ)) *
          ((2 * (((r + 1 : ℕ) : ℝ))) /
            Real.log (z : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 * (((r + 1 : ℕ) : ℝ)) * A := by
        dsimp [A]
        ring
  have hcoef : (1 : ℝ) ≤ 6 * (((r + 1 : ℕ) : ℝ)) := by
    have hrp : (1 : ℝ) ≤ (((r + 1 : ℕ) : ℝ)) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le r))
    nlinarith
  have hG :
      (3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log (w : ℝ)) +
          (z : ℝ) ^ 2 ≤
        6 * (((r + 1 : ℕ) : ℝ)) *
          (A + (z : ℝ) ^ 2) := by
    calc
      (3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log (w : ℝ)) +
          (z : ℝ) ^ 2
          =
        3 * ((y : ℝ) /
          ((k.totient : ℝ) * Real.log (w : ℝ))) +
          (z : ℝ) ^ 2 := by ring
      _ ≤ 3 * (2 * (((r + 1 : ℕ) : ℝ)) * A) +
          (z : ℝ) ^ 2 := by
        gcongr
      _ ≤ 6 * (((r + 1 : ℕ) : ℝ)) * A +
          6 * (((r + 1 : ℕ) : ℝ)) * (z : ℝ) ^ 2 := by
        apply _root_.add_le_add
        · ring_nf
          exact le_rfl
        · simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hcoef (sq_nonneg (z : ℝ))
      _ = 6 * (((r + 1 : ℕ) : ℝ)) *
          (A + (z : ℝ) ^ 2) := by ring
  have hfac0 :
      0 ≤ 4 * Real.exp (classIVRankinH A1) *
        Real.exp (-8 * (r : ℝ)) *
        Real.exp (primeMass f z k) := by
    positivity
  calc
    classIVShellOvercount f x y z k a p w
        ≤
      (4 * (1 + A1) ^ (320 * r)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) *
        Real.exp (primeMass f z k - R) := hshell
    _ =
      (4 * Real.exp (classIVRankinH A1) *
        Real.exp (-8 * (r : ℝ)) *
        Real.exp (primeMass f z k)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) := by
      calc
        (4 * (1 + A1) ^ (320 * r)) *
            ((3 * (y : ℝ)) /
              ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) *
            Real.exp (primeMass f z k - R)
            =
          4 * ((1 + A1) ^ (320 * r) *
            Real.exp (primeMass f z k - R)) *
            ((3 * (y : ℝ)) /
              ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) := by ring
        _ =
          4 * (Real.exp (classIVRankinH A1) *
            Real.exp (-8 * (r : ℝ)) *
            Real.exp (primeMass f z k)) *
            ((3 * (y : ℝ)) /
              ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) := by
            rw [hexpcancel]
        _ =
          (4 * Real.exp (classIVRankinH A1) *
            Real.exp (-8 * (r : ℝ)) *
            Real.exp (primeMass f z k)) *
            ((3 * (y : ℝ)) /
              ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) := by ring
    _ ≤
      (4 * Real.exp (classIVRankinH A1) *
        Real.exp (-8 * (r : ℝ)) *
        Real.exp (primeMass f z k)) *
        (6 * (((r + 1 : ℕ) : ℝ)) *
          (A + (z : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hG hfac0
    _ =
      (24 * Real.exp (classIVRankinH A1)) *
        ((((r + 1 : ℕ) : ℝ)) * Real.exp (-8 * (r : ℝ))) *
        ((A + (z : ℝ) ^ 2) *
          Real.exp (primeMass f z k)) := by ring
    _ =
      (24 * Real.exp (classIVRankinH A1)) *
        ((((r + 1 : ℕ) : ℝ)) * Real.exp (-8 * (r : ℝ))) *
        ((((y : ℝ)) /
            ((k.totient : ℝ) * Real.log (z : ℝ)) +
          (z : ℝ) ^ 2) *
          Real.exp (primeMass f z k)) := by rfl

set_option maxHeartbeats 1200000 in
/-- S11: Class IV estimate (source (5.8)), specialized to the fixed-quarter
squarefree CORE envelope. The constant depends only on the fixed prime-value
envelope A1 and is uniform in x,y,z,k,a. -/
theorem shiu_classIV_bound
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    {x y z k a : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hzy : z ≤ y) (hkz : k * z < y)
    (hz2 : 2 ≤ z) (hx : x < z ^ 160)
    (hL4 : 4 ≤ shiuLogLogSmoothThreshold x)
    (hlarge :
      Real.exp (classIVRankinD A1) ≤
        (shiuLogLogSmoothThreshold x : ℝ)) :
    classIVOvercount f x y z k a ≤
      shiuClassIVConstant A1 *
        ((((y : ℝ)) /
            ((k.totient : ℝ) * Real.log (z : ℝ)) +
          (z : ℝ) ^ 2) *
          Real.exp (primeMass f z k)) := by
  classical
  let R0 := shiuClassIVR0 x z
  let B : ℝ :=
    (((y : ℝ)) /
        ((k.totient : ℝ) * Real.log (z : ℝ)) +
      (z : ℝ) ^ 2) *
      Real.exp (primeMass f z k)
  have hB0 : 0 ≤ B := by
    have hk : 0 < k := lt_trans ha0 haklt
    have hphi : 0 < (k.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.2 hk
    have hlogz : 0 < Real.log (z : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < z by omega)
    dsimp [B]
    positivity
  have hpoint :
      ∀ r ∈ Finset.Icc 2 R0,
        classIVShellOvercount f x y z k a
            (classIVShellUpper z r) (classIVShellLower z r) ≤
          (24 * Real.exp (classIVRankinH A1)) *
            ((((r + 1 : ℕ) : ℝ)) * Real.exp (-8 * (r : ℝ))) *
            B := by
    intro r hr
    simpa [R0, B] using
      classIV_shell_bound_final
        hf ha0 haklt hak hyx hzy hkz hz2 hx hL4 hlarge hr
  have hsum :
      classIVOvercount f x y z k a ≤
        (24 * Real.exp (classIVRankinH A1)) *
          B *
          (∑ r ∈ Finset.Icc 2 R0,
            (((r + 1 : ℕ) : ℝ)) *
              Real.exp (-8 * (r : ℝ))) := by
    unfold classIVOvercount
    change
      (∑ r ∈ Finset.Icc 2 R0,
        classIVShellOvercount f x y z k a
          (classIVShellUpper z r) (classIVShellLower z r)) ≤ _
    calc
      (∑ r ∈ Finset.Icc 2 R0,
        classIVShellOvercount f x y z k a
          (classIVShellUpper z r) (classIVShellLower z r))
          ≤
        ∑ r ∈ Finset.Icc 2 R0,
          (24 * Real.exp (classIVRankinH A1)) *
            ((((r + 1 : ℕ) : ℝ)) * Real.exp (-8 * (r : ℝ))) *
            B :=
        Finset.sum_le_sum fun r hr => hpoint r hr
      _ =
        (24 * Real.exp (classIVRankinH A1)) *
          B *
          (∑ r ∈ Finset.Icc 2 R0,
            (((r + 1 : ℕ) : ℝ)) *
              Real.exp (-8 * (r : ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
  have hdec := classIV_decay_sum_le_four R0
  calc
    classIVOvercount f x y z k a
        ≤
      (24 * Real.exp (classIVRankinH A1)) *
        B *
        (∑ r ∈ Finset.Icc 2 R0,
          (((r + 1 : ℕ) : ℝ)) *
            Real.exp (-8 * (r : ℝ))) := hsum
    _ ≤
      (24 * Real.exp (classIVRankinH A1)) *
        B * 4 := by
      exact mul_le_mul_of_nonneg_left hdec
        (mul_nonneg (by positivity) hB0)
    _ =
      shiuClassIVConstant A1 * B := by
      dsimp [shiuClassIVConstant, classIVRankinH, classIVRankinD]
      ring
    _ =
      shiuClassIVConstant A1 *
        ((((y : ℝ)) /
            ((k.totient : ℝ) * Real.log (z : ℝ)) +
          (z : ℝ) ^ 2) *
          Real.exp (primeMass f z k)) := by rfl

end M4B
end PaperB
