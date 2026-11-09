module

/-
Paper B M4B-CORE S6: Class I preparatory bounds.
Authorized surface: M4B0 ledger row S6 only.
-/

public import PaperB.M4B.ShiuCore
public import PaperB.M4B.ShiuSplit
public import PaperB.M4B.ShiuScaledAP
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

public section

open scoped BigOperators
open Finset Nat Real
open ArithmeticFunction

noncomputable section

namespace PaperB
namespace M4B

/-- Fixed-quarter specialization of Shiu (5.2), with the source-faithful
natural threshold `⌊√z⌋`: if every prime factor of `d` is larger than
`Nat.sqrt z`, `x < z^160`, and `d ≤ x`, then `d` has fewer than
320 prime factors. -/
theorem rough_primeFactorsList_length_lt_320
    {d x z : ℕ}
    (hdpos : 0 < d)
    (hx : x < z ^ 160)
    (hdx : d ≤ x)
    (hrough : PaperB.M4A.shiuRough d (Nat.sqrt z)) :
    d.primeFactorsList.length < 320 := by
  rcases hrough with rfl | hmin
  · simp
  have hd0 : d ≠ 0 := Nat.ne_of_gt hdpos
  let r : ℕ := Nat.succ (Nat.sqrt z)
  have hrpos : 0 < r := Nat.succ_pos _
  have hprod : r ^ d.primeFactorsList.length ≤ d := by
    calc
      r ^ d.primeFactorsList.length ≤ d.primeFactorsList.prod :=
        List.pow_length_le_prod d.primeFactorsList r (fun p hp => by
          have hpprime : p.Prime := Nat.prime_of_mem_primeFactorsList hp
          have hpd : p ∣ d := Nat.dvd_of_mem_primeFactorsList hp
          have hminle : d.minFac ≤ p := Nat.minFac_le_of_dvd hpprime.two_le hpd
          dsimp [r]
          omega)
      _ = d := Nat.prod_primeFactorsList hd0
  by_contra hlen
  have h320 : 320 ≤ d.primeFactorsList.length := by omega
  have hrpow : r ^ 320 ≤ r ^ d.primeFactorsList.length :=
    Nat.pow_le_pow_right hrpos h320
  have hzlt : z < r ^ 2 := by
    dsimp [r]
    simpa using Nat.lt_succ_sqrt' z
  have hzpow : z ^ 160 < r ^ 320 := by
    calc
      z ^ 160 < (r ^ 2) ^ 160 :=
        Nat.pow_lt_pow_left hzlt (by norm_num)
      _ = r ^ 320 := by
        rw [← pow_mul]
  have hxd : x < d :=
    hx.trans (hzpow.trans_le (hrpow.trans hprod))
  exact (not_lt_of_ge hdx) hxd

/-- Class-I pointwise weight bound obtained from the fixed prime envelope.
The deliberately coarse base 1+A1 avoids any lower-bound assumption on A1. -/
theorem fixedQuarter_rough_value_le
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    {d x z : ℕ}
    (hdpos : 0 < d)
    (hx : x < z ^ 160)
    (hdx : d ≤ x)
    (hrough : PaperB.M4A.shiuRough d (Nat.sqrt z)) :
    f d ≤ (1 + A1) ^ 320 := by
  by_cases hs : Squarefree d
  · have hlen :=
      rough_primeFactorsList_length_lt_320 hdpos hx hdx hrough
    have hcard : d.primeFactors.card ≤ 320 := by
      calc
        d.primeFactors.card
            ≤ d.primeFactorsList.length := by
              change d.primeFactorsList.toFinset.card ≤ d.primeFactorsList.length
              exact List.toFinset_card_le (l := d.primeFactorsList)
        _ ≤ 320 := Nat.le_of_lt hlen
    have hprod :
        (∏ p ∈ d.primeFactors, f p) ≤
          ∏ _p ∈ d.primeFactors, (1 + A1) := by
      refine Finset.prod_le_prod₀ (fun p hp => hf.nonneg p) ?_
      intro p hp
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hple : f p ≤ A1 := hf.prime_le p hpprime
      linarith [hf.A1_nonneg]
    calc
      f d = ∏ p ∈ d.primeFactors, f p :=
        (hf.multiplicative.prod_primeFactors hs).symm
      _ ≤ ∏ _p ∈ d.primeFactors, (1 + A1) := hprod
      _ = (1 + A1) ^ d.primeFactors.card := by simp
      _ ≤ (1 + A1) ^ 320 := by
        exact pow_le_pow_right₀ (by linarith [hf.A1_nonneg]) hcard
  · rw [hf.squarefree_support d hs]
    positivity


/-- The Class-I complementary factors for a fixed extracted factor `b`.
This is the exact source interval before the one-unit C5 over-cover. -/
@[expose] def classIInnerSet (x y z k a b : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (scaledLower x y b) (scaledUpper x b)).filter
    (fun d => b * d ≡ a [MOD k] ∧
      PaperB.M4A.shiuRough d (Nat.sqrt z))

/-- S6 inner estimate: after fixing `b`, the source Class-I complementary
factor sum is bounded by the already-paid C5 rough progression count.
The residue representative is fixed once for `a,b,k`, and the one-unit
over-cover is exactly S5. -/
theorem shiu_classI_inner_bound
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    {x y z k a b : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hbpos : 0 < b) (hbk : b.Coprime k)
    (hkb : k * b < y) (hzsqrt : 2 ≤ Nat.sqrt z)
    (hx : x < z ^ 160) :
    (∑ d ∈ classIInnerSet x y z k a b, f d) ≤
      (1 + A1) ^ 320 *
        (4 * (((scaledCoverLength x y b : ℕ) : ℝ) /
          ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
          ((Nat.sqrt z : ℕ) : ℝ) ^ 2)) := by
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
      (Nat.sqrt z) k a'
      ha'0 ha'lt ha'cop hklen hcover hzsqrt
  let S : Finset ℕ := classIInnerSet x y z k a b
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
      (S.card : ℝ) ≤
        PaperB.M4A.shiuPhi
          (scaledCoverUpper x b) (scaledCoverLength x y b)
          (Nat.sqrt z) k a' := by
    unfold PaperB.M4A.shiuPhi
    calc
      (S.card : ℝ) = ∑ d ∈ S, (1 : ℝ) := by simp
      _ = ∑ d ∈ S,
          if d ≡ a' [MOD k] ∧
              PaperB.M4A.shiuRough d (Nat.sqrt z)
          then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro d hd
            have hdF := Finset.mem_filter.mp hd
            have hdres : d ≡ a' [MOD k] := (hres d).mp hdF.2.1
            simp [hdres, hdF.2.2]
      _ ≤ ∑ d ∈ T,
          if d ≡ a' [MOD k] ∧
              PaperB.M4A.shiuRough d (Nat.sqrt z)
          then (1 : ℝ) else 0 := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
            intro d hdT hdnot
            split <;> positivity
  have hC : 0 ≤ (1 + A1) ^ 320 := by
    exact pow_nonneg (by linarith [hf.A1_nonneg]) _
  have hpoint :
      ∀ d ∈ S, f d ≤ (1 + A1) ^ 320 := by
    intro d hd
    have hdF := Finset.mem_filter.mp hd
    have hdI := Finset.mem_Ioc.mp hdF.1
    have hdpos : 0 < d :=
      lt_of_le_of_lt (Nat.zero_le _) hdI.1
    have hdupper : d ≤ x / b := by
      simpa [scaledUpper] using hdI.2
    have hdle : d ≤ x :=
      hdupper.trans (Nat.div_le_self x b)
    exact fixedQuarter_rough_value_le hf hdpos hx hdle hdF.2.2
  change (∑ d ∈ S, f d) ≤ _
  calc
    (∑ d ∈ S, f d)
        ≤ ∑ _d ∈ S, (1 + A1) ^ 320 :=
      Finset.sum_le_sum fun d hd => hpoint d hd
    _ = (1 + A1) ^ 320 * (S.card : ℝ) := by
      simp [mul_comm]
    _ ≤ (1 + A1) ^ 320 *
          PaperB.M4A.shiuPhi
            (scaledCoverUpper x b) (scaledCoverLength x y b)
            (Nat.sqrt z) k a' :=
      mul_le_mul_of_nonneg_left hcount hC
    _ ≤ (1 + A1) ^ 320 *
          (4 * (((scaledCoverLength x y b : ℕ) : ℝ) /
            ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
            ((Nat.sqrt z : ℕ) : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hphi hC


/-- Source Class-I overcount after summing the fixed-`b` complementary-factor
sums. The coprimality filter is the one needed by S2. -/
@[expose] def classIOvercount
    (f : ArithmeticFunction ℝ) (x y z k a : ℕ) : ℝ := by
  classical
  exact ∑ b ∈ Finset.Icc 1 z with b.Coprime k,
    f b * ∑ d ∈ classIInnerSet x y z k a b, f d

/-- Scalar bridge for the S6 outer sum.  The one-unit interval over-cover
costs only a fixed factor, and the square-root roughness error is absorbed
by `z^2`. -/
theorem classI_scaled_weight_bound
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    {x y z k b : ℕ}
    (hyx : y ≤ x) (hb1 : 1 ≤ b) (hbz : b ≤ z) (hzy : z ≤ y)
    (hk : 0 < k) (hzsqrt : 2 ≤ Nat.sqrt z) :
    f b * (((scaledCoverLength x y b : ℕ) : ℝ) /
        ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
        ((Nat.sqrt z : ℕ) : ℝ) ^ 2) ≤
      (f b / (b : ℝ)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
          (z : ℝ) ^ 2) := by
  have hbpos : 0 < b := by omega
  have hfb : 0 ≤ f b := hf.nonneg b
  have hq : 0 ≤ f b / (b : ℝ) := div_nonneg hfb (by positivity)
  have hkpos : 0 < k.totient := Nat.totient_pos.2 hk
  have hlog : 0 < Real.log (Nat.sqrt z : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < Nat.sqrt z by omega)
  have hden :
      0 < (k.totient : ℝ) * Real.log (Nat.sqrt z) := by
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
  have hrbNat :
      (Nat.sqrt z) ^ 2 * b ≤ z ^ 2 := by
    calc
      (Nat.sqrt z) ^ 2 * b ≤ z * b :=
        Nat.mul_le_mul_right b (Nat.sqrt_le' z)
      _ ≤ z * z := Nat.mul_le_mul_left z hbz
      _ = z ^ 2 := by ring
  have hrb :
      ((Nat.sqrt z : ℕ) : ℝ) ^ 2 * (b : ℝ) ≤ (z : ℝ) ^ 2 := by
    exact_mod_cast hrbNat
  have hfR :
      f b * ((Nat.sqrt z : ℕ) : ℝ) ^ 2 ≤
        (z : ℝ) ^ 2 * (f b / (b : ℝ)) := by
    calc
      f b * ((Nat.sqrt z : ℕ) : ℝ) ^ 2
          = ((b : ℝ) * (f b / (b : ℝ))) *
              ((Nat.sqrt z : ℕ) : ℝ) ^ 2 :=
        congrArg (fun t : ℝ => t * ((Nat.sqrt z : ℕ) : ℝ) ^ 2) hfb_eq
      _ = (((Nat.sqrt z : ℕ) : ℝ) ^ 2 * (b : ℝ)) *
              (f b / (b : ℝ)) := by ring
      _ ≤ (z : ℝ) ^ 2 * (f b / (b : ℝ)) :=
        mul_le_mul_of_nonneg_right hrb hq
  calc
    f b * (((scaledCoverLength x y b : ℕ) : ℝ) /
          ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
          ((Nat.sqrt z : ℕ) : ℝ) ^ 2)
        =
      (f b * ((scaledCoverLength x y b : ℕ) : ℝ)) /
          ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
        f b * ((Nat.sqrt z : ℕ) : ℝ) ^ 2 := by ring
    _ ≤
      (3 * (y : ℝ) * (f b / (b : ℝ))) /
          ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
        (z : ℝ) ^ 2 * (f b / (b : ℝ)) := by
      gcongr
    _ =
      (f b / (b : ℝ)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
          (z : ℝ) ^ 2) := by ring

set_option maxHeartbeats 800000 in
/-- S6: Class I after the paid C5 estimate and S2 harmonic Euler bound.
This is the source `b`-sum assembly, with only fixed-quarter constants
outside the moving parameters. -/
theorem shiu_classI_bound
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    {x y z k a : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hzy : z ≤ y) (hkz : k * z < y)
    (hzsqrt : 2 ≤ Nat.sqrt z) (hx : x < z ^ 160) :
    classIOvercount f x y z k a ≤
      4 * (1 + A1) ^ 320 *
        (((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
          (z : ℝ) ^ 2) *
          Real.exp (primeMass f z k)) := by
  classical
  let B : Finset ℕ :=
    (Finset.Icc 1 z).filter (fun b => b.Coprime k)
  let Q : ℕ → ℝ := fun b => f b / (b : ℝ)
  let R : ℝ :=
    (3 * (y : ℝ)) /
      ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
      (z : ℝ) ^ 2
  have hC : 0 ≤ 4 * (1 + A1) ^ 320 := by
    positivity
  have hR : 0 ≤ R := by
    have hkpos : 0 < k := lt_trans ha0 haklt
    have hphi : 0 < (k.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.2 hkpos
    have hlog : 0 < Real.log (Nat.sqrt z : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < Nat.sqrt z by omega)
    dsimp [R]
    positivity
  have hpoint :
      ∀ b ∈ B,
        f b * (∑ d ∈ classIInnerSet x y z k a b, f d) ≤
          ((4 * (1 + A1) ^ 320) * R) * Q b := by
    intro b hb
    have hbF := Finset.mem_filter.mp hb
    have hbI := Finset.mem_Icc.mp hbF.1
    have hbpos : 0 < b := by omega
    have hkb : k * b < y :=
      (Nat.mul_le_mul_left k hbI.2).trans_lt hkz
    have hin :=
      shiu_classI_inner_bound hf ha0 haklt hak hyx hbpos hbF.2
        hkb hzsqrt hx
    have hfb : 0 ≤ f b := hf.nonneg b
    have hkpos : 0 < k := lt_trans ha0 haklt
    have hscaled :=
      classI_scaled_weight_bound (k := k) hf hyx hbI.1 hbI.2 hzy hkpos hzsqrt
    calc
      f b * (∑ d ∈ classIInnerSet x y z k a b, f d)
          ≤ f b * ((1 + A1) ^ 320 *
            (4 * (((scaledCoverLength x y b : ℕ) : ℝ) /
              ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
              ((Nat.sqrt z : ℕ) : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left hin hfb
      _ = (4 * (1 + A1) ^ 320) *
          (f b * (((scaledCoverLength x y b : ℕ) : ℝ) /
            ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
            ((Nat.sqrt z : ℕ) : ℝ) ^ 2)) := by ring
      _ ≤ (4 * (1 + A1) ^ 320) * (Q b * R) :=
        mul_le_mul_of_nonneg_left hscaled hC
      _ = ((4 * (1 + A1) ^ 320) * R) * Q b := by
        dsimp [Q]
        ring
  have hsum :
      classIOvercount f x y z k a ≤
        ((4 * (1 + A1) ^ 320) * R) * coprimeHarmonicMass f z k := by
    unfold classIOvercount
    change (∑ b ∈ B, f b *
      ∑ d ∈ classIInnerSet x y z k a b, f d) ≤ _
    calc
      (∑ b ∈ B, f b * ∑ d ∈ classIInnerSet x y z k a b, f d)
          ≤ ∑ b ∈ B, ((4 * (1 + A1) ^ 320) * R) * Q b :=
        Finset.sum_le_sum fun b hb => hpoint b hb
      _ = ((4 * (1 + A1) ^ 320) * R) * ∑ b ∈ B, Q b := by
        rw [Finset.mul_sum]
      _ = ((4 * (1 + A1) ^ 320) * R) *
          coprimeHarmonicMass f z k := by
        congr 1
  have hH :=
    squarefree_coprime_harmonic_upper hf z k
  calc
    classIOvercount f x y z k a
        ≤ ((4 * (1 + A1) ^ 320) * R) *
          coprimeHarmonicMass f z k := hsum
    _ ≤ ((4 * (1 + A1) ^ 320) * R) *
          Real.exp (primeMass f z k) := by
      exact mul_le_mul_of_nonneg_left hH (mul_nonneg hC hR)
    _ = 4 * (1 + A1) ^ 320 *
        (((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
          (z : ℝ) ^ 2) *
          Real.exp (primeMass f z k)) := by
      dsimp [R]
      ring



end M4B
end PaperB
