module

public import ShiuPublic.CorvethClassicalPrefixCore
public import ShiuPublic.ClassIVRoughPower
public import PaperB.M4B.ShiuClassI

public section

noncomputable section
namespace PaperB.M4B
open scoped BigOperators
open Finset Nat Real ArithmeticFunction

/-- Genuine unrestricted Class I rough-factor weight, counting multiplicity. -/
theorem corveth_classical_rough_value_le
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    {d x z : ℕ}
    (hdpos : 0 < d) (hx : x < z ^ 160) (hdx : d ≤ x)
    (hrough : PaperB.M4A.shiuRough d (Nat.sqrt z)) :
    f d ≤ (1 + A) ^ 320 := by
  have hlen := rough_primeFactorsList_length_lt_320 hdpos hx hdx hrough
  have hcard : ArithmeticFunction.cardFactors d ≤ 320 := by
    rw [cardFactors_apply]
    omega
  calc
    f d ≤ A ^ (ArithmeticFunction.cardFactors d) :=
      Shiu.classical_weight_le_pow_omega hf d (by omega)
    _ ≤ (1 + A) ^ (ArithmeticFunction.cardFactors d) :=
      pow_le_pow_left₀ hf.A_nonnegative (by linarith) _
    _ ≤ (1 + A) ^ 320 :=
      pow_le_pow_right₀ (by linarith [hf.A_nonnegative]) hcard

theorem corveth_classical_classI_inner_bound
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    {x y z k a b : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hbpos : 0 < b) (hbk : b.Coprime k)
    (hkb : k * b < y) (hzsqrt : 2 ≤ Nat.sqrt z)
    (hx : x < z ^ 160) :
    (∑ d ∈ classIInnerSet x y z k a b, f d) ≤
      (1 + A) ^ 320 *
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
  have hC : 0 ≤ (1 + A) ^ 320 := by
    exact pow_nonneg (by linarith [hf.A_nonnegative]) _
  have hpoint :
      ∀ d ∈ S, f d ≤ (1 + A) ^ 320 := by
    intro d hd
    have hdF := Finset.mem_filter.mp hd
    have hdI := Finset.mem_Ioc.mp hdF.1
    have hdpos : 0 < d :=
      lt_of_le_of_lt (Nat.zero_le _) hdI.1
    have hdupper : d ≤ x / b := by
      simpa [scaledUpper] using hdI.2
    have hdle : d ≤ x :=
      hdupper.trans (Nat.div_le_self x b)
    exact corveth_classical_rough_value_le hf hdpos hx hdle hdF.2.2
  change (∑ d ∈ S, f d) ≤ _
  calc
    (∑ d ∈ S, f d)
        ≤ ∑ _d ∈ S, (1 + A) ^ 320 :=
      Finset.sum_le_sum fun d hd => hpoint d hd
    _ = (1 + A) ^ 320 * (S.card : ℝ) := by
      simp [mul_comm]
    _ ≤ (1 + A) ^ 320 *
          PaperB.M4A.shiuPhi
            (scaledCoverUpper x b) (scaledCoverLength x y b)
            (Nat.sqrt z) k a' :=
      mul_le_mul_of_nonneg_left hcount hC
    _ ≤ (1 + A) ^ 320 *
          (4 * (((scaledCoverLength x y b : ℕ) : ℝ) /
            ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
            ((Nat.sqrt z : ℕ) : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hphi hC



#print axioms corveth_classical_classI_inner_bound
theorem corveth_classical_scaled_weight_bound
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
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
  have hfb : 0 ≤ f b := hf.nonnegative b
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
theorem corveth_classical_classI_harmonic_bound
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    {x y z k a : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hzy : z ≤ y) (hkz : k * z < y)
    (hzsqrt : 2 ≤ Nat.sqrt z) (hx : x < z ^ 160) :
    classIOvercount f x y z k a ≤
      4 * (1 + A) ^ 320 *
        (((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
          (z : ℝ) ^ 2) *
          coprimeHarmonicMass f z k) := by
  classical
  let B : Finset ℕ :=
    (Finset.Icc 1 z).filter (fun b => b.Coprime k)
  let Q : ℕ → ℝ := fun b => f b / (b : ℝ)
  let R : ℝ :=
    (3 * (y : ℝ)) /
      ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
      (z : ℝ) ^ 2
  have hC : 0 ≤ 4 * (1 + A) ^ 320 := by
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
          ((4 * (1 + A) ^ 320) * R) * Q b := by
    intro b hb
    have hbF := Finset.mem_filter.mp hb
    have hbI := Finset.mem_Icc.mp hbF.1
    have hbpos : 0 < b := by omega
    have hkb : k * b < y :=
      (Nat.mul_le_mul_left k hbI.2).trans_lt hkz
    have hin :=
      corveth_classical_classI_inner_bound hf ha0 haklt hak hyx hbpos hbF.2
        hkb hzsqrt hx
    have hfb : 0 ≤ f b := hf.nonnegative b
    have hkpos : 0 < k := lt_trans ha0 haklt
    have hscaled :=
      corveth_classical_scaled_weight_bound (k := k) hf hyx hbI.1 hbI.2 hzy hkpos hzsqrt
    calc
      f b * (∑ d ∈ classIInnerSet x y z k a b, f d)
          ≤ f b * ((1 + A) ^ 320 *
            (4 * (((scaledCoverLength x y b : ℕ) : ℝ) /
              ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
              ((Nat.sqrt z : ℕ) : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left hin hfb
      _ = (4 * (1 + A) ^ 320) *
          (f b * (((scaledCoverLength x y b : ℕ) : ℝ) /
            ((k.totient : ℝ) * Real.log (Nat.sqrt z)) +
            ((Nat.sqrt z : ℕ) : ℝ) ^ 2)) := by ring
      _ ≤ (4 * (1 + A) ^ 320) * (Q b * R) :=
        mul_le_mul_of_nonneg_left hscaled hC
      _ = ((4 * (1 + A) ^ 320) * R) * Q b := by
        dsimp [Q]
        ring
  have hsum :
      classIOvercount f x y z k a ≤
        ((4 * (1 + A) ^ 320) * R) * coprimeHarmonicMass f z k := by
    unfold classIOvercount
    change (∑ b ∈ B, f b *
      ∑ d ∈ classIInnerSet x y z k a b, f d) ≤ _
    calc
      (∑ b ∈ B, f b * ∑ d ∈ classIInnerSet x y z k a b, f d)
          ≤ ∑ b ∈ B, ((4 * (1 + A) ^ 320) * R) * Q b :=
        Finset.sum_le_sum fun b hb => hpoint b hb
      _ = ((4 * (1 + A) ^ 320) * R) * ∑ b ∈ B, Q b := by
        rw [Finset.mul_sum]
      _ = ((4 * (1 + A) ^ 320) * R) *
          coprimeHarmonicMass f z k := by
        congr 1
  simpa [R, mul_assoc] using hsum


#print axioms corveth_classical_scaled_weight_bound
#print axioms corveth_classical_classI_harmonic_bound
#print axioms corveth_classical_rough_value_le
end PaperB.M4B
