module

public import ShiuPublic.VaelisClassIVPrefixNonSquarefree
public import ShiuPublic.ClassIVRoughPower

public section

noncomputable section
namespace PaperB.M4B
open scoped BigOperators
theorem classical_classIV_inner_weight_bound
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    {x y z k a b w r : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hbpos : 0 < b) (hbk : b.Coprime k)
    (hkb : k * b < y) (hw : 2 ≤ w)
    (hx : x < z ^ 160) (hr : 1 ≤ r)
    (hzwr : z < (w + 1) ^ (r + 1)) :
    (∑ d ∈ classIVInnerSet x y k a b w, f d) ≤
      (1 + A) ^ (320 * r) *
        (4 * (((scaledCoverLength x y b : ℕ) : ℝ) /
          ((k.totient : ℝ) * Real.log w) + (w : ℝ) ^ 2)) := by
  classical
  let S : Finset ℕ := classIVInnerSet x y k a b w
  have hcount :=
    shiu_classIV_inner_count_bound
      ha0 haklt hak hyx hbpos hbk hkb hw
  have hC : 0 ≤ (1 + A) ^ (320 * r) :=
    pow_nonneg (by linarith [hf.A_nonnegative]) _
  have hpoint :
      ∀ d ∈ S, f d ≤ (1 + A) ^ (320 * r) := by
    intro d hd
    have hdF := Finset.mem_filter.mp hd
    have hdI := Finset.mem_Ioc.mp hdF.1
    have hdpos : 0 < d := by omega
    have hdupper : d ≤ x / b := by
      simpa [scaledUpper] using hdI.2
    have hdle : d ≤ x :=
      hdupper.trans (Nat.div_le_self x b)
    exact
      Shiu.classical_classIV_rough_value_le_succ
        hf hdpos hx hdle hr hzwr hdF.2.2
  change (∑ d ∈ S, f d) ≤ _
  calc
    (∑ d ∈ S, f d)
        ≤ ∑ _d ∈ S, (1 + A) ^ (320 * r) :=
      Finset.sum_le_sum fun d hd => hpoint d hd
    _ = (1 + A) ^ (320 * r) * (S.card : ℝ) := by
      simp [mul_comm]
    _ ≤ (1 + A) ^ (320 * r) *
        (4 * (((scaledCoverLength x y b : ℕ) : ℝ) /
          ((k.totient : ℝ) * Real.log w) + (w : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hcount hC


theorem classical_classIV_scaled_weight_bound
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    {x y z k b w : ℕ}
    (hyx : y ≤ x) (hb1 : 1 ≤ b) (hbz : b ≤ z) (hzy : z ≤ y)
    (hk : 0 < k) (hw : 2 ≤ w) (hwsq : w ^ 2 ≤ z) :
    f b * (((scaledCoverLength x y b : ℕ) : ℝ) /
        ((k.totient : ℝ) * Real.log w) + (w : ℝ) ^ 2) ≤
      (f b / (b : ℝ)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) := by
  have hbpos : 0 < b := by omega
  have hfb : 0 ≤ f b := hf.nonnegative b
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

@[expose] def classicalClassIVShellOvercount
    (f : ArithmeticFunction ℝ)
    (x y z k a p w : ℕ) : ℝ := by
  classical
  exact ∑ b ∈ Shiu.classicalClassIVPrefixSet z k p,
    f b * ∑ d ∈ classIVInnerSet x y k a b w, f d

/-- S11 raw shell assembly: paid C5 is applied at fixed b, then the b-harmonic
sum is injected into the paid S3 squarefree smooth-tail object. -/
theorem classical_classIV_shell_bound_raw
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    {x y z k a p w r : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hzy : z ≤ y) (hk : 0 < k)
    (hzsqrt : 1 ≤ Nat.sqrt z)
    (hw : 2 ≤ w) (hwsq : w ^ 2 ≤ z)
    (hx : x < z ^ 160) (hr : 1 ≤ r)
    (hzwr : z < (w + 1) ^ (r + 1))
    (hkb : ∀ b ∈ Shiu.classicalClassIVPrefixSet z k p, k * b < y) :
    classicalClassIVShellOvercount f x y z k a p w ≤
      (4 * (1 + A) ^ (320 * r)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) *
        (∑ b ∈ Shiu.boundedSmoothTailSet ((Nat.primesLE p).filter (fun q => ¬ q ∣ k)) (Nat.sqrt z) z, f b / (b : ℝ)) := by
  classical
  let B : Finset ℕ := Shiu.classicalClassIVPrefixSet z k p
  let C : ℝ := (1 + A) ^ (320 * r)
  let G : ℝ :=
    (3 * (y : ℝ)) /
      ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact pow_nonneg (by linarith [hf.A_nonnegative]) _
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
    have hbk : b.Coprime k := hbF.2.1
    have hinner :=
      classical_classIV_inner_weight_bound
        hf ha0 haklt hak hyx hbpos hbk (hkb b hb)
          hw hx hr hzwr
    have hscaled :=
      classical_classIV_scaled_weight_bound
        hf hyx hb1 hbz hzy hk hw hwsq
    have hfb : 0 ≤ f b := hf.nonnegative b
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
    Shiu.classical_classIV_prefix_harmonic_le_smooth_tail hf z k p hzsqrt
  have hfac : 0 ≤ 4 * C * G := by positivity
  unfold classicalClassIVShellOvercount
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
        (∑ b ∈ Shiu.boundedSmoothTailSet ((Nat.primesLE p).filter (fun q => ¬ q ∣ k)) (Nat.sqrt z) z, f b / (b : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (by simpa [B] using hpref) hfac
    _ =
      (4 * (1 + A) ^ (320 * r)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) *
        (∑ b ∈ Shiu.boundedSmoothTailSet ((Nat.primesLE p).filter (fun q => ¬ q ∣ k)) (Nat.sqrt z) z, f b / (b : ℝ)) := by
      rfl

#print axioms classical_classIV_inner_weight_bound
#print axioms classical_classIV_scaled_weight_bound
#print axioms classical_classIV_shell_bound_raw
end PaperB.M4B
