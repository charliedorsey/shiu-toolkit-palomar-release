module

public import ShiuPublic.VaelisClassIVShellFinal

public import ChallengeDefs.ClassIV

public section

noncomputable section
namespace PaperB.M4B
open scoped BigOperators
@[expose] def classicalClassIVOvercount
    (f : ArithmeticFunction ℝ) (x y z k a : ℕ) : ℝ := by
  classical
  exact ∑ r ∈ Finset.Icc 2 (shiuClassIVR0 x z),
    classicalClassIVShellOvercount f x y z k a
      (classIVShellUpper z r) (classIVShellLower z r)
theorem classical_classIV_decay_weight_le
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

theorem classical_classIV_decay_sum_le_four (R : ℕ) :
    (∑ r ∈ Finset.Icc 2 R,
      (((r + 1 : ℕ) : ℝ)) * Real.exp (-8 * (r : ℝ))) ≤ 4 := by
  have hpoint :
      ∀ r ∈ Finset.Icc 2 R,
        (((r + 1 : ℕ) : ℝ)) * Real.exp (-8 * (r : ℝ)) ≤
          2 * ((1 / 2 : ℝ) ^ r) := by
    intro r hr
    exact classical_classIV_decay_weight_le (Finset.mem_Icc.mp hr).1
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

/- Complete non-squarefree Class IV overcount constant, depending only on
ClassicalEnvelope A and the 1/4-growth witness B. -/
-- Shared Mathlib-only source definition: ChallengeDefs.ClassIV.classicalShiuClassIVConstant

set_option maxHeartbeats 1200000 in
theorem classical_shiu_classIV_bound
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : Shiu.ClassicalEnvelope f A) (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n → f n ≤ B * (n : ℝ)^(1/4 : ℝ))
    {x y z k a : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hzy : z ≤ y) (hkz : k * z < y)
    (hz2 : 2 ≤ z) (hx : x < z ^ 160)
    (hL4 : 4 ≤ shiuLogLogSmoothThreshold x)
    (hlarge :
      Real.exp (4 * classicalClassIVRankinD A) ≤
        (shiuLogLogSmoothThreshold x : ℝ)) :
    classicalClassIVOvercount f x y z k a ≤
      classicalShiuClassIVConstant A B *
        ((((y : ℝ)) /
            ((k.totient : ℝ) * Real.log (z : ℝ)) +
          (z : ℝ) ^ 2) *
          Real.exp (primeMass f z k)) := by
  classical
  let R0 := shiuClassIVR0 x z
  let V : ℝ :=
    (((y : ℝ)) /
        ((k.totient : ℝ) * Real.log (z : ℝ)) +
      (z : ℝ) ^ 2) *
      Real.exp (primeMass f z k)
  have hB0 : 0 ≤ V := by
    have hk : 0 < k := lt_trans ha0 haklt
    have hphi : 0 < (k.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.2 hk
    have hlogz : 0 < Real.log (z : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < z by omega)
    dsimp [V]
    positivity
  have hpoint :
      ∀ r ∈ Finset.Icc 2 R0,
        classicalClassIVShellOvercount f x y z k a
            (classIVShellUpper z r) (classIVShellLower z r) ≤
          (24 * Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A (classicalClassIVRankinD A)) B * Real.exp (2*A^2*Real.exp (2*classicalClassIVRankinD A) + classicalClassIVRankinH A)) *
            ((((r + 1 : ℕ) : ℝ)) * Real.exp (-8 * (r : ℝ))) *
            V := by
    intro r hr
    simpa [R0, V] using
      classical_classIV_shell_bound_final
        hf hB hgrowth ha0 haklt hak hyx hzy hkz hz2 hx hL4 hlarge hr
  have hsum :
      classicalClassIVOvercount f x y z k a ≤
        (24 * Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A (classicalClassIVRankinD A)) B * Real.exp (2*A^2*Real.exp (2*classicalClassIVRankinD A) + classicalClassIVRankinH A)) *
          V *
          (∑ r ∈ Finset.Icc 2 R0,
            (((r + 1 : ℕ) : ℝ)) *
              Real.exp (-8 * (r : ℝ))) := by
    unfold classicalClassIVOvercount
    change
      (∑ r ∈ Finset.Icc 2 R0,
        classicalClassIVShellOvercount f x y z k a
          (classIVShellUpper z r) (classIVShellLower z r)) ≤ _
    calc
      (∑ r ∈ Finset.Icc 2 R0,
        classicalClassIVShellOvercount f x y z k a
          (classIVShellUpper z r) (classIVShellLower z r))
          ≤
        ∑ r ∈ Finset.Icc 2 R0,
          (24 * Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A (classicalClassIVRankinD A)) B * Real.exp (2*A^2*Real.exp (2*classicalClassIVRankinD A) + classicalClassIVRankinH A)) *
            ((((r + 1 : ℕ) : ℝ)) * Real.exp (-8 * (r : ℝ))) *
            V :=
        Finset.sum_le_sum fun r hr => hpoint r hr
      _ =
        (24 * Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A (classicalClassIVRankinD A)) B * Real.exp (2*A^2*Real.exp (2*classicalClassIVRankinD A) + classicalClassIVRankinH A)) *
          V *
          (∑ r ∈ Finset.Icc 2 R0,
            (((r + 1 : ℕ) : ℝ)) *
              Real.exp (-8 * (r : ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
  have hsmall : 0 ≤ Shiu.smallPrimeConstant
      (Shiu.fixedPrimePowerCutoff A (classicalClassIVRankinD A)) B := by
    have h := Shiu.small_prime_product_uniform
      (Shiu.fixedPrimePowerCutoff A (classicalClassIVRankinD A)) B
      ∅ (fun _ => (0 : ℝ)) hB (by simp) (by simp) (by simp)
    have h1 : (1 : ℝ) ≤ Shiu.smallPrimeConstant
      (Shiu.fixedPrimePowerCutoff A (classicalClassIVRankinD A)) B := by
      simpa using h
    linarith
  have hdec := classical_classIV_decay_sum_le_four R0
  calc
    classicalClassIVOvercount f x y z k a
        ≤
      (24 * Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A (classicalClassIVRankinD A)) B * Real.exp (2*A^2*Real.exp (2*classicalClassIVRankinD A) + classicalClassIVRankinH A)) *
        V *
        (∑ r ∈ Finset.Icc 2 R0,
          (((r + 1 : ℕ) : ℝ)) *
            Real.exp (-8 * (r : ℝ))) := hsum
    _ ≤
      (24 * Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A (classicalClassIVRankinD A)) B * Real.exp (2*A^2*Real.exp (2*classicalClassIVRankinD A) + classicalClassIVRankinH A)) *
        V * 4 := by
      have hcoef : 0 ≤ 24 * Shiu.smallPrimeConstant
          (Shiu.fixedPrimePowerCutoff A (classicalClassIVRankinD A)) B *
          Real.exp (2*A^2*Real.exp (2*classicalClassIVRankinD A) + classicalClassIVRankinH A) := by
        positivity
      exact mul_le_mul_of_nonneg_left hdec (mul_nonneg hcoef hB0)
    _ =
      classicalShiuClassIVConstant A B * V := by
      dsimp [classicalShiuClassIVConstant]
      ring
    _ =
      classicalShiuClassIVConstant A B *
        ((((y : ℝ)) /
            ((k.totient : ℝ) * Real.log (z : ℝ)) +
          (z : ℝ) ^ 2) *
          Real.exp (primeMass f z k)) := by rfl

#print axioms classical_shiu_classIV_bound
end PaperB.M4B
