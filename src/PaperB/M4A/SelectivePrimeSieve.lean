module

/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under the Apache License, Version 2.0, as described in the repository LICENSE.
Original source: Mathlib/NumberTheory/SelbergSieve.lean at
https://github.com/leanprover-community/mathlib4,
revision 56a005855ea17e0b0958f73ec801ae140b0a1679.
The finite lambda-squared identity and bounding proof here adapt Mathlib
sum_divisors_lambda_sq_larger_sum and upperMoebius_lambdaSquared.
Modified in 2026 for the Shiu Toolkit, under the direction of Charlie Dorsey,
with AI assistance, for selective AP sieve uses and local Lean 4.35 interfaces.
-/

public import PaperB.M4A.CoprimeHarmonicLog
public import PaperB.M4A.APDivCount

public section

open scoped BigOperators ArithmeticFunction.zeta
open Finset Nat Real ArithmeticFunction

noncomputable section

namespace PaperB
namespace M4A

private theorem sum_divisors_lambdaSquared_larger
    (P : ℕ) (hP : P ≠ 0) (f : ℕ → ℕ → ℕ → ℝ) :
    (∑ d ∈ P.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
      if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
    (∑ d ∈ P.divisors, ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors,
      if d = Nat.lcm d1 d2 then f d1 d2 d else 0) := by
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.mem_divisors] at hd
  suffices ∀ d1 d2,
      (d1 ∣ d ∧ d2 ∣ d ∧ d = d1.lcm d2) = (d = d1.lcm d2) by
    simp_rw [← Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, Finset.sum_filter,
      ite_sum_zero, ← ite_and, this]
  simp +contextual [← and_assoc, Nat.dvd_lcm_left, Nat.dvd_lcm_right]

private theorem abs_lambdaSquared_le_pair_mass
    (w : ℕ → ℝ) (d : ℕ) :
    |BoundingSieve.lambdaSquared w d| ≤
      ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
        if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 := by
  unfold BoundingSieve.lambdaSquared
  calc
    |∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
        if d = Nat.lcm d1 d2 then w d1 * w d2 else 0|
        ≤ ∑ d1 ∈ d.divisors,
            |∑ d2 ∈ d.divisors,
              if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| := by
          apply abs_sum_le_sum_abs
    _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
          |if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| := by
          gcongr with d1 hd1
          apply abs_sum_le_sum_abs
    _ = ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
          if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 := by
          apply Finset.sum_congr rfl
          intro d1 hd1
          apply Finset.sum_congr rfl
          intro d2 hd2
          by_cases h : d = Nat.lcm d1 d2 <;> simp [h, abs_mul]

private theorem sum_abs_lambdaSquared_le_square_sum_abs
    (P : ℕ) (hP : P ≠ 0) (w : ℕ → ℝ) :
    (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d|) ≤
      (∑ d ∈ P.divisors, |w d|) ^ 2 := by
  calc
    (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d|)
        ≤ ∑ d ∈ P.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
            if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 := by
          gcongr with d hd
          exact abs_lambdaSquared_le_pair_mass w d
    _ = ∑ d ∈ P.divisors, ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors,
            if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 :=
          sum_divisors_lambdaSquared_larger P hP
            (fun d1 d2 _ => |w d1| * |w d2|)
    _ = ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors, |w d1| * |w d2| := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d1 hd1
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d2 hd2
          rw [Finset.sum_ite_eq_of_mem']
          rw [Nat.mem_divisors, Nat.lcm_dvd_iff]
          exact ⟨⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩, hP⟩
    _ = (∑ d ∈ P.divisors, |w d|) ^ 2 := by
          rw [sq, Finset.sum_mul_sum]

private theorem sum_abs_weights_le_z
    (s : SelbergSieve) (z : ℕ) (hz : 1 ≤ z)
    (hlevel : s.level = (z : ℝ) ^ 2) :
    (∑ d ∈ s.prodPrimes.divisors, |selbergWeights s d|) ≤ (z : ℝ) := by
  have hsupport :
      ∀ d ∈ s.prodPrimes.divisors, ¬ d ≤ z → selbergWeights s d = 0 := by
    intro d hd hdz
    apply selbergWeights_eq_zero
    rw [hlevel]
    have hpow : z ^ 2 < d ^ 2 :=
      Nat.pow_lt_pow_left (lt_of_not_ge hdz) (by decide)
    exact_mod_cast hpow
  calc
    (∑ d ∈ s.prodPrimes.divisors, |selbergWeights s d|)
        = ∑ d ∈ s.prodPrimes.divisors,
            if d ≤ z then |selbergWeights s d| else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hdz : d ≤ z
          · simp [hdz]
          · simp [hdz, hsupport d hd hdz]
    _ ≤ ∑ d ∈ s.prodPrimes.divisors, if d ≤ z then (1 : ℝ) else 0 := by
          gcongr with d hd
          split_ifs
          · exact selbergWeights_abs_le_one s d
          · rfl
    _ = ((s.prodPrimes.divisors.filter (fun d => d ≤ z)).card : ℝ) := by
          rw [← Finset.sum_filter]
          simp
    _ ≤ (z : ℝ) := by
          norm_cast
          have hsub :
              s.prodPrimes.divisors.filter (fun d => d ≤ z) ⊆ Finset.Icc 1 z := by
            intro d hd
            rw [Finset.mem_filter] at hd
            rw [Finset.mem_Icc]
            refine ⟨?_, hd.2⟩
            exact Nat.one_le_iff_ne_zero.mpr <|
              ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero (dvd_of_mem_divisors hd.1)
          have hcard := Finset.card_le_card hsub
          simpa [hz] using hcard

/-- Amended C3 finite pair-count core: at level z^2 the lambda-squared
coefficient mass is at most z^2. -/
theorem selbergMuPlus_l1_le_sq
    (s : SelbergSieve) (z : ℕ) (hz : 1 ≤ z)
    (hlevel : s.level = (z : ℝ) ^ 2) :
    (∑ d ∈ s.prodPrimes.divisors, |selbergMuPlus s d|) ≤ (z : ℝ) ^ 2 := by
  rw [selbergMuPlus]
  refine (sum_abs_lambdaSquared_le_square_sum_abs
    s.prodPrimes s.prodPrimes_ne_zero (selbergWeights s)).trans ?_
  gcongr
  exact sum_abs_weights_le_z s z hz hlevel


/-- Reduced-progression Selberg sieve used in C3. -/
@[expose] def selectiveAPSieve
    (x y k a z : ℕ) (hz : 1 ≤ z) : SelbergSieve := {
  support := (Finset.Ioc (x - y) x).filter (fun n => n ≡ a [MOD k])
  prodPrimes := selectedPrimeProduct z k
  prodPrimes_squarefree := selectedPrimeProduct_squarefree z k
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := (y : ℝ) / (k : ℝ)
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp [if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ => by
    simp [hp.ne_zero, inv_lt_one_iff₀, hp.one_lt]
  level := (z : ℝ) ^ 2
  one_le_level := by
    have hzR : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    nlinarith [sq_nonneg ((z : ℝ) - 1)]
}

theorem selectiveAPSieve_nu
    (x y k a z d : ℕ) (hz : 1 ≤ z) (hd : d ≠ 0) :
    (selectiveAPSieve x y k a z hz).nu d = ((d : ℝ)⁻¹) := by
  simp [selectiveAPSieve, ArithmeticFunction.pdiv_apply,
    ArithmeticFunction.zeta_apply_ne hd, hd]

theorem selectiveAPSieve_multSum
    (x y k a z d : ℕ) (hz : 1 ≤ z) :
    (selectiveAPSieve x y k a z hz).multSum d =
      (apDivCount x y k a d : ℝ) := by
  simp [BoundingSieve.multSum, selectiveAPSieve, apDivCount,
    Finset.filter_filter, and_assoc, and_left_comm, and_comm]

theorem selectiveAPSieve_rem_abs_le_four
    (x y k a z d : ℕ)
    (hyx : y ≤ x) (hk : 0 < k) (hz : 1 ≤ z)
    (hdP : d ∣ selectedPrimeProduct z k) :
    |(selectiveAPSieve x y k a z hz).rem d| ≤ 4 := by
  have hd0 : d ≠ 0 :=
    ne_zero_of_dvd_ne_zero (selectedPrimeProduct_ne_zero z k) hdP
  have hd : 0 < d := Nat.pos_of_ne_zero hd0
  have hdk : d.Coprime k :=
    (selectedPrimeProduct_coprime_modulus z k).coprime_dvd_left hdP
  have hkd : k.Coprime d := hdk.symm
  obtain ⟨C, hC, hEq⟩ :=
    apDivCount_realApprox x y k a d hyx hk hd hkd
  rw [BoundingSieve.rem, selectiveAPSieve_multSum, selectiveAPSieve_nu _ _ _ _ _ _ hz hd0]
  dsimp [selectiveAPSieve]
  rw [hEq]
  have hident :
      (y : ℝ) / ((k : ℝ) * (d : ℝ)) =
        ((d : ℝ)⁻¹) * ((y : ℝ) / (k : ℝ)) := by
    field_simp [hk.ne', hd0]
  rw [hident]
  ring_nf
  exact hC

/-- Amended C3 explicit remainder court: the AP error is at most 4 z^2. -/
theorem selectiveAPSieve_errSum_le_four_sq
    (x y k a z : ℕ)
    (hyx : y ≤ x) (hk : 0 < k) (hz : 1 ≤ z) :
    (selectiveAPSieve x y k a z hz).errSum
        (selbergMuPlus (selectiveAPSieve x y k a z hz)) ≤
      4 * (z : ℝ) ^ 2 := by
  let s := selectiveAPSieve x y k a z hz
  have hl1 :
      (∑ d ∈ s.prodPrimes.divisors, |selbergMuPlus s d|) ≤
        (z : ℝ) ^ 2 := by
    exact selbergMuPlus_l1_le_sq s z hz rfl
  rw [BoundingSieve.errSum]
  calc
    (∑ d ∈ s.prodPrimes.divisors, |selbergMuPlus s d| * |s.rem d|)
        ≤ ∑ d ∈ s.prodPrimes.divisors, |selbergMuPlus s d| * 4 := by
          gcongr with d hd
          exact selectiveAPSieve_rem_abs_le_four x y k a z d hyx hk hz
            (by
              change d ∣ selectedPrimeProduct z k
              exact dvd_of_mem_divisors hd)
    _ = 4 * ∑ d ∈ s.prodPrimes.divisors, |selbergMuPlus s d| := by
          rw [Finset.mul_sum]
          ring_nf
    _ ≤ 4 * (z : ℝ) ^ 2 := by
          gcongr


/-- C3 target: the reduced arithmetic progression sieve has the quantitative
Selberg bound required by Shiu's Lemma 2 foundation. -/
theorem selectivePrimeSieve_bound
    (x y k a z : ℕ)
    (hyx : y ≤ x) (hk : 0 < k) (hz : 2 ≤ z) :
    (selectiveAPSieve x y k a z (by omega)).siftedSum ≤
      (y : ℝ) / ((k.totient : ℝ) * Real.log z) +
        4 * (z : ℝ) ^ 2 := by
  have hz1 : 1 ≤ z := by omega
  let s := selectiveAPSieve x y k a z hz1
  have hnu : ∀ n, s.nu n = ((n : ℝ)⁻¹) := by
    intro n
    dsimp [s, selectiveAPSieve]
    by_cases hn : n = 0
    · simp [hn]
    · simp [ArithmeticFunction.pdiv_apply, ArithmeticFunction.zeta_apply_ne hn, hn]
  have hcop :
      ((k.totient : ℝ) / (k : ℝ)) * Real.log (z + 1) ≤
        coprimeHarmonic z k :=
    coprimeHarmonic_log_lower z k hk
  have hsel :
      coprimeHarmonic z k ≤ selbergBoundSum s := by
    simpa [s, coprimeHarmonic] using
      (selectedPrimeBoundSum_lower s z k rfl rfl hnu)
  have hden :
      ((k.totient : ℝ) / (k : ℝ)) * Real.log (z + 1) ≤
        selbergBoundSum s :=
    hcop.trans hsel
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hphiNat : 0 < k.totient := Nat.totient_pos.mpr hk
  have hphi : (0 : ℝ) < (k.totient : ℝ) := by exact_mod_cast hphiNat
  have hzgt : (1 : ℝ) < (z : ℝ) := by
    exact_mod_cast (show 1 < z by omega)
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos hzgt
  have hlogmono :
      Real.log (z : ℝ) ≤ Real.log ((z + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log (by positivity)
    norm_cast
    omega
  have hlogsucc : 0 < Real.log ((z : ℝ) + 1) := by
    simpa [Nat.cast_add, Nat.cast_one] using hlogz.trans_le hlogmono
  have hratio : 0 < (k.totient : ℝ) / (k : ℝ) :=
    div_pos hphi hkR
  have hdenpos :
      0 < ((k.totient : ℝ) / (k : ℝ)) * Real.log (z + 1) := by
    exact mul_pos hratio hlogsucc
  have hmass : 0 ≤ s.totalMass := by
    dsimp [s, selectiveAPSieve]
    positivity
  have hmain :
      s.totalMass / selbergBoundSum s ≤
        (y : ℝ) / ((k.totient : ℝ) * Real.log z) := by
    calc
      s.totalMass / selbergBoundSum s ≤
          s.totalMass /
            (((k.totient : ℝ) / (k : ℝ)) * Real.log (z + 1)) := by
        exact div_le_div_of_nonneg_left hmass hdenpos hden
      _ = (y : ℝ) /
          ((k.totient : ℝ) * Real.log (z + 1)) := by
        dsimp [s, selectiveAPSieve]
        field_simp [hkR.ne', hphi.ne', hlogsucc.ne']
      _ ≤ (y : ℝ) /
          ((k.totient : ℝ) * Real.log z) := by
        apply div_le_div_of_nonneg_left (by positivity)
          (mul_pos hphi hlogz)
        exact mul_le_mul_of_nonneg_left
          (by simpa [Nat.cast_add, Nat.cast_one] using hlogmono) hphi.le
  have herr :
      s.errSum (selbergMuPlus s) ≤ 4 * (z : ℝ) ^ 2 := by
    simpa [s] using
      selectiveAPSieve_errSum_le_four_sq x y k a z hyx hk hz1
  have hsieve := siftedSum_le_optimal s
  change s.siftedSum ≤
    (y : ℝ) / ((k.totient : ℝ) * Real.log z) + 4 * (z : ℝ) ^ 2
  exact hsieve.trans (add_le_add hmain herr)


end M4A
end PaperB
