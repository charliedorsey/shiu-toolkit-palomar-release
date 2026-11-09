module

public import ShiuPublic.ClassicalRankinCorrection
public import ShiuPublic.VaelisClassIVShellRankin

public import ChallengeDefs.Rankin

public section

namespace PaperB.M4B
open scoped BigOperators
theorem classical_shell_geometric_rankin_bound
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
theorem classical_primeRankinCorrection_le_endpoint_rpow
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    {P k : ℕ} {ε : ℝ}
    (hP : 2 ≤ P) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    primeRankinCorrection f P k ε ≤
      ((4 * A * Real.log 4) / Real.log 2) * (P : ℝ) ^ ε := by
  have hdy :=
    classical_primeRankinCorrection_le_dyadic hf P k hε0.le hε1
  have hgeom := classical_shell_geometric_rankin_bound hP hε0 hε1
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ 2 * A * Real.log 4 := by
    exact mul_nonneg (mul_nonneg (by norm_num) hf.A_nonnegative) hlog4
  calc
    primeRankinCorrection f P k ε
        ≤ (A * ε) *
          (2 * Real.log 4 *
            ∑ j ∈ Finset.range (Nat.log 2 P + 1),
              (((2 ^ j : ℕ) : ℝ)) ^ ε) := hdy
    _ = (2 * A * Real.log 4) *
          (ε * ∑ j ∈ Finset.range (Nat.log 2 P + 1),
            (((2 ^ j : ℕ) : ℝ)) ^ ε) := by ring
    _ ≤ (2 * A * Real.log 4) *
          ((2 / Real.log 2) * (P : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left hgeom hA
    _ = ((4 * A * Real.log 4) / Real.log 2) *
          (P : ℝ) ^ ε := by ring


-- Shared Mathlib-only source definition: ChallengeDefs.Rankin.classicalClassIVRankinD

-- Shared Mathlib-only source definition: ChallengeDefs.Rankin.classicalClassIVRankinH

/-- Endpoint form of the Class-IV Rankin budget. The fixed-envelope weight
loss is cancelled by the square-root tail, leaving an additional exp(-8r)
shell decay and only an A-dependent scalar. -/
theorem classical_classIV_rankin_budget_of_endpoints
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    {z p k r : ℕ}
    (hr : 2 ≤ r) (hp : 2 ≤ p) (hpr : p ^ r ≤ z)
    (hzsqrt : 1 ≤ Nat.sqrt z)
    (hlarge : Real.exp (classicalClassIVRankinD A) ≤ (p : ℝ)) :
    ∃ ε : ℝ,
      0 ≤ ε ∧ ε ≤ 1 ∧
      primeRankinCorrection f p k ε -
          ε * Real.log ((Nat.sqrt z : ℕ) : ℝ) ≤
        -(320 * (r : ℝ) * Real.log (1 + A) +
            8 * (r : ℝ) - classicalClassIVRankinH A) := by
  let D : ℝ := classicalClassIVRankinD A
  let H : ℝ := classicalClassIVRankinH A
  let ε : ℝ := D / Real.log (p : ℝ)
  have hbase : (1 : ℝ) ≤ 1 + A := by
    linarith [hf.A_nonnegative]
  have hlogbase : 0 ≤ Real.log (1 + A) :=
    Real.log_nonneg hbase
  have hD : 0 < D := by
    dsimp [D, classicalClassIVRankinD]
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
    classical_primeRankinCorrection_le_endpoint_rpow
      (k := k) hf hp hε0 hε1
  have hcorr :
      primeRankinCorrection f p k ε ≤ H := by
    dsimp [H, classicalClassIVRankinH]
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
      320 * (r : ℝ) * Real.log (1 + A) +
          8 * (r : ℝ) ≤
        ε * Real.log ((Nat.sqrt z : ℕ) : ℝ) := by
    calc
      320 * (r : ℝ) * Real.log (1 + A) +
          8 * (r : ℝ)
          = D * (r : ℝ) / 3 := by
            dsimp [D, classicalClassIVRankinD]
            ring
      _ ≤ ε * Real.log ((Nat.sqrt z : ℕ) : ℝ) := hDscale
  refine ⟨ε, hε0.le, hε1, ?_⟩
  change primeRankinCorrection f p k ε -
      ε * Real.log ((Nat.sqrt z : ℕ) : ℝ) ≤
    -(320 * (r : ℝ) * Real.log (1 + A) +
        8 * (r : ℝ) - H)
  linarith

#print axioms classical_primeRankinCorrection_le_endpoint_rpow
#print axioms classical_classIV_rankin_budget_of_endpoints
end PaperB.M4B
