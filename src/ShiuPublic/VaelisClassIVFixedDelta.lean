module

public import ShiuPublic.VaelisClassIVEndpointCorrection

public section

namespace PaperB.M4B
open scoped BigOperators
theorem classical_classIV_rankin_budget_fixed_delta
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    {z p k r : ℕ}
    (hr : 2 ≤ r) (hp : 2 ≤ p) (hpr : p ^ r ≤ z)
    (hzsqrt : 1 ≤ Nat.sqrt z)
    (hlarge : Real.exp (classicalClassIVRankinD A) ≤ (p : ℝ)) :
    0 ≤ classicalClassIVRankinD A / Real.log (p : ℝ) ∧
    classicalClassIVRankinD A / Real.log (p : ℝ) ≤ 1 ∧
      primeRankinCorrection f p k (classicalClassIVRankinD A / Real.log (p : ℝ)) -
          (classicalClassIVRankinD A / Real.log (p : ℝ)) * Real.log ((Nat.sqrt z : ℕ) : ℝ) ≤
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
  refine ⟨hε0.le, hε1, ?_⟩
  change primeRankinCorrection f p k ε -
      ε * Real.log ((Nat.sqrt z : ℕ) : ℝ) ≤
    -(320 * (r : ℝ) * Real.log (1 + A) +
        8 * (r : ℝ) - H)
  linarith

#print axioms classical_classIV_rankin_budget_fixed_delta
end PaperB.M4B
