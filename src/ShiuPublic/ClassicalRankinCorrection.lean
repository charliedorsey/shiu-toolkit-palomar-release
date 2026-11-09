module

public import ShiuPublic.PrimePowerEnvelope
public import PaperB.M4B.ShiuSmoothTail

public section

namespace PaperB.M4B
open scoped BigOperators
open Shiu

theorem classical_primeRankinCorrection_le_weighted
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : ClassicalEnvelope f A)
    (Y k : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) :
    primeRankinCorrection f Y k ε ≤
      (A * ε) * primeLogRpowMass Y ε := by
  classical
  let P : Finset ℕ := (Nat.primesLE Y).filter (fun p => ¬ p ∣ k)
  have hpoint : ∀ p ∈ P,
      f p * ((p : ℝ) ^ ε - 1) / (p : ℝ) ≤
        (A * ε) *
          (Real.log (p : ℝ) * (p : ℝ) ^ (ε - 1)) := by
    intro p hp
    have hpP := Finset.mem_filter.mp hp
    have hpprime : p.Prime := Nat.prime_of_mem_primesLE hpP.1
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.pos
    have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.one_le
    have hpow1 : (1 : ℝ) ≤ (p : ℝ) ^ ε :=
      Real.one_le_rpow hp1R hε0
    have hsub0 : 0 ≤ (p : ℝ) ^ ε - 1 := sub_nonneg.mpr hpow1
    have hlog0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1R
    have hself :=
      Real.self_sub_one_le_mul_log
        (Real.rpow_nonneg hpR.le ε)
    have hsub :
        (p : ℝ) ^ ε - 1 ≤
          ε * Real.log (p : ℝ) * (p : ℝ) ^ ε := by
      calc
        (p : ℝ) ^ ε - 1
            ≤ (p : ℝ) ^ ε * Real.log ((p : ℝ) ^ ε) := hself
        _ = ε * Real.log (p : ℝ) * (p : ℝ) ^ ε := by
          rw [Real.log_rpow hpR]
          ring
    have hq0 :
        0 ≤ ((p : ℝ) ^ ε - 1) / (p : ℝ) :=
      div_nonneg hsub0 hpR.le
    have hfp :
        f p * (((p : ℝ) ^ ε - 1) / (p : ℝ)) ≤
          A * (((p : ℝ) ^ ε - 1) / (p : ℝ)) :=
      mul_le_mul_of_nonneg_right ((by simpa using hf.prime_power p 1 hpprime (by omega))) hq0
    have hdiv :
        ((p : ℝ) ^ ε - 1) / (p : ℝ) ≤
          (ε * Real.log (p : ℝ) * (p : ℝ) ^ ε) / (p : ℝ) :=
      (div_le_div_iff_of_pos_right hpR).2 hsub
    calc
      f p * ((p : ℝ) ^ ε - 1) / (p : ℝ)
          = f p * (((p : ℝ) ^ ε - 1) / (p : ℝ)) := by ring
      _ ≤ A * (((p : ℝ) ^ ε - 1) / (p : ℝ)) := hfp
      _ ≤ A *
          ((ε * Real.log (p : ℝ) * (p : ℝ) ^ ε) / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv hf.A_nonnegative
      _ = (A * ε) *
          (Real.log (p : ℝ) * (p : ℝ) ^ (ε - 1)) := by
        rw [Real.rpow_sub hpR, Real.rpow_one]
        field_simp [hpR.ne']
  have hnonneg :
      ∀ p ∈ Nat.primesLE Y,
        0 ≤ (A * ε) *
          (Real.log (p : ℝ) * (p : ℝ) ^ (ε - 1)) := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primesLE hp
    have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.one_le
    exact mul_nonneg
      (mul_nonneg hf.A_nonnegative hε0)
      (mul_nonneg (Real.log_nonneg hp1R)
        (Real.rpow_nonneg (by positivity) _))
  unfold primeRankinCorrection primeLogRpowMass
  change
    (∑ p ∈ P, f p * ((p : ℝ) ^ ε - 1) / (p : ℝ)) ≤
      (A * ε) *
        ∑ p ∈ Nat.primesLE Y,
          Real.log (p : ℝ) * (p : ℝ) ^ (ε - 1)
  calc
    (∑ p ∈ P, f p * ((p : ℝ) ^ ε - 1) / (p : ℝ))
        ≤ ∑ p ∈ P,
            (A * ε) *
              (Real.log (p : ℝ) * (p : ℝ) ^ (ε - 1)) :=
      Finset.sum_le_sum fun p hp => hpoint p hp
    _ ≤ ∑ p ∈ Nat.primesLE Y,
          (A * ε) *
            (Real.log (p : ℝ) * (p : ℝ) ^ (ε - 1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun p hp _ => hnonneg p hp)
    _ = (A * ε) *
        ∑ p ∈ Nat.primesLE Y,
          Real.log (p : ℝ) * (p : ℝ) ^ (ε - 1) := by
      rw [Finset.mul_sum]


#print axioms classical_primeRankinCorrection_le_weighted
theorem classical_primeRankinCorrection_le_dyadic
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : ClassicalEnvelope f A)
    (Y k : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    primeRankinCorrection f Y k ε ≤
      (A * ε) *
        (2 * Real.log 4 *
          ∑ j ∈ Finset.range (Nat.log 2 Y + 1),
            (((2 ^ j : ℕ) : ℝ)) ^ ε) := by
  have hbridge :=
    classical_primeRankinCorrection_le_weighted hf Y k hε0
  have hmass := primeLogRpowMass_le_dyadic Y hε1
  exact hbridge.trans
    (mul_le_mul_of_nonneg_left hmass
      (mul_nonneg hf.A_nonnegative hε0))
#print axioms classical_primeRankinCorrection_le_dyadic
end PaperB.M4B
