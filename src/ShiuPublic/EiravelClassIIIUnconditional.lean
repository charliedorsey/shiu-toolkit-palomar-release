module

public import ShiuPublic.EiravelClassIIIRankin
public import ShiuPublic.EiravelClassIIIEulerMass
public import ShiuPublic.EiravelClassIIIEventualMass
public import ShiuPublic.CorvethClassicalClassIIIWeighted

public section

open scoped BigOperators
open Finset Nat Real

namespace PaperB.M4B

/-- The exact unrestricted Class III cardinality is EVENTUALLY at most
z^(1/4). Not valid for all x; the threshold is compulsory. The theorem
is uniform in z and k, retains all prime powers and all source filters. -/
theorem eiravel_classIII_card_quarter_eventually :
    ∃ X0 : ℕ, ∀ x z k : ℕ,
      X0 ≤ x → x < z ^ 160 →
        ((corvethClassicalClassIIIFactors x z k).card : ℝ) ≤
          (z : ℝ) ^ (1/4 : ℝ) := by
  obtain ⟨X1, hmass⟩ := eiravel_prime_mass_fixed_eta_absorption
  refine ⟨max X1 2, ?_⟩
  intro x z k hx hxz
  have hx1 : X1 ≤ x := (le_max_left X1 2).trans hx
  have hx2 : 2 ≤ x := (le_max_right X1 2).trans hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hzposNat : 0 < z := by
    by_contra hz
    have : z = 0 := Nat.eq_zero_of_not_pos hz
    subst z
    simp at hxz
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hzposNat
  have hxzR : (x : ℝ) < (z : ℝ) ^ 160 := by exact_mod_cast hxz
  have hlogxz : Real.log (x : ℝ) < 160 * Real.log (z : ℝ) := by
    rw [Real.log_lt_iff_lt_exp hxpos]
    calc
      (x : ℝ) < (z : ℝ) ^ 160 := hxzR
      _ = Real.exp (160 * Real.log (z : ℝ)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hzpos]
        congr 1
        ring
  let S : Finset ℕ := Nat.primesLE (shiuLogLogSmoothThreshold x)
  have hS : ∀ p ∈ S, p.Prime :=
    fun p hp => Nat.prime_of_mem_primesLE hp
  let eta : ℝ := (1/8 : ℝ)
  have heta : 0 < eta := by dsimp [eta]; norm_num
  let C : ℝ := eiravelEulerC
  have hC : 0 < C := eiravelEulerC_pos
  have hRank := Eiravel.corveth_full_power_classIII_rankin_at_z
    x z k hzposNat eta heta.le
  have hEuler := Eiravel.smooth_divisor_euler_mass_le
    S hS z hzposNat eta heta
  have hmass' :
      C * primeRankinMass (shiuLogLogSmoothThreshold x) eta ≤
        Real.log (x : ℝ) / 1280 := by
    simpa only [C, eta] using hmass x hx1
  have hlogbound :
      C * primeRankinMass (shiuLogLogSmoothThreshold x) eta ≤
        Real.log (z : ℝ) / 8 := by
    linarith [hmass']
  have hExp :
      Real.exp (C * primeRankinMass (shiuLogLogSmoothThreshold x) eta) ≤
        (z : ℝ) ^ (1/8 : ℝ) := by
    rw [Real.rpow_def_of_pos hzpos]
    apply Real.exp_le_exp.mpr
    dsimp [eta] at hlogbound
    linarith
  have hEuler' :
      (∑ n ∈ ((∏ p ∈ S, p) ^ z).divisors, (n : ℝ) ^ (-eta)) ≤
        Real.exp (C * primeRankinMass (shiuLogLogSmoothThreshold x) eta) := by
    simpa only [C, eta, S, eiravelEulerC, primeRankinMass] using hEuler
  calc
    ((corvethClassicalClassIIIFactors x z k).card : ℝ) ≤
      (z : ℝ) ^ eta *
      (∑ n ∈ ((∏ p ∈ S, p) ^ z).divisors, (n : ℝ) ^ (-eta)) := by
        simpa only [eta, S] using hRank
    _ ≤ (z : ℝ) ^ eta *
          Real.exp (C * primeRankinMass (shiuLogLogSmoothThreshold x) eta) :=
      mul_le_mul_of_nonneg_left hEuler' (Real.rpow_nonneg hzpos.le _)
    _ ≤ (z : ℝ) ^ eta * (z : ℝ) ^ (1/8 : ℝ) :=
      mul_le_mul_of_nonneg_left hExp (Real.rpow_nonneg hzpos.le _)
    _ = (z : ℝ) ^ (1/4 : ℝ) := by
      dsimp [eta]
      rw [← Real.rpow_add hzpos]
      norm_num

/-- Weighted original full-power S9 Class III bound, with the old
unrestricted hcard premise ELIMINATED in its mathematically valid eventual
region. Remaining hzabsorb is an independent original interval-size premise. -/
theorem eiravel_classIII_weighted_eventual_no_card :
    ∃ X0 : ℕ,
      ∀ {f : ArithmeticFunction ℝ} {A B : ℝ},
        Shiu.ClassicalEnvelope f A →
        0 ≤ B →
        (∀ n : ℕ, 1 ≤ n →
          f n ≤ B * (n : ℝ) ^ (1 / 1280 : ℝ)) →
        ∀ x y z k a : ℕ,
          X0 ≤ x → y ≤ x → x < z ^ 160 → 0 < k →
          (z : ℝ) ≤
            ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ) →
          corvethClassicalClassIIIWeightedOvercount f x y z k a ≤
            (10 * B) *
              (((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 8 : ℝ)) := by
  obtain ⟨X0,hcard⟩ := eiravel_classIII_card_quarter_eventually
  refine ⟨X0, ?_⟩
  intro f A B hf hB hgrowth x y z k a hx hyx hxz hk hzabsorb
  exact corveth_classical_classIII_weighted_of_card hf hB hgrowth
    x y z k a hyx hxz hk (hcard x z k hx hxz) hzabsorb

#print axioms eiravel_classIII_card_quarter_eventually
#print axioms eiravel_classIII_weighted_eventual_no_card

end PaperB.M4B
