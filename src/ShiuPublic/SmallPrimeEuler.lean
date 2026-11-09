module

public import ShiuPublic.PrimePowerEnvelope

public section

namespace Shiu
open Finset

/-- Finite upper bound for a small prime Euler factor using the
subpower growth estimate rather than a geometric A/p assumption. -/
theorem small_prime_euler_finite
    (f : ℕ → ℝ) (p N : ℕ)
    (hp : 2 ≤ p) (B ε δ : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hscale : δ + ε < 1)
    (hfgrowth : ∀ m : ℕ, 1 ≤ m →
      f (p ^ m) ≤ B * ((p : ℝ) ^ ((m : ℝ) * ε))) :
    (∑ j ∈ Finset.range N,
      f (p ^ (j+1)) / (p : ℝ) ^ ((j+1 : ℕ) * (1-δ))) ≤
        B * (∑ j ∈ Finset.range N,
          ((p : ℝ) ^ (-(1-δ-ε))) ^ (j+1)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hp)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hpd : 0 < (p : ℝ) ^ ((j+1 : ℕ) * (1-δ)) :=
    Real.rpow_pos_of_pos hp0 _
  have hf := hfgrowth (j+1) (by omega)
  have heq : ((p : ℝ) ^ (-(1-δ-ε))) ^ (j+1) =
      (p : ℝ) ^ ((j+1 : ℕ) * ε) /
        (p : ℝ) ^ ((j+1 : ℕ) * (1-δ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, div_eq_mul_inv,
      ← Real.rpow_neg hp0.le, ← Real.rpow_add hp0]
    congr 1
    push_cast
    ring
  rw [heq]
  exact (div_le_div_of_nonneg_right hf hpd.le).trans_eq (by ring)

/-- Uniform finite Euler factor control with a geometric denominator. -/
theorem small_prime_euler_geometric
    (f : ℕ → ℝ) (p N : ℕ) (hp : 2 ≤ p)
    (B ε δ : ℝ) (hB : 0 ≤ B)
    (hδ : 0 ≤ δ) (hscale : δ + ε < 1)
    (hfgrowth : ∀ m : ℕ, 1 ≤ m →
      f (p ^ m) ≤ B * ((p : ℝ) ^ ((m : ℝ) * ε))) :
    (∑ j ∈ Finset.range N,
      f (p ^ (j+1)) / (p : ℝ) ^ ((j+1 : ℕ) * (1-δ))) ≤
      B * (1 / (1 - (p : ℝ) ^ (-(1-δ-ε)))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  let t := (p : ℝ) ^ (-(1-δ-ε))
  have ht0 : 0 ≤ t := Real.rpow_nonneg hp0.le _
  have ht1 : t < 1 := by
    dsimp [t]
    have he : -(1-δ-ε) < 0 := by linarith
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp) he
  have hsum : (∑ j ∈ Finset.range N, t^(j+1)) ≤ 1 / (1-t) := by
    have hgeo : (∑ j ∈ Finset.range N, t ^ j) * (1-t) = 1-t^N := geom_sum_mul_neg t N
    have hh : 0 ≤ t^N := pow_nonneg ht0 N
    have hb : 0 < 1-t := sub_pos.mpr ht1
    have hl : (∑ j ∈ Finset.range N, t ^ (j+1)) ≤
      ∑ j ∈ Finset.range N, t ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      rw [pow_succ]
      nlinarith [mul_nonneg (pow_nonneg ht0 j) (sub_nonneg.mpr ht1.le)]
    have hg : (∑ j ∈ Finset.range N, t ^ j) ≤ 1/(1-t) := by
      apply (le_div_iff₀ hb).mpr
      nlinarith
    exact hl.trans hg
  calc
    _ ≤ B * (∑ j ∈ Finset.range N, t^(j+1)) := small_prime_euler_finite f p N hp B ε δ hB hδ hscale hfgrowth
    _ ≤ B * (1/(1-t)) := mul_le_mul_of_nonneg_left hsum hB

#print axioms Shiu.small_prime_euler_finite
#print axioms Shiu.small_prime_euler_geometric
