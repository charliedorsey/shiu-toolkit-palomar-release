module

public import ShiuPublic.FiniteEulerDivisors
public import ShiuPublic.VaelisEulerUniformCutoff
public import PaperB.M4B.ShiuSmoothCount

public section

open scoped BigOperators ArithmeticFunction.zeta
open Finset Nat ArithmeticFunction

namespace Eiravel

/-!
The all-prime-power Euler budget, with an explicit positive fixed Rankin
exponent and no squarefree restriction.
-/

/-- Uniform geometric upper bound. The constant depends only on eta and the
least possible prime, not on the cutoff, the exponent vector, or p. -/
theorem truncated_geometric_uniform
    (eta : ℝ) (heta : 0 < eta)
    (p N : ℕ) (hp : p.Prime) :
    (∑ j ∈ Finset.range N, ((p : ℝ) ^ (-eta)) ^ j) ≤
      1 + ((1 - (2 : ℝ) ^ (-eta))⁻¹) * ((p : ℝ) ^ (-eta)) := by
  let r : ℝ := (p : ℝ) ^ (-eta)
  let r0 : ℝ := (2 : ℝ) ^ (-eta)
  have h0 : 0 ≤ r := by dsimp [r]; positivity
  have h1 : r ≤ r0 := by
    dsimp [r, r0]
    exact Real.rpow_le_rpow_of_nonpos
      (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
  have h2 : r0 < 1 := by
    dsimp [r0]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hr : r < 1 := lt_of_le_of_lt h1 h2
  have hD : 0 < 1-r := by linarith
  have hD0 : 0 < 1-r0 := by linarith
  have hsum :
      (∑ j ∈ Finset.range N, r ^ j) ≤ (1-r)⁻¹ := by
    have h := (summable_geometric_of_lt_one h0 hr).sum_le_tsum
      (Finset.range N) (fun j hj => pow_nonneg h0 _)
    simpa [tsum_geometric_of_lt_one h0 hr] using h
  have hdiv : r / (1-r) ≤ r / (1-r0) := by
    exact div_le_div_of_nonneg_left h0 hD0 (by linarith)
  calc
    (∑ j ∈ Finset.range N, ((p : ℝ) ^ (-eta)) ^ j)
        ≤ (1-r)⁻¹ := hsum
    _ = 1 + r / (1-r) := by
      field_simp
      ring
    _ ≤ 1 + r / (1-r0) := by simpa [add_comm] using (add_le_add_left hdiv 1)
    _ = 1 + (1-r0)⁻¹ * r := by ring
    _ = 1 + (1 - (2 : ℝ) ^ (-eta))⁻¹ * ((p : ℝ) ^ (-eta)) := rfl

/-- An exact local weight: all prime powers, including exponent zero,
are the truncated geometric series. -/
theorem zeta_local_rankin_sum
    (p N : ℕ) (hp : p.Prime) (eta : ℝ) :
    (∑ j ∈ Finset.range N,
      (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) (p ^ j)) /
        ((p ^ j : ℕ) : ℝ) ^ eta) =
      ∑ j ∈ Finset.range N, ((p : ℝ) ^ (-eta)) ^ j := by
  apply Finset.sum_congr rfl
  intro j hj
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hz :
    (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) (p ^ j)) = 1 := by
    simp [ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne (pow_ne_zero _ hp.ne_zero)]
  rw [hz, one_div, Nat.cast_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul hp0.le]
  rw [mul_comm (j : ℝ) eta, Real.rpow_mul hp0.le, Real.rpow_natCast, ← inv_pow, ← Real.rpow_neg hp0.le]

/-- The full prime-power divisor mass has a uniform exponential majorant
given by an elementary prime Rankin mass. -/
theorem smooth_divisor_euler_mass_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (X : ℕ) (hX : 0 < X) (eta : ℝ) (heta : 0 < eta) :
    (∑ n ∈ ((∏ p ∈ S, p) ^ X).divisors, (n : ℝ) ^ (-eta)) ≤
    Real.exp (((1 - (2 : ℝ) ^ (-eta))⁻¹) *
      ∑ p ∈ S, (p : ℝ) ^ (-eta)) := by
  let T : ℕ := (∏ p ∈ S, p) ^ X
  let C : ℝ := (1 - (2 : ℝ)^(-eta))⁻¹
  have hbase : 0 < ∏ p ∈ S, p := by
    apply Finset.prod_pos
    intro p hp
    exact (hS p hp).pos
  have hT : T ≠ 0 := pow_ne_zero _ hbase.ne'
  have hEuler :=
    Shiu.finite_euler_divisor_rankin
      (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ))
      (ArithmeticFunction.isMultiplicative_zeta.natCast)
      T hT eta
  have hprimes : T.primeFactors = S := by
    exact Shiu.bounded_smooth_base_primeFactors S hS X hX
  rw [hprimes] at hEuler
  have hsum :
      (∑ n ∈ T.divisors, (n : ℝ) ^ (-eta)) =
      ∑ n ∈ T.divisors,
        (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) n) /
          (n : ℝ) ^ eta := by
    apply Finset.sum_congr rfl
    intro n hn
    have hpos : n ≠ 0 := (Nat.pos_of_mem_divisors hn).ne'
    simp [ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne hpos,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ n)]
  have hloc : ∀ p ∈ S,
      (∑ j ∈ Finset.range (T.factorization p + 1),
        (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) (p ^ j)) /
          ((p ^ j : ℕ) : ℝ) ^ eta) ≤
        1 + C * (p : ℝ) ^ (-eta) := by
    intro p hp
    rw [zeta_local_rankin_sum p _ (hS p hp) eta]
    exact truncated_geometric_uniform eta heta p _ (hS p hp)
  have hPpos : ∀ p ∈ S, 0 ≤
      ∑ j ∈ Finset.range (T.factorization p + 1),
        (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) (p ^ j)) /
          ((p ^ j : ℕ) : ℝ) ^ eta := by
    intro p hp
    rw [zeta_local_rankin_sum p _ (hS p hp) eta]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    have hz : (2 : ℝ)^(-eta) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    positivity
  have hCpoint : ∀ p ∈ S, 0 ≤ C * (p : ℝ)^(-eta) := by
    intro p hp
    positivity
  calc
    (∑ n ∈ ((∏ p ∈ S, p) ^ X).divisors, (n : ℝ) ^ (-eta)) =
        ∏ p ∈ S, ∑ j ∈ Finset.range (T.factorization p + 1),
          (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) (p ^ j)) /
            ((p ^ j : ℕ) : ℝ) ^ eta := by
      rw [hsum, ← hEuler]
    _ ≤ ∏ p ∈ S, (1 + C * (p : ℝ) ^ (-eta)) := by
      exact Finset.prod_le_prod₀ hPpos hloc
    _ ≤ Real.exp (∑ p ∈ S, C * (p : ℝ) ^ (-eta)) :=
      Real.prod_one_add_le_exp_sum S (fun p => by
        by_cases hp : p ∈ S
        · exact hCpoint p hp
        · exact mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
    _ = Real.exp (C * ∑ p ∈ S, (p : ℝ) ^ (-eta)) := by rw [Finset.mul_sum]
    _ = Real.exp (((1 - (2 : ℝ) ^ (-eta))⁻¹) *
        ∑ p ∈ S, (p : ℝ)^(-eta)) := rfl

#print axioms Eiravel.truncated_geometric_uniform
#print axioms Eiravel.zeta_local_rankin_sum
#print axioms Eiravel.smooth_divisor_euler_mass_le

end Eiravel
