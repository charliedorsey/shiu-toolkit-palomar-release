module

public import ShiuPublic.LargePrimeRelativeProduct
public import ShiuPublic.UniformQuadraticCorrection

public section

/-! Uniform large-prime Euler product with first-prime mass and explicit
quadratic error, independently of the shell index or modulus. -/

namespace Shiu
open scoped BigOperators

/-- The exact first-prime decomposition used by the Shiu Class IV correction. -/
theorem shifted_first_prime_mass
    (f : ℕ → ℝ) (q : ℕ) (δ : ℝ) (hq : 0 < q) :
    f q / (q : ℝ) ^ (1-δ) =
      f q / (q : ℝ) + f q * ((q : ℝ)^δ-1) / (q : ℝ) := by
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [Real.rpow_sub hqr, Real.rpow_one]
  have hpow : 0 < (q : ℝ)^δ := Real.rpow_pos_of_pos hqr _
  field_simp
  ring

/-- The finite large-prime product carries just the first-prime mass
and a *uniform* quadratic error. -/
theorem classical_large_prime_mass_uniform
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : ClassicalEnvelope f A)
    (S : Finset ℕ) (N P : ℕ) (D δ : ℝ)
    (hP : 1 ≤ P)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≤ P)
    (hgate : ∀ q ∈ S, 2*A ≤ (q : ℝ)^(1-δ))
    (hpow : ∀ q ∈ S, (q : ℝ)^δ ≤ Real.exp D) :
    (∏ q ∈ S, ∑ j ∈ Finset.range (N+2),
       f (q^j)/(q : ℝ)^((j : ℝ)*(1-δ))) ≤
      Real.exp ((∑ q ∈ S, (f q/(q : ℝ) +
        f q*((q : ℝ)^δ-1)/(q : ℝ))) +
        2*A^2*Real.exp (2*D)) := by
  have hprod := classical_large_prime_relative_product hf S N δ
    (fun q hq => (hS q hq).1) hgate
  have hquad := shifted_quadratic_uniform S P A D δ hf.A_nonnegative
    hP (fun q hq => ⟨(hS q hq).1.two_le, (hS q hq).2⟩) hpow
  have hmass : (∑ q ∈ S, f q/(q : ℝ)^(1-δ)) =
      ∑ q ∈ S, (f q/(q : ℝ) +
        f q*((q : ℝ)^δ-1)/(q : ℝ)) := by
    apply Finset.sum_congr rfl
    intro q hq
    exact shifted_first_prime_mass (fun x => f x) q δ (hS q hq).1.pos
  calc
    _ ≤ Real.exp (∑ q ∈ S,
         (f q/(q : ℝ)^(1-δ) +
          2*(A/(q : ℝ)^(1-δ))^2)) := hprod
    _ = Real.exp ((∑ q ∈ S, f q/(q : ℝ)^(1-δ)) +
         (∑ q ∈ S, 2*(A/(q : ℝ)^(1-δ))^2)) := by
           rw [Finset.sum_add_distrib]
    _ ≤ Real.exp ((∑ q ∈ S, f q/(q : ℝ)^(1-δ)) +
         2*A^2*Real.exp (2*D)) :=
          Real.exp_le_exp.mpr (add_le_add_right hquad _)
    _ = _ := by rw [hmass]

#print axioms Shiu.shifted_first_prime_mass
#print axioms Shiu.classical_large_prime_mass_uniform
end Shiu
