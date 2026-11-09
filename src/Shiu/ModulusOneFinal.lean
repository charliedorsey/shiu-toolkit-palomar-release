module

public import Shiu.ModulusOneNineCover
public import Shiu.ModulusOnePrimeNormalized
public import Shiu.ModulusOneRealGeometry

public section

/-!
# Unrestricted-with-respect-to-squarefree Shiu, modulus k=1

The estimate is deduced from the frozen fixed-quarter progression theorem,
not assumed from the historical manuscript. The nine-prime cover and its
eventual window, the exact residue partition, totient cancellation,
prime-mass monotonicity, and sign of the classical constant are all
independent certified suppliers.

No squarefree-support assumption. The growth bound with fixed B
remains independent of ClassicalEnvelope's existential growth field.
-/
namespace Shiu.API
open scoped BigOperators

/-- Fixed-quarter classical short-interval estimate at modulus one.
The constant is exactly nine times the original classical coefficient.
X0 depends on A,B and is chosen BEFORE f. -/
theorem classical_modulus_one_quarter (A B : ℝ) :
    ∃ X0 : ℕ, ∀ f : ArithmeticFunction ℝ,
      Shiu.ClassicalEnvelope f A →
      0 ≤ B →
      (∀ n : ℕ, 1 ≤ n →
        f n ≤ B * (n : ℝ) ^ (1 / 1280 : ℝ)) →
      ∀ x y : ℕ,
        X0 ≤ x →
        (x : ℝ) ^ (1 / 4 : ℝ) < (y : ℝ) →
        y ≤ x →
        (∑ n ∈ Finset.Ioc (x-y) x, f n) ≤
          9 * classicalConstant A B *
            ((y : ℝ) / Real.log (x : ℝ)) *
            Real.exp (PaperB.M4B.primeMass f x 1) := by
  obtain ⟨X0, hX⟩ := classical_filtered_prime_normalized A B
  refine ⟨max X0 ((512 ^ 4) ^ 4), ?_⟩
  intro f hf hB hgrowth x y hx hxy hyx
  have hxX0 : X0 ≤ x := (le_max_left X0 _) |>.trans hx
  have hxLarge : (512 ^ 4) ^ 4 ≤ x :=
    (le_max_right X0 _) |>.trans hx
  have hyLarge : 512 ^ 4 < y :=
    modulus_one_large_y_of_large_x x y hxLarge hxy
  obtain ⟨N, hN, hprodN, hwindow⟩ :=
    modulus_one_real_geometry x y hxy hyLarge
  obtain ⟨S, hcard, hprimes, hpair, hprodS⟩ :=
    nine_moduli_cover_certificate N x hN hprodN
  have hcovered :
      (∑ n ∈ Finset.Ioc (x-y) x, f n) ≤
      ∑ p ∈ S, ∑ n ∈ Finset.Ioc (x-y) x,
          if ¬ p ∣ n then f n else 0 :=
    short_interval_le_modulus_cover f x y S hf.nonnegative hpair hprodS
  let K : ℝ :=
    classicalConstant A B *
      ((y : ℝ) / Real.log (x : ℝ)) *
      Real.exp (PaperB.M4B.primeMass f x 1)
  have hsum :
      (∑ p ∈ S, ∑ n ∈ Finset.Ioc (x-y) x,
        if ¬ p ∣ n then f n else 0) ≤
      ∑ p ∈ S, K := by
    apply Finset.sum_le_sum
    intro p hp
    have hpProps := hprimes p hp
    have hpWindow : (p : ℝ) < (y : ℝ) ^ (3 / 4 : ℝ) := by
      have hple : (p : ℝ) ≤ (512 * N : ℝ) := by
        exact_mod_cast hpProps.2.2
      exact lt_of_le_of_lt hple hwindow
    exact hX f hf hB hgrowth x y p
      hxX0 hxy hyx hpProps.1 hpWindow
  calc
    (∑ n ∈ Finset.Ioc (x-y) x, f n)
        ≤ ∑ p ∈ S, ∑ n ∈ Finset.Ioc (x-y) x,
            if ¬ p ∣ n then f n else 0 := hcovered
    _ ≤ ∑ p ∈ S, K := hsum
    _ = 9 * K := by
      simp [Finset.sum_const, hcard, nsmul_eq_mul]
    _ = 9 * classicalConstant A B *
          ((y : ℝ) / Real.log (x : ℝ)) *
          Real.exp (PaperB.M4B.primeMass f x 1) := by
      dsimp [K]
      ring

#print axioms classical_modulus_one_quarter
end Shiu.API
