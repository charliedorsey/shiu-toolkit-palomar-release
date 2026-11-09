module

public import Shiu.ModulusOneAP
public import Shiu.ModulusOneMass

public section

/-!
# Prime-modulus filtered bound with complete totient cancellation
# and exact unrestricted (k=1) prime-mass normalization
-/
namespace Shiu.API
open scoped BigOperators

theorem classical_filtered_prime_normalized (A B : ℝ) :
    ∃ X0 : ℕ, ∀ f : ArithmeticFunction ℝ,
      Shiu.ClassicalEnvelope f A →
      0 ≤ B →
      (∀ n : ℕ, 1 ≤ n →
        f n ≤ B * (n : ℝ) ^ (1 / 1280 : ℝ)) →
      ∀ x y p : ℕ,
        X0 ≤ x →
        (x : ℝ) ^ (1 / 4 : ℝ) < (y : ℝ) →
        y ≤ x →
        p.Prime →
        (p : ℝ) < (y : ℝ) ^ (3 / 4 : ℝ) →
        (∑ n ∈ Finset.Ioc (x-y) x,
          if ¬ p ∣ n then f n else 0) ≤
        classicalConstant A B *
          ((y : ℝ) / Real.log (x : ℝ)) *
          Real.exp (PaperB.M4B.primeMass f x 1) := by
  obtain ⟨X0, hX⟩ := classical_filtered_prime_bound A B
  refine ⟨max X0 2, ?_⟩
  intro f hf hB hgrowth x y p hx hxy hyx hp hpy
  have hxX : X0 ≤ x := (le_max_left X0 2).trans hx
  have hx2 : 2 ≤ x := (le_max_right X0 2).trans hx
  have hlog : 0 < Real.log (x : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < x by omega)
  have hphi : 0 < (p.totient : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hp.pos)
  have hC : 0 ≤ classicalConstant A B :=
    classicalConstant_nonneg A B hf.A_nonnegative hB
  have hy0 : 0 ≤ (y : ℝ) := Nat.cast_nonneg _
  have hmass := primeMass_le_modulus_one f x p hf.nonnegative
  have hfactor : 0 ≤ classicalConstant A B * ((y : ℝ) / Real.log (x : ℝ)) :=
    mul_nonneg hC (div_nonneg hy0 hlog.le)
  have hidentity :
    (p.totient : ℝ) *
        (classicalConstant A B *
          ((y : ℝ) / ((p.totient : ℝ) * Real.log (x : ℝ))) *
          Real.exp (PaperB.M4B.primeMass f x p)) =
      classicalConstant A B * ((y : ℝ) / Real.log (x : ℝ)) *
        Real.exp (PaperB.M4B.primeMass f x p) := by
    field_simp
  calc
    (∑ n ∈ Finset.Ioc (x-y) x, if ¬ p ∣ n then f n else 0)
        ≤ (p.totient : ℝ) *
            (classicalConstant A B *
              ((y : ℝ) / ((p.totient : ℝ) * Real.log (x : ℝ))) *
              Real.exp (PaperB.M4B.primeMass f x p)) :=
          hX f hf hB hgrowth x y p hxX hxy hyx hp hpy
    _ = classicalConstant A B * ((y : ℝ) / Real.log (x : ℝ)) *
          Real.exp (PaperB.M4B.primeMass f x p) := hidentity
    _ ≤ classicalConstant A B * ((y : ℝ) / Real.log (x : ℝ)) *
          Real.exp (PaperB.M4B.primeMass f x 1) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmass) hfactor

#print axioms classical_filtered_prime_normalized
end Shiu.API
