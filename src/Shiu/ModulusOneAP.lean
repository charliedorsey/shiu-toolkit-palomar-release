module

public import Shiu.ModulusOneResidues

public section

/-!
# Sum the source fixed-quarter Shiu theorem over all reduced classes

No analytic hypotheses are dropped, and this module is not a
k=1 corollary by itself. It isolates the exact totient cancellation.
-/
namespace Shiu.API
open scoped BigOperators

theorem classical_filtered_prime_bound (A B : ℝ) :
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
        (p.totient : ℝ) *
          (classicalConstant A B *
            ((y : ℝ) / ((p.totient : ℝ) * Real.log (x : ℝ))) *
            Real.exp (PaperB.M4B.primeMass f x p)) := by
  obtain ⟨X0, hX⟩ := classical_quarter A B
  refine ⟨X0, ?_⟩
  intro f hf hB hgrowth x y p hx hxy hyx hp hpy
  have hp0 : 0 < p := hp.pos
  rw [nondivisible_sum_eq_reduced_progressions f x y p hp0]
  let K : ℝ :=
    classicalConstant A B *
      ((y : ℝ) / ((p.totient : ℝ) * Real.log (x : ℝ))) *
      Real.exp (PaperB.M4B.primeMass f x p)
  have hsum : (∑ a ∈ Finset.Ico 1 p, progressionSum f x y p a) ≤
      ∑ a ∈ Finset.Ico 1 p, K := by
    apply Finset.sum_le_sum
    intro a ha
    have haI := Finset.mem_Ico.mp ha
    have ha0 : 0 < a := by omega
    have haC : a.Coprime p :=
      (Nat.coprime_of_lt_prime (by omega) haI.2 hp).symm
    exact hX f hf hB hgrowth x y p a
      hx hxy hyx hpy ha0 haI.2 haC
  have hcard : (Finset.Ico 1 p).card = p.totient := by
    rw [Nat.card_Ico, Nat.totient_prime hp]
  calc
    (∑ a ∈ Finset.Ico 1 p, progressionSum f x y p a)
        ≤ ∑ a ∈ Finset.Ico 1 p, K := hsum
    _ = (p.totient : ℝ) * K := by
      simp [Finset.sum_const, hcard, nsmul_eq_mul]
    _ = (p.totient : ℝ) *
          (classicalConstant A B *
            ((y : ℝ) / ((p.totient : ℝ) * Real.log (x : ℝ))) *
            Real.exp (PaperB.M4B.primeMass f x p)) := rfl

#print axioms classical_filtered_prime_bound
end Shiu.API
