module

public import Shiu.ModulusOne

public section

/-!
# Exact residue-class partition for a prime modulus

This is a non-asymptotic sum identity. No Shiu analytic estimate
is invoked until its existing hypotheses can be supplied.
-/
namespace Shiu.API
open scoped BigOperators

/-- Every n not divisible by p belongs to precisely one of the
reduced residue classes 1 <= a < p. Ordinary Ioc endpoints retained. -/
theorem nondivisible_sum_eq_reduced_progressions
    (f : ArithmeticFunction ℝ) (x y p : ℕ) (hp : 0 < p) :
    (∑ n ∈ Finset.Ioc (x-y) x, if ¬ p ∣ n then f n else 0) =
      ∑ a ∈ Finset.Ico 1 p, progressionSum f x y p a := by
  classical
  unfold progressionSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hmem : (n % p ∈ Finset.Ico 1 p) ↔ ¬ p ∣ n := by
    constructor
    · intro h hpdiv
      have hz : n % p = 0 := Nat.mod_eq_zero_of_dvd hpdiv
      have hpos : 0 < n % p := (Finset.mem_Ico.mp h).1
      omega
    · intro h
      have hne : n % p ≠ 0 := by
        intro hz
        exact h (Nat.dvd_of_mod_eq_zero hz)
      exact Finset.mem_Ico.mpr
        ⟨Nat.pos_of_ne_zero hne, Nat.mod_lt n hp⟩
  have hsum :
      (∑ a ∈ Finset.Ico 1 p,
        if n ≡ a [MOD p] then f n else 0) =
      (∑ a ∈ Finset.Ico 1 p,
        if n % p = a then f n else 0) := by
    apply Finset.sum_congr rfl
    intro a ha
    have hap : a < p := (Finset.mem_Ico.mp ha).2
    simp only [Nat.ModEq, Nat.mod_eq_of_lt hap]
  calc
    (if ¬ p ∣ n then f n else 0) =
        (if n % p ∈ Finset.Ico 1 p then f n else 0) := by
      simp only [hmem]
    _ = ∑ a ∈ Finset.Ico 1 p,
          if n % p = a then f n else 0 := by
      rw [Finset.sum_ite_eq]
    _ = ∑ a ∈ Finset.Ico 1 p,
          if n ≡ a [MOD p] then f n else 0 := hsum.symm

#print axioms nondivisible_sum_eq_reduced_progressions
end Shiu.API
