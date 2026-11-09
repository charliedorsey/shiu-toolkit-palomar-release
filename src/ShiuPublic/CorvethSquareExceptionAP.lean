module

public import ShiuPublic.PrimePowerEnvelope
public import PaperB.M4A.APDivCount

public section

namespace PaperB.M4B
open scoped BigOperators
open Finset Nat Real
noncomputable section

/-- Real weighted mass of the actual sharp progression, overcovered by
square divisibility for a finite collection of eligible base primes. -/
noncomputable def corvethSquareExceptionalMass
    (f : ArithmeticFunction ℝ) (x y k a : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, ∑ n ∈ (Finset.Ioc (x-y) x).filter
    (fun n => n ≡ a [MOD k] ∧ p ^ 2 ∣ n), f n

/-- Complete arithmetic estimate, keeping the literal p², modulus k,
sharp endpoints and source weights, without asserting smallness of the
remaining divisor mass. -/
theorem corveth_square_exception_mass_le
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n → f n ≤
      B * (n : ℝ) ^ (1/1280 : ℝ))
    (x y k a : ℕ) (P : Finset ℕ)
    (hyx : y ≤ x) (hk : 0 < k)
    (hprimes : ∀ p ∈ P, p.Prime)
    (hcop : ∀ p ∈ P, p.Coprime k) :
    corvethSquareExceptionalMass f x y k a P ≤
      (B * (x : ℝ) ^ (1/1280 : ℝ)) *
        ((y : ℝ) / (k : ℝ) *
          (∑ p ∈ P, (1 : ℝ) / (p : ℝ)^2) +
          4 * (P.card : ℝ)) := by
  classical
  let G : ℝ := B * (x : ℝ) ^ (1/1280 : ℝ)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hpoint : ∀ n ∈ Finset.Ioc (x-y) x, f n ≤ G := by
    intro n hn
    have hnI := Finset.mem_Ioc.mp hn
    have hnr : (n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hnI.2
    have hp := Real.rpow_le_rpow (by positivity) hnr (by norm_num : (0:ℝ) ≤ 1/1280)
    exact (hgrowth n (by omega)).trans
      (mul_le_mul_of_nonneg_left hp hB)
  have hlocal : ∀ p ∈ P,
      (∑ n ∈ (Finset.Ioc (x-y) x).filter
        (fun n => n ≡ a [MOD k] ∧ p^2 ∣ n), f n) ≤
        G * ((y : ℝ) / ((k : ℝ) * (p : ℝ)^2) + 4) := by
    intro p hp
    let S := (Finset.Ioc (x-y) x).filter
        (fun n => n ≡ a [MOD k] ∧ p^2 ∣ n)
    have hcard : ((S.card : ℝ)) =
        (PaperB.M4A.apDivCount x y k a (p^2) : ℝ) := rfl
    have hpd : 0 < p^2 := pow_pos (hprimes p hp).pos _
    have hkpd : k.Coprime (p^2) :=
      (hcop p hp).symm.pow_right 2
    obtain ⟨C,hC,hEq⟩ := PaperB.M4A.apDivCount_realApprox
      x y k a (p^2) hyx hk hpd hkpd
    have hC' : C ≤ 4 := (le_abs_self C).trans hC
    have hcount : (S.card : ℝ) ≤
      (y : ℝ) / ((k : ℝ) * (p : ℝ)^2) + 4 := by
      rw [hcard, hEq]
      push_cast
      nlinarith [hC']
    have hsum : (∑ n ∈ S, f n) ≤ G * (S.card : ℝ) := by
      calc
        _ ≤ ∑ _n ∈ S, G := Finset.sum_le_sum (fun n hn =>
          hpoint n (Finset.mem_filter.mp hn).1)
        _ = G * (S.card : ℝ) := by simp [mul_comm]
    calc
      _ ≤ G * (S.card : ℝ) := hsum
      _ ≤ G * ((y : ℝ) / ((k : ℝ) * (p : ℝ)^2) + 4) :=
        mul_le_mul_of_nonneg_left hcount hG
  unfold corvethSquareExceptionalMass
  calc
    _ ≤ ∑ p ∈ P, G * ((y : ℝ) / ((k : ℝ) * (p : ℝ)^2) + 4) :=
      Finset.sum_le_sum hlocal
    _ = G * ((y : ℝ) / (k : ℝ) *
          (∑ p ∈ P, (1 : ℝ) / (p : ℝ)^2) +
          4 * (P.card : ℝ)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      congr 1
      have hs : (∑ p ∈ P, (y : ℝ) / ((k : ℝ) * (p : ℝ)^2)) =
          (y : ℝ) / (k : ℝ) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ)^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      rw [hs]
      simp
      ring

#print axioms corveth_square_exception_mass_le
end
end PaperB.M4B
