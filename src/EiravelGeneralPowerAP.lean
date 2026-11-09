module

public import ShiuPublic.CorvethSquareExceptionAP
public import EiravelLowBaseReciprocal
public import PaperB.M4A.APDivCount

public section

namespace PaperB.M4B
open scoped BigOperators
open Finset Nat Real
noncomputable section

/-- Real weighted mass of the actual sharp progression, overcovered by
square divisibility for a finite collection of eligible base primes. -/
@[expose] noncomputable def eiravelPowerExceptionalMass
    (f : ArithmeticFunction ℝ) (x y k a : ℕ) (P : Finset ℕ) (m : ℕ → ℕ) : ℝ :=
  ∑ p ∈ P, ∑ n ∈ (Finset.Ioc (x-y) x).filter
    (fun n => n ≡ a [MOD k] ∧ m p ∣ n), f n

/-- Complete arithmetic estimate, keeping the literal p², modulus k,
sharp endpoints and source weights, without asserting smallness of the
remaining divisor mass. -/
theorem eiravel_power_exception_mass_le
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n → f n ≤
      B * (n : ℝ) ^ (1/1280 : ℝ))
    (x y k a : ℕ) (P : Finset ℕ) (m : ℕ → ℕ)
    (hyx : y ≤ x) (hk : 0 < k)
    (hpositive : ∀ p ∈ P, 0 < m p)
    (hcop : ∀ p ∈ P, (m p).Coprime k) :
    eiravelPowerExceptionalMass f x y k a P m ≤
      (B * (x : ℝ) ^ (1/1280 : ℝ)) *
        ((y : ℝ) / (k : ℝ) *
          (∑ p ∈ P, (1 : ℝ) / (m p : ℝ)) +
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
        (fun n => n ≡ a [MOD k] ∧ m p ∣ n), f n) ≤
        G * ((y : ℝ) / ((k : ℝ) * (m p : ℝ)) + 4) := by
    intro p hp
    let S := (Finset.Ioc (x-y) x).filter
        (fun n => n ≡ a [MOD k] ∧ m p ∣ n)
    have hcard : ((S.card : ℝ)) =
        (PaperB.M4A.apDivCount x y k a (m p) : ℝ) := rfl
    have hpd : 0 < m p := hpositive p hp
    have hkpd : k.Coprime (m p) := (hcop p hp).symm
    obtain ⟨C,hC,hEq⟩ := PaperB.M4A.apDivCount_realApprox
      x y k a (m p) hyx hk hpd hkpd
    have hC' : C ≤ 4 := (le_abs_self C).trans hC
    have hcount : (S.card : ℝ) ≤
      (y : ℝ) / ((k : ℝ) * (m p : ℝ)) + 4 := by
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
      _ ≤ G * ((y : ℝ) / ((k : ℝ) * (m p : ℝ)) + 4) :=
        mul_le_mul_of_nonneg_left hcount hG
  unfold eiravelPowerExceptionalMass
  calc
    _ ≤ ∑ p ∈ P, G * ((y : ℝ) / ((k : ℝ) * (m p : ℝ)) + 4) :=
      Finset.sum_le_sum hlocal
    _ = G * ((y : ℝ) / (k : ℝ) *
          (∑ p ∈ P, (1 : ℝ) / (m p : ℝ)) +
          4 * (P.card : ℝ)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      congr 1
      have hs : (∑ p ∈ P, (y : ℝ) / ((k : ℝ) * (m p : ℝ))) =
          (y : ℝ) / (k : ℝ) * (∑ p ∈ P, (1 : ℝ) / (m p : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      rw [hs]
      simp
      ring

#print axioms eiravel_power_exception_mass_le
end
end PaperB.M4B


namespace PaperB.M4B

/-- The physical eligible base primes and *minimal whole-power divisors*
specialization of the sharp weighted AP bound. -/
theorem eiravel_eligible_minimal_power_exception_mass_le
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n →
      f n ≤ B * (n : ℝ) ^ (1/1280 : ℝ))
    (x y z k a : ℕ) (hyx : y ≤ x) (hk : 0 < k) :
    eiravelPowerExceptionalMass f x y k a
        ((Nat.primesLE (Nat.sqrt z)).filter (fun p => ¬ p ∣ k))
        (fun p => p ^ (Nat.log p (Nat.sqrt z) + 1)) ≤
      (B * (x : ℝ) ^ (1/1280 : ℝ)) *
        ((y : ℝ) / (k : ℝ) *
          (∑ p ∈ (Nat.primesLE (Nat.sqrt z)).filter (fun p => ¬ p ∣ k),
            (1 : ℝ) / (p ^ (Nat.log p (Nat.sqrt z) + 1) : ℕ)) +
          4 * (((Nat.primesLE (Nat.sqrt z)).filter (fun p => ¬ p ∣ k)).card : ℝ)) := by
  apply eiravel_power_exception_mass_le hf hB hgrowth
    x y k a ((Nat.primesLE (Nat.sqrt z)).filter (fun p => ¬ p ∣ k))
    (fun p => p ^ (Nat.log p (Nat.sqrt z) + 1)) hyx hk
  · intro p hp
    have hprime : p.Prime :=
      Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
    exact pow_pos hprime.pos _
  · intro p hp
    have hprime : p.Prime :=
      Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
    have hnot : ¬ p ∣ k := (Finset.mem_filter.mp hp).2
    exact ((hprime.coprime_iff_not_dvd).mpr hnot).pow_left _

#print axioms eiravel_eligible_minimal_power_exception_mass_le

end PaperB.M4B


namespace PaperB.M4B

/-- The selected full-power exceptional overcover has a quantitative
source-weighted sharp-AP budget, with BOTH the reciprocal and endpoint terms
visible and bounded. No final Shiu absorption is asserted here. -/
theorem eiravel_eligible_minimal_power_mass_budget
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n →
      f n ≤ B * (n : ℝ) ^ (1/1280 : ℝ))
    (x y z k a : ℕ) (hyx : y ≤ x) (hk : 0 < k)
    (hT : 0 < Nat.sqrt z) :
    eiravelPowerExceptionalMass f x y k a
        ((Nat.primesLE (Nat.sqrt z)).filter (fun p => ¬ p ∣ k))
        (fun p => p ^ (Nat.log p (Nat.sqrt z) + 1)) ≤
      (B * (x : ℝ) ^ (1/1280 : ℝ)) *
        ((y : ℝ) / (k : ℝ) *
          ((Nat.sqrt (Nat.sqrt z) : ℝ) / (Nat.sqrt z : ℝ) +
            2 / ((Nat.sqrt (Nat.sqrt z) + 1 : ℕ) : ℝ)) +
           4 * ((Nat.sqrt z + 1 : ℕ) : ℝ)) := by
  let P : Finset ℕ :=
    (Nat.primesLE (Nat.sqrt z)).filter (fun p => ¬ p ∣ k)
  let T : ℕ := Nat.sqrt z
  let U : ℕ := Nat.sqrt T
  let R : ℝ :=
    (U : ℝ) / (T : ℝ) + 2 / ((U + 1 : ℕ) : ℝ)
  have hrec :
      (∑ p ∈ P,
        (1 : ℝ) / (p ^ (Nat.log p T + 1) : ℕ)) ≤ R := by
    simpa only [P, T, U, R] using
      eiravel_eligible_crossing_prime_mass z k hT
  have hcount : ((P.card : ℝ)) ≤ ((T + 1 : ℕ) : ℝ) := by
    have hs : P ⊆ Finset.range (T + 1) := by
      intro p hp
      have hm : p ∈ Nat.primesLE T := (Finset.mem_filter.mp hp).1
      exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Nat.mem_primesLE.mp hm).1)
    have hc : P.card ≤ T + 1 := by
      simpa using Finset.card_le_card hs
    exact_mod_cast hc
  have hmain :
      ((y : ℝ) / (k : ℝ)) *
          (∑ p ∈ P,
            (1 : ℝ) / (p ^ (Nat.log p T + 1) : ℕ)) +
          4 * (P.card : ℝ) ≤
      ((y : ℝ) / (k : ℝ)) * R + 4 * ((T + 1 : ℕ) : ℝ) := by
    have hydiv : 0 ≤ (y : ℝ) / (k : ℝ) := by positivity
    exact add_le_add
      (mul_le_mul_of_nonneg_left hrec hydiv)
      (mul_le_mul_of_nonneg_left hcount (by norm_num))
  have hG : 0 ≤ B * (x : ℝ) ^ (1/1280 : ℝ) := by positivity
  have hAP := eiravel_eligible_minimal_power_exception_mass_le
    hf hB hgrowth x y z k a hyx hk
  calc
    eiravelPowerExceptionalMass f x y k a P
        (fun p => p ^ (Nat.log p T + 1)) ≤
        (B * (x : ℝ) ^ (1/1280 : ℝ)) *
          (((y : ℝ) / (k : ℝ)) *
            (∑ p ∈ P,
              (1 : ℝ) / (p ^ (Nat.log p T + 1) : ℕ)) +
            4 * (P.card : ℝ)) := by
              simpa only [P, T] using hAP
    _ ≤ (B * (x : ℝ) ^ (1/1280 : ℝ)) *
          (((y : ℝ) / (k : ℝ)) * R +
            4 * ((T + 1 : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hmain hG
    _ = (B * (x : ℝ) ^ (1/1280 : ℝ)) *
        (((y : ℝ) / (k : ℝ)) *
          ((Nat.sqrt (Nat.sqrt z) : ℝ) / (Nat.sqrt z : ℝ) +
            2 / ((Nat.sqrt (Nat.sqrt z) + 1 : ℕ) : ℝ)) +
         4 * ((Nat.sqrt z + 1 : ℕ) : ℝ)) := rfl

#print axioms eiravel_eligible_minimal_power_mass_budget

end PaperB.M4B
