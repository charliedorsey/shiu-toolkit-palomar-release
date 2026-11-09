module

/-
Paper B M4B-CORE deletion test for historical Shiu Class II.
Authorized purpose: determine whether FixedQuarterEnvelope.squarefree_support
kills the historical Class-II route pointwise before any S7 counting work.
-/

public import PaperB.M4B.ShiuCore
public import Mathlib.Data.Nat.Squarefree

public section

open Nat
open ArithmeticFunction

noncomputable section

namespace PaperB
namespace M4B

/-- Historical Class II crossing data forces the crossing prime-power exponent
to be at least two: both the extracted prefix and the crossing prime are at
most floor(sqrt z), while adjoining the full prime power crosses z. -/
theorem historical_classII_exponent_ge_two
    {b p s z : ℕ}
    (hpprime : p.Prime)
    (hb : b ≤ Nat.sqrt z)
    (hp : p ≤ Nat.sqrt z)
    (hcross : z < b * p ^ s) :
    2 ≤ s := by
  by_contra hs
  have hsle : s ≤ 1 := by omega
  interval_cases s
  · simp only [pow_zero, mul_one] at hcross
    have hsqrt_ge_two : 2 ≤ Nat.sqrt z := hpprime.two_le.trans hp
    have hsqrt_self : Nat.sqrt z ≤ (Nat.sqrt z) ^ 2 := by
      nlinarith
    have hsqrt_sq : (Nat.sqrt z) ^ 2 ≤ z := Nat.sqrt_le' z
    omega
  · simp only [pow_one] at hcross
    have hprod : b * p ≤ Nat.sqrt z * Nat.sqrt z :=
      Nat.mul_le_mul hb hp
    have hsqrt_sq : Nat.sqrt z * Nat.sqrt z ≤ z := by
      simpa [pow_two] using Nat.sqrt_le' z
    omega

/-- Historical Class II is incompatible with squarefree support: the crossing
prime occurs to exponent at least two, so its square divides n. -/
theorem historical_classII_not_squarefree
    {n b p s z : ℕ}
    (hpprime : p.Prime)
    (hb : b ≤ Nat.sqrt z)
    (hp : p ≤ Nat.sqrt z)
    (hcross : z < b * p ^ s)
    (hpow : p ^ s ∣ n) :
    ¬ Squarefree n := by
  intro hn
  have hs : 2 ≤ s :=
    historical_classII_exponent_ge_two hpprime hb hp hcross
  have hpow2 : p ^ 2 ∣ p ^ s := Nat.pow_dvd_pow p hs
  have hsq : p * p ∣ n := by
    simpa [pow_two] using hpow2.trans hpow
  exact (Nat.squarefree_iff_prime_squarefree.mp hn p hpprime) hsq

/-- Exact deletion test requested by PM: every historical Class-II term is
pointwise zero for a FixedQuarterEnvelope. -/
theorem historical_classII_pointwise_zero
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    {n b p s z : ℕ}
    (hpprime : p.Prime)
    (hb : b ≤ Nat.sqrt z)
    (hp : p ≤ Nat.sqrt z)
    (hcross : z < b * p ^ s)
    (hpow : p ^ s ∣ n) :
    f n = 0 := by
  apply hf.squarefree_support n
  exact historical_classII_not_squarefree hpprime hb hp hcross hpow

end M4B
end PaperB
