module

public import Shiu.Classical

public section

/-!
# Modulus-one Shiu estimate — finite prime-cover engine

The nine-prime geometry and analytic window are now proved downstream by
ModulusOneNineCover, ModulusOneRealGeometry and ModulusOneFinal. This module
supplies the unconditional finite combinatorial covering inequality.
The ordinary k=1 short-interval theorem is a proved downstream corollary.
-/

namespace Shiu.API
open scoped BigOperators

/-- An ordinary nonnegative weight is covered by the filters of a finite
set of moduli whenever each integer avoids at least one modulus. -/
theorem sum_le_coprime_cover
    (f : ArithmeticFunction ℝ) (I S : Finset ℕ)
    (hf : ∀ n, 0 ≤ f n)
    (hcover : ∀ n ∈ I, ∃ p ∈ S, ¬ p ∣ n) :
    (∑ n ∈ I, f n) ≤
      ∑ p ∈ S, ∑ n ∈ I, if ¬ p ∣ n then f n else 0 := by
  classical
  have hpoint : ∀ n ∈ I, f n ≤
      ∑ p ∈ S, if ¬ p ∣ n then f n else 0 := by
    intro n hn
    obtain ⟨p, hp, hpn⟩ := hcover n hn
    have h0 : ∀ q ∈ S, 0 ≤ (if ¬ q ∣ n then f n else 0) := by
      intro q hq
      by_cases hq : q ∣ n
      · simp [hq]
      · simpa [hq] using hf n
    calc
      f n = (if ¬ p ∣ n then f n else 0) := by simp [hpn]
      _ ≤ ∑ q ∈ S, if ¬ q ∣ n then f n else 0 :=
        Finset.single_le_sum h0 hp
  calc
    (∑ n ∈ I, f n) ≤
        ∑ n ∈ I, ∑ p ∈ S, if ¬ p ∣ n then f n else 0 :=
      Finset.sum_le_sum hpoint
    _ = ∑ p ∈ S, ∑ n ∈ I, if ¬ p ∣ n then f n else 0 :=
      Finset.sum_comm

/-- If the moduli are pairwise coprime and their product exceeds x,
then each positive integer n in (x-y,x] misses at least one modulus.
The proof is exact for any finite S, with no use of asymptotics. -/
theorem interval_has_unoccupied_modulus
    (x y : ℕ) (S : Finset ℕ)
    (hpair : (S : Set ℕ).Pairwise ((fun a b : ℕ => IsRelPrime a b)))
    (hprod : x < ∏ p ∈ S, p) :
    ∀ n ∈ Finset.Ioc (x-y) x, ∃ p ∈ S, ¬ p ∣ n := by
  intro n hn
  have hnI := Finset.mem_Ioc.mp hn
  have hn0 : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hnI.1
  by_contra hno
  have hdiv : ∀ p ∈ S, p ∣ n := by
    intro p hp
    by_contra hnp
    exact hno ⟨p, hp, hnp⟩
  have hprod_dvd : (∏ p ∈ S, p) ∣ n :=
    Finset.prod_dvd_of_isRelPrime hpair hdiv
  have hle : (∏ p ∈ S, p) ≤ n := Nat.le_of_dvd hn0 hprod_dvd
  omega

/-- The core modulus-one covering inequality, for real nonnegative
arithmetic weights and any exact coprime-product certificate. -/
theorem short_interval_le_modulus_cover
    (f : ArithmeticFunction ℝ) (x y : ℕ) (S : Finset ℕ)
    (hf : ∀ n, 0 ≤ f n)
    (hpair : (S : Set ℕ).Pairwise ((fun a b : ℕ => IsRelPrime a b)))
    (hprod : x < ∏ p ∈ S, p) :
    (∑ n ∈ Finset.Ioc (x-y) x, f n) ≤
      ∑ p ∈ S, ∑ n ∈ Finset.Ioc (x-y) x,
        if ¬ p ∣ n then f n else 0 := by
  exact sum_le_coprime_cover f _ S hf
    (interval_has_unoccupied_modulus x y S hpair hprod)

#print axioms sum_le_coprime_cover
#print axioms interval_has_unoccupied_modulus
#print axioms short_interval_le_modulus_cover
end Shiu.API
