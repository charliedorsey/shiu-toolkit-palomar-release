module

public import Mathlib.NumberTheory.Primorial
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Nat.Squarefree

public section

open Finset Nat

namespace PaperB
namespace M4A

/-- The finite set of sieve primes in Shiu's reduced progression: primes at
most `z` which do not divide the progression modulus `k`. -/
def selectedPrimes (z k : ℕ) : Finset ℕ :=
  (Nat.primesLE z).filter (fun p => ¬ p ∣ k)

/-- Product of the selective sieve primes. -/
def selectedPrimeProduct (z k : ℕ) : ℕ :=
  ∏ p ∈ selectedPrimes z k, p

@[simp] theorem mem_selectedPrimes_iff {p z k : ℕ} :
    p ∈ selectedPrimes z k ↔ p ≤ z ∧ p.Prime ∧ ¬ p ∣ k := by
  simp [selectedPrimes, Nat.mem_primesLE, and_assoc]

theorem selectedPrimeProduct_squarefree (z k : ℕ) :
    Squarefree (selectedPrimeProduct z k) := by
  unfold selectedPrimeProduct
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro p hp q hq hpq
    simp only [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes
      (mem_selectedPrimes_iff.mp hp).2.1
      (mem_selectedPrimes_iff.mp hq).2.1).mpr hpq
  · intro p hp
    exact (mem_selectedPrimes_iff.mp hp).2.1.squarefree

theorem selectedPrimeProduct_ne_zero (z k : ℕ) :
    selectedPrimeProduct z k ≠ 0 :=
  (selectedPrimeProduct_squarefree z k).ne_zero

theorem selectedPrimeProduct_primeFactors (z k : ℕ) :
    (selectedPrimeProduct z k).primeFactors = selectedPrimes z k := by
  unfold selectedPrimeProduct
  exact Nat.primeFactors_prod fun p hp =>
    (mem_selectedPrimes_iff.mp hp).2.1

theorem prime_dvd_selectedPrimeProduct_iff
    {p z k : ℕ} (hp : p.Prime) :
    p ∣ selectedPrimeProduct z k ↔ p ≤ z ∧ ¬ p ∣ k := by
  constructor
  · intro hpd
    have hmem : p ∈ (selectedPrimeProduct z k).primeFactors := by
      rw [Nat.mem_primeFactors]
      exact ⟨hp, hpd, selectedPrimeProduct_ne_zero z k⟩
    rw [selectedPrimeProduct_primeFactors] at hmem
    exact ⟨(mem_selectedPrimes_iff.mp hmem).1,
      (mem_selectedPrimes_iff.mp hmem).2.2⟩
  · intro h
    have hmem : p ∈ selectedPrimes z k :=
      mem_selectedPrimes_iff.mpr ⟨h.1, hp, h.2⟩
    rw [← selectedPrimeProduct_primeFactors] at hmem
    exact Nat.dvd_of_mem_primeFactors hmem

theorem selectedPrimeProduct_coprime_modulus (z k : ℕ) :
    (selectedPrimeProduct z k).Coprime k := by
  unfold selectedPrimeProduct
  rw [Nat.coprime_prod_left_iff]
  intro p hp
  have hprime := (mem_selectedPrimes_iff.mp hp).2.1
  rw [hprime.coprime_iff_not_dvd]
  exact (mem_selectedPrimes_iff.mp hp).2.2

/-- Coprimality with the selective product is exactly avoidance of all
selected primes. -/
theorem coprime_selectedPrimeProduct_iff
    {n z k : ℕ} :
    n.Coprime (selectedPrimeProduct z k) ↔
      ∀ p : ℕ, p.Prime → p ≤ z → ¬ p ∣ k → ¬ p ∣ n := by
  unfold selectedPrimeProduct
  rw [Nat.coprime_prod_right_iff]
  constructor
  · intro h p hp hpz hpk
    have hmem : p ∈ selectedPrimes z k :=
      mem_selectedPrimes_iff.mpr ⟨hpz, hp, hpk⟩
    have hnp : n.Coprime p := h p hmem
    exact (hp.coprime_iff_not_dvd.mp hnp.symm)
  · intro h p hpS
    have hs := mem_selectedPrimes_iff.mp hpS
    exact (hs.2.1.coprime_iff_not_dvd.mpr
      (h p hs.2.1 hs.1 hs.2.2)).symm

/-- In a reduced residue class, avoiding the selective primes is equivalent to
avoiding every prime up to `z`: primes dividing `k` cannot divide a number
coprime to `k`.  This is the support bridge used to identify the Selberg
sifted support with Shiu's least-prime-factor condition (apart from Shiu's
special convention at `n=1`). -/
theorem reducedClass_coprime_selected_iff_all_small_primes
    {n a k z : ℕ} (hak : a.Coprime k) (hna : n ≡ a [MOD k]) :
    n.Coprime (selectedPrimeProduct z k) ↔
      ∀ p : ℕ, p.Prime → p ≤ z → ¬ p ∣ n := by
  have hnk : n.Coprime k := by
    rw [Nat.coprime_iff_gcd_eq_one, hna.gcd_eq]
    exact hak.gcd_eq_one
  rw [coprime_selectedPrimeProduct_iff]
  constructor
  · intro h p hp hpz
    by_cases hpk : p ∣ k
    · have hnp : n.Coprime p := hnk.coprime_dvd_right hpk
      exact hp.coprime_iff_not_dvd.mp hnp.symm
    · exact h p hp hpz hpk
  · intro h p hp hpz hpk
    exact h p hp hpz

end M4A
end PaperB
