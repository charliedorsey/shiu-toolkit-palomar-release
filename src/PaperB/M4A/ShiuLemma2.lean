module

/-
Paper B M4A C5: exact Shiu Chapter 3, Section 3.4, Lemma 2 wrapper.
-/

public import PaperB.M4A.SelectivePrimeSieve

public section

open scoped BigOperators
open Finset Nat Real

noncomputable section

namespace PaperB
namespace M4A

/-- Shiu's least-prime-factor convention: 1 is rough, and otherwise the
least prime factor is larger than z. -/
@[expose] def shiuRough (n z : ℕ) : Prop :=
  n = 1 ∨ z < n.minFac

theorem allSmallPrimesAvoid_iff_shiuRough
    {n z : ℕ} :
    (∀ p : ℕ, p.Prime → p ≤ z → ¬ p ∣ n) ↔ shiuRough n z := by
  constructor
  · intro h
    by_cases hn : n = 1
    · exact Or.inl hn
    · right
      by_contra hz
      have hle : n.minFac ≤ z := by omega
      exact h n.minFac (Nat.minFac_prime hn) hle (Nat.minFac_dvd n)
  · intro h p hp hpz hpd
    rcases h with rfl | hmin
    · exact hp.not_dvd_one hpd
    · have hle : n.minFac ≤ p :=
        Nat.minFac_le_of_dvd hp.two_le hpd
      omega

/-- In a reduced progression, coprimality with the selected sieve product is
exactly Shiu's P^-(n) > z condition, with the standard n=1 convention. -/
theorem selectivePrimeSupport_iff_leastPrimeFactor
    {n a k z : ℕ} (hak : a.Coprime k) (hna : n ≡ a [MOD k]) :
    n.Coprime (selectedPrimeProduct z k) ↔ shiuRough n z := by
  rw [reducedClass_coprime_selected_iff_all_small_primes hak hna]
  exact allSmallPrimesAvoid_iff_shiuRough

/-- Real-valued indicator count for Shiu's
`Phi(x,y,z;k,a)`: integers `x-y < n ≤ x` in the class `a mod k`
whose least prime factor is greater than `z`, with `n = 1` rough. -/
@[expose] def shiuPhi (x y z k a : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ Finset.Ioc (x - y) x,
    if n ≡ a [MOD k] ∧ shiuRough n z then (1 : ℝ) else 0

private theorem shiuPhi_eq_siftedSum
    (x y k a z : ℕ) (hz : 1 ≤ z) (hak : a.Coprime k) :
    shiuPhi x y z k a =
      (selectiveAPSieve x y k a z hz).siftedSum := by
  classical
  unfold shiuPhi
  rw [BoundingSieve.siftedSum]
  change
    (∑ n ∈ Finset.Ioc (x - y) x,
      if n ≡ a [MOD k] ∧ shiuRough n z then (1 : ℝ) else 0) =
    ∑ n ∈ (Finset.Ioc (x - y) x).filter (fun n => n ≡ a [MOD k]),
      if (selectedPrimeProduct z k).Coprime n then (1 : ℝ) else 0
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hna : n ≡ a [MOD k]
  · have hsupport :
        (selectedPrimeProduct z k).Coprime n ↔ shiuRough n z := by
      simpa [Nat.coprime_comm] using
        (selectivePrimeSupport_iff_leastPrimeFactor
          (n := n) (a := a) (k := k) (z := z) hak hna)
    by_cases hrough : shiuRough n z
    · have hcop : (selectedPrimeProduct z k).Coprime n :=
        hsupport.mpr hrough
      simp [hna, hrough, hcop]
    · have hncop : ¬ (selectedPrimeProduct z k).Coprime n := by
        intro hcop
        exact hrough (hsupport.mp hcop)
      simp [hna, hrough, hncop]
  · simp [hna]

/-- Shiu Chapter 3, Section 3.4, Lemma 2, with an explicit absolute
implied constant 4. The constant is outside and independent of all varying
source parameters `x,y,z,k,a`. -/
theorem shiuLemma2
    (x y z k a : ℕ)
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hky : k < y) (hyx : y ≤ x) (hz : 2 ≤ z) :
    shiuPhi x y z k a ≤
      4 * ((y : ℝ) / ((k.totient : ℝ) * Real.log z) +
        (z : ℝ) ^ 2) := by
  have hk : 0 < k := by omega
  have hz1 : 1 ≤ z := by omega
  have hphi : (0 : ℝ) < (k.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hk
  have hlog : 0 < Real.log (z : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < z by omega)
  have hmain_nonneg :
      0 ≤ (y : ℝ) / ((k.totient : ℝ) * Real.log z) := by
    positivity
  calc
    shiuPhi x y z k a =
        (selectiveAPSieve x y k a z hz1).siftedSum :=
      shiuPhi_eq_siftedSum x y k a z hz1 hak
    _ ≤ (y : ℝ) / ((k.totient : ℝ) * Real.log z) +
        4 * (z : ℝ) ^ 2 := by
      simpa only using
        (selectivePrimeSieve_bound x y k a z hyx hk hz)
    _ ≤ 4 * ((y : ℝ) / ((k.totient : ℝ) * Real.log z) +
        (z : ℝ) ^ 2) := by
      nlinarith

end M4A
end PaperB
