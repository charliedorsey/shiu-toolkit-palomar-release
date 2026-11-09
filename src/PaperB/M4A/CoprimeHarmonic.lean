module

/-
Paper B M4A C2A: finite coprime harmonic mass and Euler/totient factor.
-/

public import PaperB.M4A.SelectedPrimeBoundSum
public import Mathlib.Data.Nat.Totient

public section

open scoped BigOperators
open Finset Nat Real

noncomputable section

namespace PaperB
namespace M4A

/-- Harmonic mass up to `M` restricted to integers coprime to `k`. -/
@[expose] def coprimeHarmonic (M k : ℕ) : ℝ :=
  ∑ m ∈ (Finset.Icc 1 M).filter (fun m => m.Coprime k), ((m : ℝ)⁻¹)

@[simp]
theorem coprimeHarmonic_one (M : ℕ) :
    coprimeHarmonic M 1 = ∑ m ∈ Finset.Icc 1 M, ((m : ℝ)⁻¹) := by
  simp [coprimeHarmonic]

private theorem coprimeHarmonic_mul_prime_lower
    (M K p : ℕ) (hp : p.Prime) :
    coprimeHarmonic M (K * p) ≥
      (1 - ((p : ℝ)⁻¹)) * coprimeHarmonic M K := by
  classical
  let S := (Finset.Icc 1 M).filter (fun m => m.Coprime K)
  let D := S.filter (fun m => p ∣ m)
  let N := S.filter (fun m => ¬ p ∣ m)

  have hK : coprimeHarmonic M K = ∑ m ∈ S, ((m : ℝ)⁻¹) := by
    simp [coprimeHarmonic, S]

  have hKp : coprimeHarmonic M (K * p) = ∑ m ∈ N, ((m : ℝ)⁻¹) := by
    unfold coprimeHarmonic
    apply Finset.sum_congr
    · ext m
      simp only [N, S, Finset.mem_filter, Finset.mem_Icc]
      rw [Nat.coprime_mul_iff_right]
      constructor
      · rintro ⟨hmIcc, hmK, hmp⟩
        refine ⟨⟨hmIcc, hmK⟩, ?_⟩
        rw [Nat.coprime_comm, hp.coprime_iff_not_dvd] at hmp
        exact hmp
      · rintro ⟨⟨hmIcc, hmK⟩, hnp⟩
        refine ⟨hmIcc, hmK, ?_⟩
        rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
        exact hnp
    · intro m hm
      rfl

  have hsplit :
      (∑ m ∈ D, ((m : ℝ)⁻¹)) + (∑ m ∈ N, ((m : ℝ)⁻¹)) =
        ∑ m ∈ S, ((m : ℝ)⁻¹) := by
    simpa [D, N] using
      (Finset.sum_filter_add_sum_filter_not S (fun m : ℕ => p ∣ m)
        (fun m : ℕ => ((m : ℝ)⁻¹)))

  have hquot_inj :
      ∀ a ∈ D, ∀ b ∈ D, a / p = b / p → a = b := by
    intro a ha b hb hab
    have hpa : p ∣ a := (Finset.mem_filter.mp ha).2
    have hpb : p ∣ b := (Finset.mem_filter.mp hb).2
    calc
      a = a / p * p := (Nat.div_mul_cancel hpa).symm
      _ = b / p * p := by rw [hab]
      _ = b := Nat.div_mul_cancel hpb

  have hquot_subset :
      D.image (fun m => m / p) ⊆ S := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨m, hmD, rfl⟩
    have hmS : m ∈ S := (Finset.mem_filter.mp hmD).1
    have hpm : p ∣ m := (Finset.mem_filter.mp hmD).2
    rcases Finset.mem_filter.mp hmS with ⟨hmIcc, hmCop⟩
    rw [Finset.mem_Icc] at hmIcc
    rw [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · constructor
      · exact Nat.succ_le.mpr <|
          Nat.div_pos (Nat.le_of_dvd (Nat.succ_le.mp hmIcc.1) hpm) hp.pos
      · exact (Nat.div_le_self m p).trans hmIcc.2
    · exact hmCop.coprime_div_left hpm

  have hquot_sum :
      (∑ q ∈ D.image (fun m => m / p), ((q : ℝ)⁻¹)) =
        ∑ m ∈ D, (((m / p : ℕ) : ℝ)⁻¹) := by
    exact Finset.sum_image hquot_inj

  have hlost :
      (∑ m ∈ D, ((m : ℝ)⁻¹)) ≤
        ((p : ℝ)⁻¹) * ∑ m ∈ S, ((m : ℝ)⁻¹) := by
    have hweight :
        (∑ m ∈ D, ((m : ℝ)⁻¹)) =
          ((p : ℝ)⁻¹) * ∑ m ∈ D, (((m / p : ℕ) : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hpm : p ∣ m := (Finset.mem_filter.mp hm).2
      have hm_eq : m = m / p * p := (Nat.div_mul_cancel hpm).symm
      conv_lhs => rw [hm_eq, Nat.cast_mul, mul_inv]
      ring
    rw [hweight, ← hquot_sum]
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum_of_subset_of_nonneg hquot_subset
      intro i hi hnot
      positivity
    · positivity

  rw [hK, hKp]
  calc
    (1 - ((p : ℝ)⁻¹)) * (∑ m ∈ S, ((m : ℝ)⁻¹))
        = (∑ m ∈ S, ((m : ℝ)⁻¹)) -
            ((p : ℝ)⁻¹) * (∑ m ∈ S, ((m : ℝ)⁻¹)) := by ring
    _ ≤ (∑ m ∈ S, ((m : ℝ)⁻¹)) - (∑ m ∈ D, ((m : ℝ)⁻¹)) :=
      sub_le_sub_left hlost _
    _ = ∑ m ∈ N, ((m : ℝ)⁻¹) := by linarith [hsplit]

private theorem coprimeHarmonic_prod_primes_lower
    (M : ℕ) (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) :
    coprimeHarmonic M (∏ p ∈ S, p) ≥
      (∏ p ∈ S, (1 - ((p : ℝ)⁻¹))) * coprimeHarmonic M 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [coprimeHarmonic]
  | @insert p S hpS ih =>
      have hpp : p.Prime := hprime p (Finset.mem_insert_self p S)
      have hprimeS : ∀ q ∈ S, q.Prime :=
        fun q hq => hprime q (Finset.mem_insert_of_mem hq)
      have hih := ih hprimeS
      have hstep :=
        coprimeHarmonic_mul_prime_lower M (∏ q ∈ S, q) p hpp
      have hp_one : (1 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast hpp.one_lt.le
      have hfactor_nonneg : 0 ≤ (1 - ((p : ℝ)⁻¹)) := by
        exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp_one)
      have hscaled := mul_le_mul_of_nonneg_left hih hfactor_nonneg
      exact (by
        simpa [Finset.prod_insert, hpS, mul_comm, mul_left_comm, mul_assoc] using
          hscaled.trans hstep)

private theorem coprimeHarmonic_prod_primeFactors_eq
    (M k : ℕ) (hk : 0 < k) :
    coprimeHarmonic M (∏ p ∈ k.primeFactors, p) = coprimeHarmonic M k := by
  classical
  unfold coprimeHarmonic
  apply Finset.sum_congr
  · ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hmIcc, hmCopRad⟩
      refine ⟨hmIcc, ?_⟩
      by_contra hmCopK
      obtain ⟨p, hp, hpm, hpk⟩ := Nat.Prime.not_coprime_iff_dvd.mp hmCopK
      have hpmem : p ∈ k.primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨hp, hpk, hk.ne'⟩
      have hpRad : p ∣ ∏ q ∈ k.primeFactors, q := by
        exact Finset.dvd_prod_of_mem (fun q => q) hpmem
      exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpm hpRad) hmCopRad
    · rintro ⟨hmIcc, hmCopK⟩
      exact ⟨hmIcc, hmCopK.coprime_dvd_right (Nat.prod_primeFactors_dvd k)⟩
  · intro m hm
    rfl

private theorem totient_ratio_eq_prod_primeFactors
    (k : ℕ) (hk : 0 < k) :
    ((k.totient : ℝ) / (k : ℝ)) =
      ∏ p ∈ k.primeFactors, (1 - ((p : ℝ)⁻¹)) := by
  have hq := Nat.totient_eq_mul_prod_factors k
  have hq' := congrArg (fun q : ℚ => (q : ℝ)) hq
  have hr :
      (k.totient : ℝ) =
        (k : ℝ) * ∏ p ∈ k.primeFactors, (1 - ((p : ℝ)⁻¹)) := by
    simpa using hq'
  rw [hr]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast hk.ne')

/-- C2A target: deleting the prime factors of `k` costs at most the Euler
factor `φ(k)/k` in finite harmonic mass. -/
theorem coprimeHarmonic_lower
    (M k : ℕ) (hk : 0 < k) :
    coprimeHarmonic M k ≥
      ((k.totient : ℝ) / (k : ℝ)) * coprimeHarmonic M 1 := by
  have hprime : ∀ p ∈ k.primeFactors, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  have h :=
    coprimeHarmonic_prod_primes_lower M k.primeFactors hprime
  rw [coprimeHarmonic_prod_primeFactors_eq M k hk] at h
  rw [totient_ratio_eq_prod_primeFactors k hk]
  exact h

end M4A
end PaperB
