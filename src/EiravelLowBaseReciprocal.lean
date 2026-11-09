module

public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.PrimeCounting

public section

namespace PaperB.M4B
open scoped BigOperators
open Finset Nat

/-- Low-base part of the full-power reciprocal sum. This keeps the actual
positive modulus function, not a surrogate square-divisibility condition. -/
theorem eiravel_low_base_reciprocal_mass
    (T u : ℕ) (P : Finset ℕ) (m : ℕ → ℕ)
    (hP : P ⊆ Finset.Icc 1 u)
    (hT : 0 < T)
    (hm : ∀ p ∈ P, T < m p) :
    (∑ p ∈ P, (1 : ℝ) / (m p : ℝ)) ≤ (u : ℝ) / (T : ℝ) := by
  have hterm : ∀ p ∈ P, (1 : ℝ) / (m p : ℝ) ≤
      (1 : ℝ) / (T : ℝ) := by
    intro p hp
    have hpT : (T : ℝ) ≤ (m p : ℝ) := by
      exact_mod_cast (hm p hp).le
    exact one_div_le_one_div_of_le (by exact_mod_cast hT) hpT
  calc
    (∑ p ∈ P, (1 : ℝ) / (m p : ℝ)) ≤
        ∑ _p ∈ P, (1 : ℝ) / (T : ℝ) :=
      Finset.sum_le_sum hterm
    _ = (P.card : ℝ) * ((1 : ℝ) / (T : ℝ)) := by simp
    _ ≤ (u : ℝ) * ((1 : ℝ) / (T : ℝ)) := by
      have hcard : P.card ≤ u := by
        exact (Finset.card_le_card hP).trans (by simp)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (by positivity)
    _ = (u : ℝ) / (T : ℝ) := by ring

#print axioms eiravel_low_base_reciprocal_mass
end PaperB.M4B


/-- High-base reciprocal tail with the full crossing moduli. The bound is
controlled by mathlib's reciprocal-square interval sum, not a PNT estimate. -/
theorem eiravel_high_base_reciprocal_mass
    (T u : ℕ) (P : Finset ℕ) (m : ℕ → ℕ)
    (hP : P ⊆ Finset.Ioo u (T + 1))
    (hm : ∀ p ∈ P, p ^ 2 ≤ m p) :
    (∑ p ∈ P, (1 : ℝ) / (m p : ℝ)) ≤
      2 / ((u + 1 : ℕ) : ℝ) := by
  have hterm : ∀ p ∈ P, (1 : ℝ) / (m p : ℝ) ≤
      ((p : ℝ) ^ 2)⁻¹ := by
    intro p hp
    have hpp : 0 < (p : ℝ) ^ 2 := by
      have hpos : 0 < p := lt_of_le_of_lt (Nat.zero_le u) (Finset.mem_Ioo.mp (hP hp)).1
      positivity
    have hpcast : (p : ℝ)^2 ≤ (m p : ℝ) := by
      exact_mod_cast hm p hp
    simpa [one_div] using (inv_anti₀ hpp hpcast)
  calc
    (∑ p ∈ P, (1 : ℝ) / (m p : ℝ)) ≤
      ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ := Finset.sum_le_sum hterm
    _ ≤ ∑ p ∈ Finset.Ioo u (T + 1), ((p : ℝ) ^ 2)⁻¹ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hP
        (by intro p hp _; positivity)
    _ ≤ 2 / ((u + 1 : ℕ) : ℝ) := by
      push_cast
      exact sum_Ioo_inv_sq_le u (T + 1)

#print axioms eiravel_high_base_reciprocal_mass


namespace PaperB.M4B

/-- The two-regime reciprocal crossing mass bound. Exactly the interface
needed for minimal whole prime-power AP exceptions; no PNT and no
squarefree assumption on source integers. -/
theorem eiravel_full_power_reciprocal_split
    (T u : ℕ) (P : Finset ℕ) (m : ℕ → ℕ)
    (hP : P ⊆ Finset.Icc 1 T)
    (hT : 0 < T)
    (hmod : ∀ p ∈ P, T < m p)
    (hhigh : ∀ p ∈ P, u < p → p ^ 2 ≤ m p) :
    (∑ p ∈ P, (1 : ℝ) / (m p : ℝ)) ≤
      (u : ℝ) / (T : ℝ) + 2 / ((u + 1 : ℕ) : ℝ) := by
  let Lo := P.filter (fun p => p ≤ u)
  let Hi := P.filter (fun p => ¬ p ≤ u)
  have hlo : Lo ⊆ Finset.Icc 1 u := by
    intro p hp
    have hmemb := Finset.mem_filter.mp hp
    have hbase := Finset.mem_Icc.mp (hP hmemb.1)
    exact Finset.mem_Icc.mpr ⟨hbase.1, hmemb.2⟩
  have hhi : Hi ⊆ Finset.Ioo u (T + 1) := by
    intro p hp
    have hmemb := Finset.mem_filter.mp hp
    have hbase := Finset.mem_Icc.mp (hP hmemb.1)
    exact Finset.mem_Ioo.mpr ⟨Nat.lt_of_not_ge hmemb.2, Nat.lt_succ_of_le hbase.2⟩
  have hLo := eiravel_low_base_reciprocal_mass T u Lo m hlo hT
    (by intro p hp; exact hmod p (Finset.mem_filter.mp hp).1)
  have hHi := eiravel_high_base_reciprocal_mass T u Hi m hhi
    (by
      intro p hp
      have hmem := Finset.mem_filter.mp hp
      exact hhigh p hmem.1 (Nat.lt_of_not_ge hmem.2))
  calc
    (∑ p ∈ P, (1 : ℝ) / (m p : ℝ)) =
      (∑ p ∈ Lo, (1 : ℝ) / (m p : ℝ)) +
        (∑ p ∈ Hi, (1 : ℝ) / (m p : ℝ)) := by
      exact (Finset.sum_filter_add_sum_filter_not P (fun p => p ≤ u)
        (fun p => (1 : ℝ) / (m p : ℝ))).symm
    _ ≤ (u : ℝ) / (T : ℝ) + 2 / ((u + 1 : ℕ) : ℝ) :=
      add_le_add hLo hHi

#print axioms eiravel_full_power_reciprocal_split

end PaperB.M4B


namespace PaperB.M4B

/-- Apply the combined reciprocal estimate to the *actual minimal power*
p^(log_p T + 1) for any prime-base set below T. -/
theorem eiravel_minimal_crossing_prime_mass
    (T : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ T)
    (hT : 0 < T) :
    (∑ p ∈ P, (1 : ℝ) / (p ^ (Nat.log p T + 1) : ℕ)) ≤
       (Nat.sqrt T : ℝ) / (T : ℝ) +
         2 / ((Nat.sqrt T + 1 : ℕ) : ℝ) := by
  have hset : P ⊆ Finset.Icc 1 T := by
    intro p hp
    obtain ⟨hprime, hle⟩ := hP p hp
    exact Finset.mem_Icc.mpr ⟨hprime.one_le, hle⟩
  have hmod : ∀ p ∈ P, T < p ^ (Nat.log p T + 1) := by
    intro p hp
    exact Nat.lt_pow_succ_log_self (hP p hp).1.one_lt T
  have hhigh : ∀ p ∈ P, Nat.sqrt T < p →
      p ^ 2 ≤ p ^ (Nat.log p T + 1) := by
    intro p hp hpu
    obtain ⟨hprime, hle⟩ := hP p hp
    have hlog : 1 ≤ Nat.log p T := by
      exact Nat.le_log_of_pow_le hprime.one_lt
        (by simpa using hle)
    exact Nat.pow_le_pow_right hprime.pos (by omega)
  exact eiravel_full_power_reciprocal_split T (Nat.sqrt T)
    P (fun p => p ^ (Nat.log p T + 1)) hset hT hmod hhigh

#print axioms eiravel_minimal_crossing_prime_mass

end PaperB.M4B


namespace PaperB.M4B

/-- Literal eligible-prime set used in Tessara's source geometry.
The additional p∤k filter cannot increase the reciprocal mass. -/
theorem eiravel_eligible_crossing_prime_mass
    (z k : ℕ) (hT : 0 < Nat.sqrt z) :
    (∑ p ∈ (Nat.primesLE (Nat.sqrt z)).filter (fun p => ¬ p ∣ k),
      (1 : ℝ) /
        (p ^ (Nat.log p (Nat.sqrt z) + 1) : ℕ)) ≤
      (Nat.sqrt (Nat.sqrt z) : ℝ) / (Nat.sqrt z : ℝ) +
        2 / ((Nat.sqrt (Nat.sqrt z) + 1 : ℕ) : ℝ) := by
  apply eiravel_minimal_crossing_prime_mass (Nat.sqrt z)
    ((Nat.primesLE (Nat.sqrt z)).filter (fun p => ¬ p ∣ k)) ?_ hT
  intro p hp
  obtain ⟨hle, hprime⟩ := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
  exact ⟨hprime, hle⟩

#print axioms eiravel_eligible_crossing_prime_mass

end PaperB.M4B
