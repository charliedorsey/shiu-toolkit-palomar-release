module

public import ShiuPublic.VaelisOriginalSmoothEuler
public import PaperB.M4B.ShiuCore

public section

namespace PaperB.M4B
open scoped BigOperators
open Finset Nat Real
noncomputable section

/-- Original Shiu harmonic mass with all prime powers: exact Rankin-Euler
transport retaining the original primeMass and rankinCorrection. -/
theorem corveth_classical_coprime_harmonic_rankin
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : Shiu.ClassicalEnvelope f A) (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n → f n ≤ B * (n : ℝ) ^ (1 / 4 : ℝ))
    (z k : ℕ) (hz : 0 < z)
    (hzlarge : Real.exp 4 ≤ (z : ℝ)) :
    coprimeHarmonicMass f z k ≤
      Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A 1) B *
        Real.exp (primeMass f z k +
          primeRankinCorrection f z k (1 / Real.log (z : ℝ)) +
          2 * A ^ 2 * Real.exp 2) := by
  classical
  let P := (Nat.primesLE z).filter (fun p => ¬ p ∣ k)
  let Q := (Finset.Icc 1 z).filter (fun b => b.Coprime k)
  let δ : ℝ := 1 / Real.log (z : ℝ)
  have hz1 : (1 : ℝ) < z := (show (1 : ℝ) < Real.exp 4 by
    nlinarith [Real.add_one_le_exp (4 : ℝ)]).trans_le hzlarge
  have hlog : 0 < Real.log (z : ℝ) := Real.log_pos hz1
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hsubset : Q ⊆ Shiu.boundedSmoothSet P z := by
    intro b hb
    obtain ⟨hbI, hbCop⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb1, hbz⟩ := Finset.mem_Icc.mp hbI
    apply Finset.mem_filter.mpr
    refine ⟨hbI, ?_⟩
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpb : p ∣ b := Nat.dvd_of_mem_primeFactors hp
    have hple : p ≤ z := (Nat.le_of_dvd (by omega) hpb).trans hbz
    have hnot : ¬ p ∣ k := by
      intro hpk
      have hone : p ∣ 1 := by
        rw [← hbCop.gcd_eq_one]
        exact Nat.dvd_gcd hpb hpk
      exact hpp.not_dvd_one hone
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_primesLE.mpr ⟨hple, hpp⟩, hnot⟩
  have hpoint : ∀ b ∈ Q,
      f b / (b : ℝ) ≤ f b / (b : ℝ) ^ (1 - δ) := by
    intro b hb
    have hb1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
    have hb1R : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    have hpow : (b : ℝ) ^ (1 - δ) ≤ (b : ℝ) :=
      Real.rpow_le_self_of_one_le hb1R (by linarith)
    have hpowpos : 0 < (b : ℝ) ^ (1 - δ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < b by omega)) _
    exact div_le_div_of_nonneg_left (hf.nonnegative b) hpowpos hpow
  have hmass := Shiu.classical_bounded_smooth_original_mass
    hf hB hgrowth z z k hz (1 : ℝ) (by norm_num) (by simpa only [mul_one] using hzlarge)
  calc
    coprimeHarmonicMass f z k =
        ∑ b ∈ Q, f b / (b : ℝ) := by rfl
    _ ≤ ∑ b ∈ Q, f b / (b : ℝ) ^ (1 - δ) :=
      Finset.sum_le_sum hpoint
    _ ≤ ∑ b ∈ Shiu.boundedSmoothSet P z,
        f b / (b : ℝ) ^ (1 - δ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun b hb _ => div_nonneg (hf.nonnegative b)
          (Real.rpow_nonneg (by positivity) _))
    _ ≤ _ := by simpa only [P, δ, mul_one] using hmass

#print axioms corveth_classical_coprime_harmonic_rankin
end
end PaperB.M4B
