module

/-
Paper B M4A C2B: logarithmic lower bound for coprime harmonic mass.
-/

public import PaperB.M4A.CoprimeHarmonic
public import Mathlib.NumberTheory.Harmonic.Bounds

public section

open scoped BigOperators
open Finset Nat Real

noncomputable section

namespace PaperB
namespace M4A

/-- C2B target: finite coprime harmonic mass dominates the totient ratio
times the pinned logarithmic harmonic lower bound. -/
theorem coprimeHarmonic_log_lower
    (M k : ℕ) (hk : 0 < k) :
    coprimeHarmonic M k ≥
      ((k.totient : ℝ) / (k : ℝ)) * Real.log (M + 1) := by
  have hbase := coprimeHarmonic_lower M k hk
  have hlog :
      Real.log (M + 1) ≤ coprimeHarmonic M 1 := by
    rw [coprimeHarmonic_one]
    calc
      Real.log (M + 1) ≤ (harmonic M : ℝ) := by
        simpa [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic M
      _ = ∑ m ∈ Finset.Icc 1 M, ((m : ℝ)⁻¹) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hratio : 0 ≤ ((k.totient : ℝ) / (k : ℝ)) := by
    positivity
  exact (mul_le_mul_of_nonneg_left hlog hratio).trans hbase

end M4A
end PaperB
