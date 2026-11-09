module

public import EiravelSourceWeightedAssembly

public import ChallengeDefs.Progressions

public section

/-! Conventional short arithmetic progressions, proven source-faithful. -/
namespace Shiu.API
open scoped BigOperators

/- Public name for the exact source prime-mass term
`∑_{p≤x, p prime, p∤k} f(p)/p`. This is a reducible alias,
not a new estimate or a changed normalization. -/
-- Shared Mathlib-only source definition: ChallengeDefs.Progressions.primeMass

def progressionSet (x y k a : ℕ) : Finset ℕ :=
  (Finset.Ioc (x-y) x).filter (fun n => n ≡ a [MOD k])

-- Shared Mathlib-only source definition: ChallengeDefs.Progressions.progressionSum

theorem progressionSum_eq_sum_set
    (f : ArithmeticFunction ℝ) (x y k a : ℕ) :
    progressionSum f x y k a = ∑ n ∈ progressionSet x y k a, f n := by
  classical
  simp [progressionSum, progressionSet, Finset.sum_filter]

/-- Source's extra coprime guard follows from the reduced residue. -/
theorem progressionSet_eq_source (x y k a : ℕ) (ha : a.Coprime k) :
    progressionSet x y k a =
      PaperB.M4B.eiravelShiuPhysicalSet x y k a := by
  classical
  ext n
  simp only [progressionSet, PaperB.M4B.eiravelShiuPhysicalSet,
    Finset.mem_filter]
  constructor
  · intro hn
    exact ⟨hn.1, hn.2,
      PaperB.M4B.coprime_of_modEq_reduced ha hn.2⟩
  · intro hn
    exact ⟨hn.1, hn.2.1⟩

theorem progressionSum_eq_source
    (f : ArithmeticFunction ℝ) (x y k a : ℕ)
    (ha : a.Coprime k) :
    progressionSum f x y k a =
      ∑ n ∈ PaperB.M4B.eiravelShiuPhysicalSet x y k a, f n := by
  rw [progressionSum_eq_sum_set, progressionSet_eq_source x y k a ha]

#print axioms progressionSum_eq_source
end Shiu.API
