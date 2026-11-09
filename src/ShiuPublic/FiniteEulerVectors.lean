module

public import ShiuPublic.PrimePowerEnvelope

public section

/-! Exact finite prime-power Euler expansion, indexed by exponent vectors.
No squarefree-support assumption and no infinite convergence assertion. -/
namespace Shiu
open scoped BigOperators

/-- Complete finite expansion retaining exponent multiplicity, with
a finite prime set and a uniform exponent cutoff. -/
theorem finite_euler_vector_expansion
    (S : Finset ℕ) (N : ℕ) (w : ℕ → ℕ → ℝ) :
    (∏ p ∈ S, ∑ j ∈ Finset.range (N + 1), w p j) =
      ∑ e ∈ S.pi (fun _ => Finset.range (N + 1)),
        ∏ p ∈ S.attach, w p.val (e p.val p.property) := by
  exact Finset.prod_sum S (fun _ => Finset.range (N + 1)) w

/-- An Euler expansion at the actual Rankin-shifted local factors.
The product is indexed by all exponent vectors, including repeated powers. -/
theorem finite_euler_rankin_vectors
    (f : ℕ → ℝ) (S : Finset ℕ) (N : ℕ) (s : ℝ) :
    (∏ p ∈ S,
      ∑ j ∈ Finset.range (N + 1),
        f (p ^ j) / (p : ℝ) ^ ((j : ℝ) * s)) =
      ∑ e ∈ S.pi (fun _ => Finset.range (N + 1)),
        ∏ p ∈ S.attach,
          f (p.val ^ e p.val p.property) /
            (p.val : ℝ) ^ ((e p.val p.property : ℝ) * s) := by
  exact finite_euler_vector_expansion S N
    (fun p j => f (p ^ j) / (p : ℝ) ^ ((j : ℝ) * s))

#print axioms Shiu.finite_euler_vector_expansion
#print axioms Shiu.finite_euler_rankin_vectors
end Shiu
