module

public import ShiuPublic.VaelisGeneralPrefixSplit
public import Mathlib.Data.Nat.Factorization.Basic

public section

namespace PaperB.M4B

/-- One atom for each distinct prime, retaining its full valuation. -/
@[expose] noncomputable def classicalPrimePowerAtoms (n : ℕ) : List ℕ :=
  n.primeFactors.toList.map (fun p => p ^ n.factorization p)

/-- The complete original integer is the product of its distinct-prime
prime-power atoms; no squarefree assumption. -/
theorem classical_primePowerAtoms_prod (n : ℕ) (hn : n ≠ 0) :
    (classicalPrimePowerAtoms n).prod = n := by
  unfold classicalPrimePowerAtoms
  have hprod (S : Finset ℕ) (g : ℕ → ℕ) :
      (S.toList.map g).prod = S.prod g := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | @insert p S hp ih => simp [hp, ih]
  rw [hprod]
  exact Nat.prod_factorization_pow_eq_self hn

#print axioms classical_primePowerAtoms_prod
end PaperB.M4B
