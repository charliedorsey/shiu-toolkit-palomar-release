module

public import Mathlib

public section

namespace PaperB.M4B

/-- Finite weighted overcover for a four-way pointwise disjunction.
The sum of all four indicated masses dominates the unpartitioned
physical source, even if the classes overlap. -/
theorem eiravel_four_way_finite_weighted_cover
    {α : Type*} [DecidableEq α]
    (S : Finset α) (w : α → ℝ)
    (P₁ P₂ P₃ P₄ : α → Prop)
    [DecidablePred P₁] [DecidablePred P₂]
    [DecidablePred P₃] [DecidablePred P₄]
    (hw : ∀ a ∈ S, 0 ≤ w a)
    (hcover : ∀ a ∈ S, P₁ a ∨ P₂ a ∨ P₃ a ∨ P₄ a) :
    (∑ a ∈ S, w a) ≤
      (∑ a ∈ S.filter P₁, w a) +
      (∑ a ∈ S.filter P₂, w a) +
      (∑ a ∈ S.filter P₃, w a) +
      (∑ a ∈ S.filter P₄, w a) := by
  have hpoint : ∀ a ∈ S,
      w a ≤
      (if P₁ a then w a else 0) +
      (if P₂ a then w a else 0) +
      (if P₃ a then w a else 0) +
      (if P₄ a then w a else 0) := by
    intro a ha
    rcases hcover a ha with h1 | h2 | h3 | h4
    · simp only [if_pos h1]
      split_ifs <;> nlinarith [hw a ha]
    · simp only [if_pos h2]
      split_ifs <;> nlinarith [hw a ha]
    · simp only [if_pos h3]
      split_ifs <;> nlinarith [hw a ha]
    · simp only [if_pos h4]
      split_ifs <;> nlinarith [hw a ha]
  calc
    (∑ a ∈ S, w a) ≤
      ∑ a ∈ S,
        ((if P₁ a then w a else 0) +
         (if P₂ a then w a else 0) +
         (if P₃ a then w a else 0) +
         (if P₄ a then w a else 0)) :=
      Finset.sum_le_sum hpoint
    _ = (∑ a ∈ S.filter P₁, w a) +
        (∑ a ∈ S.filter P₂, w a) +
        (∑ a ∈ S.filter P₃, w a) +
        (∑ a ∈ S.filter P₄, w a) := by
      simp only [Finset.sum_add_distrib, Finset.sum_filter]

#print axioms eiravel_four_way_finite_weighted_cover

end PaperB.M4B
