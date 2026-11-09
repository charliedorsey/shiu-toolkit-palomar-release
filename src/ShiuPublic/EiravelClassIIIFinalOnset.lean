module

public import ShiuPublic.EiravelClassIIIUnconditional

public section

namespace PaperB.M4B

/-- Compose the source-exact eventual Class III cardinality onset with a
separately supplied final assembly threshold. -/
theorem eiravel_shiu_classIII_onset_reaches_final
    (Xassembly : ℕ) :
    ∃ Xfinal : ℕ,
      Xassembly ≤ Xfinal ∧
      ∀ x z k : ℕ,
        Xfinal ≤ x → x < z ^ 160 →
          Xassembly ≤ x ∧
          ((corvethClassicalClassIIIFactors x z k).card : ℝ) ≤
            (z : ℝ) ^ (1 / 4 : ℝ) := by
  obtain ⟨XIII, hIII⟩ := eiravel_classIII_card_quarter_eventually
  refine ⟨max Xassembly XIII, le_max_left _ _, ?_⟩
  intro x z k hx hxz
  constructor
  · exact (le_max_left _ _).trans hx
  · exact hIII x z k ((le_max_right _ _).trans hx) hxz

#print axioms eiravel_shiu_classIII_onset_reaches_final

end PaperB.M4B
