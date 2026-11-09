module

public import ShiuPublic.CorvethClassicalPrefixCore
public import PaperB.M4B.ShiuClassI

public section

namespace PaperB.M4B
open scoped BigOperators
noncomputable section

/-- Public classical counterpart of the source's Class I witness,
with no squarefree predicate on the source integer. -/
@[expose] def corvethClassicalClassIPays
    (f : ArithmeticFunction ℝ) (x y z k a n : ℕ) : Prop :=
  ∃ u : ℕ × ℕ,
    n = u.1 * u.2 ∧
    f n = f u.1 * f u.2 ∧
    u.1 ∈ (Finset.Icc 1 z).filter (fun b => b.Coprime k) ∧
    u.2 ∈ classIInnerSet x y z k a u.1

/-- Every actual admissible progression point whose prime-power suffix
is sqrt(z)-rough is covered by the literal Class I overcount. -/
theorem corveth_classical_source_classI_of_rough
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    {x y z k a n : ℕ}
    (hnI : n ∈ Finset.Ioc (x - y) x)
    (hna : n ≡ a [MOD k])
    (hncop : n.Coprime k)
    (hz : 1 ≤ z)
    (hrough : PaperB.M4A.shiuRough
      (classical_primePower_prefix_split n z
        (by
          have hlow := (Finset.mem_Ioc.mp hnI).1
          omega) hz).large.prod (Nat.sqrt z)) :
    corvethClassicalClassIPays f x y z k a n := by
  classical
  have hn0 : n ≠ 0 := by
    have hlow := (Finset.mem_Ioc.mp hnI).1
    omega
  let S := classical_primePower_prefix_split n z hn0 hz
  obtain ⟨hfac, hbz, hcop, hbk, hdk, hfmul⟩ :=
    corveth_classical_primePower_source_core hf n z k hn0 hz hncop
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hbpos : 0 < S.small.prod := by
    have hpos : 0 < S.small.prod * S.large.prod := by
      rw [← hfac]
      exact hnpos
    exact pos_of_mul_pos_left hpos (Nat.zero_le _)
  have hblow : x - y < S.small.prod * S.large.prod := by
    rw [← hfac]
    exact (Finset.mem_Ioc.mp hnI).1
  have hbhigh : S.small.prod * S.large.prod ≤ x := by
    rw [← hfac]
    exact (Finset.mem_Ioc.mp hnI).2
  have hdscaled := scaledInterval_mem hbpos hblow hbhigh
  have hres : S.small.prod * S.large.prod ≡ a [MOD k] := by
    simpa only [hfac] using hna
  have hbmem : S.small.prod ∈
      (Finset.Icc 1 z).filter (fun b => b.Coprime k) := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hbz⟩, hbk⟩
  refine ⟨(S.small.prod, S.large.prod), hfac, hfmul, hbmem, ?_⟩
  unfold classIInnerSet
  rw [Finset.mem_filter]
  exact ⟨hdscaled, hres, hrough⟩

#print axioms corveth_classical_source_classI_of_rough
end
end PaperB.M4B
