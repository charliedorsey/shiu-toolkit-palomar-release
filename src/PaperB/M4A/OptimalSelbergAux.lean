module

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under the Apache License, Version 2.0, as described in the repository LICENSE.
Author: Arend Mellendijk.

Modified in 2026 for the Shiu Toolkit, under the direction of Charlie Dorsey,
with AI assistance; ported finite Mobius identities to pinned Lean 4.35.

Provenance:
https://github.com/amellendijk/selberg-sieve4
commit 64530a38a1e7e32357e1be8462dbfce5e445919a
SelbergSieve/AuxResults.lean.

Only the finite Möbius identities required by the locally ported optimal
Selberg weights are retained.
-/

public import Mathlib.NumberTheory.SelbergSieve

public section

open scoped ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction

namespace PaperB
namespace M4A

theorem sum_over_dvd_ite
    {α : Type*} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} :
    ∑ d ∈ n.divisors, f d =
      ∑ d ∈ P.divisors, if d ∣ n then f d else 0 := by
  rw [← Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]

theorem sum_intro
    {α M : Type*} [AddCommMonoid M] [DecidableEq α]
    (s : Finset α) {f : α → M} (d : α) (hd : d ∈ s) :
    f d = ∑ k ∈ s, if k = d then f k else 0 := by
  trans ∑ k ∈ s, if k = d then f d else 0
  · rw [sum_eq_single_of_mem d hd]
    · rw [if_pos rfl]
    · intro _ _ h
      rw [if_neg h]
  · apply sum_congr rfl
    intro k hk
    split_ifs with h
    · rw [h]
    · rfl

theorem moebius_inv_dvd_lower_bound
    (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d : ℤ) else 0) =
      if l = m then (μ l : ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  revert hm
  revert m
  apply
    (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on
      {n | Squarefree n}
      (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal'
    (f := fun x y => μ x • if l = y then μ l else 0)]
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul,
        ← isMultiplicative_moebius.map_mul_of_coprime, hmul]
      apply coprime_of_squarefree_mul
      rw [hmul]
      exact hm
    · intro d hd hdl
      rw [if_neg hdl.symm, smul_zero]
    · intro h
      rw [mem_divisors] at h
      exact (h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩).elim
  · rw [if_neg hl, sum_eq_zero]
    intro d hd
    rw [if_neg, smul_zero]
    intro h
    rw [← h] at hd
    exact hl (dvd_of_mem_divisors hd)

theorem moebius_inv_dvd_lower_bound'
    {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) =
      if l = m then μ l else 0 := by
  rw [← moebius_inv_dvd_lower_bound _ _
      (Squarefree.squarefree_of_dvd hm hP),
    sum_over_dvd_ite hP.ne_zero hm]
  simp_rw [ite_and, ← sum_filter, filter_comm]

theorem moebius_inv_dvd_lower_bound_real
    {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors,
      if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  norm_cast
  exact moebius_inv_dvd_lower_bound' hP l m hm

end M4A
end PaperB
