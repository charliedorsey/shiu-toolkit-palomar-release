module

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under the Apache License, Version 2.0, as described in the repository LICENSE.
Author: Arend Mellendijk and contributors to Mathlib.

Modified in 2026 for the Shiu Toolkit, under the direction of Charlie Dorsey,
with AI assistance; adapted for the pinned Lean 4.35 and local sieve proof interfaces.

Provenance:
* https://github.com/amellendijk/selberg-sieve4
  commit 64530a38a1e7e32357e1be8462dbfce5e445919a
  especially SelbergSieve/Selberg.lean.
* mathlib PR #27707, head
  7df57a4044c8c8a00c44944786e838a24ee229cb,
  Mathlib/NumberTheory/SelbergSieve.lean.

This file is a local port to the frozen Paper B M3 dependency closure.  The
upstream projects are proof/reference provenance only; no dependency is
retargeted.
-/

public import Mathlib.NumberTheory.SelbergSieve
public import PaperB.M4A.OptimalSelbergAux
public import Mathlib.Tactic

public section

open scoped ArithmeticFunction.Moebius
open Finset Real Nat ArithmeticFunction

noncomputable section

namespace PaperB
namespace M4A

/-- Local optimal Selberg bounding sum on the frozen M3 mathlib API. -/
@[expose] def selbergBoundSum (s : SelbergSieve) : ℝ :=
  ∑ l ∈ divisors s.prodPrimes with (l : ℕ) ^ 2 ≤ s.level, s.selbergTerms l

theorem selbergBoundSum_pos (s : SelbergSieve) :
    0 < selbergBoundSum s := by
  dsimp only [selbergBoundSum]
  apply sum_pos
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    exact s.selbergTerms_pos hl.1.1
  · simp_rw [Finset.nonempty_def, mem_filter]
    use 1
    simpa using ⟨s.prodPrimes_ne_zero, s.one_le_level⟩

/-- Local Selberg optimal weights, ported onto the frozen M3 API. -/
def selbergWeights (s : SelbergSieve) (d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes then
    (s.nu d)⁻¹ * s.selbergTerms d * μ d * (selbergBoundSum s)⁻¹ *
      ∑ m ∈ divisors s.prodPrimes with
        (d * (m : ℕ)) ^ 2 ≤ s.level ∧ m.Coprime d, s.selbergTerms m
  else 0

theorem selbergWeights_eq_zero_of_not_dvd
    (s : SelbergSieve) {d : ℕ} (hd : ¬ d ∣ s.prodPrimes) :
    selbergWeights s d = 0 := by
  rw [selbergWeights, ite_eq_right hd]

theorem selbergWeights_eq_zero
    (s : SelbergSieve) (d : ℕ) (hd : s.level < d ^ 2) :
    selbergWeights s d = 0 := by
  dsimp only [selbergWeights]
  split_ifs with h
  · rw [mul_eq_zero_of_right _]
    apply Finset.sum_eq_zero
    simp only [mem_filter, mem_divisors, ne_eq, and_imp]
    rintro m hmP - hmLevel hmCoprime
    have hmono : (d ^ 2 : ℝ) ≤ (d * m)^2 := by
      norm_cast
      gcongr
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_dvd_of_pos hmP s.prodPrimes_ne_zero.pos)
    linarith
  · rfl

theorem selbergWeights_mul_mu_nonneg
    (s : SelbergSieve) {d : ℕ} (hdP : d ∣ s.prodPrimes) :
    0 ≤ selbergWeights s d * μ d := by
  dsimp only [selbergWeights]
  rw [ite_eq_left hdP, mul_assoc]
  trans ((μ d : ℝ) ^ 2 * (s.nu d)⁻¹ * s.selbergTerms d * (selbergBoundSum s)⁻¹ *
    ∑ m ∈ divisors s.prodPrimes with
      (d * (m : ℕ)) ^ 2 ≤ s.level ∧ Coprime m d, s.selbergTerms m)
  · apply mul_nonneg
    · positivity [s.selbergTerms_pos hdP, s.nu_pos_of_dvd_prodPrimes hdP,
        (selbergBoundSum_pos s).le]
    refine sum_nonneg fun m hm ↦ ?_
    exact le_of_lt <| s.selbergTerms_pos (dvd_of_mem_divisors (mem_of_mem_filter _ hm))
  · apply le_of_eq
    ring

private lemma sum_mul_subst
    (k n : ℕ) {f : ℕ → ℝ}
    (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
    ∑ l ∈ n.divisors, f l =
      ∑ m ∈ n.divisors, if k * m ∣ n then f (k * m) else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  · have hk : k ≠ 0 := by
      intro hk0
      subst k
      exact hn (zero_dvd_iff.mp hkn)
    trans ∑ l ∈ n.divisors, ∑ m ∈ n.divisors,
        if l = k * m then f l else 0
    · apply sum_congr rfl
      intro l hl
      by_cases hkl : k ∣ l
      · rw [sum_eq_single (l / k)]
        · simp [Nat.mul_div_cancel' hkl]
        · intro m hm hne
          rw [if_neg]
          intro heq
          apply hne
          apply Nat.mul_left_cancel (Nat.pos_of_ne_zero hk)
          rw [← heq, Nat.mul_div_cancel' hkl]
        · intro hnot
          exfalso
          apply hnot
          rw [mem_divisors]
          exact ⟨(Nat.div_dvd_of_dvd hkl).trans
            (dvd_of_mem_divisors hl), hn⟩
      · rw [h l (dvd_of_mem_divisors hl) hkl, sum_eq_zero]
        intro m hm
        split_ifs <;> rfl
    · rw [sum_comm]
      apply sum_congr rfl
      intro m hm
      by_cases hkm : k * m ∣ n
      · rw [ite_eq_left hkm, sum_eq_single (k * m)]
        · simp
        · intro l hl hne
          simp [hne]
        · intro hnot
          exact (hnot (mem_divisors.mpr ⟨hkm, hn⟩)).elim
      · rw [ite_eq_right hkm, sum_eq_zero]
        intro l hl
        rw [if_neg]
        intro heq
        exact hkm (heq ▸ dvd_of_mem_divisors hl)
  · rw [sum_eq_zero, sum_eq_zero]
    · intro m hm
      rw [ite_eq_right]
      intro hkm
      exact hkn ((Nat.dvd_mul_right k m).trans hkm)
    · intro l hl
      apply h l (dvd_of_mem_divisors hl)
      intro hkl
      exact hkn (hkl.trans (dvd_of_mem_divisors hl))

theorem sum_selbergTerms_dvd_eq_mul_sum_coprime
    (s : SelbergSieve) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    ∑ l ∈ divisors s.prodPrimes with d ∣ l ∧ l ^ 2 ≤ s.level, s.selbergTerms l =
      s.selbergTerms d *
        ∑ m ∈ divisors s.prodPrimes with
          (d * (m : ℕ)) ^ 2 ≤ s.level ∧ m.Coprime d, s.selbergTerms m := by
  rw [sum_filter, sum_mul_subst d s.prodPrimes (by simp +contextual)]
  simp_rw [← sum_filter, mul_sum]
  apply sum_congr _
  · intro m
    simp only [mem_filter, mem_divisors, ne_eq, and_imp]
    intro x _ _ h
    exact s.selbergTerms_isMultiplicative.map_mul_of_coprime h.symm
  · ext m
    simp only [dvd_mul_right, cast_mul, true_and, mem_filter, mem_divisors, ne_eq,
      and_assoc, and_congr_right_iff]
    rw [and_comm, and_congr_right_iff]
    intro hmP hP _
    constructor
    · intro h
      apply Coprime.symm <| coprime_of_squarefree_mul _
      apply s.prodPrimes_squarefree.squarefree_of_dvd h
    · intro h
      refine Coprime.mul_dvd_of_dvd_of_dvd h.symm hd hmP

theorem nu_mul_selbergWeights_eq
    (s : SelbergSieve) (d : ℕ) :
    s.nu d * selbergWeights s d =
      (selbergBoundSum s)⁻¹ * μ d *
        ∑ l ∈ divisors s.prodPrimes with
          d ∣ l ∧ l ^ 2 ≤ s.level, s.selbergTerms l := by
  by_cases h_dvd : d ∣ s.prodPrimes
  · dsimp only [selbergWeights]
    rw [ite_eq_left h_dvd]
    simp_rw [mul_sum]
    apply symm
    simp_rw [← mul_sum, sum_selbergTerms_dvd_eq_mul_sum_coprime s h_dvd, ← mul_assoc]
    rw [mul_inv_cancel₀ (s.nu_ne_zero h_dvd)]
    ring
  · rw [selbergWeights, ite_eq_right h_dvd, sum_eq_zero]
    · ring
    intro l hl
    rw [mem_filter, mem_divisors] at hl
    exact (h_dvd (dvd_trans hl.2.1 hl.1.1)).elim

/-- Diagonalisation of the locally ported optimal Selberg weights. -/
theorem selbergWeights_diagonalisation
    (s : SelbergSieve) (l : ℕ) (hl : l ∈ divisors s.prodPrimes) :
    (∑ d ∈ divisors s.prodPrimes,
        if l ∣ d then s.nu d * selbergWeights s d else 0) =
      if l ^ 2 ≤ s.level then
        s.selbergTerms l * μ l * (selbergBoundSum s)⁻¹
      else 0 := by
  calc
    (∑ d ∈ divisors s.prodPrimes,
        if l ∣ d then s.nu d * selbergWeights s d else 0) =
      ∑ d ∈ divisors s.prodPrimes, ∑ k ∈ divisors s.prodPrimes,
        if l ∣ d ∧ d ∣ k ∧ k ^ 2 ≤ s.level then
          s.selbergTerms k * (selbergBoundSum s)⁻¹ * (μ d : ℝ)
        else 0 := by
      apply sum_congr rfl
      intro d hd
      rw [nu_mul_selbergWeights_eq s d, ← boole_mul, mul_sum, mul_sum,
        Finset.sum_filter]
      apply sum_congr rfl
      intro k hk
      by_cases hld : l ∣ d
      · by_cases hdk : d ∣ k ∧ (k : ℝ) ^ 2 ≤ s.level
        · simp [hld, hdk]
          ring
        · simp [hld, hdk]
      · simp [hld]
    _ = ∑ k ∈ divisors s.prodPrimes,
        if k ^ 2 ≤ s.level then
          (∑ d ∈ divisors s.prodPrimes,
            if l ∣ d ∧ d ∣ k then (μ d : ℝ) else 0) *
            s.selbergTerms k * (selbergBoundSum s)⁻¹
        else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro k hk
      apply symm
      rw [← boole_mul, sum_mul, sum_mul, mul_sum]
      apply sum_congr rfl
      intro d hd
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ← ite_and]
      apply if_ctx_congr
      · tauto
      · intro _
        ring
      · intro _
        rfl
    _ = if l ^ 2 ≤ s.level then
        s.selbergTerms l * μ l * (selbergBoundSum s)⁻¹
      else 0 := by
      rw [sum_intro
        (f := fun _ =>
          if l ^ 2 ≤ s.level then
            s.selbergTerms l * μ l * (selbergBoundSum s)⁻¹
          else 0)
        (divisors s.prodPrimes) l hl]
      apply sum_congr rfl
      intro k hk
      rw [moebius_inv_dvd_lower_bound_real
        s.prodPrimes_squarefree l k (dvd_of_mem_divisors hk),
        ← ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr
      · rw [and_comm, eq_comm]
        apply and_congr_right
        intro heq
        rw [heq]
      · intro h
        rw [h.1]
        ring
      · intro _
        rfl

/-- The local optimal weight is normalized by gamma(1)=1. -/
theorem selbergWeights_one (s : SelbergSieve) :
    selbergWeights s 1 = 1 := by
  have h := nu_mul_selbergWeights_eq s 1
  have hnu : s.nu 1 = 1 := s.nu_mult.1
  have hS : selbergBoundSum s ≠ 0 := (selbergBoundSum_pos s).ne'
  rw [hnu, one_mul] at h
  have h' :
      selbergWeights s 1 =
        (selbergBoundSum s)⁻¹ * selbergBoundSum s := by
    simpa [selbergBoundSum] using h
  rw [inv_mul_cancel₀ hS] at h'
  exact h'

/-- Lambda-squared upper-sieve coefficients built from the local optimal weights. -/
@[expose] def selbergMuPlus (s : SelbergSieve) : ℕ → ℝ :=
  BoundingSieve.lambdaSquared (selbergWeights s)

theorem selbergMuPlus_upper (s : SelbergSieve) :
    BoundingSieve.IsUpperMoebius (selbergMuPlus s) := by
  exact BoundingSieve.upperMoebius_lambdaSquared
    (selbergWeights s) (selbergWeights_one s)

/-- Exact main-term evaluation for the locally ported optimal Selberg weights. -/
theorem selberg_mainSum_eq_inv (s : SelbergSieve) :
    s.mainSum (selbergMuPlus s) = (selbergBoundSum s)⁻¹ := by
  rw [selbergMuPlus, s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  trans ∑ l ∈ divisors s.prodPrimes,
      if (l : ℝ) ^ 2 ≤ s.level then
        s.selbergTerms l * (selbergBoundSum s)⁻¹ ^ 2
      else 0
  · apply sum_congr rfl
    intro l hl
    rw [selbergWeights_diagonalisation s l hl]
    by_cases hLevel : (l : ℝ) ^ 2 ≤ s.level
    · simp only [if_pos hLevel]
      have hsq : ((μ l : ℝ) ^ 2) = 1 := by
        norm_cast
        exact moebius_sq_eq_one_of_squarefree
          (s.squarefree_of_mem_divisors_prodPrimes hl)
      have hg : s.selbergTerms l ≠ 0 :=
        (s.selbergTerms_pos (dvd_of_mem_divisors hl)).ne'
      calc
        (s.selbergTerms l)⁻¹ *
            (s.selbergTerms l * (μ l : ℝ) * (selbergBoundSum s)⁻¹) ^ 2 =
          (s.selbergTerms l)⁻¹ * (s.selbergTerms l) ^ 2 *
            ((μ l : ℝ) ^ 2) * ((selbergBoundSum s)⁻¹ ^ 2) := by ring
        _ = s.selbergTerms l * (selbergBoundSum s)⁻¹ ^ 2 := by
          rw [hsq]
          field_simp [hg]
    · simp [hLevel]
  · have hS : selbergBoundSum s ≠ 0 := (selbergBoundSum_pos s).ne'
    simp_rw [← ite_zero_mul]
    rw [← sum_mul]
    have hsum :
        (∑ l ∈ divisors s.prodPrimes,
          if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0) =
          selbergBoundSum s := by
      rw [selbergBoundSum, ← sum_filter]
    rw [hsum]
    field_simp [hS]

private lemma eq_gcd_mul_of_dvd_of_coprime
    {k d m : ℕ} (hkd : k ∣ d) (hmd : Coprime m d) (hk : k ≠ 0) :
    k = d.gcd (k * m) := by
  rcases hkd with ⟨r, rfl⟩
  have hrdvd : r ∣ k * r := by simp
  apply symm
  rw [Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  exact hmd.coprime_dvd_right hrdvd

private lemma selberg_bound_helper
    (s : SelbergSieve) {k m d : ℕ}
    (hkd : k ∣ d) (hk : k ∈ divisors s.prodPrimes)
    (hm : m ∈ divisors s.prodPrimes) :
    (k * m ∣ s.prodPrimes ∧
        k = Nat.gcd d (k * m) ∧
        ((k * m : ℕ) : ℝ) ^ 2 ≤ s.level) ↔
      (((k * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ Coprime m d) := by
  constructor
  · intro h
    constructor
    · exact h.2.2
    · rcases hkd with ⟨r, rfl⟩
      rw [Nat.gcd_mul_left, eq_comm,
        mul_eq_left₀ (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero
          (dvd_of_mem_divisors hk))] at h
      rw [coprime_comm]
      apply Nat.Coprime.mul_left
      · apply coprime_of_squarefree_mul
        exact s.prodPrimes_squarefree.squarefree_of_dvd h.1
      · exact h.2.1
  · intro h
    constructor
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [coprime_comm]
        exact h.2.coprime_dvd_right hkd
      · exact dvd_of_mem_divisors hk
      · exact dvd_of_mem_divisors hm
    constructor
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h.2
        (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero
          (dvd_of_mem_divisors hk))
    · exact h.1

private theorem selbergBoundSum_ge_weight
    (s : SelbergSieve) {d : ℕ} (hdP : d ∣ s.prodPrimes) :
    selbergBoundSum s ≥
      selbergWeights s d * (μ d : ℝ) * selbergBoundSum s := by
  let P := s.prodPrimes
  let S := selbergBoundSum s
  calc
    S = ∑ l ∈ divisors P,
        if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0 := by
      dsimp [S, P, selbergBoundSum]
      rw [Finset.sum_filter]
    _ = ∑ k ∈ divisors P, ∑ l ∈ divisors P,
        if k = d.gcd l ∧ (l : ℝ) ^ 2 ≤ s.level
        then s.selbergTerms l else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro l hl
      simp_rw [ite_and]
      rw [← sum_intro
        (f := fun k =>
          if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0)
        (divisors P) (d.gcd l)]
      rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_right d l).trans (dvd_of_mem_divisors hl),
        s.prodPrimes_ne_zero⟩
    _ = ∑ k ∈ divisors P,
        if k ∣ d then
          s.selbergTerms k *
            ∑ m ∈ divisors P,
              if ((k * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d
              then s.selbergTerms m else 0
        else 0 := by
      apply sum_congr rfl
      intro k hk
      by_cases hkd : k ∣ d
      · rw [if_pos hkd, mul_sum]
        have hzero :
            ∀ l, l ∣ P → ¬ k ∣ l →
              (if k = d.gcd l ∧ (l : ℝ) ^ 2 ≤ s.level
                then s.selbergTerms l else 0) = 0 := by
          intro l hl hnot
          rw [if_neg]
          intro h
          exact hnot (h.1 ▸ Nat.gcd_dvd_right d l)
        rw [sum_mul_subst k P hzero]
        apply sum_congr rfl
        intro m hm
        rw [mul_ite_zero, ← ite_and]
        apply if_ctx_congr
        · exact selberg_bound_helper s hkd hk hm
        · intro h
          have hkm : k.Coprime m :=
            (h.2.coprime_dvd_right hkd).symm
          exact s.selbergTerms_isMultiplicative.map_mul_of_coprime hkm
        · intro _
          rfl
      · rw [if_neg hkd, sum_eq_zero]
        intro l hl
        rw [if_neg]
        intro h
        exact hkd (h.1 ▸ Nat.gcd_dvd_left d l)
    _ ≥ ∑ k ∈ divisors P,
        if k ∣ d then
          s.selbergTerms k *
            ∑ m ∈ divisors P,
              if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d
              then s.selbergTerms m else 0
        else 0 := by
      apply sum_le_sum
      intro k hk
      by_cases hkd : k ∣ d
      · rw [if_pos hkd, if_pos hkd]
        apply mul_le_mul le_rfl
        · apply sum_le_sum
          intro m hm
          by_cases hkm :
              ((k * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d
          · by_cases hdm :
                ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d
            · rw [if_pos hkm, if_pos hdm]
            · rw [if_pos hkm, if_neg hdm]
              exact le_of_lt (s.selbergTerms_pos (dvd_of_mem_divisors hm))
          · rw [if_neg hkm]
            by_cases hdm :
                ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d
            · exfalso
              apply hkm
              refine ⟨?_, hdm.2⟩
              have hk_le_d : k ≤ d := Nat.le_of_dvd
                (Nat.pos_of_ne_zero
                  (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP)) hkd
              have hmul : k * m ≤ d * m :=
                Nat.mul_le_mul_right m hk_le_d
              have hsquare : (k * m) ^ 2 ≤ (d * m) ^ 2 :=
                Nat.pow_le_pow_left hmul 2
              have hsquareR :
                  (((k * m : ℕ) : ℝ) ^ 2) ≤
                    (((d * m : ℕ) : ℝ) ^ 2) := by
                exact_mod_cast hsquare
              exact hsquareR.trans hdm.1
            · rw [if_neg hdm]
        · exact sum_nonneg fun m hm => by
            split_ifs
            · exact le_of_lt (s.selbergTerms_pos (dvd_of_mem_divisors hm))
            · rfl
        · exact le_of_lt (s.selbergTerms_pos (hkd.trans hdP))
      · rw [if_neg hkd, if_neg hkd]
    _ = selbergWeights s d * (μ d : ℝ) * S := by
      dsimp [P, S]
      simp_rw [← ite_zero_mul]
      rw [← sum_mul]
      have hconv :
          (∑ k ∈ divisors s.prodPrimes,
            if k ∣ d then s.selbergTerms k else 0) =
            s.selbergTerms d * (s.nu d)⁻¹ := by
        exact s.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hdP
      rw [hconv]
      dsimp [selbergWeights]
      rw [if_pos hdP]
      have hS : selbergBoundSum s ≠ 0 := (selbergBoundSum_pos s).ne'
      have hsq : ((μ d : ℝ) ^ 2) = 1 := by
        norm_cast
        exact moebius_sq_eq_one_of_squarefree
          (s.squarefree_of_dvd_prodPrimes hdP)
      have hA :
          (∑ x ∈ divisors s.prodPrimes,
              if (((d * x : ℕ) : ℝ) ^ 2 ≤ s.level ∧ x.Coprime d)
              then s.selbergTerms x else 0) =
            ∑ x ∈ divisors s.prodPrimes with
              (((d * x : ℕ) : ℝ) ^ 2 ≤ s.level ∧ x.Coprime d),
              s.selbergTerms x := by
        rw [← Finset.sum_filter]
      rw [hA]
      simp only [Nat.cast_mul, mul_pow]
      field_simp [hS]
      rw [hsq]
      ring_nf

/-- Absolute bound on the local optimal Selberg weights. -/
theorem selbergWeights_abs_le_one (s : SelbergSieve) (d : ℕ) :
    |selbergWeights s d| ≤ 1 := by
  by_cases hdP : d ∣ s.prodPrimes
  · have hnonneg := selbergWeights_mul_mu_nonneg s hdP
    have hge := selbergBoundSum_ge_weight s hdP
    have hS := selbergBoundSum_pos s
    have hle : selbergWeights s d * (μ d : ℝ) ≤ 1 := by
      nlinarith
    have hsquare : Squarefree d := s.squarefree_of_dvd_prodPrimes hdP
    have habsmu : |(μ d : ℝ)| = 1 := by
      norm_cast
      exact abs_moebius_eq_one_of_squarefree hsquare
    calc
      |selbergWeights s d| =
          |selbergWeights s d * (μ d : ℝ)| := by
            rw [abs_mul, habsmu, mul_one]
      _ = selbergWeights s d * (μ d : ℝ) := abs_of_nonneg hnonneg
      _ ≤ 1 := hle
  · rw [selbergWeights_eq_zero_of_not_dvd s hdP]
    simp

/-- The frozen-M3 upper-sieve inequality specialized to the local optimal weights. -/
theorem siftedSum_le_optimal (s : SelbergSieve) :
    s.siftedSum ≤
      s.totalMass / selbergBoundSum s +
        s.errSum (selbergMuPlus s) := by
  calc
    s.siftedSum ≤
        s.totalMass * s.mainSum (selbergMuPlus s) +
          s.errSum (selbergMuPlus s) :=
      s.siftedSum_le_mainSum_errSum_of_upperMoebius
        (selbergMuPlus s) (selbergMuPlus_upper s)
    _ = _ := by
      rw [selberg_mainSum_eq_inv]
      simp [div_eq_mul_inv]

end M4A
end PaperB
