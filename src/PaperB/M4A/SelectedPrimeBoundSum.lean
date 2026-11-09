module

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under the Apache License, Version 2.0, as described in the repository LICENSE.
Author: Arend Mellendijk.

Modified in 2026 for the Shiu Toolkit, under the direction of Charlie Dorsey,
with AI assistance; ported and specialized adapted sieve bounds to local Lean 4.35 proof.

Provenance:
https://github.com/amellendijk/selberg-sieve4
commit 64530a38a1e7e32357e1be8462dbfce5e445919a
SelbergSieve/Applications/PrimeCountingUpperBound.lean.

The selected-support theorem below is the proved local realization of the
historical file's commented "Proposed generalisation". The upstream sieve development supplies substantial adapted proof text
and architecture; this module does not directly import its upstream files.
-/

public import PaperB.M4A.OptimalSelberg
public import PaperB.M4A.SelectivePrimeProduct
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

public section

open scoped BigOperators ArithmeticFunction.Moebius
open Finset Nat Real ArithmeticFunction

noncomputable section

namespace PaperB
namespace M4A

/-- Pointwise complete multiplicativity for real-valued arithmetic functions. -/
def NatCompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
  f 1 = 1 ∧ ∀ a b, f (a * b) = f a * f b

namespace NatCompletelyMultiplicative

theorem isMultiplicative {f : ArithmeticFunction ℝ}
    (hf : NatCompletelyMultiplicative f) :
    ArithmeticFunction.IsMultiplicative f :=
  ⟨hf.1, fun _ => hf.2 _ _⟩

theorem apply_pow (f : ArithmeticFunction ℝ)
    (hf : NatCompletelyMultiplicative f) (a n : ℕ) :
    f (a ^ n) = f a ^ n := by
  induction n with
  | zero => simp [hf.1]
  | succ n ih => simp [pow_succ, hf.2, ih]

end NatCompletelyMultiplicative

private theorem prod_factors_one_div_compMult_ge
    (M : ℕ) (f : ArithmeticFunction ℝ)
    (hf : NatCompletelyMultiplicative f)
    (hf_nonneg : ∀ n, 0 ≤ f n) (d : ℕ) (hd : Squarefree d)
    (hf_size : ∀ n, n.Prime → n ∣ d → f n < 1) :
    f d * ∏ p ∈ d.primeFactors, 1 / (1 - f p) ≥
      ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p ^ n) := by
  calc
    f d * ∏ p ∈ d.primeFactors, 1 / (1 - f p) =
        ∏ p ∈ d.primeFactors, f p / (1 - f p) := by
      conv =>
        lhs
        congr
        rw [← Nat.prod_primeFactors_of_squarefree hd]
      rw [hf.isMultiplicative.map_prod_of_subset_primeFactors _ _ subset_rfl,
        ← Finset.prod_mul_distrib]
      simp_rw [one_div, div_eq_mul_inv]
    _ ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, (f p) ^ n := by
      gcongr with p hp
      · exact fun p _ => Finset.sum_nonneg fun n _ => pow_nonneg (hf_nonneg p) n
      rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
      rw [← Finset.Ico_succ_right_eq_Icc]
      simpa [pow_one] using
        (geom_sum_Ico_le_of_lt_one (m := 1) (n := M + 1)
          (hf_nonneg p) (hf_size p hp.1 hp.2))
    _ = ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p ^ n) := by
      simp_rw [hf.apply_pow]

private theorem prod_factors_sum_pow_compMult
    (M : ℕ) (hM : M ≠ 0) (f : ArithmeticFunction ℝ)
    (hf : NatCompletelyMultiplicative f) (d : ℕ) (hd : Squarefree d) :
    ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p ^ n) =
      ∑ m ∈ (d ^ M).divisors.filter (d ∣ ·), f m := by
  classical
  rw [Finset.prod_sum]
  let i : (a : _) →
      (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M) → ℕ :=
    fun a _ => ∏ p ∈ d.primeFactors.attach, p.1 ^ (a p p.2)
  have hfact_i : ∀ a ha p,
      Nat.factorization (i a ha) p =
        if hp : p ∈ d.primeFactors then a p hp else 0 := by
    intro a ha p
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp, Nat.factorization_prod, Finset.sum_apply',
        Finset.sum_eq_single ⟨p, hp⟩, Nat.factorization_pow, Finsupp.smul_apply,
        Nat.Prime.factorization_self
          (Nat.prime_of_mem_primeFactors hp)]
      · ring
      · intro q _ hq
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_zero]
        right
        apply Nat.factorization_eq_zero_of_not_dvd
        rw [Nat.Prime.dvd_iff_eq, ← exists_eq_subtype_mk_iff]
        push_neg
        exact fun _ => hq
        exact Nat.prime_of_mem_primeFactors q.2
        exact (Nat.prime_of_mem_primeFactors hp).ne_one
      · intro h
        exact (h (Finset.mem_attach _ _)).elim
      · exact fun q _ => pow_ne_zero _
          (ne_of_gt ((Nat.prime_of_mem_primeFactors q.property).pos))
    · rw [dif_neg hp]
      by_cases hpp : p.Prime
      · apply Nat.factorization_eq_zero_of_not_dvd
        intro hp_dvd
        obtain ⟨⟨q, hq⟩, _, hp_dvd_pow⟩ :=
          Prime.exists_mem_finset_dvd hpp.prime hp_dvd
        apply hp
        rw [Nat.mem_primeFactors]
        constructor
        · exact hpp
        refine ⟨?_, hd.ne_zero⟩
        trans q
        · exact Nat.Prime.dvd_of_dvd_pow hpp hp_dvd_pow
        · exact Nat.dvd_of_mem_primeFactors hq
      · exact Nat.factorization_eq_zero_of_not_prime _ hpp

  have hi_ne_zero : ∀ (a : _)
      (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ≠ 0 := by
    intro a ha
    rw [Finset.prod_ne_zero_iff]
    exact fun p _ => pow_ne_zero _
      (ne_of_gt ((Nat.prime_of_mem_primeFactors p.property).pos))

  have hi : ∀ (a : _)
      (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ∈ (d ^ M).divisors.filter (d ∣ ·) := by
    intro a ha
    rw [Finset.mem_filter, Nat.mem_divisors,
      ← Nat.factorization_le_iff_dvd hd.ne_zero (hi_ne_zero a ha),
      ← Nat.factorization_le_iff_dvd (hi_ne_zero a ha) (pow_ne_zero _ hd.ne_zero)]
    constructor
    · constructor
      · rw [Finsupp.le_iff]
        intro p _
        rw [hfact_i a ha]
        by_cases hp : p ∈ d.primeFactors
        · rw [dif_pos hp, Nat.factorization_pow, Finsupp.smul_apply]
          simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
          trans M • 1
          · norm_num
            exact (ha p hp).2
          · gcongr
            rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
            rw [← Nat.Prime.dvd_iff_one_le_factorization hp.1 hd.ne_zero]
            exact hp.2
        · rw [dif_neg hp]
          norm_num
      · exact pow_ne_zero _ hd.ne_zero
    · rw [Finsupp.le_iff]
      intro p hp
      rw [Nat.support_factorization] at hp
      rw [hfact_i a ha, dif_pos hp]
      trans 1
      · exact hd.natFactorization_le_one p
      simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
      exact (ha p hp).1

  have hmap : ∀ (a : _)
      (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      ∏ p ∈ d.primeFactors.attach, f (p.1 ^ (a p p.2)) = f (i a ha) := by
    intro a ha
    apply symm
    apply hf.isMultiplicative.map_prod
    intro x _ y _ hxy
    simp_rw [Finset.mem_pi, Finset.mem_Icc, Nat.succ_le] at ha
    apply (Nat.coprime_pow_left_iff (ha x x.2).1 ..).mpr
    apply (Nat.coprime_pow_right_iff (ha y y.2).1 ..).mpr
    have hxp := Nat.prime_of_mem_primeFactors x.2
    rw [Nat.Prime.coprime_iff_not_dvd hxp]
    rw [Nat.prime_dvd_prime_iff_eq hxp
      (Nat.prime_of_mem_primeFactors y.2)]
    exact fun hc => hxy (Subtype.eq hc)

  have i_inj : ∀ a ha b hb, i a ha = i b hb → a = b := by
    intro a ha b hb hiab
    apply_fun Nat.factorization at hiab
    ext p hp
    obtain hiabp := DFunLike.ext_iff.mp hiab p
    rw [hfact_i a ha, hfact_i b hb, dif_pos hp, dif_pos hp] at hiabp
    exact hiabp

  have i_surj : ∀ b : ℕ, b ∈ (d ^ M).divisors.filter (d ∣ ·) →
      ∃ a ha, i a ha = b := by
    intro b hb
    have h : (fun p _ => Nat.factorization b p) ∈
        Finset.pi d.primeFactors fun _p => Finset.Icc 1 M := by
      rw [Finset.mem_pi]
      intro p hp
      rw [Finset.mem_Icc]
      rw [Finset.mem_filter] at hb
      have hb_ne_zero : b ≠ 0 :=
        ne_of_gt (Nat.pos_of_mem_divisors hb.1)
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      constructor
      · rw [← Nat.Prime.dvd_iff_one_le_factorization hpp hb_ne_zero]
        exact (Nat.dvd_of_mem_primeFactors hp).trans hb.2
      · rw [Nat.mem_divisors] at hb
        trans Nat.factorization (d ^ M) p
        · exact (Nat.factorization_le_iff_dvd hb_ne_zero hb.1.2).mpr hb.1.1 p
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        have hfac : d.factorization p ≤ 1 := hd.natFactorization_le_one p
        exact (mul_le_iff_le_one_right (Nat.pos_of_ne_zero hM)).mpr hfac
    refine ⟨(fun p _ => Nat.factorization b p), h, ?_⟩
    apply Nat.eq_of_factorization_eq
    · exact hi_ne_zero _ h
    · exact ne_of_gt (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hb).1)
    intro p
    rw [hfact_i (fun p _ => Nat.factorization b p) h p]
    rw [Finset.mem_filter, Nat.mem_divisors] at hb
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp]
    · rw [dif_neg hp, eq_comm, Nat.factorization_eq_zero_iff, ← or_assoc]
      rw [Nat.mem_primeFactors] at hp
      left
      push_neg at hp
      by_cases hpp : p.Prime
      · right
        intro hpb
        apply absurd (hp hpp)
        push_neg
        exact ⟨hpp.dvd_of_dvd_pow (hpb.trans hb.1.1), hd.ne_zero⟩
      · left
        exact hpp

  exact Finset.sum_bij i hi i_inj i_surj hmap

private theorem prod_primes_dvd_of_primeFactors_supported
    (P m : ℕ)
    (h : m.primeFactors ⊆ P.primeFactors) :
    ∏ p ∈ m.primeFactors, p ∣ P := by
  have hprime : ∀ p ∈ m.primeFactors, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  simp_rw [Nat.prime_iff] at hprime
  apply Finset.prod_primes_dvd _ hprime
  intro p hp
  exact Nat.dvd_of_mem_primeFactors (h hp)

private lemma squarefree_dvd_pow_local
    (a b N : ℕ) (ha : Squarefree a) (hab : a ∣ b ^ N) : a ∣ b := by
  by_cases hN : N = 0
  · rw [hN, pow_zero, Nat.dvd_one] at hab
    simpa [hab]
  exact (ha.dvd_pow_iff_dvd hN).mp hab

/-- Generic finite selected-support lower bound for the local Selberg bounding sum. -/
theorem selbergBoundSum_ge_selectedSupport
    (s : SelbergSieve) (B : ℕ)
    (hB : ((B : ℝ) ^ 2) ≤ s.level)
    (hnu : NatCompletelyMultiplicative s.nu)
    (hnu_nonneg : ∀ n, 0 ≤ s.nu n) :
    selbergBoundSum s ≥
      ∑ m ∈
        (Finset.Icc 1 B).filter
          (fun m => m.primeFactors ⊆ s.prodPrimes.primeFactors),
        s.nu m := by
  classical
  calc
    selbergBoundSum s =
        ∑ l ∈ s.prodPrimes.divisors,
          if ((l : ℝ) ^ 2 ≤ s.level) then s.selbergTerms l else 0 := by
      rw [selbergBoundSum, Finset.sum_filter]
    _ ≥ ∑ l ∈ s.prodPrimes.divisors.filter (fun l : ℕ => (l : ℝ) ^ 2 ≤ s.level),
        ∑ m ∈ (l ^ (Nat.floor s.level)).divisors.filter (l ∣ ·), s.nu m := by
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum
      intro l hl
      rw [Finset.mem_filter, Nat.mem_divisors] at hl
      have hlsq : Squarefree l :=
        Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
      have hfloor_ne : Nat.floor s.level ≠ 0 := by
        rw [ne_eq, Nat.floor_eq_zero, not_lt]
        exact s.one_le_level
      trans ∏ p ∈ l.primeFactors,
          ∑ n ∈ Finset.Icc 1 (Nat.floor s.level), s.nu (p ^ n)
      · rw [prod_factors_sum_pow_compMult
          (Nat.floor s.level) hfloor_ne s.nu hnu l hlsq]
      · rw [s.selbergTerms_apply l]
        simpa [one_div] using
          (prod_factors_one_div_compMult_ge
            (Nat.floor s.level) s.nu hnu hnu_nonneg l hlsq
            (fun p hpp hpl =>
              s.nu_lt_one_of_prime p hpp (hpl.trans hl.1.1)))
    _ ≥ ∑ m ∈
        (Finset.Icc 1 B).filter
          (fun m => m.primeFactors ⊆ s.prodPrimes.primeFactors),
        s.nu m := by
      rw [← Finset.sum_biUnion]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        rcases Finset.mem_filter.mp hm with ⟨hmIcc, hmSupport⟩
        rw [Finset.mem_Icc] at hmIcc
        have hm_ne_zero : m ≠ 0 := ne_of_gt (Nat.succ_le.mp hmIcc.1)
        have hm_sq_le_level : ((m : ℝ) ^ 2) ≤ s.level := by
          have hmB : (m : ℝ) ≤ (B : ℝ) := by exact_mod_cast hmIcc.2
          have hsq : ((m : ℝ) ^ 2) ≤ ((B : ℝ) ^ 2) := by
            gcongr
          exact hsq.trans hB
        have hm_le_level : (m : ℝ) ≤ s.level := by
          have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmIcc.1
          have hm_le_sq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
          exact hm_le_sq.trans hm_sq_le_level
        have hprod_pos : 0 < ∏ p ∈ m.primeFactors, p := by
          apply Finset.prod_pos
          intro p hp
          exact (Nat.prime_of_mem_primeFactors hp).pos
        have hprod_ne_zero :
            (∏ p ∈ m.primeFactors, p) ^ Nat.floor s.level ≠ 0 := by
          exact pow_ne_zero _ (ne_of_gt hprod_pos)
        rw [Finset.mem_biUnion]
        refine ⟨(∏ p ∈ m.primeFactors, p), ?_, ?_⟩
        · rw [Finset.mem_filter, Nat.mem_divisors]
          constructor
          · constructor
            · exact prod_primes_dvd_of_primeFactors_supported
                s.prodPrimes m hmSupport
            · exact s.prodPrimes_ne_zero
          · have hprod_le_m : (∏ p ∈ m.primeFactors, p) ≤ m := by
              apply Nat.le_of_dvd (Nat.succ_le.mp hmIcc.1)
              exact Nat.prod_primeFactors_dvd m
            have hprod_sq :
                (((∏ p ∈ m.primeFactors, p : ℕ) : ℝ) ^ 2) ≤ ((m : ℝ) ^ 2) := by
              exact_mod_cast Nat.pow_le_pow_left hprod_le_m 2
            exact hprod_sq.trans hm_sq_le_level
        · rw [Finset.mem_filter, Nat.mem_divisors]
          constructor
          · constructor
            · rw [← Nat.factorization_le_iff_dvd hm_ne_zero hprod_ne_zero,
                Nat.factorization_pow]
              intro p
              have hy_mul_prod_nonneg :
                  0 ≤ Nat.floor s.level *
                    Nat.factorization (∏ p ∈ m.primeFactors, p) p := by
                omega
              trans Nat.factorization m p * 1
              · rw [mul_one]
              trans Nat.floor s.level *
                  Nat.factorization (∏ p ∈ m.primeFactors, p) p
              · by_cases hpp : p.Prime
                · by_cases hpdvd : p ∣ m
                  · apply mul_le_mul
                    · trans m
                      · exact le_of_lt (Nat.factorization_lt p hm_ne_zero)
                      · apply Nat.le_floor
                        exact hm_le_level
                    · rw [← Nat.Prime.pow_dvd_iff_le_factorization hpp
                        (ne_of_gt hprod_pos), pow_one]
                      apply Finset.dvd_prod_of_mem
                      rw [Nat.mem_primeFactors]
                      exact ⟨hpp, hpdvd, hm_ne_zero⟩
                    · omega
                    · omega
                  · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]
                    exact hy_mul_prod_nonneg
                · rw [Nat.factorization_eq_zero_of_not_prime _ hpp, zero_mul]
                  exact hy_mul_prod_nonneg
              · rfl
            · exact hprod_ne_zero
          · exact Nat.prod_primeFactors_dvd m
      · intro i _ _
        exact hnu_nonneg i
      · intro i hi j hj hij
        intro t hti htj
        intro x hx
        specialize hti hx
        specialize htj hx
        simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
        have h : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ x → x ∣ j ^ n → i ∣ j := by
          intro i j n hiP hix hij
          apply squarefree_dvd_pow_local i j n
            (s.squarefree_of_dvd_prodPrimes hiP)
          exact hix.trans hij
        have hidvdj : i ∣ j := h i j hi.1.1 hti.2 htj.1.1
        have hjdvdi : j ∣ i := h j i hj.1.1 htj.2 hti.1.1
        exact False.elim (hij (Nat.dvd_antisymm hidvdj hjdvdi))

private theorem selectedSupport_iff_coprime
    {m z k : ℕ} (hm1 : 1 ≤ m) (hmz : m ≤ z) :
    m.primeFactors ⊆ (selectedPrimeProduct z k).primeFactors ↔
      m.Coprime k := by
  constructor
  · intro hsupp
    by_contra hcop
    obtain ⟨p, hp, hpm, hpk⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    have hpmem : p ∈ m.primeFactors := by
      rw [Nat.mem_primeFactors]
      exact ⟨hp, hpm, ne_of_gt (Nat.succ_le.mp hm1)⟩
    have hpP : p ∣ selectedPrimeProduct z k :=
      Nat.dvd_of_mem_primeFactors (hsupp hpmem)
    exact ((prime_dvd_selectedPrimeProduct_iff hp).mp hpP).2 hpk
  · intro hcop p hpmem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hpmem
    rw [Nat.mem_primeFactors]
    refine ⟨hp, (prime_dvd_selectedPrimeProduct_iff hp).mpr ?_,
      selectedPrimeProduct_ne_zero z k⟩
    constructor
    · exact (Nat.le_of_dvd (Nat.succ_le.mp hm1) hpm).trans hmz
    · have hpc : p.Coprime k := hcop.coprime_dvd_left hpm
      exact hp.coprime_iff_not_dvd.mp hpc

/-- C1 target: the selected-prime Selberg denominator exposes precisely the
coprime harmonic mass up to `z`. No `φ(k)/k` lower bound is used here. -/
theorem selectedPrimeBoundSum_lower
    (s : SelbergSieve) (z k : ℕ)
    (hP : s.prodPrimes = selectedPrimeProduct z k)
    (hlevel : s.level = (z : ℝ) ^ 2)
    (hnu : ∀ n, s.nu n = ((n : ℝ)⁻¹)) :
    selbergBoundSum s ≥
      ∑ m ∈ (Finset.Icc 1 z).filter (fun m => m.Coprime k),
        ((m : ℝ)⁻¹) := by
  have hcomp : NatCompletelyMultiplicative s.nu := by
    constructor
    · rw [hnu]
      norm_num
    · intro a b
      rw [hnu, hnu, hnu, Nat.cast_mul, mul_inv]
  have hnonneg : ∀ n, 0 ≤ s.nu n := by
    intro n
    rw [hnu]
    positivity
  have hcut : ((z : ℝ) ^ 2) ≤ s.level := by
    rw [hlevel]
  have hbound := selbergBoundSum_ge_selectedSupport s z hcut hcomp hnonneg
  rw [hP] at hbound
  have hfilter :
      (Finset.Icc 1 z).filter
          (fun m => m.primeFactors ⊆ (selectedPrimeProduct z k).primeFactors) =
        (Finset.Icc 1 z).filter (fun m => m.Coprime k) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro hm
      exact ⟨hm.1, (selectedSupport_iff_coprime hm.1.1 hm.1.2).mp hm.2⟩
    · intro hm
      exact ⟨hm.1, (selectedSupport_iff_coprime hm.1.1 hm.1.2).mpr hm.2⟩
  rw [hfilter] at hbound
  simpa [hnu] using hbound

end M4A
end PaperB
