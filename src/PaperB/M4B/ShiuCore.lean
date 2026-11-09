module

/-
Paper B M4B-CORE: fixed-quarter Shiu core.
Authorized surface: M4B0 ledger rows S1-S13 only.
-/

public import PaperB.M4A.ShiuLemma2
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.SmoothNumbers
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Order.Filter.AtTopBot.Finite

public import ChallengeDefs.Mass

public section

open scoped BigOperators Topology
open Finset Nat Real Filter
open ArithmeticFunction

noncomputable section

namespace PaperB
namespace M4B

/-- Exact CORE envelope: nonnegative multiplicative, squarefree-supported,
one fixed prime-value bound, and the single K1 growth exponent 1/1280. -/
structure FixedQuarterEnvelope (f : ArithmeticFunction ℝ) (A1 A2 : ℝ) : Prop where
  multiplicative : f.IsMultiplicative
  nonneg : ∀ n : ℕ, 0 ≤ f n
  squarefree_support : ∀ n : ℕ, ¬ Squarefree n → f n = 0
  prime_le : ∀ p : ℕ, p.Prime → f p ≤ A1
  A1_nonneg : 0 ≤ A1
  A2_nonneg : 0 ≤ A2
  growth : ∀ n : ℕ, f n ≤ A2 * (n : ℝ) ^ (1 / 1280 : ℝ)

/- Prime mass occurring in the fixed-quarter Shiu conclusion. -/
-- Shared Mathlib-only source definition: ChallengeDefs.Mass.primeMass

/-- Weighted coprime harmonic mass in Shiu Lemma 3. -/
@[expose] def coprimeHarmonicMass (f : ArithmeticFunction ℝ) (X k : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X with n.Coprime k, f n / n

/-- S2: the squarefree-supported Lemma 3 Euler-product bound.
The constant is exactly 1 and is uniform in the modulus. -/
theorem squarefree_coprime_harmonic_upper
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2) (X k : ℕ) :
    coprimeHarmonicMass f X k ≤ Real.exp (primeMass f X k) := by
  classical
  let N : Finset ℕ :=
    (Finset.Icc 1 X).filter (fun n => n.Coprime k ∧ Squarefree n)
  let P : Finset ℕ :=
    (Nat.primesLE X).filter (fun p => ¬ p ∣ k)
  let w : Finset ℕ → ℝ :=
    fun t => ∏ p ∈ t, f p / (p : ℝ)
  have hdrop :
      coprimeHarmonicMass f X k =
        ∑ n ∈ N, f n / (n : ℝ) := by
    unfold coprimeHarmonicMass N
    simp_rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : n.Coprime k
    · by_cases hs : Squarefree n
      · simp [hc, hs]
      · simp [hc, hs, hf.squarefree_support n hs]
    · simp [hc]
  have hweight :
      ∀ n ∈ N, f n / (n : ℝ) = w n.primeFactors := by
    intro n hn
    have hs : Squarefree n := (Finset.mem_filter.mp hn).2.2
    unfold w
    rw [Finset.prod_div_distrib, hf.multiplicative.prod_primeFactors hs]
    have hprod := Nat.prod_primeFactors_of_squarefree hs
    rw [← Nat.cast_prod, hprod]
  have hinj :
      ∀ ⦃n₁⦄, n₁ ∈ N → ∀ ⦃n₂⦄, n₂ ∈ N →
        n₁.primeFactors = n₂.primeFactors → n₁ = n₂ := by
    intro n₁ hn₁ n₂ hn₂ heq
    have hs₁ : Squarefree n₁ := (Finset.mem_filter.mp hn₁).2.2
    have hs₂ : Squarefree n₂ := (Finset.mem_filter.mp hn₂).2.2
    calc
      n₁ = ∏ p ∈ n₁.primeFactors, p :=
        (Nat.prod_primeFactors_of_squarefree hs₁).symm
      _ = ∏ p ∈ n₂.primeFactors, p := by rw [heq]
      _ = n₂ := Nat.prod_primeFactors_of_squarefree hs₂
  have hsubset : N.image Nat.primeFactors ⊆ P.powerset := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨n, hnN, rfl⟩
    rw [Finset.mem_powerset]
    intro p hp
    have hnI : n ∈ Finset.Icc 1 X := (Finset.mem_filter.mp hnN).1
    have hcop : n.Coprime k := (Finset.mem_filter.mp hnN).2.1
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hnmem := Finset.mem_Icc.mp hnI
    have hple : p ≤ X :=
      (Nat.le_of_dvd (by omega) hpdvd).trans hnmem.2
    have hpnot : ¬ p ∣ k := by
      intro hpk
      have hpone : p ∣ 1 := by
        rw [← hcop.gcd_eq_one]
        exact Nat.dvd_gcd hpdvd hpk
      exact hpprime.not_dvd_one hpone
    simp [P, Nat.mem_primesLE, hpprime, hple, hpnot]
  have hw_nonneg : ∀ t ∈ P.powerset, 0 ≤ w t := by
    intro t ht
    unfold w
    exact Finset.prod_nonneg fun p hp =>
      div_nonneg (hf.nonneg p) (by positivity)
  calc
    coprimeHarmonicMass f X k
        = ∑ n ∈ N, f n / (n : ℝ) := hdrop
    _ = ∑ n ∈ N, w n.primeFactors := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hweight n hn
    _ = ∑ t ∈ N.image Nat.primeFactors, w t := by
      symm
      exact Finset.sum_image hinj
    _ ≤ ∑ t ∈ P.powerset, w t :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun t htP _ => hw_nonneg t htP)
    _ = ∏ p ∈ P, (1 + f p / (p : ℝ)) := by
      simpa [w] using
        (Finset.prod_one_add (s := P) (f := fun p => f p / (p : ℝ))).symm
    _ ≤ Real.exp (∑ p ∈ P, f p / (p : ℝ)) := by
      exact Real.prod_one_add_le_exp_sum P
        (fun p => div_nonneg (hf.nonneg p) (by positivity))
    _ = Real.exp (primeMass f X k) := by
      simp [P, primeMass]

/-- Squarefree numbers up to X with every prime factor at most Y. -/
@[expose] def squarefreeSmoothSet (X Y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter
    (fun n => Squarefree n ∧ n.primeFactors ⊆ Nat.primesLE Y)

@[expose] def squarefreeSmoothCount (X Y : ℕ) : ℕ :=
  #(squarefreeSmoothSet X Y)

@[expose] def primeRankinMass (Y : ℕ) (δ : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE Y, (p : ℝ) ^ (-δ)

/-- Finite squarefree Rankin bound. This is the K1-strength replacement for
the generic prime-power Euler product in Shiu Lemma 1. -/
theorem squarefreeSmooth_rankin
    (X Y : ℕ) {δ : ℝ} (hX : 1 ≤ X) (hδ : 0 < δ) :
    (squarefreeSmoothCount X Y : ℝ) ≤
      (X : ℝ) ^ δ * Real.exp (primeRankinMass Y δ) := by
  classical
  let N := squarefreeSmoothSet X Y
  let P := Nat.primesLE Y
  let w : Finset ℕ → ℝ := fun t => ∏ p ∈ t, (p : ℝ) ^ (-δ)
  have hpoint : ∀ n ∈ N,
      (1 : ℝ) ≤ (X : ℝ) ^ δ * (n : ℝ) ^ (-δ) := by
    intro n hn
    have hnN := Finset.mem_filter.mp hn
    have hnI := Finset.mem_Icc.mp hnN.1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hnI.1
    have hXpos : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hX)
    have hnX : (n : ℝ) ≤ X := by exact_mod_cast hnI.2
    have hratio : (1 : ℝ) ≤ (X : ℝ) / n := by
      rw [le_div_iff₀ hnpos]
      simpa using hnX
    have hr := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 1) hratio hδ.le
    rw [Real.one_rpow] at hr
    have heq :
        ((X : ℝ) / n) ^ δ =
          (X : ℝ) ^ δ * (n : ℝ) ^ (-δ) := by
      rw [Real.div_rpow hXpos.le hnpos.le, div_eq_mul_inv,
        Real.rpow_neg hnpos.le]
    simpa [heq] using hr
  have hweight : ∀ n ∈ N, (n : ℝ) ^ (-δ) = w n.primeFactors := by
    intro n hn
    have hs : Squarefree n := (Finset.mem_filter.mp hn).2.1
    unfold w
    rw [Real.finsetProd_rpow]
    · rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hs]
    · intro p hp
      positivity
  have hinj :
      ∀ ⦃n₁⦄, n₁ ∈ N → ∀ ⦃n₂⦄, n₂ ∈ N →
        n₁.primeFactors = n₂.primeFactors → n₁ = n₂ := by
    intro n₁ hn₁ n₂ hn₂ heq
    have hs₁ : Squarefree n₁ := (Finset.mem_filter.mp hn₁).2.1
    have hs₂ : Squarefree n₂ := (Finset.mem_filter.mp hn₂).2.1
    calc
      n₁ = ∏ p ∈ n₁.primeFactors, p :=
        (Nat.prod_primeFactors_of_squarefree hs₁).symm
      _ = ∏ p ∈ n₂.primeFactors, p := by rw [heq]
      _ = n₂ := Nat.prod_primeFactors_of_squarefree hs₂
  have hsubset : N.image Nat.primeFactors ⊆ P.powerset := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨n, hn, rfl⟩
    exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hn).2.2
  have hw_nonneg : ∀ t ∈ P.powerset, 0 ≤ w t := by
    intro t ht
    unfold w
    exact Finset.prod_nonneg fun p hp => Real.rpow_nonneg (by positivity) _
  have hsum :
      (∑ n ∈ N, (n : ℝ) ^ (-δ)) ≤
        Real.exp (primeRankinMass Y δ) := by
    calc
      (∑ n ∈ N, (n : ℝ) ^ (-δ)) =
          ∑ t ∈ N.image Nat.primeFactors, w t := by
        rw [Finset.sum_image hinj]
        apply Finset.sum_congr rfl
        intro n hn
        exact hweight n hn
      _ ≤ ∑ t ∈ P.powerset, w t :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun t htP _ => hw_nonneg t htP)
      _ = ∏ p ∈ P, (1 + (p : ℝ) ^ (-δ)) := by
        simpa [w] using
          (Finset.prod_one_add (s := P)
            (f := fun p : ℕ => (p : ℝ) ^ (-δ))).symm
      _ ≤ Real.exp (∑ p ∈ P, (p : ℝ) ^ (-δ)) :=
        Real.prod_one_add_le_exp_sum P
          (fun p => Real.rpow_nonneg (by positivity) _)
      _ = Real.exp (primeRankinMass Y δ) := rfl
  calc
    (squarefreeSmoothCount X Y : ℝ) =
        ∑ n ∈ N, (1 : ℝ) := by simp [squarefreeSmoothCount, N]
    _ ≤ ∑ n ∈ N, (X : ℝ) ^ δ * (n : ℝ) ^ (-δ) :=
      Finset.sum_le_sum fun n hn => hpoint n hn
    _ = (X : ℝ) ^ δ * ∑ n ∈ N, (n : ℝ) ^ (-δ) := by
      rw [Finset.mul_sum]
    _ ≤ (X : ℝ) ^ δ * Real.exp (primeRankinMass Y δ) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (by positivity) _)

/-- Finite squarefree smooth tail, represented by subsets of admissible primes.
This is the exact finite object needed for the squarefree specialization of Shiu Lemma 4. -/
@[expose] def squarefreeSmoothTailMass
    (f : ArithmeticFunction ℝ) (X Y k : ℕ) : ℝ :=
  let P := (Nat.primesLE Y).filter (fun p => ¬ p ∣ k)
  ∑ t ∈ P.powerset with X ≤ t.prod id,
    ∏ p ∈ t, f p / (p : ℝ)

/-- The exact Rankin correction in Shiu Lemma 4 after separating the
ordinary prime mass. -/
@[expose] def primeRankinCorrection
    (f : ArithmeticFunction ℝ) (Y k : ℕ) (ε : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE Y with ¬ p ∣ k,
    f p * ((p : ℝ) ^ ε - 1) / p

/-- S3 Rankin engine, before choosing Shiu's ε = r log r / (4 log z).
No asymptotic estimate is hidden here: the correction is left exact. -/
theorem squarefree_smoothTail_rankin_raw
    {f : ArithmeticFunction ℝ} {A1 A2 : ℝ}
    (hf : FixedQuarterEnvelope f A1 A2)
    (X Y k : ℕ) {ε : ℝ}
    (hX : 1 ≤ X) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    squarefreeSmoothTailMass f X Y k ≤
      (X : ℝ) ^ (-ε) *
        Real.exp (primeMass f Y k + primeRankinCorrection f Y k ε) := by
  classical
  let P : Finset ℕ := (Nat.primesLE Y).filter (fun p => ¬ p ∣ k)
  let w0 : Finset ℕ → ℝ :=
    fun t => ∏ p ∈ t, f p / (p : ℝ)
  let wε : Finset ℕ → ℝ :=
    fun t => ∏ p ∈ t, f p / (p : ℝ) ^ (1 - ε)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hX)
  have hpoint :
      ∀ t ∈ P.powerset, X ≤ t.prod id →
        w0 t ≤ (X : ℝ) ^ (-ε) * wε t := by
    intro t ht hXt
    have hprodpos : (0 : ℝ) < (t.prod id : ℕ) := by
      exact_mod_cast Finset.prod_pos fun p hp => (Nat.prime_of_mem_primesLE
        (Finset.mem_filter.mp (Finset.mem_powerset.mp ht hp)).1).pos
    have hFX : (0 : ℝ) < (X : ℝ) ^ ε := Real.rpow_pos_of_pos hXpos _
    have hpow :
        (X : ℝ) ^ ε ≤ ((t.prod id : ℕ) : ℝ) ^ ε := by
      apply Real.rpow_le_rpow (by positivity)
      · exact_mod_cast hXt
      · exact hε0
    have hratio :
        (1 : ℝ) ≤ (X : ℝ) ^ (-ε) * ((t.prod id : ℕ) : ℝ) ^ ε := by
      rw [Real.rpow_neg hXpos.le, inv_mul_eq_div]
      exact (le_div_iff₀ hFX).2 (by simpa using hpow)
    have hFnonneg : 0 ≤ ∏ p ∈ t, f p := Finset.prod_nonneg fun p hp => hf.nonneg p
    unfold w0 wε
    rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
    have hden0 :
        ∏ p ∈ t, (p : ℝ) = ((t.prod id : ℕ) : ℝ) := by
      simpa only [id_eq, Nat.cast_prod]
    have hdenε :
        ∏ p ∈ t, (p : ℝ) ^ (1 - ε) =
          ((t.prod id : ℕ) : ℝ) ^ (1 - ε) := by
      rw [Real.finsetProd_rpow]
      · exact congrArg (fun u : ℝ => u ^ (1 - ε)) hden0
      · intro p hp
        positivity
    rw [hden0, hdenε]
    have hnpos : (0 : ℝ) < ((t.prod id : ℕ) : ℝ) := hprodpos
    have hneps : (0 : ℝ) < ((t.prod id : ℕ) : ℝ) ^ ε :=
      Real.rpow_pos_of_pos hnpos _
    have hinv :
        ((t.prod id : ℕ) : ℝ) ^ (-ε) ≤ (X : ℝ) ^ (-ε) := by
      rw [Real.rpow_neg hnpos.le, Real.rpow_neg hXpos.le]
      exact (inv_le_inv₀ hneps hFX).mpr hpow
    have hscale :
        (1 : ℝ) / ((t.prod id : ℕ) : ℝ) ≤
          (X : ℝ) ^ (-ε) /
            (((t.prod id : ℕ) : ℝ) ^ (1 - ε)) := by
      rw [Real.rpow_sub hnpos, Real.rpow_one, div_div_eq_mul_div,
        div_le_div_iff_of_pos_right hnpos]
      simpa using hratio
    calc
      (∏ p ∈ t, f p) / ((t.prod id : ℕ) : ℝ)
          = (∏ p ∈ t, f p) *
              ((1 : ℝ) / ((t.prod id : ℕ) : ℝ)) := by ring
      _ ≤ (∏ p ∈ t, f p) *
              ((X : ℝ) ^ (-ε) /
                (((t.prod id : ℕ) : ℝ) ^ (1 - ε))) :=
        mul_le_mul_of_nonneg_left hscale hFnonneg
      _ = (X : ℝ) ^ (-ε) *
              ((∏ p ∈ t, f p) /
                (((t.prod id : ℕ) : ℝ) ^ (1 - ε))) := by ring
  have hwε_nonneg : ∀ t ∈ P.powerset, 0 ≤ wε t := by
    intro t ht
    unfold wε
    exact Finset.prod_nonneg fun p hp =>
      div_nonneg (hf.nonneg p) (Real.rpow_nonneg (by positivity) _)
  have hsum :
      (∑ t ∈ P.powerset with X ≤ t.prod id, w0 t) ≤
        (X : ℝ) ^ (-ε) * ∑ t ∈ P.powerset, wε t := by
    calc
      (∑ t ∈ P.powerset with X ≤ t.prod id, w0 t)
          ≤ ∑ t ∈ P.powerset with X ≤ t.prod id,
              (X : ℝ) ^ (-ε) * wε t := by
            exact Finset.sum_le_sum fun t ht =>
              hpoint t (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2
      _ ≤ ∑ t ∈ P.powerset, (X : ℝ) ^ (-ε) * wε t := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _)
              (fun t ht _ =>
                mul_nonneg (Real.rpow_nonneg (by positivity) _)
                  (hwε_nonneg t ht))
      _ = (X : ℝ) ^ (-ε) * ∑ t ∈ P.powerset, wε t := by
            rw [Finset.mul_sum]
  have hprod :
      (∑ t ∈ P.powerset, wε t) ≤
        Real.exp (∑ p ∈ P, f p / (p : ℝ) ^ (1 - ε)) := by
    calc
      (∑ t ∈ P.powerset, wε t) =
          ∏ p ∈ P, (1 + f p / (p : ℝ) ^ (1 - ε)) := by
        simpa [wε] using
          (Finset.prod_one_add (s := P)
            (f := fun p : ℕ => f p / (p : ℝ) ^ (1 - ε))).symm
      _ ≤ Real.exp (∑ p ∈ P, f p / (p : ℝ) ^ (1 - ε)) := by
        exact Real.prod_one_add_le_exp_sum P
          (fun p => div_nonneg (hf.nonneg p) (Real.rpow_nonneg (by positivity) _))
  have hsplit :
      (∑ p ∈ P, f p / (p : ℝ) ^ (1 - ε)) =
        primeMass f Y k + primeRankinCorrection f Y k ε := by
    have hterm : ∀ p ∈ P,
        f p / (p : ℝ) ^ (1 - ε) =
          f p / p + f p * ((p : ℝ) ^ ε - 1) / p := by
      intro p hp
      have hpprime : p.Prime :=
        Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
      have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.pos
      rw [Real.rpow_sub hpR, Real.rpow_one, div_div_eq_mul_div]
      field_simp [hpR.ne', (Real.rpow_pos_of_pos hpR ε).ne']
      ring
    unfold primeMass primeRankinCorrection P
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    exact hterm p hp
  unfold squarefreeSmoothTailMass
  dsimp only
  change (∑ t ∈ P.powerset with X ≤ t.prod id, w0 t) ≤ _
  calc
    (∑ t ∈ P.powerset with X ≤ t.prod id, w0 t)
        ≤ (X : ℝ) ^ (-ε) * ∑ t ∈ P.powerset, wε t := hsum
    _ ≤ (X : ℝ) ^ (-ε) *
          Real.exp (∑ p ∈ P, f p / (p : ℝ) ^ (1 - ε)) := by
      gcongr
    _ = (X : ℝ) ^ (-ε) *
          Real.exp (primeMass f Y k + primeRankinCorrection f Y k ε) := by
      rw [hsplit]

/-- Weighted progression sum on the natural interval corresponding to (x-y,x]. -/
@[expose] def progressionSum (f : ArithmeticFunction ℝ) (x y k a : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc (x - y) x, if n ≡ a [MOD k] then f n else 0

end M4B
end PaperB
