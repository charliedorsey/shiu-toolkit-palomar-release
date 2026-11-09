module

public import ShiuPublic.RelativeEulerCombined
public import ShiuPublic.RankinPowerGate

public import ChallengeDefs.Cutoff

public section

/-! Source-neutral complete finite prime-power Euler comparison on any
eligible prime set. The only threshold is a fixed A-dependent natural. -/

namespace Shiu
open scoped BigOperators

-- Shared Mathlib-only source definition: ChallengeDefs.Cutoff.fixedPrimePowerCutoff

theorem fixed_cutoff_dominates (A D : ℝ) :
    2 * A * Real.exp D ≤ (fixedPrimePowerCutoff A D : ℝ) := by
  unfold fixedPrimePowerCutoff
  exact (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right 5 ⌈2 * A * Real.exp D⌉₊))

theorem large_prime_gate_of_cutoff
    (A D : ℝ) (hA : 0 ≤ A) (hD : 0 < D)
    (P q : ℕ)
    (hP : Real.exp (4*D) ≤ (P : ℝ))
    (hq : 2 ≤ q) (hqP : q ≤ P)
    (hQ : fixedPrimePowerCutoff A D < q) :
    2*A ≤ (q : ℝ)^(1 - D / Real.log (P : ℝ)) := by
  let δ := D / Real.log (P : ℝ)
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hpow0 : 0 < (q : ℝ)^δ := Real.rpow_pos_of_pos hq0 _
  have hsmall : (q : ℝ)^δ ≤ Real.exp D :=
    rankin_small_power hD hP
      (by exact_mod_cast (by omega : 1 ≤ q))
      (by exact_mod_cast hqP)
  have hcut := fixed_cutoff_dominates A D
  have hqbig : 2*A*Real.exp D ≤ (q : ℝ) := by
    exact hcut.trans (by exact_mod_cast (Nat.le_of_lt hQ))
  have hbound : 2*A*(q : ℝ)^δ ≤ (q : ℝ) := by
    calc
      2*A*(q : ℝ)^δ ≤ 2*A*Real.exp D :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ ≤ (q : ℝ) := hqbig
  change 2*A ≤ (q : ℝ)^(1-δ)
  rw [Real.rpow_sub hq0, Real.rpow_one]
  exact (le_div_iff₀ hpow0).mpr hbound

/-- Full finite relative Euler bound over *every* prime in S,
with the usual prime mass and correction counted over the full S. -/
theorem classical_relative_euler_fixed_cutoff
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : ClassicalEnvelope f A)
    (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n →
      f n ≤ B * (n : ℝ)^(1/4 : ℝ))
    (S : Finset ℕ) (N P : ℕ) (D : ℝ)
    (hD : 0 < D)
    (hP : Real.exp (4*D) ≤ (P : ℝ))
    (hS : ∀ q ∈ S, q.Prime ∧ q ≤ P) :
    (∏ q ∈ S,
      ∑ j ∈ Finset.range (N+2),
        f (q^j)/(q : ℝ)^((j : ℝ)*(1-D/Real.log (P:ℝ)))) ≤
      smallPrimeConstant (fixedPrimePowerCutoff A D) B *
      Real.exp ((∑ q ∈ S,
        (f q/(q : ℝ) +
         f q*((q : ℝ)^(D/Real.log (P:ℝ))-1)/(q : ℝ))) +
        2*A^2*Real.exp (2*D)) := by
  let δ := D / Real.log (P : ℝ)
  let Q := fixedPrimePowerCutoff A D
  let Ssmall := S.filter (fun q => q ≤ Q)
  let Slarge := S.filter (fun q => Q < q)
  have hδ := rankin_delta_quarter hD hP
  have hPnat : 1 ≤ P := by
    have hh : (1 : ℝ) ≤ Real.exp (4*D) :=
      le_of_lt (by
        calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
             _ < Real.exp (4*D) := Real.exp_lt_exp.mpr (by linarith))
    have hm : (1 : ℝ) ≤ P := hh.trans hP
    exact_mod_cast hm
  have hsmall : Ssmall ⊆ Nat.primesLE Q := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqS,hqQ⟩
    exact Nat.mem_primesLE.mpr ⟨hqQ,(hS q hqS).1⟩
  have hlarge : ∀ q ∈ Slarge, q.Prime ∧ q ≤ P := by
    intro q hq
    exact hS q (Finset.mem_filter.mp hq).1
  have hgate : ∀ q ∈ Slarge, 2*A ≤ (q : ℝ)^(1-δ) := by
    intro q hq
    obtain ⟨hqS,hqQ⟩ := Finset.mem_filter.mp hq
    exact large_prime_gate_of_cutoff A D hf.A_nonnegative hD P q hP
      (hS q hqS).1.two_le (hS q hqS).2 hqQ
  have hpow : ∀ q ∈ Slarge, (q : ℝ)^δ ≤ Real.exp D := by
    intro q hq
    obtain ⟨hqS,_⟩ := Finset.mem_filter.mp hq
    exact rankin_small_power hD hP
      (by exact_mod_cast (hS q hqS).1.one_le)
      (by exact_mod_cast (hS q hqS).2)
  have hdisj : Disjoint Ssmall Slarge := by
    apply Finset.disjoint_left.mpr
    intro q hq1 hq2
    have h1 := (Finset.mem_filter.mp hq1).2
    have h2 := (Finset.mem_filter.mp hq2).2
    omega
  have hunion : Ssmall ∪ Slarge = S := by
    ext q
    simp only [Finset.mem_union]
    constructor
    · intro h
      rcases h with h1 | h2
      · exact (Finset.mem_filter.mp h1).1
      · exact (Finset.mem_filter.mp h2).1
    · intro hq
      by_cases hqQ : q ≤ Q
      · exact Or.inl (Finset.mem_filter.mpr ⟨hq,hqQ⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨hq, by omega⟩)
  have hrelative := classical_relative_euler_partition hf hB hgrowth
    Ssmall Slarge N P Q D δ hPnat hδ.1.le hδ.2
    hsmall hlarge hgate hpow hdisj
  have hsum :
      (∑ q ∈ Slarge, (f q/(q : ℝ) +
        f q*((q : ℝ)^δ-1)/(q : ℝ))) ≤
      ∑ q ∈ S, (f q/(q : ℝ) +
        f q*((q : ℝ)^δ-1)/(q : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _)
    intro q hq hnot
    have hprime : q.Prime := (hS q hq).1
    rw [← shifted_first_prime_mass (fun n => f n) q δ hprime.pos]
    exact div_nonneg (hf.nonnegative _) (Real.rpow_nonneg (by positivity) _)
  have hconstant : 0 ≤ smallPrimeConstant Q B := by
    have h := small_prime_product_uniform Q B ∅ (fun _ => 1)
      hB (Finset.empty_subset _) (by simp) (by simp)
    have hh : (1:ℝ) ≤ smallPrimeConstant Q B := by simpa using h
    linarith
  change (∏ q ∈ S, ∑ j ∈ Finset.range (N+2),
        f (q^j)/(q : ℝ)^((j : ℝ)*(1-δ))) ≤ _
  rw [hunion] at hrelative
  exact hrelative.trans
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (add_le_add_left hsum _)) hconstant)

#print axioms Shiu.large_prime_gate_of_cutoff
#print axioms Shiu.classical_relative_euler_fixed_cutoff
end Shiu
