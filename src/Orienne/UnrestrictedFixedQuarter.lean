module

public import EiravelUnrestrictedConditionalFinal
public import Orienne.ClassicalThreshold
public import Orienne.QuarterCutoffLarge

public section

open scoped BigOperators
open Filter Nat Real
open ArithmeticFunction

namespace PaperB.M4B

/--
The unrestricted original Shiu progression estimate for the literal
fixed-quarter choice z(y) = (ceil(y^(1/80)))^2.

The source, the prime-power exception, both orientations and all four original
overcounts are supplied by Eiravel's kernel-checked unrestricted conditional
theorem. The numerical readiness is furnished by the independently compiled
original fixed-quarter scalar proof, now promoted as an importable lemma.
No squarefree-support hypothesis is introduced.
-/
theorem orienne_unrestricted_shiu_fixed_quarter (A B : ℝ) :
    ∃ X0 : ℕ, ∀ f : ArithmeticFunction ℝ,
      Shiu.ClassicalEnvelope f A →
      0 ≤ B →
      (∀ n : ℕ, 1 ≤ n →
        f n ≤ B * (n : ℝ) ^ (1 / 1280 : ℝ)) →
      ∀ x y k a : ℕ,
        X0 ≤ x →
        (x : ℝ) ^ (1 / 4 : ℝ) < (y : ℝ) →
        y ≤ x →
        (k : ℝ) < (y : ℝ) ^ (3 / 4 : ℝ) →
        0 < a → a < k → a.Coprime k →
        (∑ n ∈ eiravelShiuPhysicalSet x y k a, f n) ≤
          (961 * corvethClassicalClassIConstant A B +
            161 * classicalShiuClassIVConstant A B + 56330 * B) *
            ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
            Real.exp (primeMass f x k) := by
  obtain ⟨Xterminal, hterminal⟩ :=
    eiravel_unrestricted_shiu_of_endpoint_gates A B
  obtain ⟨Xrankin, hrankin⟩ :=
    orienne_classical_shiu_eventually_strong_threshold A
  obtain ⟨Ybasic, hybasic⟩ :=
    Filter.eventually_atTop.1 eventually_fixedQuarter_basic
  obtain ⟨Ylarge, hylarge⟩ :=
    Filter.eventually_atTop.1 orienne_quarter_cutoff_eventually_exp_four
  let M : ℕ := max Ybasic Ylarge
  let X : ℕ := max Xterminal (max Xrankin (max 2 ((M + 1) ^ 4)))
  refine ⟨X, ?_⟩
  intro f hf hB hgrowth x y k a hx hxy hyx hky ha0 haklt hak
  have hxterminal : Xterminal ≤ x := by
    dsimp [X] at hx
    omega
  have hxrankin : Xrankin ≤ x := by
    dsimp [X] at hx
    omega
  have hx2 : 2 ≤ x := by
    dsimp [X] at hx
    omega
  have hxFourth : (M + 1) ^ 4 ≤ x := by
    dsimp [X] at hx
    omega
  have hyM : M ≤ y :=
    fixedQuarter_y_ge_of_x_ge_fourth hxFourth hxy
  have hyYbasic : Ybasic ≤ y :=
    (le_max_left Ybasic Ylarge).trans hyM
  have hyYlarge : Ylarge ≤ y :=
    (le_max_right Ybasic Ylarge).trans hyM
  obtain ⟨hy1, hyw, hzyScale, hkzScale, hz2Scale, hlog64, hlog4⟩ :=
    hybasic y hyYbasic
  obtain ⟨hL4, hRankin⟩ := hrankin x hxrankin
  have hkpos : 0 < k := lt_trans ha0 haklt
  let z : ℕ := fixedQuarterZ y
  obtain ⟨hzy, hkz, hsqrt, hxz, hzabsorb,
      hlogSqrt, hlogZ, hz2absorb, hsmall, hzx⟩ :=
    fixedQuarter_scalar_readiness
      hx2 hy1 hyw hzyScale hkzScale hz2Scale hlog64 hlog4
      hxy hyx hkpos hky
  have hzlarge : Real.exp (4 : ℝ) ≤ (z : ℝ) := by
    simpa [z, fixedQuarterZ, fixedQuarterW,
      orienneQuarterZ, orienneQuarterW] using
      (hylarge y hyYlarge)
  exact hterminal f hf hB hgrowth x y z k a
    hxterminal hx2 ha0 haklt hak hyx
    hzy hkz hsqrt hxz hzlarge hL4 hRankin
    hzabsorb hlogSqrt hlogZ hz2absorb hsmall hzx

#print axioms orienne_unrestricted_shiu_fixed_quarter
end PaperB.M4B
