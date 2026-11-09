module

public import ShiuPublic.FixedQuarter

public section

/-!
Reusable cutoff-level Shiu interface. The theorem does not fix an interval
exponent or modulus exponent: users may furnish any integer cutoff z
satisfying the explicit scalar inequalities below.

This is a proof-facing API, not a claim that the conditions hold for
every x,y,k. The public bound has no Paper B terminology; the
implementation currently delegates to the audited M4B assembly.
-/

namespace Shiu
open scoped BigOperators
open ArithmeticFunction

/-- Explicit numerical readiness of a cutoff for the squarefree short-AP
estimate. The arithmetic function and its constants are independent of
this predicate; cutoff choices may vary with x,y,k. -/
structure CutoffConditions (x y z k a : ℕ) : Prop where
  x_ge_two : 2 ≤ x
  a_positive : 0 < a
  a_lt_modulus : a < k
  coprime : a.Coprime k
  interval_le_x : y ≤ x
  cutoff_le_interval : z ≤ y
  modulus_cutoff : k * z < y
  sqrt_cutoff_ge_two : 2 ≤ Nat.sqrt z
  x_lt_cutoff_pow : x < z ^ 160
  loglog_threshold :
    4 ≤ PaperB.M4B.shiuLogLogSmoothThreshold x
  rankin_threshold (A : ℝ) :
    Real.exp (PaperB.M4B.classIVRankinD A) ≤
      (PaperB.M4B.shiuLogLogSmoothThreshold x : ℝ)
  rankin_absorption :
    (z : ℝ) ≤
      ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 4 : ℝ)
  sqrt_log_bound :
    Real.log (x : ℝ) ≤
      320 * Real.log (Nat.sqrt z : ℝ)
  cutoff_log_bound :
    Real.log (x : ℝ) ≤ 160 * Real.log (z : ℝ)
  cutoff_square_absorption :
    (z : ℝ) ^ 2 ≤
      (y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))
  small_exception_absorption :
    ((y : ℝ) / (k : ℝ)) * (z : ℝ) ^ (-1 / 8 : ℝ) ≤
      (y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))
  cutoff_le_x : z ≤ x

/-- Source-neutral uniform Shiu bound under an explicitly certified
cutoff. It applies to any numeric range for which a caller can produce
CutoffConditions; no particular theta or modulus-power bound is built in. -/
theorem progression_of_cutoff (A B : ℝ) :
    ∃ X0 : ℕ, ∀ f : ArithmeticFunction ℝ,
      SquarefreeEnvelope f A B →
      ∀ x y z k a : ℕ,
        X0 ≤ x →
        CutoffConditions x y z k a →
        (∑ n ∈ Finset.Ioc (x - y) x,
          if n ≡ a [MOD k] then f n else 0) ≤
          constant A B *
            ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
            Real.exp (∑ p ∈ Nat.primesLE x with ¬ p ∣ k, f p / p) := by
  obtain ⟨X0, h⟩ :=
    PaperB.M4B.shiu_fixed_quarter_assemble_uniform A B
  refine ⟨X0, ?_⟩
  intro f hf x y z k a hx hc
  exact h f
    ⟨hf.multiplicative, hf.nonnegative, hf.squarefree,
      hf.prime_values, hf.primeBound_nonneg,
      hf.growthBound_nonneg, hf.growth⟩
    x y z k a hx hc.x_ge_two hc.a_positive hc.a_lt_modulus
    hc.coprime hc.interval_le_x hc.cutoff_le_interval
    hc.modulus_cutoff hc.sqrt_cutoff_ge_two hc.x_lt_cutoff_pow
    hc.loglog_threshold (hc.rankin_threshold A)
    hc.rankin_absorption hc.sqrt_log_bound hc.cutoff_log_bound
    hc.cutoff_square_absorption hc.small_exception_absorption
    hc.cutoff_le_x

#print axioms Shiu.progression_of_cutoff
end Shiu
