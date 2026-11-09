module

public import Mathlib

public section

/-!
# SHIU exact Palomar Challenge (self-contained canonical source)
Source-aligned shared declarations inlined for isolated canonical build.
The three theorem proof holes are deliberately confined to Challenge.
-/
namespace Shiu

open scoped BigOperators
open ArithmeticFunction

structure ClassicalEnvelope (f : ArithmeticFunction ℝ) (A : ℝ) : Prop where
  multiplicative : f.IsMultiplicative
  nonnegative : ∀ n : ℕ, 0 ≤ f n
  A_nonnegative : 0 ≤ A
  prime_power : ∀ p m : ℕ, p.Prime → 1 ≤ m → f (p ^ m) ≤ A ^ m
  growth : ∀ ε : ℝ, 0 < ε →
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 1 ≤ n → f n ≤ B * (n : ℝ) ^ ε

end Shiu

namespace Shiu

open scoped BigOperators
open ArithmeticFunction

@[expose] noncomputable def fixedPrimePowerCutoff (A D : ℝ) : ℕ :=
  max 5 ⌈2 * A * Real.exp D⌉₊

end Shiu

namespace Shiu

open scoped BigOperators
open ArithmeticFunction

@[expose] noncomputable def smallPrimeConstant (Q : ℕ) (B : ℝ) : ℝ :=
  ∏ q ∈ Nat.primesLE Q,
    (1 + B / (1 - (q : ℝ) ^ (-(1/2 : ℝ))))

end Shiu

namespace PaperB.M4B

open scoped BigOperators

@[expose] noncomputable def classicalClassIVRankinD (A : ℝ) : ℝ :=
  960 * Real.log (1 + A) + 24

@[expose] noncomputable def classicalClassIVRankinH (A : ℝ) : ℝ :=
  ((4 * A * Real.log 4) / Real.log 2) *
    Real.exp (classicalClassIVRankinD A)

end PaperB.M4B

namespace PaperB.M4B

open scoped BigOperators

@[expose] noncomputable def corvethClassicalClassIConstant (A B : ℝ) : ℝ :=
  (4 * (1 + A) ^ 320) *
    Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A 1) B *
      Real.exp (((4 * A * Real.log 4) / Real.log 2) * Real.exp 1 +
        2 * A ^ 2 * Real.exp 2)

end PaperB.M4B

namespace PaperB.M4B

open scoped BigOperators

@[expose] noncomputable def classicalShiuClassIVConstant (A B : ℝ) : ℝ :=
  96 * Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A (classicalClassIVRankinD A)) B *
    Real.exp (2*A^2*Real.exp (2*classicalClassIVRankinD A) + classicalClassIVRankinH A)

end PaperB.M4B

namespace PaperB.M4B

open scoped BigOperators

@[expose] noncomputable def primeMass (f : ArithmeticFunction ℝ) (X k : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE X with ¬ p ∣ k, f p / p

end PaperB.M4B

namespace Shiu.API

open scoped BigOperators

noncomputable abbrev primeMass (f : ArithmeticFunction ℝ)
    (x k : ℕ) : ℝ := PaperB.M4B.primeMass f x k

@[expose] def progressionSum (f : ArithmeticFunction ℝ) (x y k a : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc (x-y) x, if n ≡ a [MOD k] then f n else 0

end Shiu.API

namespace Shiu.API

open scoped BigOperators

@[expose] noncomputable def classicalConstant (A B : ℝ) : ℝ :=
  961 * PaperB.M4B.corvethClassicalClassIConstant A B +
  161 * PaperB.M4B.classicalShiuClassIVConstant A B + 56330 * B

end Shiu.API

namespace Shiu.API

open scoped BigOperators

theorem classical_quarter (A B : ℝ) :
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
        progressionSum f x y k a ≤
          classicalConstant A B *
            ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
            Real.exp (primeMass f x k) := by
  sorry

theorem classical_modulus_one_quarter (A B : ℝ) :
    ∃ X0 : ℕ, ∀ f : ArithmeticFunction ℝ,
      Shiu.ClassicalEnvelope f A →
      0 ≤ B →
      (∀ n : ℕ, 1 ≤ n →
        f n ≤ B * (n : ℝ) ^ (1 / 1280 : ℝ)) →
      ∀ x y : ℕ,
        X0 ≤ x →
        (x : ℝ) ^ (1 / 4 : ℝ) < (y : ℝ) →
        y ≤ x →
        (∑ n ∈ Finset.Ioc (x-y) x, f n) ≤
          9 * classicalConstant A B *
            ((y : ℝ) / Real.log (x : ℝ)) *
            Real.exp (PaperB.M4B.primeMass f x 1) := by
  sorry

theorem classical_two_parameter_quadrant (A B : ℝ) :
    ∃ X0 : ℕ, ∀ alpha beta : ℝ,
      (1 / 4 : ℝ) ≤ alpha →
      alpha < (1 / 2 : ℝ) →
      (1 / 4 : ℝ) ≤ beta →
      beta < (1 / 2 : ℝ) →
      ∀ f : ArithmeticFunction ℝ,
        Shiu.ClassicalEnvelope f A →
        0 ≤ B →
        (∀ n : ℕ, 1 ≤ n →
          f n ≤ B * (n : ℝ) ^ (1 / 1280 : ℝ)) →
        ∀ x y k a : ℕ,
          X0 ≤ x →
          (x : ℝ) ^ beta < (y : ℝ) →
          y ≤ x →
          (k : ℝ) < (y : ℝ) ^ (1 - alpha) →
          0 < a → a < k → a.Coprime k →
          progressionSum f x y k a ≤
            classicalConstant A B *
              ((y : ℝ) / ((k.totient : ℝ) * Real.log (x : ℝ))) *
              Real.exp (primeMass f x k) := by
  sorry

end Shiu.API
