module

public import ShiuPublic.PrimePowerLocal

public import ChallengeDefs.Envelope

public section

/-!
The actual non-squarefree weight class in Shiu's published theorem:
multiplicative, nonnegative, controlled on every p^m, and subpower
growth for each positive epsilon. This module proves only local Euler
and exact factorization consequences, not distribution in progressions.
-/

namespace Shiu
open ArithmeticFunction
open scoped BigOperators

/- Source-independent form of the classical controlled-prime-power
weight class. Growth constants may depend on epsilon. -/
-- Shared Mathlib-only source definition: ChallengeDefs.Envelope.ClassicalEnvelope

/-- Every original f(p^m) for m >= 2 is controlled in an Euler tail.
This estimates an arbitrary finite range, uniformly in the exponent
cutoff and in f within its stated weight class. -/
theorem classical_prime_power_tail
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : ClassicalEnvelope f A)
    (p n : ℕ) (hp : p.Prime) (hpA : 2 * A ≤ (p : ℝ)) :
    (∑ j ∈ Finset.range n,
      f (p ^ (j + 2)) / (p : ℝ) ^ (j + 2)) ≤
      2 * (A / (p : ℝ)) ^ 2 := by
  exact controlled_prime_power_tail (fun t => f t) A p n
    hf.A_nonnegative hp.pos hpA
    (fun m hm => hf.prime_power p m hp (by omega))

/-- Exact factorization over distinct primes but retaining each full
prime-power exponent, valid without squarefree support. -/
theorem classical_multiplicative_factorization
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : ClassicalEnvelope f A)
    (n : ℕ) (hn : n ≠ 0) :
    f n = n.factorization.prod (fun p m => f (p ^ m)) :=
  hf.multiplicative.multiplicative_factorization f hn

/-- Non-squarefree analogue of the elementary Class IV weight bound:
all multiplicities are retained in the local factor product. -/
theorem classical_factorization_weight_bound
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : ClassicalEnvelope f A)
    (n : ℕ) (hn : n ≠ 0) :
    f n ≤ n.factorization.prod (fun p m => A ^ m) := by
  rw [classical_multiplicative_factorization hf n hn]
  change (∏ p ∈ n.factorization.support,
      f (p ^ n.factorization p)) ≤
    ∏ p ∈ n.factorization.support, A ^ n.factorization p
  apply Finset.prod_le_prod₀
  · intro p hp
    exact hf.nonnegative _
  · intro p hp
    have hprime : p.Prime :=
      Nat.prime_of_mem_primeFactors (by
        simpa only [Nat.support_factorization] using hp)
    have hexp : 0 < n.factorization p := by
      have hne : n.factorization p ≠ 0 :=
        (Finsupp.mem_support_iff).mp hp
      omega
    exact hf.prime_power p (n.factorization p) hprime hexp

#print axioms Shiu.classical_prime_power_tail
#print axioms Shiu.classical_multiplicative_factorization
#print axioms Shiu.classical_factorization_weight_bound
end Shiu
