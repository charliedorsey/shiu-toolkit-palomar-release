module

public import Mathlib.NumberTheory.Bertrand
public import Mathlib.Tactic

public section

/-!
# Nine dyadic Bertrand primes — arithmetic supplier for k=1 Shiu

For a positive scale N, choose one prime in each of the disjoint
intervals (2^i*N, 2^(i+1)*N], i = 0,...,8.
All nine primes are mathematically distinct, greater than N,
and no larger than 512*N. This does NOT by itself establish the
required analytic relation between N, x, y.
-/
namespace Shiu.API

private theorem dyadic_nonzero (N i : ℕ) (hN : 0 < N) : N * 2 ^ i ≠ 0 :=
  mul_ne_zero (Nat.ne_of_gt hN) (pow_ne_zero i (by decide))

/-- One Bertrand prime in each dyadic interval. -/
noncomputable def dyadicPrime (N i : ℕ) (hN : 0 < N) : ℕ :=
  Classical.choose
    (Nat.exists_prime_lt_and_le_two_mul (N * 2 ^ i)
      (dyadic_nonzero N i hN))

theorem dyadicPrime_spec (N i : ℕ) (hN : 0 < N) :
    (dyadicPrime N i hN).Prime ∧
      N * 2 ^ i < dyadicPrime N i hN ∧
      dyadicPrime N i hN ≤ 2 * (N * 2 ^ i) := by
  exact Classical.choose_spec
    (Nat.exists_prime_lt_and_le_two_mul (N * 2 ^ i)
      (dyadic_nonzero N i hN))

theorem dyadicPrime_gt_scale (N i : ℕ) (hN : 0 < N) :
    N < dyadicPrime N i hN := by
  have hpow : 1 ≤ 2 ^ i := (pow_pos (by decide : 0 < (2 : ℕ)) i)
  have hmul : N ≤ N * 2 ^ i := by
    calc
      N = N * 1 := by omega
      _ ≤ N * 2 ^ i := Nat.mul_le_mul_left N hpow
  exact lt_of_le_of_lt hmul (dyadicPrime_spec N i hN).2.1

theorem dyadicPrime_strictMono (N : ℕ) (hN : 0 < N) :
    StrictMono (fun i : ℕ => dyadicPrime N i hN) := by
  intro i j hij
  have hi := (dyadicPrime_spec N i hN).2.2
  have hj := (dyadicPrime_spec N j hN).2.1
  have hpower : 2 ^ (i + 1) ≤ 2 ^ j :=
    pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by omega)
  have hmul : N * 2 ^ (i + 1) ≤ N * 2 ^ j :=
    Nat.mul_le_mul_left N hpower
  have hrewrite : 2 * (N * 2 ^ i) = N * 2 ^ (i + 1) := by
    rw [pow_succ]
    ring
  calc
    dyadicPrime N i hN ≤ 2 * (N * 2 ^ i) := hi
    _ = N * 2 ^ (i + 1) := hrewrite
    _ ≤ N * 2 ^ j := hmul
    _ < dyadicPrime N j hN := hj

theorem nine_bertrand_primes
    (N : ℕ) (hN : 0 < N) :
    ∃ q : Fin 9 → ℕ,
      (∀ i, (q i).Prime ∧ N < q i ∧ q i ≤ 512 * N) ∧
      Function.Injective q := by
  refine ⟨(fun i => dyadicPrime N i hN), ?_, ?_⟩
  · intro i
    have hi := dyadicPrime_spec N i hN
    have hi8 : (i : ℕ) ≤ 8 := by omega
    have hpower : 2 ^ (i : ℕ) ≤ 2 ^ 8 :=
      pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hi8
    have hmul : 2 * (N * 2 ^ (i : ℕ)) ≤ 512 * N := by
      nlinarith [Nat.mul_le_mul_left N hpower]
    exact ⟨hi.1, dyadicPrime_gt_scale N i hN, hi.2.2.trans hmul⟩
  · intro i j heq
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (ne_of_lt (dyadicPrime_strictMono N hN hlt)) heq
    · exact (ne_of_gt (dyadicPrime_strictMono N hN hgt)) heq

#print axioms nine_bertrand_primes
end Shiu.API
