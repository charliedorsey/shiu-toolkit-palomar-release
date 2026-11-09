module

public import Shiu.ModulusOneNineCover

public section

/-!
Issue #8: genuinely compiled consumer for the *finite arithmetic*
nine-prime cover. Not yet the unrestricted k=1 Shiu bound.
-/
namespace Shiu.ConsumerExamples
open scoped BigOperators

example (f : ArithmeticFunction ℝ) (N x y : ℕ)
    (hN : 0 < N) (hx : x < (N + 1) ^ 9)
    (hf : ∀ n : ℕ, 0 ≤ f n) :
    ∃ S : Finset ℕ,
      S.card = 9 ∧
      (∀ p ∈ S, p.Prime ∧ N < p ∧ p ≤ 512 * N) ∧
      (∑ n ∈ Finset.Ioc (x-y) x, f n) ≤
        ∑ p ∈ S, ∑ n ∈ Finset.Ioc (x-y) x,
          if ¬ p ∣ n then f n else 0 := by
  exact Shiu.API.short_interval_nine_prime_cover f N x y hN hx hf

end Shiu.ConsumerExamples
