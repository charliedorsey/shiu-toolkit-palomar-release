module

public import Shiu.ModulusOne
public import Shiu.ModulusOnePrimes

public section

/-!
# The nine-prime finite-cover certificate

Fully source-connected *arithmetic* reduction. For any N>0 and
x < (N+1)^9, nine separate Bertrand primes provide a positive-weight
cover of (x-y,x]. All primes lie in (N,512*N]. The downstream
ModulusOneRealGeometry and ModulusOneFinal modules discharge the analytic
window and AP summation. When N is Nat.sqrt y, N^2 <= y (not N^2 > y).
-/
namespace Shiu.API
open scoped BigOperators

/-- Nine different Bertrand primes yield pairwise coprime moduli with
product greater than x when x < (N+1)^9. -/
theorem nine_moduli_cover_certificate
    (N x : ℕ) (hN : 0 < N) (hx : x < (N + 1) ^ 9) :
    ∃ S : Finset ℕ,
      S.card = 9 ∧
      (∀ p ∈ S, p.Prime ∧ N < p ∧ p ≤ 512 * N) ∧
      (S : Set ℕ).Pairwise (fun a b : ℕ => IsRelPrime a b) ∧
      x < ∏ p ∈ S, p := by
  classical
  obtain ⟨q, hq, hinj⟩ := nine_bertrand_primes N hN
  let S : Finset ℕ := Finset.univ.image q
  have hcard : S.card = 9 := by
    simp [S, Finset.card_image_of_injective _ hinj]
  have hprops : ∀ p ∈ S, p.Prime ∧ N < p ∧ p ≤ 512 * N := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact hq i
  have hpair : (S : Set ℕ).Pairwise
      (fun a b : ℕ => IsRelPrime a b) := by
    intro a ha b hb hab
    change a ∈ S at ha
    change b ∈ S at hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    have hc : (q i).Coprime (q j) :=
      (Nat.coprime_primes (hq i).1 (hq j).1).mpr hab
    exact Nat.coprime_iff_isRelPrime.mp hc
  have hinjOn : Set.InjOn q (Finset.univ : Finset (Fin 9)) := by
    intro i hi j hj hij
    exact hinj hij
  have hprodimage : (∏ p ∈ S, p) = ∏ i : Fin 9, q i := by
    simpa only [S] using
      (Finset.prod_image (f := fun p : ℕ => p) (s := Finset.univ)
        (g := q) hinjOn)
  have hbound : (∏ i : Fin 9, (N + 1)) ≤ ∏ i : Fin 9, q i := by
    exact
      (Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 9)))
        (fun i hi => Nat.succ_le_iff.mpr (hq i).2.1))
  have hprod : x < ∏ p ∈ S, p := by
    calc
      x < (N + 1) ^ 9 := hx
      _ = ∏ i : Fin 9, (N + 1) := by rw [Finset.prod_const, Finset.card_fin]
      _ ≤ ∏ i : Fin 9, q i := hbound
      _ = ∏ p ∈ S, p := hprodimage.symm
  exact ⟨S, hcard, hprops, hpair, hprod⟩

/-- Concrete nonnegative weighted short-interval reduction to nine
prime moduli; the later analytic Shiu summation is still separate. -/
theorem short_interval_nine_prime_cover
    (f : ArithmeticFunction ℝ) (N x y : ℕ)
    (hN : 0 < N) (hx : x < (N + 1) ^ 9)
    (hf : ∀ n : ℕ, 0 ≤ f n) :
    ∃ S : Finset ℕ,
      S.card = 9 ∧
      (∀ p ∈ S, p.Prime ∧ N < p ∧ p ≤ 512 * N) ∧
      (∑ n ∈ Finset.Ioc (x-y) x, f n) ≤
        ∑ p ∈ S, ∑ n ∈ Finset.Ioc (x-y) x,
          if ¬ p ∣ n then f n else 0 := by
  obtain ⟨S, hcard, hprime, hpair, hprod⟩ :=
    nine_moduli_cover_certificate N x hN hx
  exact ⟨S, hcard, hprime,
    short_interval_le_modulus_cover f x y S hf hpair hprod⟩

#print axioms nine_moduli_cover_certificate
#print axioms short_interval_nine_prime_cover
end Shiu.API
