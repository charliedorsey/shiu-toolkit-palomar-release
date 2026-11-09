module

public import Mathlib

public section

/-!
# Explicit natural square-root geometry for nine Bertrand primes

An exact, symbolic cutoff mechanism: N = floor(sqrt(y)).
Given x<y^4 and y>512^4, the nine-prime product condition
and the fourth-power modulus window both follow.
The fractional real-power conversion is a separate obligation.
-/
namespace Shiu.API

theorem modulus_one_natural_geometry
    (x y : ℕ) (hxy : x < y ^ 4)
    (hyLarge : 512 ^ 4 < y) :
    let N := Nat.sqrt y
    0 < N ∧
      x < (N + 1) ^ 9 ∧
      (512 * N) ^ 4 < y ^ 3 := by
  dsimp
  have hy0 : 0 < y := by omega
  have hN0 : 0 < Nat.sqrt y := Nat.sqrt_pos.mpr hy0
  have hlow : (Nat.sqrt y) ^ 2 ≤ y := Nat.sqrt_le' y
  have hupp : y < (Nat.sqrt y + 1) ^ 2 := Nat.lt_succ_sqrt' y
  have hpow4 : y ^ 4 < ((Nat.sqrt y + 1) ^ 2) ^ 4 := by
    gcongr
  have hpow9 : x < (Nat.sqrt y + 1) ^ 9 := by
    calc
      x < y ^ 4 := hxy
      _ < ((Nat.sqrt y + 1) ^ 2) ^ 4 := hpow4
      _ = (Nat.sqrt y + 1) ^ 8 := by rw [← pow_mul]
      _ ≤ (Nat.sqrt y + 1) ^ 9 :=
        pow_le_pow_right₀ (by omega) (by omega)
  have hroot4 : (Nat.sqrt y) ^ 4 ≤ y ^ 2 := by
    calc
      (Nat.sqrt y) ^ 4 = ((Nat.sqrt y) ^ 2) ^ 2 := by ring
      _ ≤ y ^ 2 := by gcongr
  have hgeom : (512 * Nat.sqrt y) ^ 4 < y ^ 3 := by
    calc
      (512 * Nat.sqrt y) ^ 4 = 512 ^ 4 * (Nat.sqrt y) ^ 4 := by
        rw [mul_pow]
      _ ≤ 512 ^ 4 * y ^ 2 := Nat.mul_le_mul_left _ hroot4
      _ < y * y ^ 2 :=
        Nat.mul_lt_mul_of_pos_right hyLarge (pow_pos hy0 2)
      _ = y ^ 3 := by ring
  exact ⟨hN0, hpow9, hgeom⟩

#print axioms modulus_one_natural_geometry
end Shiu.API
