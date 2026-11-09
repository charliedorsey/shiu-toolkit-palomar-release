module

public import ShiuPublic.VaelisClassIVEndpointCorrection

public section

namespace PaperB.M4B
open scoped BigOperators
theorem classical_classIV_shell_endpoints
    {A : ℝ} {x z r : ℕ}
    (hz2 : 2 ≤ z)
    (hL4 : 4 ≤ shiuLogLogSmoothThreshold x)
    (hlarge :
      Real.exp (4 * classicalClassIVRankinD A) ≤
        (shiuLogLogSmoothThreshold x : ℝ))
    (hr : r ∈ Finset.Icc 2 (shiuClassIVR0 x z)) :
    let p := classIVShellUpper z r
    let w := classIVShellLower z r
    2 ≤ p ∧ p ^ r ≤ z ∧ p ≤ z ∧
    Real.exp (4 * classicalClassIVRankinD A) ≤ (p : ℝ) ∧
    2 ≤ w ∧ w ^ 2 ≤ z ∧ z < (w + 1) ^ (r + 1) := by
  let L : ℕ := shiuLogLogSmoothThreshold x
  let r0 : ℕ := shiuClassIVR0 x z
  let p : ℕ := classIVShellUpper z r
  let w : ℕ := classIVShellLower z r
  have hrI := Finset.mem_Icc.mp hr
  have hr2 : 2 ≤ r := hrI.1
  have hrr0 : r ≤ r0 := hrI.2
  have hz0 : z ≠ 0 := by omega
  have hLpos : 0 < L := by
    dsimp [L]
    omega
  have hLpow0 : L ^ r0 ≤ z := by
    dsimp [r0, shiuClassIVR0]
    exact Nat.pow_log_le_self L hz0
  have hLpow : L ^ r ≤ z := by
    exact (Nat.pow_le_pow_right hLpos hrr0).trans hLpow0
  have hLp : L ≤ p := by
    dsimp [p, classIVShellUpper]
    exact (Nat.le_nthRoot_iff (by omega)).2 hLpow
  have hp2 : 2 ≤ p := by
    dsimp [L] at hLp
    omega
  have hpr : p ^ r ≤ z := by
    dsimp [p, classIVShellUpper]
    exact Nat.pow_nthRoot_le (Or.inl (by omega))
  have hpz : p ≤ z := by
    exact (Nat.le_self_pow (by omega) p).trans hpr
  have hlargeP :
      Real.exp (4 * classicalClassIVRankinD A) ≤ (p : ℝ) := by
    have hLpR : (L : ℝ) ≤ (p : ℝ) := by exact_mod_cast hLp
    simpa [L] using hlarge.trans hLpR
  have htwoexp : 2 ^ (r + 1) ≤ z := by
    have he : r + 1 ≤ 2 * r := by omega
    have h24 : 2 ^ (r + 1) ≤ 2 ^ (2 * r) :=
      Nat.pow_le_pow_right (by omega) he
    have hpow4 : 2 ^ (2 * r) = 4 ^ r := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    have h4L : 4 ^ r ≤ L ^ r :=
      Nat.pow_le_pow_left (by simpa [L] using hL4) r
    calc
      2 ^ (r + 1) ≤ 2 ^ (2 * r) := h24
      _ = 4 ^ r := hpow4
      _ ≤ L ^ r := h4L
      _ ≤ z := hLpow
  have hw2 : 2 ≤ w := by
    dsimp [w, classIVShellLower]
    exact (Nat.le_nthRoot_iff (by omega)).2 htwoexp
  have hwpow : w ^ (r + 1) ≤ z := by
    dsimp [w, classIVShellLower]
    exact Nat.pow_nthRoot_le (Or.inl (by omega))
  have hwsq : w ^ 2 ≤ z := by
    have hpowmono : w ^ 2 ≤ w ^ (r + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact hpowmono.trans hwpow
  have hzwr : z < (w + 1) ^ (r + 1) := by
    dsimp [w, classIVShellLower]
    exact (Nat.nthRoot_lt_iff (by omega)).1
      (Nat.lt_succ_self (Nat.nthRoot (r + 1) z))
  exact ⟨hp2, hpr, hpz, hlargeP, hw2, hwsq, hzwr⟩
#print axioms classical_classIV_shell_endpoints
end PaperB.M4B
