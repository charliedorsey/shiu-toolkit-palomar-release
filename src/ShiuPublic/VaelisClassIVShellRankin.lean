module

public import ShiuPublic.VaelisClassIVShellRaw
public import ShiuPublic.VaelisClassIVPrefixNonSquarefree

public section

namespace PaperB.M4B
open scoped BigOperators

/-- Source-shaped non-squarefree Class IV raw shell controlled by Cendrel's
original prime mass and complete relative Euler comparison. -/
theorem classical_classIV_shell_bound_of_original_rankin
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : Shiu.ClassicalEnvelope f A) (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n → f n ≤ B * (n : ℝ)^(1/4 : ℝ))
    {x y z k a p w r : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hzy : z ≤ y) (hk : 0 < k)
    (hzsqrt : 1 ≤ Nat.sqrt z)
    (hw : 2 ≤ w) (hwsq : w ^ 2 ≤ z)
    (hx : x < z ^ 160) (hr : 1 ≤ r)
    (hzwr : z < (w + 1) ^ (r + 1))
    (hkb : ∀ b ∈ Shiu.classicalClassIVPrefixSet z k p, k * b < y)
    (D : ℝ) (hD : 0 < D) (hP : Real.exp (4 * D) ≤ (p : ℝ))
    (hδ : 0 ≤ D / Real.log (p : ℝ)) :
    classicalClassIVShellOvercount f x y z k a p w ≤
      (4 * (1 + A) ^ (320 * r)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) *
        ((Nat.sqrt z : ℝ) ^ (-(D / Real.log (p : ℝ))) *
          (Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A D) B *
            Real.exp (primeMass f p k +
              primeRankinCorrection f p k (D / Real.log (p : ℝ)) +
              2 * A ^ 2 * Real.exp (2 * D)))) := by
  have hraw := classical_classIV_shell_bound_raw hf
    ha0 haklt hak hyx hzy hk hzsqrt hw hwsq hx hr hzwr hkb
  have hzpos : 0 < z := by
    have hh := Nat.sqrt_le_self z
    omega
  have hmass := Shiu.classical_bounded_smooth_tail_original_mass
    hf hB hgrowth (Nat.sqrt z) z p k hzsqrt hzpos D hD hP hδ
  have hlog : 0 < Real.log (w : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < w by omega)
  have htot : 0 < k.totient := Nat.totient_pos.2 hk
  have hcoeff : 0 ≤
      (4 * (1 + A) ^ (320 * r)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) := by
    have hA := hf.A_nonnegative
    positivity
  exact hraw.trans (mul_le_mul_of_nonneg_left hmass hcoeff)

#print axioms classical_classIV_shell_bound_of_original_rankin
end PaperB.M4B
