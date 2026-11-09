module

public import ShiuPublic.VaelisClassIVFixedDelta
public import ShiuPublic.VaelisClassIVShellScalarBudget
public import ShiuPublic.VaelisClassIVStrongEndpoints

public section

namespace PaperB.M4B
open scoped BigOperators
theorem classical_classIV_log_shell_compare
    {z w r : ℕ}
    (hz2 : 2 ≤ z) (hw2 : 2 ≤ w)
    (hzwr : z < (w + 1) ^ (r + 1)) :
    Real.log (z : ℝ) ≤
      2 * ((r + 1 : ℕ) : ℝ) * Real.log (w : ℝ) := by
  have hzpos : (0 : ℝ) < (z : ℝ) := by positivity
  have hzwR :
      (z : ℝ) < (((w + 1) ^ (r + 1) : ℕ) : ℝ) := by
    exact_mod_cast hzwr
  have hlog1 :
      Real.log (z : ℝ) <
        Real.log ((((w + 1) ^ (r + 1) : ℕ) : ℝ)) :=
    Real.log_lt_log hzpos hzwR
  have hlog1' :
      Real.log (z : ℝ) <
        (((r + 1 : ℕ) : ℝ)) * Real.log ((w + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_pow, Real.log_pow] using hlog1
  have hwpowNat : w + 1 ≤ w ^ 2 := by
    nlinarith
  have hwpowR :
      ((w + 1 : ℕ) : ℝ) ≤ ((w ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hwpowNat
  have hlog2 :
      Real.log ((w + 1 : ℕ) : ℝ) ≤
        Real.log ((w ^ 2 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) hwpowR
  have hlog2' :
      Real.log ((w + 1 : ℕ) : ℝ) ≤
        2 * Real.log (w : ℝ) := by
    simpa [Nat.cast_pow, Real.log_pow] using hlog2
  have hm :=
    mul_le_mul_of_nonneg_left hlog2'
      (by positivity : 0 ≤ (((r + 1 : ℕ) : ℝ)))
  nlinarith

theorem classical_classIV_shell_bound_final
    {f : ArithmeticFunction ℝ} {A B : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (hB : 0 ≤ B)
    (hgrowth : ∀ n : ℕ, 1 ≤ n → f n ≤ B * (n : ℝ)^(1/4 : ℝ))
    {x y z k a r : ℕ}
    (ha0 : 0 < a) (haklt : a < k) (hak : a.Coprime k)
    (hyx : y ≤ x) (hzy : z ≤ y) (hkz : k * z < y)
    (hz2 : 2 ≤ z) (hx : x < z ^ 160)
    (hL4 : 4 ≤ shiuLogLogSmoothThreshold x)
    (hlarge :
      Real.exp (4 * classicalClassIVRankinD A) ≤
        (shiuLogLogSmoothThreshold x : ℝ))
    (hr : r ∈ Finset.Icc 2 (shiuClassIVR0 x z)) :
    classicalClassIVShellOvercount f x y z k a
        (classIVShellUpper z r) (classIVShellLower z r) ≤
      (24 * Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A (classicalClassIVRankinD A)) B * Real.exp (2*A^2*Real.exp (2*classicalClassIVRankinD A) + classicalClassIVRankinH A)) *
        ((((r + 1 : ℕ) : ℝ)) * Real.exp (-8 * (r : ℝ))) *
        ((((y : ℝ)) /
            ((k.totient : ℝ) * Real.log (z : ℝ)) +
          (z : ℝ) ^ 2) *
          Real.exp (primeMass f z k)) := by
  let p := classIVShellUpper z r
  let w := classIVShellLower z r
  let D : ℝ := classicalClassIVRankinD A
  have hD : 0 < D := by
    dsimp [D, classicalClassIVRankinD]
    have hbase : (1 : ℝ) ≤ 1 + A := by linarith [hf.A_nonnegative]
    have hlogbase : 0 ≤ Real.log (1 + A) := Real.log_nonneg hbase
    linarith
  obtain ⟨hp2, hpr, hpz, hlargeP, hw2, hwsq, hzwr⟩ :=
    classical_classIV_shell_endpoints
      (A := A) (x := x) hz2 hL4 hlarge hr
  have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
  have hzsqrt : 1 ≤ Nat.sqrt z := by
    rw [Nat.le_sqrt]
    omega
  have hk : 0 < k := lt_trans ha0 haklt
  have hkb :
      ∀ b ∈ Shiu.classicalClassIVPrefixSet z k p, k * b < y := by
    intro b hb
    have hbF := Finset.mem_filter.mp hb
    have hbI := Finset.mem_Icc.mp hbF.1
    exact (Nat.mul_le_mul_left k hbI.2).trans_lt hkz
  have hlargePsmall : Real.exp D ≤ (p : ℝ) := by
    have hh : D ≤ 4 * D := by linarith [hD]
    exact (Real.exp_le_exp.mpr hh).trans hlargeP
  obtain ⟨hε0, hε1, hbudget⟩ :=
    classical_classIV_rankin_budget_fixed_delta
      hf hr2 hp2 hpr hzsqrt (by simpa [D] using hlargePsmall)
  let R : ℝ :=
    320 * (r : ℝ) * Real.log (1 + A) +
      8 * (r : ℝ) - classicalClassIVRankinH A
  have hshell :=
    classical_classIV_shell_bound_of_rankin_budget hf hB hgrowth
      ha0 haklt hak hyx hzy hk hzsqrt hw2 hwsq hx
      (by omega : 1 ≤ r) hzwr hpz hkb D hD
      (by simpa [D] using hlargeP) (by simpa [D] using hε0)
      (R := R) (by simpa [D, R] using hbudget)

  let C0 : ℝ := Shiu.smallPrimeConstant (Shiu.fixedPrimePowerCutoff A D) B
  let F0 : ℝ := 2*A^2*Real.exp (2*D)
  have hC0 : 0 ≤ C0 := by
    have h := Shiu.small_prime_product_uniform
      (Shiu.fixedPrimePowerCutoff A D) B ∅ (fun _ => (0 : ℝ)) hB
      (by simp) (by simp) (by simp)
    have h1 : (1 : ℝ) ≤ C0 := by simpa [C0] using h
    linarith
  have hbasepos : 0 < 1 + A := by
    linarith [hf.A_nonnegative]
  have hpowexp :
      (1 + A) ^ (320 * r) =
        Real.exp (320 * (r : ℝ) * Real.log (1 + A)) := by
    calc
      (1 + A) ^ (320 * r)
          = Real.exp (Real.log (1 + A)) ^ (320 * r) := by
            rw [Real.exp_log hbasepos]
      _ = Real.exp
          (((320 * r : ℕ) : ℝ) * Real.log (1 + A)) := by
            rw [← Real.exp_nat_mul]
      _ = Real.exp (320 * (r : ℝ) * Real.log (1 + A)) := by
            congr 1
            norm_num
  have hexpcancel :
      (1 + A) ^ (320 * r) *
        (C0 * Real.exp (primeMass f z k + F0 - R)) =
      C0 * Real.exp (F0 + classicalClassIVRankinH A) *
        Real.exp (-8 * (r : ℝ)) *
        Real.exp (primeMass f z k) := by
    rw [hpowexp]
    calc
      _ = C0 * Real.exp
            (320 * (r : ℝ) * Real.log (1 + A) +
              (primeMass f z k + F0 - R)) := by
            rw [Real.exp_add]
            ring
      _ = C0 * Real.exp
            ((F0 + classicalClassIVRankinH A) + (-8 * (r : ℝ)) +
              primeMass f z k) := by
            congr 1
            dsimp [R]
            ring
      _ = _ := by
            rw [Real.exp_add, Real.exp_add]
            ring
  have hlogz : 0 < Real.log (z : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < z by omega)
  have hlogw : 0 < Real.log (w : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < w by omega)
  have hlogcmp :=
    classical_classIV_log_shell_compare (z := z) (w := w) (r := r)
      hz2 hw2 hzwr
  have hinv :
      1 / Real.log (w : ℝ) ≤
        (2 * (((r + 1 : ℕ) : ℝ))) / Real.log (z : ℝ) := by
    apply (le_div_iff₀ hlogz).2
    have hratio :
        Real.log (z : ℝ) / Real.log (w : ℝ) ≤
          2 * (((r + 1 : ℕ) : ℝ)) :=
      (div_le_iff₀ hlogw).2 hlogcmp
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using hratio
  let J : ℝ :=
    (y : ℝ) /
      ((k.totient : ℝ) * Real.log (z : ℝ))
  have hJ0 : 0 ≤ J := by
    dsimp [J]
    positivity
  have hscaled :
      (y : ℝ) /
          ((k.totient : ℝ) * Real.log (w : ℝ)) ≤
        2 * (((r + 1 : ℕ) : ℝ)) * J := by
    have hphi : (0 : ℝ) ≤ (k.totient : ℝ) := by positivity
    calc
      (y : ℝ) /
          ((k.totient : ℝ) * Real.log (w : ℝ))
          =
        ((y : ℝ) / (k.totient : ℝ)) *
          (1 / Real.log (w : ℝ)) := by ring
      _ ≤ ((y : ℝ) / (k.totient : ℝ)) *
          ((2 * (((r + 1 : ℕ) : ℝ))) /
            Real.log (z : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 * (((r + 1 : ℕ) : ℝ)) * J := by
        dsimp [J]
        ring
  have hcoef : (1 : ℝ) ≤ 6 * (((r + 1 : ℕ) : ℝ)) := by
    have hrp : (1 : ℝ) ≤ (((r + 1 : ℕ) : ℝ)) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le r))
    nlinarith
  have hG :
      (3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log (w : ℝ)) +
          (z : ℝ) ^ 2 ≤
        6 * (((r + 1 : ℕ) : ℝ)) *
          (J + (z : ℝ) ^ 2) := by
    calc
      (3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log (w : ℝ)) +
          (z : ℝ) ^ 2
          =
        3 * ((y : ℝ) /
          ((k.totient : ℝ) * Real.log (w : ℝ))) +
          (z : ℝ) ^ 2 := by ring
      _ ≤ 3 * (2 * (((r + 1 : ℕ) : ℝ)) * J) +
          (z : ℝ) ^ 2 := by
        gcongr
      _ ≤ 6 * (((r + 1 : ℕ) : ℝ)) * J +
          6 * (((r + 1 : ℕ) : ℝ)) * (z : ℝ) ^ 2 := by
        apply _root_.add_le_add
        · ring_nf
          exact le_rfl
        · simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hcoef (sq_nonneg (z : ℝ))
      _ = 6 * (((r + 1 : ℕ) : ℝ)) *
          (J + (z : ℝ) ^ 2) := by ring
  have hfac0 :
      0 ≤ 4 * C0 * Real.exp (F0 + classicalClassIVRankinH A) *
        Real.exp (-8 * (r : ℝ)) *
        Real.exp (primeMass f z k) := by
    positivity
  calc
    classicalClassIVShellOvercount f x y z k a p w
        ≤
      (4 * (1 + A) ^ (320 * r)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) *
        (C0 * Real.exp (primeMass f z k + F0 - R)) := by simpa [C0, F0] using hshell
    _ =
      (4 * C0 * Real.exp (F0 + classicalClassIVRankinH A) *
        Real.exp (-8 * (r : ℝ)) *
        Real.exp (primeMass f z k)) *
        ((3 * (y : ℝ)) /
          ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) := by
      calc
        (4 * (1 + A) ^ (320 * r)) *
            ((3 * (y : ℝ)) /
              ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) *
            (C0 * Real.exp (primeMass f z k + F0 - R))
            =
          4 * ((1 + A) ^ (320 * r) *
            (C0 * Real.exp (primeMass f z k + F0 - R))) *
            ((3 * (y : ℝ)) /
              ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) := by ring
        _ =
          4 * (C0 * Real.exp (F0 + classicalClassIVRankinH A) *
            Real.exp (-8 * (r : ℝ)) *
            Real.exp (primeMass f z k)) *
            ((3 * (y : ℝ)) /
              ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) := by
            rw [hexpcancel]
        _ =
          (4 * C0 * Real.exp (F0 + classicalClassIVRankinH A) *
            Real.exp (-8 * (r : ℝ)) *
            Real.exp (primeMass f z k)) *
            ((3 * (y : ℝ)) /
              ((k.totient : ℝ) * Real.log w) + (z : ℝ) ^ 2) := by ring
    _ ≤
      (4 * C0 * Real.exp (F0 + classicalClassIVRankinH A) *
        Real.exp (-8 * (r : ℝ)) *
        Real.exp (primeMass f z k)) *
        (6 * (((r + 1 : ℕ) : ℝ)) *
          (J + (z : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hG hfac0
    _ =
      (24 * C0 * Real.exp (F0 + classicalClassIVRankinH A)) *
        ((((r + 1 : ℕ) : ℝ)) * Real.exp (-8 * (r : ℝ))) *
        ((J + (z : ℝ) ^ 2) *
          Real.exp (primeMass f z k)) := by ring
    _ =
      (24 * C0 * Real.exp (F0 + classicalClassIVRankinH A)) *
        ((((r + 1 : ℕ) : ℝ)) * Real.exp (-8 * (r : ℝ))) *
        ((((y : ℝ)) /
            ((k.totient : ℝ) * Real.log (z : ℝ)) +
          (z : ℝ) ^ 2) *
          Real.exp (primeMass f z k)) := by
      rfl

#print axioms classical_classIV_shell_bound_final
end PaperB.M4B
