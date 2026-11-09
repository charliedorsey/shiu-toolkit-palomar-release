module

public import EiravelFourOvercounts
public import ShiuPublic.CorvethClassicalClassIFinal
public import ShiuPublic.EiravelClassIIIUnconditional
public import ShiuPublic.VaelisClassIVAllShell
public import EiravelShiuTargetException
public import ShiuPublic.VaelisClassIVMassMonotone

public section

namespace PaperB.M4B
open scoped BigOperators
noncomputable section

/-- The unrestricted classical Shiu estimate, CONDITIONAL on the literal
parameter/endpoint gates of the existing analytic suppliers. No squarefree
hypothesis; source covering, all four reindexings and exception are paid.
The z² absorption condition is deliberately exposed, NOT derived. -/
theorem eiravel_unrestricted_shiu_of_endpoint_gates (A B : ℝ) :
    ∃ X0 : ℕ, ∀ (f : ArithmeticFunction ℝ),
      Shiu.ClassicalEnvelope f A →
      0 ≤ B →
      (∀ n : ℕ, 1 ≤ n →
        f n ≤ B * (n : ℝ) ^ (1/1280 : ℝ)) →
      ∀ x y z k a : ℕ,
        X0 ≤ x → 2 ≤ x →
        0 < a → a < k → a.Coprime k →
        y ≤ x → z ≤ y → k*z < y →
        2 ≤ Nat.sqrt z → x < z ^ 160 →
        Real.exp 4 ≤ (z : ℝ) →
        4 ≤ shiuLogLogSmoothThreshold x →
        Real.exp (4 * classicalClassIVRankinD A) ≤
          (shiuLogLogSmoothThreshold x : ℝ) →
        (z : ℝ) ≤ ((y : ℝ)/(k : ℝ)) * (z : ℝ)^(-1/4 : ℝ) →
        Real.log (x : ℝ) ≤ 320 * Real.log (Nat.sqrt z : ℝ) →
        Real.log (x : ℝ) ≤ 160 * Real.log (z : ℝ) →
        (z : ℝ)^2 ≤
          (y : ℝ)/((k.totient : ℝ) * Real.log (x : ℝ)) →
        ((y : ℝ)/(k : ℝ)) * (z : ℝ)^(-1/8 : ℝ) ≤
          (y : ℝ)/((k.totient : ℝ) * Real.log (x : ℝ)) →
        z ≤ x →
        (∑ n ∈ eiravelShiuPhysicalSet x y k a, f n) ≤
          (961 * corvethClassicalClassIConstant A B +
            161 * classicalShiuClassIVConstant A B + 56330 * B) *
          ((y : ℝ)/((k.totient : ℝ)*Real.log (x : ℝ))) *
          Real.exp (primeMass f x k) := by
  obtain ⟨XIII, hIIIevent⟩ := eiravel_classIII_weighted_eventual_no_card
  refine ⟨XIII, ?_⟩
  intro f hf hB hgrowth x y z k a hX hx2 ha0 haklt hak
    hyx hzy hkz hzsqrt hxz hzlarge hL4 hRankin
    hzabsorb hlogSqrt hlogZ hz2absorb hsmallabsorb hzx
  have hk : 0 < k := lt_trans ha0 haklt
  have hz4 : 4 ≤ z := by
    have := Nat.sqrt_le' z
    nlinarith
  have hL2 : 2 ≤ shiuLogLogSmoothThreshold x := by omega
  have hquarter : ∀ n : ℕ, 1 ≤ n →
      f n ≤ B * (n : ℝ) ^ (1/4 : ℝ) := by
    intro n hn
    have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hp := Real.rpow_le_rpow_of_exponent_le hnOne
      (by norm_num : (1/1280 : ℝ) ≤ (1/4 : ℝ))
    exact (hgrowth n hn).trans (mul_le_mul_of_nonneg_left hp hB)
  have hphi : (0 : ℝ) < k.totient := by
    exact_mod_cast Nat.totient_pos.mpr hk
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hlogs : 0 < Real.log (Nat.sqrt z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Nat.sqrt z by omega))
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  let Q : ℝ := (y : ℝ)/((k.totient : ℝ)*Real.log (x : ℝ))
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hfracI :
      (y : ℝ)/((k.totient : ℝ)*Real.log (Nat.sqrt z : ℝ)) ≤
        320 * Q := by
    have hd1 : (0 : ℝ) <
        (k.totient : ℝ)*Real.log (Nat.sqrt z : ℝ) :=
      mul_pos hphi hlogs
    have hd2 : (0 : ℝ) <
        (k.totient : ℝ)*Real.log (x : ℝ) :=
      mul_pos hphi hlogx
    dsimp [Q]
    rw [show
      320 * ((y : ℝ)/((k.totient : ℝ)*Real.log (x : ℝ))) =
      (320*(y : ℝ))/((k.totient : ℝ)*Real.log (x : ℝ)) by ring]
    apply (div_le_div_iff₀ hd1 hd2).2
    have hm := mul_le_mul_of_nonneg_left hlogSqrt
      (mul_nonneg (Nat.cast_nonneg y) hphi.le)
    ring_nf at hm ⊢
    exact hm
  have hfracIV :
      (y : ℝ)/((k.totient : ℝ)*Real.log (z : ℝ)) ≤
        160 * Q := by
    have hd1 : (0 : ℝ) <
        (k.totient : ℝ)*Real.log (z : ℝ) :=
      mul_pos hphi hlogz
    have hd2 : (0 : ℝ) <
        (k.totient : ℝ)*Real.log (x : ℝ) :=
      mul_pos hphi hlogx
    dsimp [Q]
    rw [show
      160 * ((y : ℝ)/((k.totient : ℝ)*Real.log (x : ℝ))) =
      (160*(y : ℝ))/((k.totient : ℝ)*Real.log (x : ℝ)) by ring]
    apply (div_le_div_iff₀ hd1 hd2).2
    have hm := mul_le_mul_of_nonneg_left hlogZ
      (mul_nonneg (Nat.cast_nonneg y) hphi.le)
    ring_nf at hm ⊢
    exact hm
  have hRI :
      3*(y : ℝ)/((k.totient : ℝ)*Real.log (Nat.sqrt z : ℝ))+
        (z : ℝ)^2 ≤ 961*Q := by
    have h3 : 3*(y : ℝ)/((k.totient : ℝ)*Real.log (Nat.sqrt z : ℝ)) ≤
        960*Q := by
      calc
        _ = 3 * ((y : ℝ)/((k.totient : ℝ)*Real.log (Nat.sqrt z : ℝ))) := by ring
        _ ≤ 3*(320*Q) :=
          mul_le_mul_of_nonneg_left hfracI (by norm_num)
        _ = 960*Q := by ring
    have hz2Q : (z : ℝ)^2 ≤ Q := hz2absorb
    calc
      _ ≤ 960*Q+Q := add_le_add h3 hz2Q
      _ = 961*Q := by ring
  have hRIV :
      (y : ℝ)/((k.totient : ℝ)*Real.log (z : ℝ))+
        (z : ℝ)^2 ≤ 161*Q := by
    nlinarith [hfracIV, hz2absorb]
  have hmassZX :=
    classical_primeMass_mono hf (k := k) hzx
  have hExp :
      Real.exp (primeMass f z k) ≤ Real.exp (primeMass f x k) :=
    Real.exp_le_exp.mpr hmassZX
  have hExpOne : (1 : ℝ) ≤ Real.exp (primeMass f x k) := by
    have hmass0 : 0 ≤ primeMass f x k := by
      classical
      unfold primeMass
      apply Finset.sum_nonneg
      intro p hp
      exact div_nonneg (hf.nonnegative p) (by positivity)
    rw [Real.one_le_exp_iff]
    exact hmass0
  have hS1 : 0 ≤ Shiu.smallPrimeConstant
      (Shiu.fixedPrimePowerCutoff A 1) B := by
    have hs := Shiu.small_prime_product_uniform
      (Shiu.fixedPrimePowerCutoff A 1) B
      ∅ (fun _ => (0:ℝ)) hB (by simp) (by simp) (by simp)
    have h1 : 1 ≤ Shiu.smallPrimeConstant
      (Shiu.fixedPrimePowerCutoff A 1) B := by simpa using hs
    linarith
  have hS4 : 0 ≤ Shiu.smallPrimeConstant
      (Shiu.fixedPrimePowerCutoff A (classicalClassIVRankinD A)) B := by
    have hs := Shiu.small_prime_product_uniform
      (Shiu.fixedPrimePowerCutoff A (classicalClassIVRankinD A)) B
      ∅ (fun _ => (0:ℝ)) hB (by simp) (by simp) (by simp)
    have h1 : 1 ≤ Shiu.smallPrimeConstant
      (Shiu.fixedPrimePowerCutoff A (classicalClassIVRankinD A)) B := by
      simpa using hs
    linarith
  have hCI : 0 ≤ corvethClassicalClassIConstant A B := by
    unfold corvethClassicalClassIConstant
    have hbase : 0 ≤ (1+A) := by linarith [hf.A_nonnegative]
    positivity
  have hCIV : 0 ≤ classicalShiuClassIVConstant A B := by
    unfold classicalShiuClassIVConstant
    positivity
  have hI := corveth_classical_classI_final
    hf hB hquarter ha0 haklt hak hyx hzy hkz hzsqrt hxz hzlarge
  have hIV := classical_shiu_classIV_bound
    hf hB hquarter ha0 haklt hak hyx hzy hkz
      (by omega : 2 ≤ z) hxz hL4 hRankin
  have hIII := hIIIevent hf hB hgrowth x y z k a
    hX hyx hxz hk hzabsorb
  have hE := eiravel_selected_full_power_exception_shiu_target
    hf hB hgrowth x y z k a hx2 hz4 hyx hk hkz hxz
  have hIbound :
      classIOvercount f x y z k a ≤
      (961 * corvethClassicalClassIConstant A B) * Q *
        Real.exp (primeMass f x k) := by
    calc
      classIOvercount f x y z k a ≤
        corvethClassicalClassIConstant A B *
          ((3*(y : ℝ)/((k.totient : ℝ)*Real.log (Nat.sqrt z : ℝ))+
              (z : ℝ)^2) * Real.exp (primeMass f z k)) := hI
      _ ≤ corvethClassicalClassIConstant A B *
          ((961*Q) * Real.exp (primeMass f z k)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hRI (Real.exp_nonneg _)) hCI
      _ ≤ corvethClassicalClassIConstant A B *
          ((961*Q) * Real.exp (primeMass f x k)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hExp (mul_nonneg (by norm_num) hQ)) hCI
      _ = (961*corvethClassicalClassIConstant A B)*Q*
          Real.exp (primeMass f x k) := by ring
  have hIVbound :
      classicalClassIVOvercount f x y z k a ≤
      (161 * classicalShiuClassIVConstant A B) * Q *
        Real.exp (primeMass f x k) := by
    calc
      classicalClassIVOvercount f x y z k a ≤
        classicalShiuClassIVConstant A B *
          (((y : ℝ)/((k.totient : ℝ)*Real.log (z : ℝ))+
              (z : ℝ)^2) * Real.exp (primeMass f z k)) := hIV
      _ ≤ classicalShiuClassIVConstant A B *
          ((161*Q) * Real.exp (primeMass f z k)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hRIV (Real.exp_nonneg _)) hCIV
      _ ≤ classicalShiuClassIVConstant A B *
          ((161*Q) * Real.exp (primeMass f x k)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hExp (mul_nonneg (by norm_num) hQ)) hCIV
      _ = (161*classicalShiuClassIVConstant A B)*Q*
          Real.exp (primeMass f x k) := by ring
  have hIIIbound :
      corvethClassicalClassIIIWeightedOvercount f x y z k a ≤
      (10*B)*Q*Real.exp (primeMass f x k) := by
    have h10 : 0 ≤ (10:ℝ)*B := by positivity
    have htemp :
        (10*B)*(((y : ℝ)/(k : ℝ))*(z : ℝ)^(-1/8 : ℝ)) ≤
        (10*B)*Q := mul_le_mul_of_nonneg_left hsmallabsorb h10
    calc
      corvethClassicalClassIIIWeightedOvercount f x y z k a ≤
        (10*B)*(((y : ℝ)/(k : ℝ))*(z : ℝ)^(-1/8 : ℝ)) := hIII
      _ ≤ (10*B)*Q := htemp
      _ = (10*B)*Q*1 := by ring
      _ ≤ (10*B)*Q*Real.exp (primeMass f x k) :=
        mul_le_mul_of_nonneg_left hExpOne (mul_nonneg h10 hQ)
  have hEbound :
      eiravelPowerExceptionalMass f x y k a
        ((Nat.primesLE (Nat.sqrt z)).filter (fun p => ¬ p ∣ k))
        (fun p => p^(Nat.log p (Nat.sqrt z)+1)) ≤
      (56320*B)*Q*Real.exp (primeMass f x k) := by
    simpa only [Q, mul_assoc] using hE
  have hsource :=
    eiravel_unrestricted_shiu_four_overcounts hf x y z k a hz4 hL2
  calc
    (∑ n ∈ eiravelShiuPhysicalSet x y k a, f n) ≤
      classIOvercount f x y z k a +
      corvethClassicalClassIIIWeightedOvercount f x y z k a +
      classicalClassIVOvercount f x y z k a +
      eiravelPowerExceptionalMass f x y k a
        ((Nat.primesLE (Nat.sqrt z)).filter (fun p => ¬ p ∣ k))
        (fun p => p^(Nat.log p (Nat.sqrt z)+1)) := hsource
    _ ≤
      (961*corvethClassicalClassIConstant A B)*Q*Real.exp (primeMass f x k) +
      (10*B)*Q*Real.exp (primeMass f x k) +
      (161*classicalShiuClassIVConstant A B)*Q*Real.exp (primeMass f x k) +
      (56320*B)*Q*Real.exp (primeMass f x k) :=
      add_le_add (add_le_add (add_le_add hIbound hIIIbound) hIVbound) hEbound
    _ =
      (961*corvethClassicalClassIConstant A B +
         161*classicalShiuClassIVConstant A B + 56330*B) *
       Q * Real.exp (primeMass f x k) := by ring
    _ =
      (961*corvethClassicalClassIConstant A B +
         161*classicalShiuClassIVConstant A B + 56330*B) *
       ((y : ℝ)/((k.totient : ℝ)*Real.log (x : ℝ))) *
       Real.exp (primeMass f x k) := rfl

#print axioms eiravel_unrestricted_shiu_of_endpoint_gates
end
end PaperB.M4B
