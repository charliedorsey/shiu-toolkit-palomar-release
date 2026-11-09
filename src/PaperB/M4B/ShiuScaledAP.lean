module

/-
Paper B M4B-CORE S5: scaled progression adapter.
Authorized surface: M4B0 ledger row S5 only.
-/

public import PaperB.M4A.ShiuLemma2
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Int.GCD

public section

open Finset Nat

namespace PaperB
namespace M4B

/-- Natural endpoints after dividing the source interval by a positive factor. -/
@[expose] def scaledUpper (x b : ℕ) : ℕ := x / b

def scaledLower (x y b : ℕ) : ℕ := (x - y) / b

@[expose] def scaledLength (x y b : ℕ) : ℕ :=
  scaledUpper x b - scaledLower x y b

/-- The source interval `x-y < b*d ≤ x` maps into the exact natural
interval consumed by the C5 sieve after division by positive `b`. -/
theorem scaledInterval_mem
    {x y b d : ℕ} (hb : 0 < b)
    (hlo : x - y < b * d) (hhi : b * d ≤ x) :
    d ∈ Finset.Ioc (scaledLower x y b) (scaledUpper x b) := by
  rw [Finset.mem_Ioc]
  constructor
  · exact (Nat.div_lt_iff_lt_mul hb).2 <| by
      simpa [Nat.mul_comm] using hlo
  · exact (Nat.le_div_iff_mul_le hb).2 <| by
      simpa [Nat.mul_comm] using hhi

/-- The divided interval has the source length `y/b` up to the single
integer-rounding unit that is harmless in the fixed-quarter argument. -/
theorem scaledLength_le
    {x y b : ℕ} (hyx : y ≤ x) :
    scaledLength x y b ≤ y / b + 1 := by
  have h :=
    Nat.add_div_le_div_add_div_add_one (x - y) y b
  rw [Nat.sub_add_cancel hyx] at h
  unfold scaledLength scaledUpper scaledLower
  rw [Nat.sub_le_iff_le_add]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h


/-- One-unit upper over-cover used to feed the natural-valued C5 interval.
The lower endpoint is unchanged, while the interval length gains one. -/
@[expose] def scaledCoverUpper (x b : ℕ) : ℕ := scaledUpper x b + 1

@[expose] def scaledCoverLength (x y b : ℕ) : ℕ := scaledLength x y b + 1

theorem scaledLower_le_upper (x y b : ℕ) :
    scaledLower x y b ≤ scaledUpper x b := by
  unfold scaledLower scaledUpper
  exact Nat.div_le_div_right (Nat.sub_le x y)

theorem scaledCover_lower_eq (x y b : ℕ) :
    scaledCoverUpper x b - scaledCoverLength x y b =
      scaledLower x y b := by
  have h := scaledLower_le_upper x y b
  unfold scaledCoverUpper scaledCoverLength scaledLength
  omega

/-- Every divided source point lies in the one-unit over-cover consumed by C5. -/
theorem scaledCover_mem
    {x y b d : ℕ} (hb : 0 < b)
    (hlo : x - y < b * d) (hhi : b * d ≤ x) :
    d ∈ Finset.Ioc
      (scaledCoverUpper x b - scaledCoverLength x y b)
      (scaledCoverUpper x b) := by
  have hm := scaledInterval_mem hb hlo hhi
  rw [Finset.mem_Ioc] at hm ⊢
  rw [scaledCover_lower_eq]
  exact ⟨hm.1, by
    simpa [scaledCoverUpper] using hm.2.trans (Nat.le_succ _)⟩

/-- The exact divided length dominates the floored source length. -/
theorem div_le_scaledLength
    {x y b : ℕ} (hyx : y ≤ x) :
    y / b ≤ scaledLength x y b := by
  have h := Nat.add_div_le_add_div (x - y) y b
  rw [Nat.sub_add_cancel hyx] at h
  unfold scaledLength scaledUpper scaledLower
  omega

/-- The C5 over-cover costs at most two integer units versus `y/b`. -/
theorem scaledCoverLength_le
    {x y b : ℕ} (hyx : y ≤ x) :
    scaledCoverLength x y b ≤ y / b + 2 := by
  have h := scaledLength_le (x := x) (y := y) (b := b) hyx
  unfold scaledCoverLength
  omega

/-- Source condition `k*b < y` gives the strict modulus-length hypothesis
needed by sealed C5 after the one-unit over-cover. -/
theorem modulus_lt_scaledCoverLength
    {x y b k : ℕ} (hb : 0 < b) (hyx : y ≤ x)
    (hkb : k * b < y) :
    k < scaledCoverLength x y b := by
  have hkdiv : k ≤ y / b :=
    (Nat.le_div_iff_mul_le hb).2 (Nat.le_of_lt hkb)
  have hlen := div_le_scaledLength (x := x) (y := y) (b := b) hyx
  unfold scaledCoverLength
  omega

/-- Congruence to a reduced residue class preserves coprimality with the modulus. -/
theorem coprime_of_modEq_reduced
    {n a k : ℕ} (hak : a.Coprime k) (hna : n ≡ a [MOD k]) :
    n.Coprime k := by
  apply Nat.coprime_of_dvd'
  intro p hp hpn hpk
  have hmod : n ≡ a [MOD p] := hna.of_dvd hpk
  have hpa : p ∣ a := by
    apply Nat.modEq_zero_iff_dvd.mp
    exact hmod.symm.trans hpn.modEq_zero_nat
  have hp1 : p = 1 := Nat.eq_one_of_dvd_coprimes hak hpa hpk
  simpa [hp1]

/-- S5 residue adapter: after extracting a positive factor `b` coprime to
`k`, the complementary factor lies in a uniquely cancellable reduced
residue class modulo `k`. The representative is chosen in `[0,k)`. -/
theorem scaledResidue_exists
    {a b d k : ℕ}
    (hk : 0 < k) (hak : a.Coprime k) (hbk : b.Coprime k)
    (hna : b * d ≡ a [MOD k]) :
    ∃ a' : ℕ, a' < k ∧ a'.Coprime k ∧ d ≡ a' [MOD k] := by
  obtain ⟨a', ha'lt, hba'⟩ :=
    Nat.exists_mul_mod_eq_of_coprime a hbk hk.ne'
  have hba : b * a' ≡ a [MOD k] := by
    simpa [Nat.ModEq] using hba'
  have hdd : d ≡ a' [MOD k] := by
    apply Nat.ModEq.cancel_left_of_coprime hbk.symm.gcd_eq_one
    exact hna.trans hba.symm
  have hd : d.Coprime k := by
    exact (coprime_of_modEq_reduced hak hna).coprime_dvd_left
      (by exact dvd_mul_left d b)
  have ha'cop : a'.Coprime k := by
    apply Nat.coprime_of_dvd'
    intro p hp hpa' hpk
    have hmod : d ≡ a' [MOD p] := hdd.of_dvd hpk
    have hpd : p ∣ d := by
      apply Nat.modEq_zero_iff_dvd.mp
      exact hmod.trans hpa'.modEq_zero_nat
    have hp1 : p = 1 := Nat.eq_one_of_dvd_coprimes hd hpd hpk
    simpa [hp1]
  exact ⟨a', ha'lt, ha'cop, hdd⟩

/-- Fixed residue representative for a scaled progression.
Unlike `scaledResidue_exists`, this witness is chosen once from `a,b,k`
and works uniformly for every complementary factor `d`. -/
theorem scaledResidue_fixed
    {a b k : ℕ}
    (ha0 : 0 < a) (haklt : a < k)
    (hak : a.Coprime k) (hbk : b.Coprime k) :
    ∃ a' : ℕ, 0 < a' ∧ a' < k ∧ a'.Coprime k ∧
      ∀ d : ℕ, (b * d ≡ a [MOD k] ↔ d ≡ a' [MOD k]) := by
  have hk : 0 < k := lt_trans ha0 haklt
  obtain ⟨a', ha'lt, hba'⟩ :=
    Nat.exists_mul_mod_eq_of_coprime a hbk hk.ne'
  have hba : b * a' ≡ a [MOD k] := by
    simpa [Nat.ModEq] using hba'
  have hba_cop : (b * a').Coprime k :=
    coprime_of_modEq_reduced hak hba
  have ha'cop : a'.Coprime k :=
    hba_cop.coprime_dvd_left (by exact dvd_mul_left a' b)
  have ha'pos : 0 < a' := by
    by_contra hpos
    have ha'0 : a' = 0 := Nat.eq_zero_of_not_pos hpos
    subst a'
    have hk1 : k = 1 := k.coprime_zero_left.mp ha'cop
    omega
  refine ⟨a', ha'pos, ha'lt, ha'cop, ?_⟩
  intro d
  constructor
  · intro hd
    apply Nat.ModEq.cancel_left_of_coprime hbk.symm.gcd_eq_one
    exact hd.trans hba.symm
  · intro hd
    exact (hd.mul_left b).trans hba

end M4B
end PaperB
