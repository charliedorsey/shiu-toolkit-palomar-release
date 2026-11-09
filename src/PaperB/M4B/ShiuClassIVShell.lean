module

/-
Paper B M4B-CORE S10: Class IV shell decomposition.
Authorized surface: exact M4B0 ledger row S10 only.

The shell is naturalized by r = Nat.log p z. Thus p^r <= z < p^(r+1),
which is the integer-power form of
z^(1/(r+1)) < p <= z^(1/r).
-/

public import PaperB.M4B.ShiuSplit
public import PaperB.M4B.ShiuSmoothCount

public section

open Nat

noncomputable section

namespace PaperB
namespace M4B

/-- Naturalized source endpoint r0 = floor(log z / log(log x loglog x)). -/
@[expose] def shiuClassIVR0 (x z : ℕ) : ℕ :=
  Nat.log (shiuLogLogSmoothThreshold x) z

/-- S10 finite Class-IV shell package. The large factor begins with the
crossing prime p; the remaining fields are exactly the finite consequences
consumed by the shellwise estimate. -/
structure ClassIVShellDecomposition
    (n x z : ℕ) (s : PrefixFactorization n z) where
  p : ℕ
  ps : List ℕ
  large_eq : s.large = p :: ps
  r : ℕ
  r_two_le : 2 ≤ r
  r_le_r0 : r ≤ shiuClassIVR0 x z
  p_prime : p.Prime
  p_pow_le : p ^ r ≤ z
  z_lt_p_pow_succ : z < p ^ (r + 1)
  small_pow_lt : ∀ q ∈ s.small, q ^ r < z
  omega_large_lt : s.large.length < 320 * r

/-- Exact S10 shell decomposition for a Class-IV prefix factorization.
The two class predicates supplied here are precisely the complements of
Class I (p <= sqrt z) and Class III (log x loglog x < p). -/
theorem shiu_classIV_shell_decomposition
    {n x z : ℕ}
    (hn : Squarefree n)
    (hnx : n ≤ x)
    (hx : x < z ^ 160)
    (s : PrefixFactorization n z)
    {p : ℕ} {ps : List ℕ}
    (hlarge : s.large = p :: ps)
    (hp_sqrt : p ≤ Nat.sqrt z)
    (hL2 : 2 ≤ shiuLogLogSmoothThreshold x)
    (hLp : shiuLogLogSmoothThreshold x < p) :
    ∃ sh : ClassIVShellDecomposition n x z s, True := by
  have hpLarge : p ∈ s.large := by
    rw [hlarge]
    simp
  have hpList : p ∈ n.primeFactorsList := by
    rw [← s.concat]
    simp [hpLarge]
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactorsList hpList
  have hz0 : z ≠ 0 := by
    intro hz
    subst z
    simp at hp_sqrt
    omega
  let r : ℕ := Nat.log p z
  have hp2z : p ^ 2 ≤ z := by
    calc
      p ^ 2 ≤ (Nat.sqrt z) ^ 2 :=
        Nat.pow_le_pow_left hp_sqrt 2
      _ ≤ z := Nat.sqrt_le' z
  have hr2 : 2 ≤ r := by
    dsimp [r]
    exact Nat.le_log_of_pow_le hpprime.one_lt hp2z
  have hr0 : r ≤ shiuClassIVR0 x z := by
    dsimp [r, shiuClassIVR0]
    exact Nat.log_anti_left (by omega) (Nat.le_of_lt hLp)
  have hpr : p ^ r ≤ z := by
    dsimp [r]
    exact Nat.pow_log_le_self p hz0
  have hzpr : z < p ^ (r + 1) := by
    dsimp [r]
    simpa [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self hpprime.one_lt z
  have hsmall : ∀ q ∈ s.small, q ^ r < z := by
    intro q hq
    have hqp : q < p := s.ordered q hq p hpLarge
    have hrpos : 0 < r := by omega
    exact (Nat.pow_lt_pow_left hqp (Nat.ne_of_gt hrpos)).trans_le hpr
  have hsortAll : (s.small ++ s.large).SortedLT := by
    rw [s.concat]
    exact
      (Nat.primeFactorsList_sorted n).sortedLT_of_nodup
        hn.nodup_primeFactorsList
  have hsortLarge : s.large.SortedLT := by
    have hsub : s.large.Sublist (s.small ++ s.large) :=
      List.sublist_append_right s.small s.large
    exact
      (List.Pairwise.sublist hsub hsortAll.pairwise).sortedLT
  have hp_le_large : ∀ q ∈ s.large, p ≤ q := by
    intro q hq
    rw [hlarge] at hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact le_rfl
    · have hs : (p :: ps).SortedLT := by
        simpa [hlarge] using hsortLarge
      have hpair := List.pairwise_cons.mp hs.pairwise
      exact (hpair.1 q hq).le
  have hp_prod : p ^ s.large.length ≤ s.large.prod := by
    exact List.pow_length_le_prod s.large p hp_le_large
  have hdvd : s.large.prod ∣ n := by
    refine ⟨s.small.prod, ?_⟩
    calc
      n = s.small.prod * s.large.prod := s.factorization
      _ = s.large.prod * s.small.prod := Nat.mul_comm _ _
  have hdle : s.large.prod ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero) hdvd
  have homega : s.large.length < 320 * r := by
    by_contra hlen
    have hlen' : 320 * r ≤ s.large.length := by omega
    have hpmono :
        p ^ (320 * r) ≤ p ^ s.large.length :=
      Nat.pow_le_pow_right hpprime.pos hlen'
    have hpleX : p ^ (320 * r) ≤ x :=
      hpmono.trans (hp_prod.trans (hdle.trans hnx))
    have hzpow :
        z ^ 160 < p ^ (320 * r) := by
      calc
        z ^ 160 < (p ^ (r + 1)) ^ 160 :=
          Nat.pow_lt_pow_left hzpr (by norm_num)
        _ = p ^ ((r + 1) * 160) := by
          rw [← pow_mul]
        _ ≤ p ^ (320 * r) := by
          apply Nat.pow_le_pow_right hpprime.pos
          omega
    exact (not_lt_of_ge hpleX) (hx.trans hzpow)
  refine ⟨{
    p := p
    ps := ps
    large_eq := hlarge
    r := r
    r_two_le := hr2
    r_le_r0 := hr0
    p_prime := hpprime
    p_pow_le := hpr
    z_lt_p_pow_succ := hzpr
    small_pow_lt := hsmall
    omega_large_lt := homega
  }, trivial⟩

end M4B
end PaperB
