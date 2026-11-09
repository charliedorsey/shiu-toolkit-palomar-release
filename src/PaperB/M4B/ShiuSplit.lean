module

/-
Paper B M4B-CORE S4-S5 finite/source adapters.
Authorized surface: M4B0 ledger rows S4-S5 only.
-/

public import PaperB.M4A.ShiuLemma2
public import Mathlib.Data.Nat.Factors
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Int.GCD

public section

open Finset Nat

namespace PaperB
namespace M4B

/-- Greedy prefix split at multiplicative threshold `z`.
The left list is the maximal initial block whose product remains at most `z`. -/
def prefixSplit : ℕ → List ℕ → List ℕ × List ℕ
  | _, [] => ([], [])
  | z, p :: ps =>
      if h : p ≤ z then
        let s := prefixSplit (z / p) ps
        (p :: s.1, s.2)
      else
        ([], p :: ps)

theorem prefixSplit_append (z : ℕ) (l : List ℕ) :
    (prefixSplit z l).1 ++ (prefixSplit z l).2 = l := by
  induction l generalizing z with
  | nil => simp [prefixSplit]
  | cons p ps ih =>
      by_cases h : p ≤ z
      · simp [prefixSplit, h, ih]
      · simp [prefixSplit, h]

theorem prefixSplit_left_prod_le
    (z : ℕ) (l : List ℕ) (hz : 1 ≤ z)
    (hpos : ∀ p ∈ l, 0 < p) :
    (prefixSplit z l).1.prod ≤ z := by
  induction l generalizing z with
  | nil => simpa [prefixSplit] using hz
  | cons p ps ih =>
      by_cases hpz : p ≤ z
      · have hp : 0 < p := hpos p (by simp)
        have hzdiv : 1 ≤ z / p := Nat.div_pos hpz hp
        have htail : ∀ q ∈ ps, 0 < q := by
          intro q hq
          exact hpos q (by simp [hq])
        have hrec := ih (z := z / p) hzdiv htail
        simp only [prefixSplit, hpz, ↓reduceDIte]
        calc
          p * (prefixSplit (z / p) ps).1.prod
              ≤ p * (z / p) := Nat.mul_le_mul_left p hrec
          _ ≤ z := by
            simpa [Nat.mul_comm] using Nat.mul_div_le z p
      · simpa [prefixSplit, hpz] using hz

theorem prefixSplit_cross
    (z : ℕ) (l : List ℕ)
    (hpos : ∀ p ∈ l, 0 < p) :
    (prefixSplit z l).2 = [] ∨
      ∃ q qs, (prefixSplit z l).2 = q :: qs ∧
        z < (prefixSplit z l).1.prod * q := by
  induction l generalizing z with
  | nil => simp [prefixSplit]
  | cons p ps ih =>
      by_cases hpz : p ≤ z
      · have hp : 0 < p := hpos p (by simp)
        have htail : ∀ q ∈ ps, 0 < q := by
          intro q hq
          exact hpos q (by simp [hq])
        rcases ih (z := z / p) htail with hnil | ⟨q, qs, hrest, hcross⟩
        · left
          simpa [prefixSplit, hpz] using hnil
        · right
          refine ⟨q, qs, ?_, ?_⟩
          · simpa [prefixSplit, hpz] using hrest
          · have hmul :
                z < ((prefixSplit (z / p) ps).1.prod * q) * p :=
              (Nat.div_lt_iff_lt_mul hp).mp hcross
            simpa [prefixSplit, hpz, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
              using hmul
      · right
        refine ⟨p, ps, by simp [prefixSplit, hpz], ?_⟩
        simpa [prefixSplit, hpz] using (lt_of_not_ge hpz)

theorem prefixSplit_ordered
    (z : ℕ) (l : List ℕ) (hsort : l.SortedLT) :
    ∀ p ∈ (prefixSplit z l).1,
      ∀ q ∈ (prefixSplit z l).2, p < q := by
  induction l generalizing z with
  | nil => simp [prefixSplit]
  | cons a l ih =>
      by_cases haz : a ≤ z
      · have hpair := List.pairwise_cons.mp hsort.pairwise
        have htail : l.SortedLT := hsort.pairwise.tail.sortedLT
        intro p hp q hq
        simp only [prefixSplit, haz, ↓reduceDIte, List.mem_cons] at hp
        have hq_rec : q ∈ (prefixSplit (z / a) l).2 := by
          simpa [prefixSplit, haz] using hq
        have hq_l : q ∈ l := by
          have happ := prefixSplit_append (z / a) l
          rw [← happ]
          simp [hq_rec]
        rcases hp with rfl | hp
        · exact hpair.1 q hq_l
        · exact ih (z := z / a) htail p hp q hq_rec
      · simp [prefixSplit, haz]

/-- Exact squarefree specialization of Shiu (5.2).
The two returned lists concatenate to the ordered prime factorization; their
products give `n=b*d`, the first product is at most `z`, and if the
second list is nonempty then multiplying its first prime crosses `z`. -/
structure PrefixFactorization (n z : ℕ) where
  small : List ℕ
  large : List ℕ
  concat : small ++ large = n.primeFactorsList
  factorization : n = small.prod * large.prod
  small_prod_le : small.prod ≤ z
  crossing :
    large = [] ∨ ∃ q qs, large = q :: qs ∧ z < small.prod * q
  ordered : ∀ p ∈ small, ∀ q ∈ large, p < q
  coprime : small.prod.Coprime large.prod

/-- S4: source-faithful first-prefix factorization at threshold `z`
for the squarefree support actually needed by K1. -/
theorem shiu_prefix_factorization_split
    (n z : ℕ) (hn : Squarefree n) (hz : 1 ≤ z) :
    ∃ s : PrefixFactorization n z, True := by
  let small := (prefixSplit z n.primeFactorsList).1
  let large := (prefixSplit z n.primeFactorsList).2
  have hpos : ∀ p ∈ n.primeFactorsList, 0 < p :=
    fun p hp => Nat.pos_of_mem_primeFactorsList hp
  have hconcat : small ++ large = n.primeFactorsList := by
    exact prefixSplit_append z n.primeFactorsList
  have hfactor : n = small.prod * large.prod := by
    have h := congrArg List.prod hconcat
    rw [List.prod_append, Nat.prod_primeFactorsList hn.ne_zero] at h
    exact h.symm
  have hsort : n.primeFactorsList.SortedLT :=
    (Nat.primeFactorsList_sorted n).sortedLT_of_nodup hn.nodup_primeFactorsList
  have hcop : small.prod.Coprime large.prod := by
    apply Nat.coprime_of_squarefree_mul
    rwa [← hfactor]
  refine ⟨{
    small := small
    large := large
    concat := hconcat
    factorization := hfactor
    small_prod_le := ?_
    crossing := ?_
    ordered := ?_
    coprime := hcop
  }, trivial⟩
  · exact prefixSplit_left_prod_le z n.primeFactorsList hz hpos
  · exact prefixSplit_cross z n.primeFactorsList hpos
  · exact prefixSplit_ordered z n.primeFactorsList hsort

end M4B
end PaperB
