module

public import ShiuPublic.CorvethClassicalPrefixCore
public import PaperB.M4B.ShiuClassIV

public section

namespace PaperB.M4B

/-- The physical large full-prime-power suffix lies in the EXACT original
C5 inner progression once its genuine shell roughness has been paid. -/
theorem eiravel_classical_large_mem_classIVInnerSet
    (n x y z k a w : ℕ)
    (hn : n ≠ 0) (hz : 1 ≤ z)
    (hlow : x - y < n) (hhigh : n ≤ x)
    (hmod : n ≡ a [MOD k])
    (hrough : PaperB.M4A.shiuRough
      (classical_primePower_prefix_split n z hn hz).large.prod w) :
    (classical_primePower_prefix_split n z hn hz).large.prod ∈
      classIVInnerSet x y k a
        (classical_primePower_prefix_split n z hn hz).small.prod w := by
  classical
  let S := classical_primePower_prefix_split n z hn hz
  have hfac : n = S.small.prod * S.large.prod := S.factorization
  have hbpos : 0 < S.small.prod := by
    by_contra hh
    have hbzero : S.small.prod = 0 := Nat.eq_zero_of_not_pos hh
    have hnzero : n = 0 := by simpa [hfac, hbzero] using hfac
    exact hn hnzero
  have hlow' : x - y < S.small.prod * S.large.prod := by
    rw [← hfac]
    exact hlow
  have hhigh' : S.small.prod * S.large.prod ≤ x := by
    rw [← hfac]
    exact hhigh
  have hmod' : S.small.prod * S.large.prod ≡ a [MOD k] := by
    rw [← hfac]
    exact hmod
  have hmem := scaledInterval_mem hbpos hlow' hhigh'
  change S.large.prod ∈ classIVInnerSet x y k a S.small.prod w
  unfold classIVInnerSet
  exact Finset.mem_filter.mpr ⟨hmem, hmod', hrough⟩

#print axioms eiravel_classical_large_mem_classIVInnerSet
end PaperB.M4B
