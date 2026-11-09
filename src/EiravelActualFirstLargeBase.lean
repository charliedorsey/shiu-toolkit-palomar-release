module

public import ShiuBaseOrderR0006

public section

namespace PaperB.M4B

/-- An actual nonempty full-prime-power suffix begins with the complete
power of the first remaining BASE prime; the original base belongs to n. -/
theorem eiravel_actual_first_large_base
    (n z : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z)
    (hlarge : (classical_primePower_prefix_split n z hn hz).large ≠ []) :
    ∃ p ts,
      p ∈ n.primeFactors ∧
      (n.primeFactors.sort (· ≤ ·)).drop
        (classical_primePower_prefix_split n z hn hz).small.length =
          p :: ts ∧
      (classical_primePower_prefix_split n z hn hz).large =
          p ^ n.factorization p ::
            ts.map (fun q => q ^ n.factorization q) := by
  classical
  let S := classical_primePower_prefix_split n z hn hz
  let L := (n.primeFactors.sort (· ≤ ·)).drop S.small.length
  have hmap : S.large = L.map (fun p => p ^ n.factorization p) :=
    kestrelle_primePower_large_eq_base_drop n z hn hz
  cases hL : L with
  | nil =>
      have he : S.large = [] := by simpa [hL] using hmap
      exact False.elim (hlarge he)
  | cons p ts =>
      have hpL : p ∈ L := by rw [hL]; simp
      have hpSorted : p ∈ n.primeFactors.sort (· ≤ ·) :=
        List.mem_of_mem_drop hpL
      have hpMem : p ∈ n.primeFactors :=
        (Finset.mem_sort (· ≤ ·)).mp hpSorted
      refine ⟨p, ts, hpMem, hL, ?_⟩
      simpa [hL] using hmap

#print axioms eiravel_actual_first_large_base


/-- The first complete prime-power suffix block still carries its base
prime as a genuine divisor of the physical large product. -/
theorem eiravel_first_large_base_dvd
    (n z p : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z)
    (hpMem : p ∈ n.primeFactors)
    (ts : List ℕ)
    (ht : (classical_primePower_prefix_split n z hn hz).large =
      p ^ n.factorization p :: ts) :
    p ∣ (classical_primePower_prefix_split n z hn hz).large.prod := by
  have hpow : p ^ n.factorization p ∣
      (classical_primePower_prefix_split n z hn hz).large.prod := by
    rw [ht]
    exact List.dvd_prod (by simp : p ^ n.factorization p ∈ p ^ n.factorization p :: ts)
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
  have hpN : p ∣ n := Nat.dvd_of_mem_primeFactors hpMem
  have hpos : 0 < n.factorization p :=
    hpPrime.factorization_pos_of_dvd hn hpN
  have hbase : p ∣ p ^ n.factorization p :=
    dvd_pow_self p (by omega)
  exact hbase.trans hpow

#print axioms eiravel_first_large_base_dvd
end PaperB.M4B
