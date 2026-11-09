module

public import EiravelLargeBaseLeast
public import EiravelSuffixRough
public import EiravelShellLower

public section

namespace PaperB.M4B

theorem eiravel_actual_large_suffix_shell_rough
    (n z p r : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z)
    (ts : List ℕ)
    (hfirst :
      (n.primeFactors.sort (· ≤ ·)).drop
        (classical_primePower_prefix_split n z hn hz).small.length =
          p :: ts)
    (hp : p.Prime)
    (hr : 0 < r)
    (hzp : z < p ^ (r+1)) :
    PaperB.M4A.shiuRough
      (classical_primePower_prefix_split n z hn hz).large.prod
      (classIVShellLower z r) := by
  apply eiravel_large_prod_rough_of_prime_lower n z hn hz
  intro q hq hqd
  have hlower := eiravel_classIV_shell_lower_lt_crossing_base
    z p r hr hp hzp
  have hupper := eiravel_large_first_base_le_divisors
    n z p hn hz ts hfirst hq hqd
  omega

#print axioms eiravel_actual_large_suffix_shell_rough
end PaperB.M4B
