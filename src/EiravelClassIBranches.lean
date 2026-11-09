module

public import ShiuPublic.CorvethClassicalClassISource
public import EiravelLargeBaseLeast

public section

namespace PaperB.M4B

/-- The actual full-prime-power large suffix is sqrt(z)-rough whenever
its first BASE prime is larger than sqrt(z). -/
theorem eiravel_actual_classI_rough_large_base
    (n z p : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z)
    (ts : List ℕ)
    (hfirst : (n.primeFactors.sort (· ≤ ·)).drop
      (classical_primePower_prefix_split n z hn hz).small.length =
      p :: ts)
    (hp : Nat.sqrt z < p) :
    PaperB.M4A.shiuRough
      (classical_primePower_prefix_split n z hn hz).large.prod
      (Nat.sqrt z) := by
  apply (PaperB.M4A.allSmallPrimesAvoid_iff_shiuRough).mp
  intro q hq hsmall hqd
  have hle := eiravel_large_first_base_le_divisors
    n z p hn hz ts hfirst hq hqd
  omega

/-- Empty *actual* prime-power suffix is automatically rough. -/
theorem eiravel_actual_classI_rough_large_empty
    (n z : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z)
    (hlarge : (classical_primePower_prefix_split n z hn hz).large = []) :
    PaperB.M4A.shiuRough
      (classical_primePower_prefix_split n z hn hz).large.prod
      (Nat.sqrt z) := by
  unfold PaperB.M4A.shiuRough
  left
  simp [hlarge]

#print axioms eiravel_actual_classI_rough_large_base
#print axioms eiravel_actual_classI_rough_large_empty
end PaperB.M4B
