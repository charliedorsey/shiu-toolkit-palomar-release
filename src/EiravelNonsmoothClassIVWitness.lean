module

public import EiravelFullPhysicalShell
public import EiravelDivisorOrder
public import EiravelBaseShellEndpoints

public section

namespace PaperB.M4B

/-- The nonsmooth actual prime-power prefix enters a paid Class IV shell.
No squarefree assumptions or surrogate weights. -/
theorem eiravel_nonsmooth_physical_classIV_witness
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (n x y z k a p : ℕ)
    (hn : n ≠ 0) (hz : 1 ≤ z)
    (hnI : n ∈ Finset.Ioc (x-y) x)
    (hna : n ≡ a [MOD k]) (hncop : n.Coprime k)
    (hL2 : 2 ≤ shiuLogLogSmoothThreshold x)
    (hpMem : p ∈ n.primeFactors) (hpsqrt : p ≤ Nat.sqrt z)
    (hfirst : ∃ ts,
      (n.primeFactors.sort (· ≤ ·)).drop
        (classical_primePower_prefix_split n z hn hz).small.length = p :: ts)
    (hpd : p ∣ (classical_primePower_prefix_split n z hn hz).large.prod)
    (hbig : Nat.sqrt z <
      (classical_primePower_prefix_split n z hn hz).small.prod)
    (hnonsmooth : ∃ q : ℕ,
      q.Prime ∧ q ∣ (classical_primePower_prefix_split n z hn hz).small.prod ∧
      shiuLogLogSmoothThreshold x < q) :
    ∃ r ∈ Finset.Icc 2 (shiuClassIVR0 x z),
      let S := classical_primePower_prefix_split n z hn hz
      S.small.prod ∈ Shiu.classicalClassIVPrefixSet z k (classIVShellUpper z r) ∧
      S.large.prod ∈ classIVInnerSet x y k a S.small.prod (classIVShellLower z r) ∧
      n = S.small.prod * S.large.prod ∧
      f n = f S.small.prod * f S.large.prod := by
  classical
  obtain ⟨q, hq, hqd, hqL⟩ := hnonsmooth
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
  have hqp : q < p :=
    eiravel_classical_primePower_prefix_divisor_order n z hn hz hq hp hqd hpd
  have hLp : shiuLogLogSmoothThreshold x < p := hqL.trans hqp
  have hs := eiravel_classical_base_shell_endpoints
    x z p hp hpsqrt hL2 hLp
  change 2 ≤ Nat.log p z ∧
    Nat.log p z ≤ shiuClassIVR0 x z ∧
    p ^ (Nat.log p z) ≤ z ∧
    z < p ^ (Nat.log p z + 1) at hs
  obtain ⟨hr2, hr0, hpr, hzpr⟩ := hs
  have horder : ∀ q : ℕ, q.Prime →
      q ∣ (classical_primePower_prefix_split n z hn hz).small.prod → q < p := by
    intro q hqprime hqdiv
    exact eiravel_classical_primePower_prefix_divisor_order
      n z hn hz hqprime hp hqdiv hpd
  refine ⟨Nat.log p z, Finset.mem_Icc.mpr ⟨hr2, hr0⟩, ?_⟩
  exact eiravel_classical_classIV_physical_shell_adapter
    hf n x y z k a p (Nat.log p z)
      hn hz (Finset.mem_Ioc.mp hnI).1 (Finset.mem_Ioc.mp hnI).2
      hna hncop hbig.le hp hpd horder hfirst (by omega : 0 < Nat.log p z)
      hpr hzpr

#print axioms eiravel_nonsmooth_physical_classIV_witness
end PaperB.M4B
