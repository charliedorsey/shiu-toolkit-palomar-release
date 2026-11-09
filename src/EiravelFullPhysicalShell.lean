module

public import EiravelClassIVPrefixMembership
public import EiravelShellCeilingTransport
public import EiravelClassIVInnerScaled
public import EiravelPhysicalSuffixShellRough
public import ShiuPublic.CorvethClassicalPrefixCore

public section

namespace PaperB.M4B

/-- Fully physical unrestricted Class IV geometry in the exact shell
consumed by the weighted public overcount. No squarefree restriction. -/
theorem eiravel_classical_classIV_physical_shell_adapter
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (n x y z k a p r : ℕ)
    (hn : n ≠ 0) (hz : 1 ≤ z)
    (hxlo : x - y < n) (hxhi : n ≤ x)
    (hmod : n ≡ a [MOD k])
    (hcop : n.Coprime k)
    (hsmall : Nat.sqrt z ≤
      (classical_primePower_prefix_split n z hn hz).small.prod)
    (hp : p.Prime)
    (hpd : p ∣ (classical_primePower_prefix_split n z hn hz).large.prod)
    (horder : ∀ q : ℕ, q.Prime →
      q ∣ (classical_primePower_prefix_split n z hn hz).small.prod →
      q < p)
    (hfirst :
      ∃ ts : List ℕ,
      (n.primeFactors.sort (· ≤ ·)).drop
        (classical_primePower_prefix_split n z hn hz).small.length =
          p :: ts)
    (hr : 0 < r) (hpr : p ^ r ≤ z)
    (hzpr : z < p ^ (r+1)) :
    let S := classical_primePower_prefix_split n z hn hz
    S.small.prod ∈
      Shiu.classicalClassIVPrefixSet z k (classIVShellUpper z r) ∧
    S.large.prod ∈
      classIVInnerSet x y k a S.small.prod (classIVShellLower z r) ∧
    n = S.small.prod * S.large.prod ∧
    f n = f S.small.prod * f S.large.prod := by
  dsimp
  let S := classical_primePower_prefix_split n z hn hz
  have hsource := corveth_classical_primePower_source_core
    hf n z k hn hz hcop
  obtain ⟨hfac, _, _, _, _, hfmul⟩ := hsource
  have hprefix : S.small.prod ∈
      Shiu.classicalClassIVPrefixSet z k (classIVShellUpper z r) := by
    apply eiravel_classical_prefix_shell_ceiling z k p r S.small.prod hr hpr
    apply eiravel_classical_classIV_prefix_of_divisor_order
      n z k p hn hz hsmall hcop hp
    · exact hpd
    · exact horder
  have hsuffix : PaperB.M4A.shiuRough S.large.prod
      (classIVShellLower z r) := by
    obtain ⟨ts, ht⟩ := hfirst
    exact eiravel_actual_large_suffix_shell_rough
      n z p r hn hz ts ht hp hr hzpr
  have hinner := eiravel_classical_large_mem_classIVInnerSet
    n x y z k a (classIVShellLower z r)
    hn hz hxlo hxhi hmod hsuffix
  exact ⟨hprefix, hinner, hfac, hfmul⟩

#print axioms eiravel_classical_classIV_physical_shell_adapter
end PaperB.M4B
