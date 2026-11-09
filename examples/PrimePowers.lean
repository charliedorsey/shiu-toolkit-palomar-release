module

public import Shiu.PrimePowers

public section

/-! Classical-weight prime-power blocks and genuine finite Euler bound. -/
namespace Shiu.ConsumerExamples

example {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (n z : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z) :
    f n =
      f (Shiu.API.primePowerPrefix n z hn hz).small.prod *
      f (Shiu.API.primePowerPrefix n z hn hz).large.prod :=
  Shiu.API.primePowerPrefix_weight hf n z hn hz

example {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    (p N : ℕ) (hp : p.Prime) (hpA : 2 * A ≤ (p : ℝ)) :
    (∑ j ∈ Finset.range N,
      f (p ^ (j + 2)) / (p : ℝ) ^ (j + 2)) ≤
      2 * (A / (p : ℝ)) ^ 2 :=
  Shiu.API.primePowerTail hf p N hp hpA

end Shiu.ConsumerExamples
