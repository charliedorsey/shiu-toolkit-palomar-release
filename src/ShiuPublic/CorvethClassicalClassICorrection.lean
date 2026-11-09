module

public import ShiuPublic.VaelisClassIVEndpointCorrection

public section

namespace PaperB.M4B

/-- The exact classical Class I Rankin correction at D=1 is uniformly bounded
in z and k, so its exponential is a fixed envelope-dependent scalar. -/
theorem corveth_classical_rankin_one_fixed
    {f : ArithmeticFunction ℝ} {A : ℝ}
    (hf : Shiu.ClassicalEnvelope f A)
    {z k : ℕ}
    (hzlarge : Real.exp 4 ≤ (z : ℝ)) :
    primeRankinCorrection f z k (1 / Real.log (z : ℝ)) ≤
      ((4 * A * Real.log 4) / Real.log 2) * Real.exp 1 := by
  have hzpos : (0 : ℝ) < z := (Real.exp_pos 4).trans_le hzlarge
  have hlog4 : 4 ≤ Real.log (z : ℝ) := by
    rw [← Real.exp_le_exp, Real.exp_log hzpos]
    exact hzlarge
  have hlog : 0 < Real.log (z : ℝ) := by linarith
  have hz2 : 2 ≤ z := by
    have hle : (2 : ℝ) ≤ Real.exp 4 := by
      nlinarith [Real.add_one_le_exp (4 : ℝ)]
    exact_mod_cast hle.trans hzlarge
  have hδpos : 0 < (1 : ℝ) / Real.log (z : ℝ) := by positivity
  have hδle : (1 : ℝ) / Real.log (z : ℝ) ≤ 1 := by
    exact (div_le_iff₀ hlog).mpr (by linarith)
  have hbound := classical_primeRankinCorrection_le_endpoint_rpow
    hf hz2 hδpos hδle (k := k)
  have hpow : (z : ℝ) ^ (1 / Real.log (z : ℝ)) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hzpos]
    congr 1
    field_simp [hlog.ne']
  simpa only [hpow] using hbound

#print axioms corveth_classical_rankin_one_fixed
end PaperB.M4B
