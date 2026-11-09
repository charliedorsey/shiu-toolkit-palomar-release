module

public import Mathlib

public section

namespace PaperB.M4B

/-- Abstract fixed-constant budget: an endpoint AP error is absorbed by
the physical interval gate Y ≥ z. -/
theorem eiravel_exception_absorption_core
    {Y z G L V R E : ℝ}
    (hz : 0 < z) (hY : z ≤ Y)
    (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hV : 0 ≤ V) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hGL : G * L ≤ 1280 * V)
    (hbr : V * (R + E / z) ≤ 44) :
    G * (Y * R + E) * L ≤ 56320 * Y := by
  have hY0 : 0 ≤ Y := hz.le.trans hY
  have hEscale : E ≤ Y * (E / z) := by
    have hez : E * z ≤ E * Y :=
      mul_le_mul_of_nonneg_left hY hE
    calc
      E = (E * z) / z := by field_simp
      _ ≤ (E * Y) / z := div_le_div_of_nonneg_right hez hz.le
      _ = Y * (E / z) := by ring
  have htotal : Y * R + E ≤ Y * (R + E / z) := by
    nlinarith [hEscale]
  have hGLnonneg : 0 ≤ G * L := mul_nonneg hG hL
  have hR0 : 0 ≤ R + E / z :=
    add_nonneg hR (div_nonneg hE hz.le)
  have hYtotal : 0 ≤ Y * (R + E / z) :=
    mul_nonneg hY0 hR0
  calc
    G * (Y * R + E) * L =
        (G * L) * (Y * R + E) := by ring
    _ ≤ (G * L) * (Y * (R + E / z)) :=
      mul_le_mul_of_nonneg_left htotal hGLnonneg
    _ ≤ (1280 * V) * (Y * (R + E / z)) :=
      mul_le_mul_of_nonneg_right hGL hYtotal
    _ = (1280 * Y) * (V * (R + E / z)) := by ring
    _ ≤ (1280 * Y) * 44 :=
      mul_le_mul_of_nonneg_left hbr (by positivity)
    _ = 56320 * Y := by ring

#print axioms eiravel_exception_absorption_core

end PaperB.M4B
