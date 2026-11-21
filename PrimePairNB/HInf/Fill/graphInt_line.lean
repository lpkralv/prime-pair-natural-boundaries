import PrimePairNB.HInf.Defs

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- The line as a graph gives PNT+'s vertical integral. -/
theorem graphInt_line (κ c : ℝ) (f : ℂ → ℂ) : graphInt (SlantGraph.line κ c) f = VerticalIntegral' f c := by
  have ha : 0 < 1 + κ ^ 2 := by positivity
  have hp (h : ℝ) : (SlantGraph.line κ c).pt h =
      (c : ℂ) + (((1 + κ ^ 2) * h + κ * c : ℝ) : ℂ) * I := by
    simp only [SlantGraph.pt, SlantGraph.line]
    dsimp [slantDir]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  have hd (h : ℝ) : slantDir κ *
      (((deriv (SlantGraph.line κ c).ξ h : ℝ) : ℂ) + I) =
      ((1 + κ ^ 2 : ℝ) : ℂ) * I := by
    simp only [SlantGraph.line, deriv_const_add]
    dsimp [slantDir]
    push_cast
    ring_nf
    simp [Complex.I_sq]
    ring
  unfold graphInt
  simp_rw [hp, hd]
  rw [integral_mul_const]
  have hc := Measure.integral_comp_mul_left
    (fun y : ℝ => f ((c : ℂ) + ((y + κ * c : ℝ) : ℂ) * I)) (1 + κ ^ 2)
  simp only [abs_of_pos (inv_pos.mpr ha), Complex.real_smul] at hc
  rw [hc, integral_add_right_eq_self (fun y : ℝ => f ((c : ℂ) + (y : ℂ) * I)) (κ * c)]
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
  have hane : ((1 + κ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  push_cast at hane ⊢
  field_simp [hane]

end GoldbachBoundaries.HInf.Fill

