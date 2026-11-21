import PrimePairNB.HInf.Fill.absc_lt_iff_re_lt

/-! Proof of `isSeparating_line`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- The line with `1 < c < Re v - 1` separates.  -/
theorem isSeparating_line (hZ1 : Z1) (κ : ℝ) {v : ℂ} {c : ℝ} (hc1 : 1 < c) (hc2 : c < v.re - 1) :
    IsSeparating v (SlantGraph.line κ c) := by
  have hB : Binf ≤ 1 := M1.Binf_le_Bsup_le_one.1.trans M1.Binf_le_Bsup_le_one.2
  have hξ (h : ℝ) : (SlantGraph.line κ c).ξ h = c + κ * h := rfl
  refine ⟨⟨1, one_pos, fun h => ?_⟩, ⟨?_, ?_⟩, fun a ha => ?_, fun b hb => ?_⟩
  · rw [pt_re, hξ]
    constructor <;> linarith
  · show Binf < c
    linarith
  · show c < v.re - Binf
    linarith
  · have := (M1.poleSetQ_re_bounds ha).2.1
    have r := re_eq_absc κ a
    rw [hξ]
    linarith
  · have hb1 := (M1.poleSetQ_re_bounds hb).2.1
    have r := re_eq_absc κ (v - b)
    have e : (v - b).re = v.re - b.re := by simp
    rw [hξ]
    linarith

end GoldbachBoundaries.HInf.Fill

