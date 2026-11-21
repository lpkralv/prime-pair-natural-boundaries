import PrimePairNB.HInf.Fill.every_path_S

/-!
# `every_path_stays_S`

The invariant `pathGoodS_all` has `γ t` in `σ > 0` at every time.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- **A continuation of `S` stays in `σ > 0`.** -/
theorem every_path_stays_S (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5)
    {γ : C(unitInterval, ℂ)} (h0 : 1 < (γ 0).re) (hc : ContinuesAlong Sser γ) (t : unitInterval) : 0 < (γ t).re := by
  obtain ⟨f, hf, hf0⟩ := hc
  obtain ⟨ρ, hρ, hsub, -⟩ := pathGoodS_all hH hZ1 hZ2 hZ3 hZ4 hZ5 h0 hf hf0 t
  exact hsub (mem_ball_self hρ)

end GoldbachBoundaries.HInf.Fill

