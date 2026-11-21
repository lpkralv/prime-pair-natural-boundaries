import PrimePairNB.HInf.Fill.every_path_G

/-!
# `every_path_stays_G`

The invariant `pathGood_all` has `γ t` in `σ > 1` at every time. This rests on `boundary_G`, which `pathGood_all` uses at any
time when the path would reach the line, in place of the docstring's route through `no_extension_any_path_G`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- **A continuation of `G` stays in `σ > 1`.** From `no_extension_any_path_G`, using `catG ⊆ HH`. -/
theorem every_path_stays_G (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6)
    {γ : C(unitInterval, ℂ)} (h0 : 2 < (γ 0).re) (hc : ContinuesAlong G γ) (t : unitInterval) : 1 < (γ t).re := by
  obtain ⟨f, hf, hf0⟩ := hc
  obtain ⟨ρ, hρ, hsub, -⟩ := pathGood_all hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 h0 hf hf0 t
  exact hsub (mem_ball_self hρ)

end GoldbachBoundaries.HInf.Fill
