import PrimePairNB.HInf.Fill.every_path_S

/-!
# `no_extension_any_path_S`

As `no_extension_any_path_G`: the end point is moved, inside the disc of holomorphy of the terminal germ, to a point off
`catS`; `pathGoodS_all` makes the germ admissible there, and `boundary_S` applies.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- **No extension along any path, `S`.** As `no_extension_any_path_G`, from `σ > 1`, at the line `σ = 0`. -/
theorem no_extension_any_path_S (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5)
    {γ : C(unitInterval, ℂ)} (h0 : 1 < (γ 0).re) {g : ℂ → ℂ} (hg : IsTerminalGerm Sser γ g) (y r : ℝ) (hr : 0 < r)
    (h1 : γ 1 ∈ ball ((y : ℂ) * I) r) :
    ¬ GermExtendsMeromorphically g (γ 1) (ball ((y : ℂ) * I) r) := by
  rintro ⟨-, F, hFm, hFg⟩
  obtain ⟨f, hf, hf0, hg1⟩ := hg
  obtain ⟨ρ, hρ, -, -, had⟩ := pathGoodS_all hH hZ1 hZ2 hZ3 hZ4 hZ5 h0 hf hf0 1
  have hFf : ∀ᶠ z in 𝓝[≠] γ 1, F z = f 1 z := hFg.trans (hg1.filter_mono nhdsWithin_le_nhds)
  rw [eventually_nhdsWithin_iff] at hFf
  obtain ⟨ρ₁, hρ₁, hb⟩ := Metric.eventually_nhds_iff_ball.mp hFf
  obtain ⟨ρ₂, hρ₂, hsub⟩ := Metric.isOpen_iff.mp isOpen_ball _ h1
  have hpos : 0 < min ρ (min ρ₁ ρ₂) := lt_min hρ (lt_min hρ₁ hρ₂)
  set V : Set ℂ := ball (γ 1) (min ρ (min ρ₁ ρ₂)) \ {γ 1} with hV
  have hVo : IsOpen V := isOpen_ball.sdiff isClosed_singleton
  have hVne : V.Nonempty := by
    obtain ⟨w, hw, hwc⟩ := (dense_compl_singleton (γ 1)).inter_open_nonempty _ isOpen_ball
      ⟨_, mem_ball_self hpos⟩
    exact ⟨w, hw, hwc⟩
  obtain ⟨w, hw, hwP⟩ := exists_not_catS hVo hVne
  have hw1 : w ∈ ball ((y : ℂ) * I) r :=
    hsub (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hw.1)
  refine boundary_S hH hZ1 hZ2 hZ3 hZ4 hZ5
    (had w (ball_subset_ball (min_le_left _ _) hw.1) hwP) y r hr hw1
    ⟨hw1, F, hFm, ?_⟩
  filter_upwards [nhdsWithin_le_nhds (hVo.mem_nhds hw)] with z hz
  exact hb z (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hz.1) hz.2

end GoldbachBoundaries.HInf.Fill

