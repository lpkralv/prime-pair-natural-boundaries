import PrimePairNB.HInf.Fill.germFam_slope
import PrimePairNB.HInf.Fill.Xc_analyticOn
import PrimePairNB.HInf.Fill.finite_inter_pinch
import PrimePairNB.HInf.Fill.local_model

/-!
# `local_form_germFam`

`local_model` (statement in `Local.lean`) at the slope `κ`, and `germFam_slope` to write every member of the family
at that slope, so the `Log` term carries the same `X_x` on every branch.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- **Local form.** Near `x ∈ X`, every member of `𝔊` is `Log_θ(v - x) X_x + holomorphic`, with the same
`X_x` on every branch. `r` depends on `κ` and `x`, not on the germ. -/
theorem local_form_germFam (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {κ : ℝ} (hκ : IsGenericSlope κ) {x : ℂ} (hx : x ∈ Xcat) (hxV : x ∈ Vt top) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ VInf top ∧ ball x r \ rayW κ x ⊆ Om κ top ∧
      ∀ q ∈ ball x r \ rayW κ x, ∀ (C : ℂ) (f : ℂ → ℂ), GermFam k top C q f →
        ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (ball x r) ∧
          f =ᶠ[𝓝 q] fun v => logK κ (v - x) * Xc k x v + h v := by
  obtain ⟨r, hr, hsub, hslit, H, hH, hform⟩ := local_model hZ1 hZ2 hZ3 hK hκ hx hxV
  refine ⟨r, hr, hsub, hslit, fun q hq C f hf => ?_⟩
  obtain ⟨m, hm, hfm⟩ := germFam_slope hZ1 hZ2 hZ3 hK hf (hslit hq)
  refine ⟨fun v => H v + m v + C, fun z hz =>
    ((hH z hz).add (MSpanK_analyticOn hZ1 hK hm z (hsub hz).1)).add analyticAt_const, ?_⟩
  have hnear : ∀ᶠ v in 𝓝 q, v ∈ ball x r \ rayW κ x := by
    filter_upwards [isOpen_ball.mem_nhds hq.1, (isOpen_Om hZ1 κ top).mem_nhds (hslit hq)] with v hv hOm
    exact ⟨hv, fun hray => hOm.2 (mem_iUnion₂.mpr ⟨x, hx.1, hray⟩)⟩
  filter_upwards [hfm, hnear] with v h1 h2
  rw [h1, hform v h2]
  ring

end GoldbachBoundaries.HInf.Fill
