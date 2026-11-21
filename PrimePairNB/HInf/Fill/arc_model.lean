import PrimePairNB.HInf.Fill.arc_model_pinch_complete
import PrimePairNB.HInf.Fill.arc_model_regular

/-! The four-term local arc model. The statement below is copied from `HInf.Local`. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

lemma arc_model_arcInt_add {r₀ : ℝ} (hr₀ : 0 < r₀) {ε : ℂ} {ξ : ℝ → ℝ}
    (hξ : IsArc r₀ ε ξ) {A B : ℂ → ℂ}
    (hA : ContinuousOn (fun h => A (arcPt ξ h)) (Icc (-r₀) r₀))
    (hB : ContinuousOn (fun h => B (arcPt ξ h)) (Icc (-r₀) r₀)) :
    arcInt r₀ ξ (fun t => A t + B t) = arcInt r₀ ξ A + arcInt r₀ ξ B := by
  have hiA := arc_integrable hr₀ hξ hA
  have hiB := arc_integrable hr₀ hξ hB
  simp only [arcPt] at hiA hiB
  unfold arcInt
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add hiA hiB, mul_add]

lemma arc_model_arcInt_const_mul (r₀ : ℝ) (ξ : ℝ → ℝ) (c : ℂ) (A : ℂ → ℂ) :
    arcInt r₀ ξ (fun t => c * A t) = c * arcInt r₀ ξ A := by
  unfold arcInt
  simp only [mul_assoc, intervalIntegral.integral_const_mul]
  ring

theorem arc_model {r₀ : ℝ} (hr₀ : 0 < r₀) {f : ℂ → ℂ → ℂ}
    (hf : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2) (ball (0 : ℂ) (2 * r₀) ×ˢ ball (0 : ℂ) (2 * r₀)))
    {E₁ E₂ : ℂ → ℂ} (hE₁ : AnalyticOnNhd ℂ E₁ (ball 0 (2 * r₀))) (hE₂ : AnalyticOnNhd ℂ E₂ (ball 0 (2 * r₀)))
    (ca cb : ℂ) :
    ∃ r : ℝ, 0 < r ∧ r < r₀ / 4 ∧ ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball 0 r) ∧
      ∀ ε ∈ ball (0 : ℂ) r, ε ∈ slitPlane → ∀ ξ : ℝ → ℝ, IsArc r₀ ε ξ →
        arcInt r₀ ξ (fun t => f t ε * (ca * Complex.log t + E₁ t) * (cb * Complex.log (ε - t) + E₂ (ε - t))) =
          ca * cb * Complex.log ε * (ε * ∫ τ in (0 : ℝ)..1, f ((τ : ℂ) * ε) ε) + H ε := by
  obtain ⟨HP, hHP, hP⟩ := arc_model_pinch_complete hr₀ hf
  obtain ⟨HL, hHL, hL⟩ := arc_model_mixed_left hr₀ hf hE₂
  obtain ⟨HR, hHR, hR⟩ := arc_model_mixed_right hr₀ hf hE₁
  obtain ⟨HB, hHB, hB⟩ := arc_model_regular hr₀ hf hE₁ hE₂
  let H : ℂ → ℂ := fun ε => ca * cb * HP ε + ca * HL ε + cb * HR ε + HB ε
  have he8 (ε : ℂ) (hε : ε ∈ ball (0 : ℂ) (r₀ / 16)) : ε ∈ ball (0 : ℂ) (r₀ / 8) :=
    mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hε).trans (by linarith))
  have he4 (ε : ℂ) (hε : ε ∈ ball (0 : ℂ) (r₀ / 16)) : ε ∈ ball (0 : ℂ) (r₀ / 4) :=
    mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hε).trans (by linarith))
  refine ⟨r₀ / 16, by positivity, by linarith, H, ?_, ?_⟩
  · intro ε hε
    exact (((analyticAt_const.mul (hHP ε (he8 ε hε))).add
      (analyticAt_const.mul (hHL ε (he4 ε hε)))).add
        (analyticAt_const.mul (hHR ε (he4 ε hε)))).add (hHB ε (he4 ε hε))
  · intro ε hε hs ξ hξ
    have he2 : ε ∈ ball (0 : ℂ) (2 * r₀) :=
      mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hε).trans (by linarith))
    have hpt := arcPt_continuousOn hξ
    have htm (h : ℝ) (hh : h ∈ Icc (-r₀) r₀) : arcPt ξ h ∈ ball (0 : ℂ) (2 * r₀) :=
      mem_ball_zero_iff.mpr ((hξ.small h hh).trans (by linarith))
    have hum (h : ℝ) (hh : h ∈ Icc (-r₀) r₀) : ε - arcPt ξ h ∈ ball (0 : ℂ) (2 * r₀) := by
      have hsmall : ‖arcPt ξ h‖ < 3 * r₀ / 2 := hξ.small h hh
      rw [mem_ball_zero_iff]
      exact (norm_sub_le ε _).trans_lt (by linarith [mem_ball_zero_iff.mp hε])
    have hfc : ContinuousOn (fun h => f (arcPt ξ h) ε) (Icc (-r₀) r₀) :=
      hf.continuousOn.comp (f := fun h => (arcPt ξ h, ε)) (hpt.prodMk continuousOn_const)
        (fun h hh => ⟨htm h hh, he2⟩)
    have hlogt := hpt.clog (fun h _ => (arcPt_slit hξ h).1)
    have hlogu := (continuousOn_const.sub hpt).clog (fun h _ => (arcPt_slit hξ h).2)
    have hcE₁ := hE₁.continuousOn.comp hpt htm
    have hcE₂ := hE₂.continuousOn.comp (continuousOn_const.sub hpt) hum
    let P : ℂ → ℂ := fun t => f t ε * Complex.log t * Complex.log (ε - t)
    let L : ℂ → ℂ := fun t => f t ε * Complex.log t * E₂ (ε - t)
    let R : ℂ → ℂ := fun t => f t ε * E₁ t * Complex.log (ε - t)
    let B : ℂ → ℂ := fun t => f t ε * E₁ t * E₂ (ε - t)
    have hcP : ContinuousOn (fun h => P (arcPt ξ h)) (Icc (-r₀) r₀) := (hfc.mul hlogt).mul hlogu
    have hcL : ContinuousOn (fun h => L (arcPt ξ h)) (Icc (-r₀) r₀) := (hfc.mul hlogt).mul hcE₂
    have hcR : ContinuousOn (fun h => R (arcPt ξ h)) (Icc (-r₀) r₀) := (hfc.mul hcE₁).mul hlogu
    have hcB : ContinuousOn (fun h => B (arcPt ξ h)) (Icc (-r₀) r₀) := (hfc.mul hcE₁).mul hcE₂
    have hexpand : (fun t => f t ε * (ca * Complex.log t + E₁ t) *
        (cb * Complex.log (ε - t) + E₂ (ε - t))) =
        (fun t => ((ca * cb) * P t + ca * L t) + cb * R t + B t) := by
      funext t
      dsimp [P, L, R, B]
      ring
    rw [hexpand,
      arc_model_arcInt_add hr₀ hξ (((hcP.const_mul (ca * cb)).add (hcL.const_mul ca)).add (hcR.const_mul cb)) hcB,
      arc_model_arcInt_add hr₀ hξ ((hcP.const_mul (ca * cb)).add (hcL.const_mul ca)) (hcR.const_mul cb),
      arc_model_arcInt_add hr₀ hξ (hcP.const_mul (ca * cb)) (hcL.const_mul ca),
      arc_model_arcInt_const_mul, arc_model_arcInt_const_mul, arc_model_arcInt_const_mul,
      hP ε (he8 ε hε) hs ξ hξ, hL ε (he4 ε hε) ξ hξ,
      hR ε (he4 ε hε) ξ hξ, hB ε (he4 ε hε) ξ hξ]
    dsimp [H]
    ring

end GoldbachBoundaries.HInf.Fill
