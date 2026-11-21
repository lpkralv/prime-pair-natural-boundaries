import PrimePairNB.HInf.Fill.arc_model_family
import PrimePairNB.HInf.Fill.exists_arc

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

lemma arc_model_swept_slit {r₀ : ℝ} (hr₀ : 0 < r₀) {ε : ℂ}
    {ξ₀ ξ₁ : ℝ → ℝ} (h₀ : IsArc r₀ ε ξ₀) (h₁ : IsArc r₀ ε ξ₁)
    {h : ℝ} (hh : h ∈ Icc (-r₀) r₀) :
    segment ℝ (arcPt ξ₀ h) (arcPt ξ₁ h) ⊆
      {t : ℂ | t ∈ ball 0 (7 * r₀ / 4) ∧ t ∈ slitPlane ∧ ε - t ∈ slitPlane} := by
  intro t ht
  have hn : t ∈ ball (0 : ℂ) (7 * r₀ / 4) :=
    (convex_ball (0 : ℂ) (7 * r₀ / 4)).segment_subset
      (mem_ball_zero_iff.mpr ((h₀.small h hh).trans (by linarith)))
      (mem_ball_zero_iff.mpr ((h₁.small h hh).trans (by linarith))) ht
  refine ⟨hn, ?_, ?_⟩ <;>
    rw [segment_eq_image'] at ht <;> obtain ⟨τ, hτ, rfl⟩ := ht
  · rw [mem_slitPlane_iff]
    by_cases hz : h = 0
    · left
      simp only [arcPt, Complex.real_smul, add_re, sub_re, mul_re, ofReal_re,
        ofReal_im, mul_im, I_re, I_im, mul_zero, zero_mul, add_zero, sub_self, hz]
      have hc := (convex_Ioi (0 : ℝ)).add_smul_sub_mem h₀.west_of h₁.west_of hτ
      simpa only [smul_eq_mul, mem_Ioi, sub_zero] using hc
    · right
      simpa [arcPt, Complex.real_smul] using hz
  · rw [mem_slitPlane_iff]
    by_cases hz : h = ε.im
    · left
      simp only [arcPt, Complex.real_smul, add_re, sub_re, mul_re, ofReal_re,
        ofReal_im, mul_im, I_re, I_im, mul_zero, zero_mul, add_zero, sub_self, hz]
      have hc := (convex_Iio ε.re).add_smul_sub_mem h₀.east_of h₁.east_of hτ
      dsimp at hc
      simpa only [smul_eq_mul, mem_Iio, sub_pos, sub_zero] using hc
    · right
      simpa [arcPt, Complex.real_smul, sub_ne_zero] using Ne.symm hz

theorem arc_model_pinch_independent {r₀ : ℝ} (hr₀ : 0 < r₀)
    {f : ℂ → ℂ → ℂ}
    (hf : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2)
      (ball (0 : ℂ) (2 * r₀) ×ˢ ball (0 : ℂ) (2 * r₀)))
    {ε μ : ℂ} (hμ : μ ∈ ball (0 : ℂ) (2 * r₀))
    {ξ₀ ξ₁ : ℝ → ℝ} (h₀ : IsArc r₀ ε ξ₀) (h₁ : IsArc r₀ ε ξ₁) :
    arcInt r₀ ξ₀ (fun t => f t μ * Complex.log t * Complex.log (ε - t)) =
      arcInt r₀ ξ₁ (fun t => f t μ * Complex.log t * Complex.log (ε - t)) := by
  let U : Set ℂ := {t | t ∈ ball 0 (7 * r₀ / 4) ∧ t ∈ slitPlane ∧ ε - t ∈ slitPlane}
  have hU : IsOpen U := isOpen_ball.inter
    (isOpen_slitPlane.inter (isOpen_slitPlane.preimage (by fun_prop)))
  apply arc_model_arc_independent hr₀ h₀ h₁ hU _ (fun h hh => arc_model_swept_slit hr₀ h₀ h₁ hh)
  intro t ht
  have ht' : t ∈ ball (0 : ℂ) (2 * r₀) :=
    mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp ht.1).trans (by linarith))
  have hd := (hf.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨ht', hμ⟩)).comp t
    (show DifferentiableAt ℂ (fun t : ℂ => (t, μ)) t by fun_prop)
  exact ((hd.mul (Complex.hasDerivAt_log ht.2.1).differentiableAt).mul
    ((Complex.hasDerivAt_log ht.2.2).differentiableAt.comp t
      (show DifferentiableAt ℂ (fun t : ℂ => ε - t) t by fun_prop))).differentiableWithinAt

/-- The value is chosen once in the pinch variable, with the coefficient parameter free. -/
theorem arc_model_pinch_family {r₀ : ℝ} (hr₀ : 0 < r₀) {f : ℂ → ℂ → ℂ}
    (hf : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2)
      (ball (0 : ℂ) (2 * r₀) ×ˢ ball (0 : ℂ) (2 * r₀))) :
    ∃ Φ : ℂ → ℂ → ℂ, ∀ ε ∈ ball (0 : ℂ) (r₀ / 4) ∩ slitPlane,
      ∀ μ ∈ ball (0 : ℂ) (2 * r₀), ∀ ξ : ℝ → ℝ, IsArc r₀ ε ξ →
        Φ ε μ = arcInt r₀ ξ (fun t => f t μ * Complex.log t * Complex.log (ε - t)) := by
  classical
  let ξ (ε : {e : ℂ // e ∈ ball (0 : ℂ) (r₀ / 4) ∩ slitPlane}) : ℝ → ℝ :=
    Classical.choose (exists_arc hr₀ (mem_ball_zero_iff.mp ε.property.1) ε.property.2)
  have hξ (ε : {e : ℂ // e ∈ ball (0 : ℂ) (r₀ / 4) ∩ slitPlane}) : IsArc r₀ ε.val (ξ ε) :=
    Classical.choose_spec (exists_arc hr₀ (mem_ball_zero_iff.mp ε.property.1) ε.property.2)
  refine ⟨fun ε μ => if he : ε ∈ ball (0 : ℂ) (r₀ / 4) ∩ slitPlane then
    arcInt r₀ (ξ ⟨ε, he⟩) (fun t => f t μ * Complex.log t * Complex.log (ε - t)) else 0, ?_⟩
  intro ε he μ hμ η hη
  dsimp only
  rw [dif_pos he]
  exact arc_model_pinch_independent hr₀ hf hμ (hξ ⟨ε, he⟩) hη

lemma arc_model_isArc_of_cut {r₀ : ℝ} (hr₀ : 0 < r₀) {ε₀ ε : ℂ} {ξ : ℝ → ℝ}
    (hξ : IsArc r₀ ε₀ ξ) (he : ‖ε‖ < r₀ / 4)
    (hc : ∀ h ∈ Icc (-r₀) r₀, ε - arcPt ξ h ∈ slitPlane) : IsArc r₀ ε ξ := by
  refine { hξ with east_of := ?_ }
  have him := (abs_im_le_norm ε).trans_lt he
  have hh : ε.im ∈ Icc (-r₀) r₀ := by constructor <;> linarith [abs_lt.mp him]
  have h := hc ε.im hh
  rw [mem_slitPlane_iff] at h
  simpa [arcPt] using h

/-- The chosen family agrees locally with every frozen arc, so it has the frozen-arc derivative. -/
theorem arc_model_pinch_family_derivative {r₀ : ℝ} (hr₀ : 0 < r₀) {f : ℂ → ℂ → ℂ}
    (hf : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2)
      (ball (0 : ℂ) (2 * r₀) ×ˢ ball (0 : ℂ) (2 * r₀)))
    {Φ : ℂ → ℂ → ℂ}
    (hΦ : ∀ ε ∈ ball (0 : ℂ) (r₀ / 4) ∩ slitPlane,
      ∀ μ ∈ ball (0 : ℂ) (2 * r₀), ∀ ξ : ℝ → ℝ, IsArc r₀ ε ξ →
        Φ ε μ = arcInt r₀ ξ (fun t => f t μ * Complex.log t * Complex.log (ε - t)))
    {ε μ : ℂ} (hε : ε ∈ ball (0 : ℂ) (r₀ / 4) ∩ slitPlane)
    (hμ : μ ∈ ball (0 : ℂ) (2 * r₀)) {ξ : ℝ → ℝ} (hξ : IsArc r₀ ε ξ) :
    HasDerivAt (fun e => Φ e μ)
      (arcInt r₀ ξ (fun t => f t μ * Complex.log t / (ε - t))) ε := by
  have hA : ContinuousOn (fun t => f t μ) (ball (0 : ℂ) (2 * r₀)) := by
    exact hf.continuousOn.comp (f := fun t : ℂ => (t, μ)) (by fun_prop) (fun t ht => ⟨ht, hμ⟩)
  apply (hasDerivAt_pinch_arc hr₀ hξ hA).congr_of_eventuallyEq
  obtain ⟨δ, hδ, hc⟩ := exists_pinch_freeze hξ
  filter_upwards [(isOpen_ball.inter isOpen_slitPlane).mem_nhds hε,
    ball_mem_nhds ε hδ] with e he heδ
  exact hΦ e he μ hμ ξ (arc_model_isArc_of_cut hr₀ hξ (mem_ball_zero_iff.mp he.1) (hc e heδ))

end GoldbachBoundaries.HInf.Fill
