import PrimePairNB.HInf.Fill.arc_model_pinch_family

/-! A smooth arc supplies the holomorphic constant of integration. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

lemma arc_model_smooth_base_arc {r₀ q : ℝ} (hr₀ : 0 < r₀) (hq : 0 < q)
    (hqr : q < r₀ / 4) :
    ∃ ξ : ℝ → ℝ, IsArc r₀ (q : ℂ) ξ ∧ Continuous (deriv ξ) := by
  let ξ : ℝ → ℝ := fun h => q / 2 * (1 - (h / r₀) ^ 2)
  have hcd : ContDiff ℝ 1 ξ := by dsimp [ξ]; fun_prop
  have hd : Continuous (deriv ξ) := hcd.continuous_deriv_one
  refine ⟨ξ, ?_, hd⟩
  refine ⟨hcd.continuous.continuousOn,
    ⟨∅, fun h _ _ => (hcd.differentiable (by norm_num)) h⟩, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hd.continuousOn
    exact ⟨L, fun h hh => by simpa only [Real.norm_eq_abs] using hL h (Ioo_subset_Icc_self hh)⟩
  · simp [ξ, ne_of_gt hr₀]
  · intro h hh
    have ha : |h / r₀| ≤ 1 := by
      rw [abs_div, abs_of_pos hr₀, div_le_one₀ hr₀]
      exact abs_le.mpr hh
    have hb : 0 ≤ 1 - (h / r₀) ^ 2 ∧ 1 - (h / r₀) ^ 2 ≤ 1 := by
      constructor
      · nlinarith [sq_abs (h / r₀), abs_nonneg (h / r₀)]
      · nlinarith [sq_nonneg (h / r₀)]
    have hx : |ξ h| ≤ q / 2 := by
      dsimp [ξ]
      rw [abs_of_nonneg (mul_nonneg (half_pos hq).le hb.1)]
      nlinarith [hb.2]
    calc ‖(ξ h : ℂ) + (h : ℂ) * I‖ ≤ ‖(ξ h : ℂ)‖ + ‖(h : ℂ) * I‖ := norm_add_le _ _
      _ = |ξ h| + |h| := by simp
      _ < 3 * r₀ / 2 := by linarith [abs_le.mpr hh]
  · simpa [ξ] using half_pos hq
  · simp only [ofReal_im, ofReal_re, ξ, zero_div, zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one]
    linarith

theorem arc_model_pinch_base {r₀ : ℝ} (hr₀ : 0 < r₀) {f : ℂ → ℂ → ℂ}
    (hf : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2)
      (ball (0 : ℂ) (2 * r₀) ×ˢ ball (0 : ℂ) (2 * r₀)))
    {Φ : ℂ → ℂ → ℂ}
    (hΦ : ∀ ε ∈ ball (0 : ℂ) (r₀ / 4) ∩ slitPlane,
      ∀ μ ∈ ball (0 : ℂ) (2 * r₀), ∀ ξ : ℝ → ℝ, IsArc r₀ ε ξ →
        Φ ε μ = arcInt r₀ ξ (fun t => f t μ * Complex.log t * Complex.log (ε - t))) :
    DifferentiableOn ℂ (fun μ => Φ ((r₀ / 16 : ℝ) : ℂ) μ) (ball 0 (r₀ / 8)) := by
  let q : ℂ := ((r₀ / 16 : ℝ) : ℂ)
  obtain ⟨ξ, hξ, hdξ⟩ := arc_model_smooth_base_arc hr₀
    (by positivity : 0 < r₀ / 16) (by linarith : r₀ / 16 < r₀ / 4)
  have hq : q ∈ ball (0 : ℂ) (r₀ / 4) ∩ slitPlane := by
    constructor
    · rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    · exact ofReal_mem_slitPlane.mpr (by positivity)
  have hm (h : ℝ) (hh : h ∈ Icc (-r₀) r₀) : arcPt ξ h ∈ ball (0 : ℂ) (2 * r₀) :=
    mem_ball_zero_iff.mpr ((hξ.small h hh).trans (by linarith))
  have hcξ := arcPt_continuousOn hξ
  have he (μ : ℂ) (hμ : μ ∈ ball (0 : ℂ) (r₀ / 8)) : μ ∈ ball (0 : ℂ) (2 * r₀) :=
    mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hμ).trans (by linarith))
  have hlog : ContinuousOn (fun h => Complex.log (arcPt ξ h) * Complex.log (q - arcPt ξ h))
      (Icc (-r₀) r₀) :=
    (hcξ.clog (fun h _ => (arcPt_slit hξ h).1)).mul
      ((continuousOn_const.sub hcξ).clog (fun h _ => (arcPt_slit hξ h).2))
  have hw : Continuous (fun h => (((deriv ξ h : ℝ) : ℂ) + I)) := by fun_prop
  have hH : DifferentiableOn ℂ
      (fun μ => arcInt r₀ ξ (fun t => f t μ * Complex.log t * Complex.log (q - t)))
      (ball 0 (r₀ / 8)) := by
    apply DifferentiableOn.const_mul
    apply ThmA.differentiableOn_intervalIntegral_of_continuousOn isOpen_ball
    · rw [uIcc_of_le (show -r₀ ≤ r₀ by linarith)]
      have hc : ContinuousOn (fun p : ℂ × ℝ => f (arcPt ξ p.2) p.1)
          (ball (0 : ℂ) (r₀ / 8) ×ˢ Icc (-r₀) r₀) :=
        hf.continuousOn.comp
          ((hcξ.comp continuousOn_snd (fun _ hp => hp.2)).prodMk continuousOn_fst)
          (fun p hp => ⟨hm p.2 hp.2, he p.1 hp.1⟩)
      change ContinuousOn (fun p : ℂ × ℝ => f (arcPt ξ p.2) p.1 * Complex.log (arcPt ξ p.2) *
        Complex.log (q - arcPt ξ p.2) * (((deriv ξ p.2 : ℝ) : ℂ) + I)) _
      convert (hc.mul (hlog.comp continuousOn_snd (fun _ hp => hp.2))).mul
        (hw.comp continuous_snd).continuousOn using 1
      funext p
      dsimp only [Pi.mul_apply, Function.comp_def]
      ring
    · intro h hh μ hμ
      have hh' : h ∈ Icc (-r₀) r₀ := by
        simpa only [uIcc_of_le (show -r₀ ≤ r₀ by linarith)] using hh
      have hd := (hf.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds
        ⟨hm h hh', he μ hμ⟩)).comp μ
          (show DifferentiableAt ℂ (fun μ : ℂ => (arcPt ξ h, μ)) μ by fun_prop)
      exact (((hd.mul_const _).mul_const _).mul_const _).differentiableWithinAt
  apply hH.congr
  intro μ hμ
  exact hΦ q hq μ (he μ hμ) ξ hξ

end GoldbachBoundaries.HInf.Fill
