import PrimePairNB.ThmA.Fill.ECommonLines
import PrimePairNB.ThmA.Fill.ECommonDom

/-!
# `verticalIntegral_Eb_shift`

Shift of the `E_b` part from `Re z = c` to `Re z = b` (no residue). Under RH, any slope.

Route. `E_b` is holomorphic on `Re z > b` (`lines_differentiableAt_Eb`). For `b < b' < c` the lines
`c` and `b'` give the same integral (`dom_verticalIntegral'_eq_of_differentiableOn`; horizontal
integrals vanish by `dom_tendsto_horizontal` against `lines_norm_integrand_le`). Then `b' → b⁺` by
dominated convergence (`dom_tendsto_verticalIntegral'`, dominating function
`C · (1+|y|)^{-3}(1 + |y| + |log|y - Im w_b||)`, pointwise convergence off `y = Im w_b`).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

namespace GroupE

/-- For `|y| ≥ |y₀| + 2`: `(1+|y|)^{-3}(1 + |y| + |log(y - y₀)|) ≤ 3 (1+|y|)^{-1}`. -/
theorem lines_logDom_le {y y₀ : ℝ} (h : |y₀| + 2 ≤ |y|) :
    ((1 + |y|) ^ 3)⁻¹ * (1 + |y| + |Real.log (y - y₀)|) ≤ 3 * (1 + |y|)⁻¹ := by
  have hA : 0 < 1 + |y| := by positivity
  have hu : 2 ≤ |y - y₀| := by
    have := abs_sub_abs_le_abs_sub y y₀
    linarith
  have hlog : |Real.log (y - y₀)| ≤ 2 * |y| := by
    rw [← Real.log_abs, abs_of_nonneg (Real.log_nonneg (by linarith))]
    have h1 := Real.log_le_sub_one_of_pos (show 0 < |y - y₀| by linarith)
    have h2 := abs_sub y y₀
    linarith [abs_nonneg y₀]
  rw [inv_mul_le_iff₀ (by positivity)]
  have : (1 + |y|) ^ 3 * (3 * (1 + |y|)⁻¹) = 3 * (1 + |y|) ^ 2 := by
    field_simp
  rw [this]
  nlinarith [abs_nonneg y]

end GroupE

open GroupE in
/-- **Shift of the `E_b` part** from `Re z = c` to `Re z = b` (no residue). Under RH.

Sketch. `E_b` is holomorphic on `{Re z > b}` (`Eaux_spec`; `Log((z - w_b)/v)` is holomorphic off
`w_b - [0,∞)v`, which lies in `Re ≤ b`). For `b < b' ≤ c` the rectangle theorem
(`RectangleIntegral`, PNT+ `ResidueCalcOnRectangles`, as in `verticalIntegral'_eq_add_of_simplePole`)
with horizontal decay (the decay of `Γ` against `norm_Eaux_le` and `|Log| ≪ log|y|`) gives equality of the lines
`c` and `b'`; then `b' → b⁺` by dominated convergence, the only singularity on `Re z = b` being the
integrable `log|y - Im w_b|` at `w_b`. -/
theorem verticalIntegral_Eb_shift (hRH : RiemannHypothesis) {κ b c t : ℝ}
    (hb : b ∈ Ioo (1 / 2 : ℝ) 1) (hc : 1 < c) (ht : 0 < t) :
    VerticalIntegral' (fun z => Gamma z * Eb κ b z * (t : ℂ) ^ (-z)) c =
      VerticalIntegral' (fun z => Gamma z * Eb κ b z * (t : ℂ) ^ (-z)) b := by
  set f : ℂ → ℂ := fun z => Gamma z * Eb κ b z * (t : ℂ) ^ (-z) with hf
  have hbc : b < c := by linarith [hb.2]
  have hb0 : 1 / 2 < b := hb.1
  obtain ⟨C, hC0, hC⟩ := lines_norm_integrand_le hRH (κ := κ) (c := c) hb0 ht
  set y₀ := (wb κ b).im with hy₀
  -- holomorphy of `f` at points where `E_b` is
  have hfdiff : ∀ z : ℂ, 1 / 2 < z.re → (z - wb κ b) / slantDir κ ∈ slitPlane →
      DifferentiableAt ℂ f z := by
    intro z hz hslit
    exact ((GoldbachBoundaries.TIdentity.differentiableAt_Gamma_of_re_pos (by linarith)).mul
      (lines_differentiableAt_Eb hRH hz hslit)).mul
      (GoldbachBoundaries.TIdentity.differentiableAt_ofReal_cpow_neg ht z)
  -- horizontal bound
  have hK : ∀ y : ℝ, |y₀| + 2 ≤ |y| → ∀ x ∈ Icc b c,
      ‖f (x + y * I)‖ ≤ 3 * C * (1 + |y|)⁻¹ := by
    intro y hy x hx
    have hne : y ≠ y₀ := by
      rintro rfl; linarith
    calc ‖f (x + y * I)‖ ≤ C * (((1 + |y|) ^ 3)⁻¹ * (1 + |y| + |Real.log (y - y₀)|)) :=
          hC x hx y hne
      _ ≤ C * (3 * (1 + |y|)⁻¹) := mul_le_mul_of_nonneg_left (lines_logDom_le hy) hC0
      _ = 3 * C * (1 + |y|)⁻¹ := by ring
  -- step A: the lines `c` and `b'` agree for `b < b' < c`
  have hshift : ∀ b' ∈ Ioo b c, VerticalIntegral' f c = VerticalIntegral' f b' := by
    intro b' hb'
    have hK' : ∀ y : ℝ, |y₀| + 2 ≤ |y| → ∀ x ∈ Icc b' c,
        ‖f (x + y * I)‖ ≤ 3 * C * (1 + |y|)⁻¹ := fun y hy x hx =>
      hK y hy x ⟨hb'.1.le.trans hx.1, hx.2⟩
    refine dom_verticalIntegral'_eq_of_differentiableOn hb'.2 ?_
      (dom_tendsto_horizontal hb'.2.le hK' tendsto_abs_atBot_atTop)
      (dom_tendsto_horizontal hb'.2.le hK' tendsto_abs_atTop_atTop)
      (integrable_Gamma_Eb_line hRH hb hb'.1.le ht)
      (integrable_Gamma_Eb_line hRH hb hbc.le ht)
    intro z hz
    have hzre : b' ≤ z.re := hz.1.1
    exact (hfdiff z (by linarith [hb'.1]) (lines_mem_slitPlane_of_re_gt (by linarith [hb'.1])))
      |>.differentiableWithinAt
  -- step B: `b' → b⁺` by dominated convergence
  have hlim : Tendsto (fun σ => VerticalIntegral' f σ) (𝓝[>] b) (𝓝 (VerticalIntegral' f b)) := by
    refine dom_tendsto_verticalIntegral'
      (D := fun y => C * (((1 + |y|) ^ 3)⁻¹ * (1 + |y| + |Real.log (y - y₀)|)))
      ((dom_integrable_logDom y₀).const_mul C) ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact lines_aestronglyMeasurable hRH (lt_trans hb0 hσ) ht
    · filter_upwards [Ioo_mem_nhdsGT hbc] with σ hσ
      filter_upwards [Measure.ae_ne volume y₀] with y hy
      exact hC σ ⟨hσ.1.le, hσ.2.le⟩ y hy
    · filter_upwards [Measure.ae_ne volume y₀] with y hy
      have hw0 : (b : ℂ) + y * I - wb κ b ≠ 0 := by
        intro h
        have := congrArg Complex.im h
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, Complex.sub_im, Complex.zero_im] at this
        apply hy
        rw [hy₀]
        linarith
      have hwre : 0 ≤ ((b : ℂ) + y * I - wb κ b).re := by
        simp [lines_wb_re]
      have hd : DifferentiableAt ℂ f ((b : ℂ) + y * I) :=
        hfdiff _ (by simpa using hb0) (lines_div_slantDir_mem_slitPlane κ hw0 hwre)
      have hcont : ContinuousAt (fun σ : ℝ => f ((σ : ℂ) + y * I)) b :=
        hd.continuousAt.comp (f := fun σ : ℝ => (σ : ℂ) + y * I)
          (by fun_prop : Continuous fun σ : ℝ => (σ : ℂ) + y * I).continuousAt
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have heq : (fun σ => VerticalIntegral' f σ) =ᶠ[𝓝[>] b] fun _ => VerticalIntegral' f c := by
    filter_upwards [Ioo_mem_nhdsGT hbc] with σ hσ
    exact (hshift σ hσ).symm
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' heq.symm) hlim

end GoldbachBoundaries.ThmA
