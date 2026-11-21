import PrimePairNB.HInf.Fill.arc_model_mixed
import Mathlib.Analysis.Complex.RemovableSingularity

/-! The clockwise pole computation, reduced to primitives of divided differences. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

lemma log_neg_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.log (-z) = Complex.log z - (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simpa [Complex.log_im] using Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz

lemma log_neg_of_im_neg {z : ℂ} (hz : z.im < 0) :
    Complex.log (-z) = Complex.log z + (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simpa [Complex.log_im] using Complex.arg_neg_eq_arg_add_pi_of_im_neg hz

lemma east_polygon_right_slit {r₀ : ℝ} (hr₀ : 0 < r₀) {ε : ℂ} (hε : ‖ε‖ < r₀ / 4) :
    ∀ t ∈ segment ℝ ((-r₀ : ℝ) * I) ((r₀ / 2 : ℝ) : ℂ) ∪
      segment ℝ ((r₀ / 2 : ℝ) : ℂ) ((r₀ : ℂ) * I), t - ε ∈ slitPlane := by
  have hre := (abs_re_le_norm ε).trans_lt hε
  have him := (abs_im_le_norm ε).trans_lt hε
  intro t ht
  rw [mem_slitPlane_iff]
  by_cases hz : (t - ε).im = 0
  · left
    rcases ht with ht | ht
    · rw [segment_eq_image'] at ht
      obtain ⟨τ, hτ, rfl⟩ := ht
      simp only [Complex.real_smul, sub_re, add_re, mul_re, ofReal_re, ofReal_im,
        I_re, I_im, sub_im, add_im, mul_im] at hz ⊢
      nlinarith [abs_lt.mp hre, abs_lt.mp him]
    · rw [segment_eq_image'] at ht
      obtain ⟨τ, hτ, rfl⟩ := ht
      simp only [Complex.real_smul, sub_re, add_re, mul_re, ofReal_re, ofReal_im,
        I_re, I_im, sub_im, add_im, mul_im] at hz ⊢
      nlinarith [abs_lt.mp hre, abs_lt.mp him]
  · exact Or.inr hz

/-- The residue identity needed after differentiating the pinch integral.
The pole has residue `-g ε`, while the curve arc minus east polygon is clockwise. -/
theorem arc_pole_eq_east_polygon {r₀ : ℝ} (hr₀ : 0 < r₀) {ε : ℂ}
    (hε : ‖ε‖ < r₀ / 4) (hslit : ε ∈ slitPlane) {ξ : ℝ → ℝ} (hξ : IsArc r₀ ε ξ)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 (7 * r₀ / 4) ∩ slitPlane)) :
    arcInt r₀ ξ (fun t => g t / (ε - t)) = g ε +
      (1 / (2 * (Real.pi : ℂ) * I)) *
        (ThmA.segInt (fun t => g t / (ε - t)) ((-r₀ : ℝ) * I) ((r₀ / 2 : ℝ) : ℂ) +
          ThmA.segInt (fun t => g t / (ε - t)) ((r₀ / 2 : ℝ) : ℂ) ((r₀ : ℂ) * I)) := by
  let V : Set ℂ := ball 0 (7 * r₀ / 4) ∩ slitPlane
  have hV : IsOpen V := isOpen_ball.inter isOpen_slitPlane
  have heV : ε ∈ V := ⟨mem_ball_zero_iff.mpr (by linarith), hslit⟩
  have hds : DifferentiableOn ℂ (dslope g ε) V :=
    (Complex.differentiableOn_dslope (hV.mem_nhds heV)).mpr hg
  obtain ⟨Ψ, hΨ⟩ := exists_primitive_slit_ball (by linarith : 0 < 7 * r₀ / 4) hds
  let A : Set ℂ := V ∩ {t | ε - t ∈ slitPlane}
  let E : Set ℂ := V ∩ {t | t - ε ∈ slitPlane}
  let PA : ℂ → ℂ := fun t => -Ψ t - g ε * Complex.log (ε - t)
  let PE : ℂ → ℂ := fun t => -Ψ t - g ε * Complex.log (t - ε)
  have hPA (t : ℂ) (ht : t ∈ A) : HasDerivAt PA (g t / (ε - t)) t := by
    have hn : t ≠ ε := by
      intro h
      have := slitPlane_ne_zero ht.2
      simp [h] at this
    have hd := (hΨ t ht.1).neg.sub
      (((Complex.hasDerivAt_log ht.2).comp t ((hasDerivAt_id t).const_sub ε)).const_mul (g ε))
    convert! hd using 1
    rw [dslope_of_ne g hn, slope_def_field]
    field_simp
    ring
  have hPE (t : ℂ) (ht : t ∈ E) : HasDerivAt PE (g t / (ε - t)) t := by
    have hn : t ≠ ε := sub_ne_zero.mp (slitPlane_ne_zero ht.2)
    have hd := (hΨ t ht.1).neg.sub
      (((Complex.hasDerivAt_log ht.2).comp t ((hasDerivAt_id t).sub_const ε)).const_mul (g ε))
    convert! hd using 1
    rw [dslope_of_ne g hn, slope_def_field]
    field_simp
    ring
  have hAc : ContinuousOn (fun t => g t / (ε - t)) A :=
    (hg.continuousOn.mono inter_subset_left).div (by fun_prop) (fun t ht => slitPlane_ne_zero ht.2)
  have hEc : ContinuousOn (fun t => g t / (ε - t)) E :=
    (hg.continuousOn.mono inter_subset_left).div (by fun_prop)
      (fun t ht => sub_ne_zero.mpr (sub_ne_zero.mp (slitPlane_ne_zero ht.2)).symm)
  have hmem (h : ℝ) (hh : h ∈ Icc (-r₀) r₀) : arcPt ξ h ∈ A :=
    ⟨⟨mem_ball_zero_iff.mpr ((hξ.small h hh).trans (by linarith)), (arcPt_slit hξ h).1⟩,
      (arcPt_slit hξ h).2⟩
  obtain ⟨hseg₁, hseg₂⟩ := east_polygon_subset hr₀
  have hE₁ : segment ℝ ((-r₀ : ℝ) * I) ((r₀ / 2 : ℝ) : ℂ) ⊆ E :=
    fun t ht => ⟨hseg₁ ht, east_polygon_right_slit hr₀ hε t (Or.inl ht)⟩
  have hE₂ : segment ℝ ((r₀ / 2 : ℝ) : ℂ) ((r₀ : ℂ) * I) ⊆ E :=
    fun t ht => ⟨hseg₂ ht, east_polygon_right_slit hr₀ hε t (Or.inr ht)⟩
  rw [arcInt_eq_primitive hr₀ hξ hAc hPA hmem,
    segInt_eq_primitive hEc hPE hE₁, segInt_eq_primitive hEc hPE hE₂]
  have hi : |ε.im| < r₀ / 4 := (abs_im_le_norm ε).trans_lt hε
  have ht : 0 < ((r₀ : ℂ) * I - ε).im := by simp; linarith [abs_lt.mp hi]
  have hb : (((-r₀ : ℝ) * I) - ε).im < 0 := by simp; linarith [abs_lt.mp hi]
  have hlogt : Complex.log (ε - (r₀ : ℂ) * I) =
      Complex.log ((r₀ : ℂ) * I - ε) - (Real.pi : ℂ) * I := by
    simpa only [neg_sub] using log_neg_of_im_pos ht
  have hlogb : Complex.log (ε - ((-r₀ : ℝ) * I)) =
      Complex.log (((-r₀ : ℝ) * I) - ε) + (Real.pi : ℂ) * I := by
    simpa only [neg_sub] using log_neg_of_im_neg hb
  dsimp [PA, PE]
  rw [hlogt, hlogb]
  have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

end GoldbachBoundaries.HInf.Fill
