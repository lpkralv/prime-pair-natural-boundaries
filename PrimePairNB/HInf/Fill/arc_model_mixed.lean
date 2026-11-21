import PrimePairNB.HInf.Fill.arcInt_primitive
import Mathlib.Analysis.Complex.Convex

/-! Primitive and polygon deformation for the one-log terms of `arc_model`. -/

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

/-- A primitive on a slit disc, obtained by pulling back to a convex half strip under `exp`.
This is a general analytic lemma; it uses no HInf theorem. -/
theorem exists_primitive_slit_ball {R : ℝ} (hR : 0 < R) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 R ∩ slitPlane)) :
    ∃ Φ : ℂ → ℂ, ∀ z ∈ ball 0 R ∩ slitPlane, HasDerivAt Φ (F z) z := by
  let U : Set ℂ := {w | w.re < Real.log R ∧ -Real.pi < w.im ∧ w.im < Real.pi}
  have hU : IsOpen U :=
    (isOpen_lt continuous_re continuous_const).inter
      ((isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const))
  have hUc : Convex ℝ U := (convex_halfSpace_re_lt _).inter
    ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))
  have hexp (w : ℂ) (hw : w ∈ U) : Complex.exp w ∈ ball 0 R ∩ slitPlane := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_exp, ← Real.exp_log hR]
      exact Real.exp_lt_exp.mpr hw.1
    · have hl : Complex.log (Complex.exp w) = w := Complex.log_exp hw.2.1 hw.2.2.le
      have harg : (Complex.exp w).arg < Real.pi := by
        rw [← log_im, hl]
        exact hw.2.2
      exact mem_slitPlane_iff_arg.mpr ⟨ne_of_lt harg, Complex.exp_ne_zero _⟩
  let G : ℂ → ℂ := fun w => F (Complex.exp w) * Complex.exp w
  have hG : DifferentiableOn ℂ G U := by
    intro w hw
    have hFo := hF.differentiableAt ((isOpen_ball.inter isOpen_slitPlane).mem_nhds (hexp w hw))
    exact ((hFo.comp w (Complex.differentiable_exp w)).mul
      (Complex.differentiable_exp w)).differentiableWithinAt
  let w₀ : ℂ := ((Real.log R - 1 : ℝ) : ℂ)
  have hw₀ : w₀ ∈ U := by
    refine ⟨?_, ?_, ?_⟩ <;> dsimp [w₀] <;> linarith [Real.pi_pos]
  let Ψ : ℂ → ℂ := fun w => ThmA.segInt G w₀ w
  have hΨ (w : ℂ) (hw : w ∈ U) : HasDerivAt Ψ (G w) w :=
    ThmA.GroupC.hasDerivAt_segInt hU hUc hG hw₀ hw
  refine ⟨fun z => Ψ (Complex.log z), ?_⟩
  intro z hz
  have hzne : z ≠ 0 := slitPlane_ne_zero hz.2
  have hlog : Complex.log z ∈ U := by
    refine ⟨?_, neg_pi_lt_log_im _, ?_⟩
    · rw [log_re]
      exact Real.log_lt_log (norm_pos_iff.mpr hzne) (mem_ball_zero_iff.mp hz.1)
    · rw [log_im]
      exact lt_of_le_of_ne (arg_le_pi z) (slitPlane_arg_ne_pi hz.2)
  have hd := (hΨ _ hlog).comp z (Complex.hasDerivAt_log hz.2)
  simpa [G, Complex.exp_log hzne, hzne, Function.comp_def] using hd

/-- FTC on any segment contained in the domain of a primitive. -/
lemma segInt_eq_primitive {U : Set ℂ} {F Φ : ℂ → ℂ}
    (hF : ContinuousOn F U) (hΦ : ∀ z ∈ U, HasDerivAt Φ (F z) z)
    {a b : ℂ} (hm : segment ℝ a b ⊆ U) : ThmA.segInt F a b = Φ b - Φ a := by
  have hmem (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) : a + (τ : ℂ) * (b - a) ∈ U :=
    hm (by
      simpa only [Complex.real_smul] using
        ((convex_segment a b).add_smul_sub_mem (left_mem_segment ℝ a b) (right_mem_segment ℝ a b) hτ))
  have hd : ∀ τ ∈ [[(0 : ℝ), 1]], HasDerivAt (fun τ : ℝ => Φ (a + (τ : ℂ) * (b - a)))
      (F (a + (τ : ℂ) * (b - a)) * (b - a)) τ := by
    intro τ hτ
    have hp : HasDerivAt (fun τ : ℝ => a + (τ : ℂ) * (b - a)) (b - a) τ := by
      simpa using ((((hasDerivAt_id (τ : ℂ)).mul_const (b - a)).const_add a).comp_ofReal)
    exact (hΦ _ (hmem τ (by simpa using hτ))).comp τ hp
  have hi : IntervalIntegrable (fun τ : ℝ => F (a + (τ : ℂ) * (b - a)) * (b - a)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    refine (hF.comp (by fun_prop) ?_).mul continuousOn_const
    intro τ hτ
    exact hmem τ (by simpa using hτ)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_mul_const] at he
  simpa [ThmA.segInt, mul_comm] using he

/-- Deformation of any arc to the fixed east polygon, for a holomorphic integrand on a slit disc. -/
theorem arcInt_eq_east_polygon {r₀ : ℝ} (hr₀ : 0 < r₀) {ε : ℂ} {ξ : ℝ → ℝ}
    (hξ : IsArc r₀ ε ξ) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 (7 * r₀ / 4) ∩ slitPlane)) :
    arcInt r₀ ξ F = (1 / (2 * (Real.pi : ℂ) * I)) *
      (ThmA.segInt F ((-r₀ : ℝ) * I) ((r₀ / 2 : ℝ) : ℂ) +
        ThmA.segInt F ((r₀ / 2 : ℝ) : ℂ) ((r₀ : ℂ) * I)) := by
  obtain ⟨Φ, hΦ⟩ := exists_primitive_slit_ball (by linarith : 0 < 7 * r₀ / 4) hF
  have hends (h : ℝ) (hh : |h| = r₀) : (h : ℂ) * I ∈ ball 0 (7 * r₀ / 4) ∩ slitPlane := by
    constructor
    · rw [mem_ball_zero_iff, norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one, hh]
      linarith
    · rw [mem_slitPlane_iff]
      right
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      intro he
      rw [he, abs_zero] at hh
      linarith
  have hc : ((r₀ / 2 : ℝ) : ℂ) ∈ ball 0 (7 * r₀ / 4) := by
    rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hstar := ((convex_ball (0 : ℂ) (7 * r₀ / 4)).starConvex hc).inter
    (Complex.starConvex_ofReal_slitPlane (show 0 < r₀ / 2 by positivity))
  have ha := hends (-r₀) (by rw [abs_neg, abs_of_pos hr₀])
  have hb := hends r₀ (abs_of_pos hr₀)
  have hseg₁ : segment ℝ ((-r₀ : ℝ) * I) ((r₀ / 2 : ℝ) : ℂ) ⊆
      ball 0 (7 * r₀ / 4) ∩ slitPlane := by
    rw [segment_symm]
    exact hstar.segment_subset ha
  have hseg₂ := hstar.segment_subset hb
  rw [segInt_eq_primitive hF.continuousOn hΦ hseg₁,
    segInt_eq_primitive hF.continuousOn hΦ hseg₂,
    arcInt_eq_primitive hr₀ hξ hF.continuousOn hΦ (fun h hh =>
      ⟨mem_ball_zero_iff.mpr ((hξ.small h hh).trans (by linarith)), (arcPt_slit hξ h).1⟩)]
  ring

/-- Parameter holomorphy along a fixed segment. -/
lemma analyticOn_segInt_param {a b : ℂ} {r : ℝ} {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    {A : ℂ → ℂ → ℂ} (hA : DifferentiableOn ℂ (fun p : ℂ × ℂ => A p.1 p.2) U)
    (hm : ∀ t ∈ segment ℝ a b, ∀ ε ∈ ball (0 : ℂ) r, (t, ε) ∈ U) :
    AnalyticOnNhd ℂ (fun ε => ThmA.segInt (fun t => A t ε) a b) (ball 0 r) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  apply DifferentiableOn.const_mul
  apply ThmA.differentiableOn_intervalIntegral_of_continuousOn isOpen_ball
  · intro p hp
    have ht : a + (p.2 : ℂ) * (b - a) ∈ segment ℝ a b := by
      simpa only [Complex.real_smul] using (convex_segment a b).add_smul_sub_mem
        (left_mem_segment ℝ a b) (right_mem_segment ℝ a b) (by simpa using hp.2)
    exact ((hA.differentiableAt (hU.mem_nhds (hm _ ht _ hp.1))).continuousAt.comp
      (f := fun p : ℂ × ℝ => (a + (p.2 : ℂ) * (b - a), p.1))
      (show ContinuousAt (fun p : ℂ × ℝ => (a + (p.2 : ℂ) * (b - a), p.1)) p by
        fun_prop)).continuousWithinAt
  · intro τ hτ ε hε
    have ht : a + (τ : ℂ) * (b - a) ∈ segment ℝ a b := by
      simpa only [Complex.real_smul] using (convex_segment a b).add_smul_sub_mem
        (left_mem_segment ℝ a b) (right_mem_segment ℝ a b) (by simpa using hτ)
    exact ((hA.differentiableAt (hU.mem_nhds (hm _ ht _ hε))).comp ε
      (show DifferentiableAt ℂ (fun ε : ℂ => (a + (τ : ℂ) * (b - a), ε)) ε by
        fun_prop)).differentiableWithinAt

/-- Both sides of the fixed east polygon stay in the slit disc. -/
lemma east_polygon_subset {r₀ : ℝ} (hr₀ : 0 < r₀) :
    segment ℝ ((-r₀ : ℝ) * I) ((r₀ / 2 : ℝ) : ℂ) ⊆ ball 0 (7 * r₀ / 4) ∩ slitPlane ∧
    segment ℝ ((r₀ / 2 : ℝ) : ℂ) ((r₀ : ℂ) * I) ⊆ ball 0 (7 * r₀ / 4) ∩ slitPlane := by
  have hc : ((r₀ / 2 : ℝ) : ℂ) ∈ ball 0 (7 * r₀ / 4) := by
    rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hs := ((convex_ball (0 : ℂ) (7 * r₀ / 4)).starConvex hc).inter
    (Complex.starConvex_ofReal_slitPlane (show 0 < r₀ / 2 by positivity))
  have he (h : ℝ) (hh : |h| = r₀) : (h : ℂ) * I ∈ ball 0 (7 * r₀ / 4) ∩ slitPlane := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one, hh]
      linarith
    · rw [mem_slitPlane_iff]
      right
      simpa only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
        using (show h ≠ 0 by intro hz; simp [hz] at hh; linarith)
  constructor
  · rw [segment_symm]
    exact hs.segment_subset (he _ (by rw [abs_neg, abs_of_pos hr₀]))
  · exact hs.segment_subset (he _ (abs_of_pos hr₀))

/-- A single `Log t` factor contributes a function holomorphic on the full parameter disc. -/
theorem arc_model_log_left {r₀ : ℝ} (hr₀ : 0 < r₀) {A : ℂ → ℂ → ℂ}
    (hA : DifferentiableOn ℂ (fun p : ℂ × ℂ => A p.1 p.2)
      (ball (0 : ℂ) (7 * r₀ / 4) ×ˢ ball (0 : ℂ) (r₀ / 4))) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball 0 (r₀ / 4)) ∧
      ∀ ε ∈ ball (0 : ℂ) (r₀ / 4), ∀ ξ : ℝ → ℝ, IsArc r₀ ε ξ →
        arcInt r₀ ξ (fun t => A t ε * Complex.log t) = H ε := by
  let U : Set (ℂ × ℂ) := (ball 0 (7 * r₀ / 4) ∩ slitPlane) ×ˢ ball 0 (r₀ / 4)
  have hU : IsOpen U := (isOpen_ball.inter isOpen_slitPlane).prod isOpen_ball
  let B : ℂ → ℂ → ℂ := fun t ε => A t ε * Complex.log t
  have hB : DifferentiableOn ℂ (fun p : ℂ × ℂ => B p.1 p.2) U := by
    intro p hp
    have ha := hA.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨hp.1.1, hp.2⟩)
    exact (ha.mul ((Complex.hasDerivAt_log hp.1.2).differentiableAt.comp p
      (show DifferentiableAt ℂ (fun p : ℂ × ℂ => p.1) p by fun_prop))).differentiableWithinAt
  let a : ℂ := (-r₀ : ℝ) * I
  let b : ℂ := ((r₀ / 2 : ℝ) : ℂ)
  let c : ℂ := (r₀ : ℂ) * I
  obtain ⟨hab, hbc⟩ := east_polygon_subset hr₀
  have hH₁ := analyticOn_segInt_param hU hB (fun t ht ε hε => ⟨hab ht, hε⟩)
  have hH₂ := analyticOn_segInt_param hU hB (fun t ht ε hε => ⟨hbc ht, hε⟩)
  refine ⟨fun ε => (1 / (2 * (Real.pi : ℂ) * I)) *
    (ThmA.segInt (fun t => B t ε) a b + ThmA.segInt (fun t => B t ε) b c), ?_, ?_⟩
  · exact fun ε hε => analyticAt_const.mul ((hH₁ ε hε).add (hH₂ ε hε))
  · intro ε hε ξ hξ
    apply arcInt_eq_east_polygon hr₀ hξ
    intro t ht
    exact ((hB.differentiableAt (hU.mem_nhds ⟨ht, hε⟩)).comp t
      (show DifferentiableAt ℂ (fun t : ℂ => (t, ε)) t by fun_prop)).differentiableWithinAt

/-- The fixed west polygon avoids the moving right cut uniformly on the small parameter disc. -/
lemma west_polygon_slit {r₀ : ℝ} (hr₀ : 0 < r₀) {ε : ℂ} (hε : ‖ε‖ < r₀ / 4) :
    ∀ t ∈ segment ℝ ((-r₀ : ℝ) * I) ((-r₀ / 2 : ℝ) : ℂ) ∪
      segment ℝ ((-r₀ / 2 : ℝ) : ℂ) ((r₀ : ℂ) * I),
      ‖t‖ ≤ r₀ ∧ ε - t ∈ slitPlane := by
  have hre := (abs_re_le_norm ε).trans_lt hε
  have him := (abs_im_le_norm ε).trans_lt hε
  have he (h : ℝ) (hh : |h| = r₀) : (h : ℂ) * I ∈ closedBall (0 : ℂ) r₀ := by
    simpa [mem_closedBall_zero_iff, norm_mul, hh] using le_refl r₀
  have hw : ((-r₀ / 2 : ℝ) : ℂ) ∈ closedBall (0 : ℂ) r₀ := by
    rw [mem_closedBall_zero_iff, norm_real, Real.norm_eq_abs,
      abs_of_neg (show -r₀ / 2 < 0 by linarith)]
    linarith
  have ha := he (-r₀) (by rw [abs_neg, abs_of_pos hr₀])
  have hb := he r₀ (abs_of_pos hr₀)
  intro t ht
  have hnorm : ‖t‖ ≤ r₀ := by
    apply mem_closedBall_zero_iff.mp
    rcases ht with ht | ht
    · exact (convex_closedBall (0 : ℂ) r₀).segment_subset ha hw ht
    · exact (convex_closedBall (0 : ℂ) r₀).segment_subset hw hb ht
  refine ⟨hnorm, ?_⟩
  rw [mem_slitPlane_iff]
  by_cases hz : (ε - t).im = 0
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

/-- The moving logarithm contributes a function holomorphic on the full parameter disc. -/
theorem arc_model_log_right {r₀ : ℝ} (hr₀ : 0 < r₀) {A : ℂ → ℂ → ℂ}
    (hA : DifferentiableOn ℂ (fun p : ℂ × ℂ => A p.1 p.2)
      (ball (0 : ℂ) (2 * r₀) ×ˢ ball (0 : ℂ) (2 * r₀))) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball 0 (r₀ / 4)) ∧
      ∀ ε ∈ ball (0 : ℂ) (r₀ / 4), ∀ ξ : ℝ → ℝ, IsArc r₀ ε ξ →
        arcInt r₀ ξ (fun t => A t ε * Complex.log (ε - t)) = H ε := by
  let U : Set (ℂ × ℂ) := {p | p.1 ∈ ball 0 (7 * r₀ / 4) ∧
    p.2 ∈ ball 0 (r₀ / 4) ∧ p.2 - p.1 ∈ slitPlane}
  have hU : IsOpen U := (isOpen_ball.preimage continuous_fst).inter
    ((isOpen_ball.preimage continuous_snd).inter
      (isOpen_slitPlane.preimage (continuous_snd.sub continuous_fst)))
  let B : ℂ → ℂ → ℂ := fun t ε => A t ε * Complex.log (ε - t)
  have hB : DifferentiableOn ℂ (fun p : ℂ × ℂ => B p.1 p.2) U := by
    intro p hp
    have ht : p.1 ∈ ball 0 (2 * r₀) := by
      rw [mem_ball_zero_iff]
      have := mem_ball_zero_iff.mp hp.1
      linarith
    have he : p.2 ∈ ball 0 (2 * r₀) := by
      rw [mem_ball_zero_iff]
      have := mem_ball_zero_iff.mp hp.2.1
      linarith
    have ha := hA.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨ht, he⟩)
    exact (ha.mul ((Complex.hasDerivAt_log hp.2.2).differentiableAt.comp p
      (show DifferentiableAt ℂ (fun p : ℂ × ℂ => p.2 - p.1) p by fun_prop))).differentiableWithinAt
  let a : ℂ := (-r₀ : ℝ) * I
  let b : ℂ := ((-r₀ / 2 : ℝ) : ℂ)
  let c : ℂ := (r₀ : ℂ) * I
  have hm (t : ℂ) (ht : t ∈ segment ℝ a b ∪ segment ℝ b c)
      (ε : ℂ) (hε : ε ∈ ball 0 (r₀ / 4)) : (t, ε) ∈ U := by
    have h := west_polygon_slit hr₀ (mem_ball_zero_iff.mp hε) t ht
    exact ⟨mem_ball_zero_iff.mpr (h.1.trans_lt (by linarith)), hε, h.2⟩
  have hH₁ := analyticOn_segInt_param hU hB (fun t ht ε hε => hm t (Or.inl ht) ε hε)
  have hH₂ := analyticOn_segInt_param hU hB (fun t ht ε hε => hm t (Or.inr ht) ε hε)
  refine ⟨fun ε => (1 / (2 * (Real.pi : ℂ) * I)) *
    (ThmA.segInt (fun t => B t ε) a b + ThmA.segInt (fun t => B t ε) b c), ?_, ?_⟩
  · exact fun ε hε => analyticAt_const.mul ((hH₁ ε hε).add (hH₂ ε hε))
  · intro ε hε ξ hξ
    have he : ‖ε‖ < r₀ / 4 := mem_ball_zero_iff.mp hε
    let V : Set ℂ := ball 0 (7 * r₀ / 4) ∩ slitPlane
    have hV : IsOpen V := isOpen_ball.inter isOpen_slitPlane
    have hC : DifferentiableOn ℂ (fun u => A (ε - u) ε * Complex.log u) V := by
      intro u hu
      have ht : ε - u ∈ ball (0 : ℂ) (2 * r₀) := by
        rw [mem_ball_zero_iff]
        exact (norm_sub_le ε u).trans_lt (by have := mem_ball_zero_iff.mp hu.1; linarith)
      have he' : ε ∈ ball (0 : ℂ) (2 * r₀) := mem_ball_zero_iff.mpr (by linarith)
      have ha := (hA.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨ht, he'⟩)).comp u
        (show DifferentiableAt ℂ (fun u : ℂ => (ε - u, ε)) u by fun_prop)
      exact (ha.mul (Complex.hasDerivAt_log hu.2).differentiableAt).differentiableWithinAt
    obtain ⟨Φ, hΦ⟩ := exists_primitive_slit_ball (by linarith : 0 < 7 * r₀ / 4) hC
    let Ψ : ℂ → ℂ := fun t => -Φ (ε - t)
    let W : Set ℂ := {t | ε - t ∈ V}
    have hΨ (t : ℂ) (ht : t ∈ W) : HasDerivAt Ψ (B t ε) t := by
      have hd := ((hΦ _ ht).comp t ((hasDerivAt_id t).const_sub ε)).neg
      convert! hd using 1 <;> simp [Ψ, B]
    have hBc : ContinuousOn (fun t => B t ε) W :=
      by
      intro t ht
      have hc := (hC.differentiableAt (hV.mem_nhds ht)).continuousAt.comp
        (show ContinuousAt (fun t : ℂ => ε - t) t by fun_prop)
      simpa [B, Function.comp_def] using hc.continuousWithinAt
    have hmem (h : ℝ) (hh : h ∈ Icc (-r₀) r₀) : arcPt ξ h ∈ W := by
      refine ⟨mem_ball_zero_iff.mpr ?_, (arcPt_slit hξ h).2⟩
      exact (norm_sub_le ε _).trans_lt (by have hs : ‖arcPt ξ h‖ < 3 * r₀ / 2 := hξ.small h hh; linarith)
    have hseg (t : ℂ) (ht : t ∈ segment ℝ a b ∪ segment ℝ b c) : t ∈ W := by
      have hv := west_polygon_slit hr₀ he t ht
      refine ⟨mem_ball_zero_iff.mpr ?_, hv.2⟩
      exact (norm_sub_le ε t).trans_lt (by linarith [hv.1])
    change arcInt r₀ ξ (fun t => B t ε) = (1 / (2 * (Real.pi : ℂ) * I)) *
      (ThmA.segInt (fun t => B t ε) a b + ThmA.segInt (fun t => B t ε) b c)
    rw [arcInt_eq_primitive hr₀ hξ hBc hΨ hmem,
      segInt_eq_primitive hBc hΨ (fun t ht => hseg t (Or.inl ht)),
      segInt_eq_primitive hBc hΨ (fun t ht => hseg t (Or.inr ht))]
    ring

/-- The `Log t · E₂` mixed term in the exact normalization of `arc_model`. -/
theorem arc_model_mixed_left {r₀ : ℝ} (hr₀ : 0 < r₀) {f : ℂ → ℂ → ℂ}
    (hf : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2)
      (ball (0 : ℂ) (2 * r₀) ×ˢ ball (0 : ℂ) (2 * r₀)))
    {E₂ : ℂ → ℂ} (hE₂ : AnalyticOnNhd ℂ E₂ (ball 0 (2 * r₀))) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball 0 (r₀ / 4)) ∧
      ∀ ε ∈ ball (0 : ℂ) (r₀ / 4), ∀ ξ : ℝ → ℝ, IsArc r₀ ε ξ →
        arcInt r₀ ξ (fun t => f t ε * Complex.log t * E₂ (ε - t)) = H ε := by
  let A : ℂ → ℂ → ℂ := fun t ε => f t ε * E₂ (ε - t)
  have hA : DifferentiableOn ℂ (fun p : ℂ × ℂ => A p.1 p.2)
      (ball (0 : ℂ) (7 * r₀ / 4) ×ˢ ball (0 : ℂ) (r₀ / 4)) := by
    intro p hp
    have ht := mem_ball_zero_iff.mp hp.1
    have he := mem_ball_zero_iff.mp hp.2
    have ht' : p.1 ∈ ball (0 : ℂ) (2 * r₀) := mem_ball_zero_iff.mpr (by linarith)
    have he' : p.2 ∈ ball (0 : ℂ) (2 * r₀) := mem_ball_zero_iff.mpr (by linarith)
    have hs : p.2 - p.1 ∈ ball (0 : ℂ) (2 * r₀) :=
      mem_ball_zero_iff.mpr ((norm_sub_le _ _).trans_lt (by linarith))
    exact ((hf.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨ht', he'⟩)).mul
      ((hE₂ _ hs).differentiableAt.comp p
        (show DifferentiableAt ℂ (fun p : ℂ × ℂ => p.2 - p.1) p by fun_prop))).differentiableWithinAt
  obtain ⟨H, hH, heq⟩ := arc_model_log_left hr₀ hA
  refine ⟨H, hH, fun ε hε ξ hξ => ?_⟩
  convert heq ε hε ξ hξ using 2
  funext t
  dsimp [A]
  ring

/-- The `E₁ · Log(ε-t)` mixed term in the exact normalization of `arc_model`. -/
theorem arc_model_mixed_right {r₀ : ℝ} (hr₀ : 0 < r₀) {f : ℂ → ℂ → ℂ}
    (hf : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2)
      (ball (0 : ℂ) (2 * r₀) ×ˢ ball (0 : ℂ) (2 * r₀)))
    {E₁ : ℂ → ℂ} (hE₁ : AnalyticOnNhd ℂ E₁ (ball 0 (2 * r₀))) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball 0 (r₀ / 4)) ∧
      ∀ ε ∈ ball (0 : ℂ) (r₀ / 4), ∀ ξ : ℝ → ℝ, IsArc r₀ ε ξ →
        arcInt r₀ ξ (fun t => f t ε * E₁ t * Complex.log (ε - t)) = H ε := by
  apply arc_model_log_right hr₀
  intro p hp
  exact ((hf.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds hp)).mul
    ((hE₁ p.1 hp.1).differentiableAt.comp p
      (show DifferentiableAt ℂ (fun p : ℂ × ℂ => p.1) p by fun_prop))).differentiableWithinAt

end GoldbachBoundaries.HInf.Fill



