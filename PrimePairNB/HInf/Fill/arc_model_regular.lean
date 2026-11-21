import PrimePairNB.HInf.Fill.arcInt_primitive

/-! The `E₁ E₂` term of `arc_model`, including independence of the arc.
Only general, already proved `ThmA` integration lemmas are used. -/

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

/-- A fixed vertical segment has a holomorphic integral in the parameter. -/
lemma analyticOn_arc_segment {r₀ r : ℝ} {F : ℂ → ℂ → ℂ}
    (hc : ContinuousOn (fun p : ℂ × ℝ => F ((p.2 : ℂ) * I) p.1)
      (ball (0 : ℂ) r ×ˢ Icc (-r₀) r₀))
    (hd : ∀ h ∈ Icc (-r₀) r₀, DifferentiableOn ℂ (fun ε => F ((h : ℂ) * I) ε) (ball 0 r))
    (hr₀ : 0 ≤ r₀) :
    AnalyticOnNhd ℂ (fun ε => (1 / (2 * (Real.pi : ℂ) * I)) *
      ∫ h in (-r₀)..r₀, F ((h : ℂ) * I) ε * I) (ball 0 r) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  apply DifferentiableOn.const_mul
  apply ThmA.differentiableOn_intervalIntegral_of_continuousOn isOpen_ball
  · rw [uIcc_of_le (show -r₀ ≤ r₀ by linarith)]
    convert! hc.mul continuousOn_const using 1
  · intro h hh
    rw [uIcc_of_le (show -r₀ ≤ r₀ by linarith)] at hh
    exact (hd h hh).mul_const I

/-- Disc primitives reduce every arc to the fixed vertical segment. -/
lemma arcInt_eq_segment {r₀ : ℝ} (hr₀ : 0 < r₀) {ε : ℂ} {ξ : ℝ → ℝ}
    (hξ : IsArc r₀ ε ξ) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 (7 * r₀ / 4))) :
    arcInt r₀ ξ F = (1 / (2 * (Real.pi : ℂ) * I)) *
      ∫ h in (-r₀)..r₀, F ((h : ℂ) * I) * I := by
  obtain ⟨Φ, hΦ⟩ := hF.isExactOn_ball
  have hm (h : ℝ) (hh : h ∈ Icc (-r₀) r₀) : (h : ℂ) * I ∈ ball 0 (7 * r₀ / 4) := by
    rw [mem_ball_zero_iff, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
    have := abs_le.mpr hh
    linarith
  have he := arcInt_eq_primitive hr₀ hξ hF.continuousOn hΦ (fun h hh => by
    rw [mem_ball_zero_iff]
    exact (hξ.small h hh).trans (by linarith))
  have hdc : ∀ h ∈ [[-r₀, r₀]], HasDerivAt (fun h : ℝ => Φ ((h : ℂ) * I))
      (F ((h : ℂ) * I) * I) h := by
    intro h hh
    rw [uIcc_of_le (show -r₀ ≤ r₀ by linarith)] at hh
    have hp : HasDerivAt (fun h : ℝ => (h : ℂ) * I) I h := by
      simpa using (((hasDerivAt_id (h : ℂ)).mul_const I).comp_ofReal)
    exact (hΦ _ (hm h hh)).comp h hp
  have hic : IntervalIntegrable (fun h : ℝ => F ((h : ℂ) * I) * I) volume (-r₀) r₀ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (show -r₀ ≤ r₀ by linarith)]
    exact (hF.continuousOn.comp (by fun_prop) hm).mul continuousOn_const
  rw [he, intervalIntegral.integral_eq_sub_of_hasDerivAt hdc hic]

/-- The holomorphic product appearing in the regular term. -/
lemma arc_regular_holo {r₀ : ℝ} {f : ℂ → ℂ → ℂ}
    (hf : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2)
      (ball (0 : ℂ) (2 * r₀) ×ˢ ball (0 : ℂ) (2 * r₀)))
    {E₁ E₂ : ℂ → ℂ} (hE₁ : AnalyticOnNhd ℂ E₁ (ball 0 (2 * r₀)))
    (hE₂ : AnalyticOnNhd ℂ E₂ (ball 0 (2 * r₀))) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2 * E₁ p.1 * E₂ (p.2 - p.1))
      {p | p.1 ∈ ball 0 (2 * r₀) ∧ p.2 ∈ ball 0 (2 * r₀) ∧ p.2 - p.1 ∈ ball 0 (2 * r₀)} := by
  intro p hp
  have hf' := hf.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨hp.1, hp.2.1⟩)
  exact ((hf'.mul ((hE₁ p.1 hp.1).differentiableAt.comp p (by fun_prop))).mul
    ((hE₂ _ hp.2.2).differentiableAt.comp p (by fun_prop))).differentiableWithinAt

/-- The `E₁ E₂` term is holomorphic on the whole small disc and independent of the arc. -/
theorem arc_model_regular {r₀ : ℝ} (hr₀ : 0 < r₀) {f : ℂ → ℂ → ℂ}
    (hf : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2)
      (ball (0 : ℂ) (2 * r₀) ×ˢ ball (0 : ℂ) (2 * r₀)))
    {E₁ E₂ : ℂ → ℂ} (hE₁ : AnalyticOnNhd ℂ E₁ (ball 0 (2 * r₀)))
    (hE₂ : AnalyticOnNhd ℂ E₂ (ball 0 (2 * r₀))) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball 0 (r₀ / 4)) ∧
      ∀ ε ∈ ball (0 : ℂ) (r₀ / 4), ∀ ξ : ℝ → ℝ, IsArc r₀ ε ξ →
        arcInt r₀ ξ (fun t => f t ε * E₁ t * E₂ (ε - t)) = H ε := by
  let F : ℂ → ℂ → ℂ := fun t ε => f t ε * E₁ t * E₂ (ε - t)
  let U : Set (ℂ × ℂ) := {p | p.1 ∈ ball 0 (2 * r₀) ∧
    p.2 ∈ ball 0 (2 * r₀) ∧ p.2 - p.1 ∈ ball 0 (2 * r₀)}
  have hU : IsOpen U := isOpen_ball.preimage continuous_fst |>.inter
    ((isOpen_ball.preimage continuous_snd).inter
      (isOpen_ball.preimage (continuous_snd.sub continuous_fst)))
  have hF : DifferentiableOn ℂ (fun p : ℂ × ℂ => F p.1 p.2) U := arc_regular_holo hf hE₁ hE₂
  have hm (t ε : ℂ) (ht : ‖t‖ < 7 * r₀ / 4) (hε : ε ∈ ball 0 (r₀ / 4)) : (t, ε) ∈ U := by
    have he : ‖ε‖ < r₀ / 4 := mem_ball_zero_iff.mp hε
    refine ⟨mem_ball_zero_iff.mpr (by linarith), mem_ball_zero_iff.mpr (by linarith), ?_⟩
    rw [mem_ball_zero_iff]
    exact (norm_sub_le ε t).trans_lt (by linarith)
  refine ⟨fun ε => (1 / (2 * (Real.pi : ℂ) * I)) *
    ∫ h in (-r₀)..r₀, F ((h : ℂ) * I) ε * I, ?_, ?_⟩
  · apply analyticOn_arc_segment (F := F) _ _ hr₀.le
    · intro p hp
      have hn : ‖(p.2 : ℂ) * I‖ < 7 * r₀ / 4 := by
        simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one]
        have := abs_le.mpr hp.2
        linarith
      exact ((hF.differentiableAt (hU.mem_nhds (hm _ _ hn hp.1))).continuousAt.comp
        (f := fun p : ℂ × ℝ => ((p.2 : ℂ) * I, p.1))
        (show ContinuousAt (fun p : ℂ × ℝ => ((p.2 : ℂ) * I, p.1)) p by fun_prop)).continuousWithinAt
    · intro h hh ε hε
      have hn : ‖(h : ℂ) * I‖ < 7 * r₀ / 4 := by
        simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one]
        have := abs_le.mpr hh
        linarith
      exact ((hF.differentiableAt (hU.mem_nhds (hm _ _ hn hε))).comp ε
        (show DifferentiableAt ℂ (fun ε : ℂ => ((h : ℂ) * I, ε)) ε by fun_prop)).differentiableWithinAt
  · intro ε hε ξ hξ
    apply arcInt_eq_segment hr₀ hξ
    intro t ht
    exact ((hF.differentiableAt (hU.mem_nhds (hm t ε (mem_ball_zero_iff.mp ht) hε))).comp t
      (show DifferentiableAt ℂ (fun t : ℂ => (t, ε)) t by fun_prop)).differentiableWithinAt

end GoldbachBoundaries.HInf.Fill
