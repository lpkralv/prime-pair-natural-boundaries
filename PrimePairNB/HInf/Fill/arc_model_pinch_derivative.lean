import PrimePairNB.HInf.Fill.arcInt_primitive
import PrimePairNB.HInf.Fill.arc_model_pinch
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! Differentiating the pinch term on a frozen arc. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

set_option maxHeartbeats 1000000

/-- On a neighborhood avoiding the moving logarithm's cut, the arc may be frozen. -/
theorem hasDerivAt_pinch_arc_of_cut {r₀ : ℝ} (hr₀ : 0 < r₀) {ε₀ : ℂ} {ξ : ℝ → ℝ}
    (hξ : IsArc r₀ ε₀ ξ) {A : ℂ → ℂ}
    (hA : ContinuousOn A (ball (0 : ℂ) (2 * r₀)))
    {W : Set ℂ} (hW : IsOpen W) (hε₀ : ε₀ ∈ W)
    (hcut : ∀ ε ∈ W, ∀ h ∈ Icc (-r₀) r₀, ε - arcPt ξ h ∈ slitPlane) :
    HasDerivAt (fun ε => arcInt r₀ ξ (fun t => A t * Complex.log t * Complex.log (ε - t)))
      (arcInt r₀ ξ (fun t => A t * Complex.log t / (ε₀ - t))) ε₀ := by
  have hab : -r₀ ≤ r₀ := by linarith
  let K : Set ℝ := Icc (-r₀) r₀
  let V : ℝ → ℂ := fun h => ((deriv ξ h : ℝ) : ℂ) + I
  let G : ℂ → ℝ → ℂ := fun ε h => A (arcPt ξ h) * Complex.log (arcPt ξ h) * Complex.log (ε - arcPt ξ h)
  let G' : ℂ → ℝ → ℂ := fun ε h => A (arcPt ξ h) * Complex.log (arcPt ξ h) / (ε - arcPt ξ h)
  have hmem (h : ℝ) (hh : h ∈ K) : arcPt ξ h ∈ ball (0 : ℂ) (2 * r₀) :=
    mem_ball_zero_iff.mpr ((hξ.small h hh).trans (by linarith))
  have hAc : ContinuousOn (fun h => A (arcPt ξ h)) K :=
    hA.comp (arcPt_continuousOn hξ) hmem
  have hlogc : ContinuousOn (fun h => Complex.log (arcPt ξ h)) K :=
    (arcPt_continuousOn hξ).clog (fun h _ => (arcPt_slit hξ h).1)
  have hGc (ε : ℂ) (hε : ε ∈ W) : ContinuousOn (G ε) K :=
    (hAc.mul hlogc).mul ((continuousOn_const.sub (arcPt_continuousOn hξ)).clog (hcut ε hε))
  have hG'c : ContinuousOn (fun p : ℂ × ℝ => G' p.1 p.2) (W ×ˢ K) := by
    apply ContinuousOn.div
    · exact (hAc.comp continuous_snd.continuousOn (fun _ hp => hp.2)).mul
        (hlogc.comp continuous_snd.continuousOn (fun _ hp => hp.2))
    · exact continuousOn_fst.sub ((arcPt_continuousOn hξ).comp continuous_snd.continuousOn (fun _ hp => hp.2))
    · intro p hp
      exact slitPlane_ne_zero (hcut p.1 hp.1 p.2 hp.2)
  obtain ⟨R, hR, hRW⟩ := Metric.isOpen_iff.mp hW ε₀ hε₀
  let ρ := R / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hcb : closedBall ε₀ ρ ⊆ W := (closedBall_subset_ball (by dsimp [ρ]; linarith)).trans hRW
  obtain ⟨M, hM⟩ := ((isCompact_closedBall ε₀ ρ).prod isCompact_Icc).exists_bound_of_continuousOn
    (hG'c.mono (Set.prod_mono hcb Subset.rfl))
  obtain ⟨L, hL⟩ := hξ.lip
  have hVm : AEStronglyMeasurable V volume :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (aestronglyMeasurable_deriv ξ volume)).add_const I
  have hmeas (ε : ℂ) (hε : ε ∈ W) :
      AEStronglyMeasurable (fun h => G ε h * V h) (volume.restrict (Ι (-r₀) r₀)) := by
    exact ((hGc ε hε).mono (by rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self)).aestronglyMeasurable
      measurableSet_uIoc |>.mul hVm.restrict
  have hint : IntervalIntegrable (fun h => G ε₀ h * V h) volume (-r₀) r₀ :=
    arc_integrable hr₀ hξ (F := fun t => A t * Complex.log t * Complex.log (ε₀ - t)) (hGc ε₀ hε₀)
  have hmeas' : AEStronglyMeasurable (fun h => G' ε₀ h * V h) (volume.restrict (Ι (-r₀) r₀)) := by
    have hc : ContinuousOn (G' ε₀) K :=
      (hAc.mul hlogc).div (continuousOn_const.sub (arcPt_continuousOn hξ))
        (fun h hh => slitPlane_ne_zero (hcut ε₀ hε₀ h hh))
    exact (hc.mono (by rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self)).aestronglyMeasurable
      measurableSet_uIoc |>.mul hVm.restrict
  have hd := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun ε h => G ε h * V h) (F' := fun ε h => G' ε h * V h)
    (bound := fun _ => max M 0 * (max L 0 + 1)) (ball_mem_nhds ε₀ hρ)
    (Filter.eventually_of_mem (hW.mem_nhds hε₀) hmeas) hint hmeas'
    (by
      filter_upwards [show ∀ᵐ h : ℝ, h ≠ r₀ from ae_iff.mpr (by simp)] with h hh
      intro ht ε hε
      rw [uIoc_of_le hab] at ht
      have hh' : h ∈ Ioo (-r₀) r₀ := ⟨ht.1, lt_of_le_of_ne ht.2 hh⟩
      rw [norm_mul]
      apply mul_le_mul ((hM (ε, h) ⟨ball_subset_closedBall hε, Ioo_subset_Icc_self hh'⟩).trans
        (le_max_left _ _)) ((norm_add_le _ _).trans ?_) (norm_nonneg _) (le_max_right _ _)
      simp only [norm_real, Real.norm_eq_abs, norm_I]
      linarith [hL h hh', le_max_left L 0])
    (intervalIntegrable_const)
    (Eventually.of_forall fun h ht ε hε => by
      have hw : ε ∈ W := hcb (ball_subset_closedBall hε)
      have hh : h ∈ Icc (-r₀) r₀ := by rw [uIoc_of_le hab] at ht; exact Ioc_subset_Icc_self ht
      have hd := hasDerivAt_pinch_log (f := fun t _ => A t) (μ := (0 : ℂ)) (hcut ε hw h hh)
      exact hd.mul_const (V h))
  exact hd.2.const_mul (1 / (2 * (Real.pi : ℂ) * I))

/-- Compactness gives a single neighborhood in which the chosen arc avoids the moving cut. -/
theorem exists_pinch_freeze {r₀ : ℝ} {ε₀ : ℂ} {ξ : ℝ → ℝ} (hξ : IsArc r₀ ε₀ ξ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε ∈ ball ε₀ δ, ∀ h ∈ Icc (-r₀) r₀, ε - arcPt ξ h ∈ slitPlane := by
  let K : Set ℂ := (fun h => ε₀ - arcPt ξ h) '' Icc (-r₀) r₀
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn
    (continuousOn_const.sub (arcPt_continuousOn hξ))
  have hKs : K ⊆ slitPlane := by
    rintro _ ⟨h, hh, rfl⟩
    exact (arcPt_slit hξ h).2
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_thickening_subset_open isOpen_slitPlane hKs
  refine ⟨δ, hδ, fun ε hε h hh => hδK ?_⟩
  rw [mem_thickening_iff]
  refine ⟨ε₀ - arcPt ξ h, ⟨h, hh, rfl⟩, ?_⟩
  simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using (mem_ball.mp hε)

/-- The actual frozen-arc derivative, with the uniform cut neighborhood supplied by compactness. -/
theorem hasDerivAt_pinch_arc {r₀ : ℝ} (hr₀ : 0 < r₀) {ε₀ : ℂ} {ξ : ℝ → ℝ}
    (hξ : IsArc r₀ ε₀ ξ) {A : ℂ → ℂ}
    (hA : ContinuousOn A (ball (0 : ℂ) (2 * r₀))) :
    HasDerivAt (fun ε => arcInt r₀ ξ (fun t => A t * Complex.log t * Complex.log (ε - t)))
      (arcInt r₀ ξ (fun t => A t * Complex.log t / (ε₀ - t))) ε₀ := by
  obtain ⟨δ, hδ, hcut⟩ := exists_pinch_freeze hξ
  exact hasDerivAt_pinch_arc_of_cut hr₀ hξ hA isOpen_ball (mem_ball_self hδ) hcut

end GoldbachBoundaries.HInf.Fill

