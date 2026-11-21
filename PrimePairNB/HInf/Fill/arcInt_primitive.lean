import PrimePairNB.HInf.Defs
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-! FTC for the piecewise differentiable arcs in `Local`. -/

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

/-- The point parametrized by an arc. -/
def arcPt (ξ : ℝ → ℝ) (h : ℝ) : ℂ := (ξ h : ℂ) + (h : ℂ) * I

lemma arcPt_continuousOn {r₀ : ℝ} {ε : ℂ} {ξ : ℝ → ℝ} (hξ : IsArc r₀ ε ξ) :
    ContinuousOn (arcPt ξ) (Icc (-r₀) r₀) :=
  (Complex.continuous_ofReal.comp_continuousOn hξ.cont).add (by fun_prop)

/-- Both principal logarithms in the local integrand are defined on an arc. -/
lemma arcPt_slit {r₀ : ℝ} {ε : ℂ} {ξ : ℝ → ℝ} (hξ : IsArc r₀ ε ξ) (h : ℝ) :
    arcPt ξ h ∈ slitPlane ∧ ε - arcPt ξ h ∈ slitPlane := by
  constructor
  · rw [Complex.mem_slitPlane_iff]
    by_cases hh : h = 0
    · left; simpa [arcPt, hh] using hξ.west_of
    · right; simpa [arcPt] using hh
  · rw [Complex.mem_slitPlane_iff]
    by_cases hh : h = ε.im
    · left; simp only [arcPt, sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, zero_mul, sub_self, add_zero]
      rw [hh]
      linarith [hξ.east_of]
    · right; simpa [arcPt, sub_ne_zero] using Ne.symm hh

/-- The bounded derivative in `IsArc` makes every continuous arc integrand integrable. -/
lemma arc_integrable {r₀ : ℝ} (hr₀ : 0 < r₀) {ε : ℂ} {ξ : ℝ → ℝ}
    (hξ : IsArc r₀ ε ξ) {F : ℂ → ℂ}
    (hF : ContinuousOn (fun h => F (arcPt ξ h)) (Icc (-r₀) r₀)) :
    IntervalIntegrable (fun h => F (arcPt ξ h) * (((deriv ξ h : ℝ) : ℂ) + I)) volume (-r₀) r₀ := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  obtain ⟨L, hL⟩ := hξ.lip
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)]
  apply IntegrableOn.of_bound (measure_Ioo_lt_top)
    ((hF.mono Ioo_subset_Icc_self).aestronglyMeasurable (by measurability) |>.mul
      (((Complex.continuous_ofReal.comp_aestronglyMeasurable
        (aestronglyMeasurable_deriv ξ volume)).add_const I).restrict)) (max B 0 * (max L 0 + 1))
  apply ae_restrict_of_forall_mem measurableSet_Ioo
  intro h hh
  change ‖F (arcPt ξ h) * (((deriv ξ h : ℝ) : ℂ) + I)‖ ≤ _
  rw [norm_mul]
  apply mul_le_mul ((hB h (Ioo_subset_Icc_self hh)).trans (le_max_left _ _))
    ((norm_add_le _ _).trans ?_) (norm_nonneg _) (le_max_right _ _)
  simp only [norm_real, Real.norm_eq_abs, norm_I]
  linarith [hL h hh, le_max_left L 0]

/-- A primitive evaluates an arc using its two fixed endpoints. -/
theorem arcInt_eq_primitive {r₀ : ℝ} (hr₀ : 0 < r₀) {ε : ℂ} {ξ : ℝ → ℝ}
    (hξ : IsArc r₀ ε ξ) {U : Set ℂ} {F Φ : ℂ → ℂ}
    (hF : ContinuousOn F U) (hΦ : ∀ z ∈ U, HasDerivAt Φ (F z) z)
    (hmem : ∀ h ∈ Icc (-r₀) r₀, arcPt ξ h ∈ U) :
    arcInt r₀ ξ F = (1 / (2 * (Real.pi : ℂ) * I)) *
      (Φ ((r₀ : ℂ) * I) - Φ ((-r₀ : ℝ) * I)) := by
  obtain ⟨S, hS⟩ := hξ.brk
  have hcont : ContinuousOn (fun h => Φ (arcPt ξ h)) (Icc (-r₀) r₀) :=
    (show ContinuousOn Φ U from fun z hz => (hΦ z hz).continuousAt.continuousWithinAt).comp
      (arcPt_continuousOn hξ) hmem
  have hi := arc_integrable hr₀ hξ (hF.comp (arcPt_continuousOn hξ) hmem)
  have he := integral_eq_of_hasDerivAt_off_countable
    (fun h => Φ (arcPt ξ h)) (fun h => F (arcPt ξ h) * (((deriv ξ h : ℝ) : ℂ) + I))
    S.finite_toSet.countable (by simpa [uIcc_of_le (show -r₀ ≤ r₀ by linarith)] using hcont)
    (by
      intro h hh
      have hh' : h ∈ Ioo (-r₀) r₀ := by
        have hab : -r₀ ≤ r₀ := by linarith
        simpa only [min_eq_left hab, max_eq_right hab] using hh.1
      have hd := hS h hh' hh.2
      have hp : HasDerivAt (arcPt ξ) (((deriv ξ h : ℝ) : ℂ) + I) h := by
        have h1 := hd.hasDerivAt.ofReal_comp
        have h2 := ((hasDerivAt_id (h : ℂ)).mul_const I).comp_ofReal
        convert! h1.fun_add h2 using 1 <;> simp [arcPt]
      exact (hΦ _ (hmem h (Ioo_subset_Icc_self hh'))).comp h hp) hi
  unfold arcInt
  rw [show (fun h => F ((ξ h : ℂ) + (h : ℂ) * I) * (((deriv ξ h : ℝ) : ℂ) + I)) =
      (fun h => F (arcPt ξ h) * (((deriv ξ h : ℝ) : ℂ) + I)) from rfl, he]
  simp only [arcPt, hξ.ends.1, hξ.ends.2, ofReal_zero, zero_add]

end GoldbachBoundaries.HInf.Fill
