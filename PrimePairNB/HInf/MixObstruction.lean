import PrimePairNB.HInf.MixGermFamily
import PrimePairNB.HInf.Fill.not_analytic_of_germFam

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.HInf.Fill
namespace GoldbachBoundaries.HInf.MixProof

/-- A nonzero value of the mixed coefficient obstructs continuation across the cut. -/
theorem not_analytic_of_germFam (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hK : IsPinchKernel kerG ⊤ G) {κ : ℝ} (hκ : IsGenericSlope κ)
    {x : ℂ} (hx : x ∈ Xcat) (hxV : x ∈ Vt ⊤) (hX : XcMix x x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ball x r \ rayW κ x ⊆ Om κ ⊤ ∧
      ∀ r' : ℝ, 0 < r' → r' ≤ r → ∀ F : ℂ → ℂ,
      (∀ s ∈ ball x r', s ≠ x → AnalyticAt ℂ F s) →
      ∀ q ∈ ball x r' \ rayW κ x, ∀ C : ℂ, ¬ GermFamMix C q F := by
  obtain ⟨r, hr, hsub, hslit, hform⟩ := local_form_germFam hZ1 hZ2 hZ3 hK hκ hx hxV
  refine ⟨r, hr, hslit, fun r' hr' hr'r F hF q hq C hq' => ?_⟩
  have hr'x : r' ≤ x.re - 1 := hr'r.trans (radius_le_of_ball_subset hr hsub)
  obtain ⟨h, hh, hev⟩ := hform q ⟨ball_subset_ball hr'r hq.1, hq.2⟩ C F hq'
  have hXa : AnalyticOnNhd ℂ (XcMix x) (ball x r') := fun z hz =>
    Xc_analyticOn hZ1 hK hx z (hsub (ball_subset_ball hr'r hz)).1
  have hY : AnalyticOnNhd ℂ (fun s => (s - x) * XcMix x s) (ball x r') :=
    fun z hz => (by fun_prop : AnalyticAt ℂ (fun s : ℂ => s - x) z).mul (hXa z hz)
  have hY' : deriv (fun s => (s - x) * XcMix x s) x ≠ 0 := by
    have hi : DifferentiableAt ℂ (fun s : ℂ => s - x) x := by fun_prop
    rw [deriv_fun_mul hi (hXa x (mem_ball_self hr')).differentiableAt]
    simpa using hX
  refine ThmA.no_analytic_across_log (κ := κ) hr' hr'x
    (X₀ := fun s => (s - x) * XcMix x s)
    (H := fun s => (s - x) * (Complex.log (slantDir κ) * XcMix x s + h s))
    (F := fun s => (s - x) * F s) hY hY' ?_ ?_
    (s₁ := q) (by rw [slitDisc_eq hr'x]; exact hq) ?_
  · intro z hz
    exact (by fun_prop : AnalyticAt ℂ (fun s : ℂ => s - x) z).mul
      ((analyticAt_const.mul (hXa z hz)).add (hh z (ball_subset_ball hr'r hz)))
  · intro z hz hne
    exact (by fun_prop : AnalyticAt ℂ (fun s : ℂ => s - x) z).mul (hF z hz hne)
  · filter_upwards [hev] with v hv
    rw [hv]
    simp only [logK, logAt]
    ring

end GoldbachBoundaries.HInf.MixProof
