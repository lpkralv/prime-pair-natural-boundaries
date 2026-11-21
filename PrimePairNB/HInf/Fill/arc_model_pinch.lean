import PrimePairNB.HInf.Defs

/-! Differential and residue identities for the pinch term. These are local identities;
the contour-residue identity and its parameter-uniform form are still required. -/

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

/-- The integrand after differentiating in the pinch variable with the other parameter frozen. -/
theorem hasDerivAt_pinch_log {f : ℂ → ℂ → ℂ} {t μ ε : ℂ} (hslit : ε - t ∈ slitPlane) :
    HasDerivAt (fun e => f t μ * Complex.log t * Complex.log (e - t))
      (f t μ * Complex.log t / (ε - t)) ε := by
  have hd := (Complex.hasDerivAt_log hslit).comp ε ((hasDerivAt_id ε).sub_const t)
  convert! hd.const_mul (f t μ * Complex.log t) using 1 <;>
    simp [Function.comp_def, div_eq_mul_inv]

/-- The segment counterterm has derivative `f(ε,μ)` in the pinch variable. -/
theorem hasDerivAt_pinch_segment {r₀ : ℝ} (hr₀ : 0 < r₀) {f : ℂ → ℂ → ℂ}
    (hf : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2)
      (ball (0 : ℂ) (2 * r₀) ×ˢ ball (0 : ℂ) (2 * r₀)))
    {ε μ : ℂ} (hε : ε ∈ ball (0 : ℂ) (2 * r₀)) (hμ : μ ∈ ball (0 : ℂ) (2 * r₀)) :
    HasDerivAt (fun e => e * ∫ τ in (0 : ℝ)..1, f ((τ : ℂ) * e) μ) (f ε μ) ε := by
  have hd : DifferentiableOn ℂ (fun t => f t μ) (ball 0 (2 * r₀)) := by
    intro t ht
    exact ((hf.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨ht, hμ⟩)).comp t
      (show DifferentiableAt ℂ (fun t : ℂ => (t, μ)) t by fun_prop)).differentiableWithinAt
  simpa [ThmA.segInt] using ThmA.GroupC.hasDerivAt_segInt isOpen_ball (convex_ball _ _) hd
    (mem_ball_self (by positivity : 0 < 2 * r₀)) hε

/-- The derivative of the logarithmic segment counterterm: the first summand extends through zero. -/
theorem hasDerivAt_pinch_counterterm {r₀ : ℝ} (hr₀ : 0 < r₀) {f : ℂ → ℂ → ℂ}
    (hf : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2)
      (ball (0 : ℂ) (2 * r₀) ×ˢ ball (0 : ℂ) (2 * r₀)))
    {ε μ : ℂ} (hε : ε ∈ ball (0 : ℂ) (2 * r₀)) (hμ : μ ∈ ball (0 : ℂ) (2 * r₀))
    (hslit : ε ∈ slitPlane) :
    HasDerivAt (fun e => Complex.log e * (e * ∫ τ in (0 : ℝ)..1, f ((τ : ℂ) * e) μ))
      ((∫ τ in (0 : ℝ)..1, f ((τ : ℂ) * ε) μ) + Complex.log ε * f ε μ) ε := by
  have hd := (Complex.hasDerivAt_log hslit).mul (hasDerivAt_pinch_segment hr₀ hf hε hμ)
  convert! hd using 1 <;>
    simp [Pi.mul_apply, ← mul_assoc, inv_mul_cancel₀ (slitPlane_ne_zero hslit)]

end GoldbachBoundaries.HInf.Fill
