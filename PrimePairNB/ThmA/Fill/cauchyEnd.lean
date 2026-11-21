import PrimePairNB.ThmA.G18_LocalAccess
import PrimePairNB.ThmA.Fill.CCommon

/-!
# `cauchyEnd` (Cauchy-kernel endpoint singularity)

`∫_0^c f(u)/(ε+u) du = ∫_0^c Q(ε,u) du + f(-ε)(Log(ε+c) - Log ε)` (`GroupC.cauchy_split`), with
`Q(ε,u) = ∫_0^1 f'(-ε + τ(u+ε)) dτ = (f(u) - f(-ε))/(u+ε)`, jointly continuous and holomorphic in
`ε` (`GroupC.differentiableOn_int_segR` with `φ(ε,w) = f'(w)`).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

open GroupC in
/-- **Cauchy-kernel endpoint singularity** (the local model, case `α = 2`, the term `𝒟`;
general).

Sketch. `∫_0^c f(u)/(ε+u) du = ∫_0^c (f(u) - f(-ε))/(ε+u) du + f(-ε)(Log(ε+c) - Log ε)`; the
difference quotient is `∫_0^1 f'(-ε + τ(u+ε)) dτ`, jointly continuous and holomorphic in `ε`. -/
theorem cauchyEnd {f : ℂ → ℂ} {ρ c : ℝ} (hρ : 0 < ρ) (hρc : ρ < c) {U : Set ℂ}
    (hU : IsOpen U)
    (hUc : Convex ℝ U) (hball : ball (0 : ℂ) ρ ⊆ U) (hseg : ∀ u ∈ Icc (0 : ℝ) c, (u : ℂ) ∈ U)
    (hf : DifferentiableOn ℂ f U) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball 0 ρ) ∧ ∀ ε ∈ ball (0 : ℂ) ρ, ε ∈ slitPlane →
      ∫ u in (0 : ℝ)..c, f u / (ε + u) = -f (-ε) * Complex.log ε + H ε := by
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hseg' : ∀ u ∈ [[(0 : ℝ), c]], (u : ℂ) ∈ U := by
    rw [uIcc_of_le hc0]; exact hseg
  have hdf : DifferentiableOn ℂ (deriv f) U := ((hf.analyticOnNhd hU).deriv).differentiableOn
  have hφ : DifferentiableOn ℂ (Function.uncurry fun (_ : ℂ) w => deriv f w)
      (ball (0 : ℂ) ρ ×ˢ U) := by
    intro p hp
    exact DifferentiableWithinAt.comp p (hdf p.2 hp.2) differentiableWithinAt_snd
      (fun q hq => hq.2)
  have hfneg : DifferentiableOn ℂ (fun ε => f (-ε)) (ball (0 : ℂ) ρ) :=
    hf.comp (differentiableOn_neg _) fun ε hε => hball (neg_mem_ball_zero hε)
  refine ⟨fun ε => (∫ u in (0 : ℝ)..c, segR (fun _ => deriv f) ε u) +
      f (-ε) * Complex.log (ε + c), ?_, ?_⟩
  · apply DifferentiableOn.analyticOnNhd _ isOpen_ball
    apply DifferentiableOn.add
    · exact differentiableOn_int_segR hU hUc hball hφ hseg'
    · refine hfneg.mul (DifferentiableOn.clog (by fun_prop) fun ε hε => ?_)
      exact Or.inl (re_add_pos hε hρc)
  · intro ε hε hslit
    have h := cauchy_split hU hUc hf (hball (neg_mem_ball_zero hε)) hseg'
      (fun u hu => add_mem_slitPlane_of_nonneg hslit (by
        rw [uIcc_of_le hc0] at hu; exact hu.1))
    rw [h]
    simp only [ofReal_zero, add_zero]
    ring

end GoldbachBoundaries.ThmA
