import PrimePairNB.ThmA.G18_LocalAccess
import PrimePairNB.ThmA.Fill.CCommon

/-!
# `logEnd` (logarithmic endpoint singularity)

Integration by parts (`GroupC.log_IBP`) with the primitive `u ↦ ∫_{[-ε,u]} φ(ε,·)`:
`∫_0^c φ Log(ε+u) = Φ(ε,c)Log(ε+c) - Φ(ε,0)Log ε - ∫_0^c R(ε,u) du`, where
`Φ(ε,u) = (u+ε)R(ε,u)` and `R = GroupC.segR φ`; `H ε = Φ(ε,c)Log(ε+c) - ∫_0^c R` is holomorphic on
`ball 0 ρ` (`GroupC.differentiableOn_int_segR`).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

open GroupC in
/-- **Logarithmic endpoint singularity** (the integration by parts of the local model; general).

Sketch. `Φ(ε,u) = ∫_{-ε}^u φ(ε,w) dw` (segment in the convex `U`) satisfies `∂ᵤΦ = φ` and
`Φ(ε,u) = (u+ε)·R(ε,u)`, `R(ε,u) = ∫_0^1 φ(ε, -ε + τ(u+ε)) dτ`, jointly continuous and holomorphic
in `ε`. For `ε ∈ slitPlane`, `ε + u ∈ slitPlane` (`u ≥ 0`), `∂ᵤ Log(ε+u) = 1/(ε+u)`; integrate by parts
(`intervalIntegral.integral_mul_deriv_eq_deriv_mul`): `∫_0^c φ Log(ε+u) = Φ(ε,c)Log(ε+c) - Φ(ε,0)Log ε
- ∫_0^c R(ε,u) du`. Put `H ε = Φ(ε,c)Log(ε+c) - ∫_0^c R`, holomorphic on `ball 0 ρ` (`ρ < c` keeps
`ε + c` in `Re > 0`), and note `Φ(ε,0) = segInt (φ ε) (-ε) 0`. -/
theorem logEnd {φ : ℂ → ℂ → ℂ} {ρ c : ℝ} (hρ : 0 < ρ) (hρc : ρ < c) {U : Set ℂ}
    (hU : IsOpen U)
    (hUc : Convex ℝ U) (hball : ball (0 : ℂ) ρ ⊆ U) (hseg : ∀ u ∈ Icc (0 : ℝ) c, (u : ℂ) ∈ U)
    (hφ : DifferentiableOn ℂ (Function.uncurry φ) (ball (0 : ℂ) ρ ×ˢ U)) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball 0 ρ) ∧ ∀ ε ∈ ball (0 : ℂ) ρ, ε ∈ slitPlane →
      ∫ u in (0 : ℝ)..c, φ ε u * Complex.log (ε + u) =
        -(segInt (φ ε) (-ε) 0) * Complex.log ε + H ε := by
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hseg' : ∀ u ∈ [[(0 : ℝ), c]], (u : ℂ) ∈ U := by
    rw [uIcc_of_le hc0]; exact hseg
  have hcU : ((c : ℝ) : ℂ) ∈ U := hseg c ⟨hc0, le_rfl⟩
  refine ⟨fun ε => ((c : ℂ) + ε) * segR φ ε c * Complex.log (ε + c) -
      ∫ u in (0 : ℝ)..c, segR φ ε u, ?_, ?_⟩
  · apply DifferentiableOn.analyticOnNhd _ isOpen_ball
    apply DifferentiableOn.sub
    · apply DifferentiableOn.mul
      · exact (differentiableOn_const _ |>.add differentiableOn_id).mul
          (differentiableOn_segR hU hUc hball hφ hcU)
      · refine DifferentiableOn.clog (by fun_prop) fun ε hε => ?_
        exact Or.inl (re_add_pos hε hρc)
    · exact differentiableOn_int_segR hU hUc hball hφ hseg'
  · intro ε hε hslit
    have h := log_IBP hU hUc (slice_differentiableOn hφ hε) (hball (neg_mem_ball_zero hε))
      hseg' (fun u hu => add_mem_slitPlane_of_nonneg hslit (by
        rw [uIcc_of_le hc0] at hu; exact hu.1))
    rw [h, segInt_eq_segR φ ε c]
    simp only [ofReal_zero, add_zero]
    have : (∫ u in (0 : ℝ)..c, segR (fun _ => φ ε) ε u) = ∫ u in (0 : ℝ)..c, segR φ ε u := rfl
    rw [this]
    ring

end GoldbachBoundaries.ThmA
