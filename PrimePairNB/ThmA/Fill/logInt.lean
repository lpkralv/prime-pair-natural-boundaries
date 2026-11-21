import PrimePairNB.ThmA.G18_LocalAccess
import PrimePairNB.ThmA.Fill.CCommon

/-!
# `logInt` (logarithmic interior point, continuation across)

Integration by parts over the whole interval (`GroupC.log_IBP`): for `Im δ > 0`,
`∫_{w₁}^{w₂} φ Log(δ+u) = Φ(δ,w₂)Log(δ+w₂) - Φ(δ,w₁)Log(δ+w₁) - ∫ R`, and
`Log(δ+w₁) = Log(-δ-w₁) + iπ` (`Im(δ+w₁) > 0`), where `-δ-w₁` has positive real part on
`ball 0 ρ`. Every term is then holomorphic on the whole ball.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

open GroupC in
/-- **Logarithmic interior point: continuation across** (the access lemma(i),(ii): the bent
segment `𝒮'`; general).

Sketch. Split `∫_{w₁}^{w₂} = ∫_{w₁}^0 + ∫_0^{w₂}`. The second is `-Φ₊(δ)Log δ + hol` by `logEnd`
(`Φ₊(δ) = ∫_{-δ}^0 φ(δ,·)`). In the first substitute `u = -u'`; for `Im δ > 0`,
`Log(δ - u') = Log(u' - δ) + iπ`, and `logEnd` applied to `φ̃(ε,u') = φ(-ε,-u')` at `ε = -δ` gives
`-Φ̃(-δ)Log(-δ) + hol`, with `Φ̃(-δ) = -Φ₊(δ)` and `Log(-δ) = Log δ - iπ`. The `Log δ` terms cancel,
leaving `-iπΦ₊(δ) + hol`, holomorphic on the whole ball. (Or: deform `[w₁,w₂]` into the upper
half-plane near `0` and use `Log(-iz) + iπ/2`.) -/
theorem logInt {φ : ℂ → ℂ → ℂ} {ρ w₁ w₂ : ℝ} (hρ : 0 < ρ) (h₁ : w₁ < -ρ) (h₂ : ρ < w₂)
    {U : Set ℂ} (hU : IsOpen U) (hUc : Convex ℝ U) (hball : ball (0 : ℂ) ρ ⊆ U)
    (hseg : ∀ u ∈ Icc w₁ w₂, (u : ℂ) ∈ U)
    (hφ : DifferentiableOn ℂ (Function.uncurry φ) (ball (0 : ℂ) ρ ×ˢ U)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball 0 ρ) ∧ ∀ δ ∈ ball (0 : ℂ) ρ, 0 < δ.im →
      F δ = ∫ u in w₁..w₂, φ δ u * Complex.log (δ + u) := by
  have hw : w₁ ≤ w₂ := by linarith
  have hseg' : ∀ u ∈ [[w₁, w₂]], (u : ℂ) ∈ U := by
    rw [uIcc_of_le hw]; exact hseg
  have hw₁U : ((w₁ : ℝ) : ℂ) ∈ U := hseg w₁ ⟨le_rfl, hw⟩
  have hw₂U : ((w₂ : ℝ) : ℂ) ∈ U := hseg w₂ ⟨hw, le_rfl⟩
  refine ⟨fun δ => ((w₂ : ℂ) + δ) * segR φ δ w₂ * Complex.log (δ + w₂) -
      ((w₁ : ℂ) + δ) * segR φ δ w₁ * (Complex.log (-δ - w₁) + (Real.pi : ℂ) * I) -
      ∫ u in w₁..w₂, segR φ δ u, ?_, ?_⟩
  · apply DifferentiableOn.analyticOnNhd _ isOpen_ball
    apply DifferentiableOn.sub
    · apply DifferentiableOn.sub
      · apply DifferentiableOn.mul
        · exact (differentiableOn_const _ |>.add differentiableOn_id).mul
            (differentiableOn_segR hU hUc hball hφ hw₂U)
        · refine DifferentiableOn.clog (by fun_prop) fun δ hδ => ?_
          exact Or.inl (re_add_pos hδ h₂)
      · apply DifferentiableOn.mul
        · exact (differentiableOn_const _ |>.add differentiableOn_id).mul
            (differentiableOn_segR hU hUc hball hφ hw₁U)
        · refine DifferentiableOn.add ?_ (differentiableOn_const _)
          refine DifferentiableOn.clog (by fun_prop) fun δ hδ => ?_
          exact Or.inl (re_neg_sub_pos hδ h₁)
    · exact differentiableOn_int_segR hU hUc hball hφ hseg'
  · intro δ hδ him
    have h := log_IBP hU hUc (slice_differentiableOn hφ hδ) (hball (neg_mem_ball_zero hδ))
      hseg' (fun u _ => add_mem_slitPlane_of_im_pos him u)
    have hlog : Complex.log (δ + w₁) = Complex.log (-δ - w₁) + (Real.pi : ℂ) * I := by
      rw [log_eq_log_neg_add (by simpa using him)]
      congr 2; ring
    rw [h, segInt_eq_segR φ δ w₂, segInt_eq_segR φ δ w₁, hlog]
    have : (∫ u in w₁..w₂, segR (fun _ => φ δ) δ u) = ∫ u in w₁..w₂, segR φ δ u := rfl
    rw [this]

end GoldbachBoundaries.ThmA
