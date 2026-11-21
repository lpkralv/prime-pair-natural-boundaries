import PrimePairNB.ThmA.G18_LocalAccess
import PrimePairNB.ThmA.Fill.CCommon

/-!
# `cauchyInt` (Cauchy-kernel interior point, continuation across)

For `Im δ > 0`, `∫_{w₁}^{w₂} f/(δ+u) = ∫ Q(δ,u) du + f(-δ)(Log(δ+w₂) - Log(δ+w₁))`
(`GroupC.cauchy_split`) and `Log(δ+w₁) = Log(-δ-w₁) + iπ`; every term is holomorphic on
`ball 0 ρ`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

open GroupC in
/-- **Cauchy-kernel interior point: continuation across** (the access lemma(ii),(iii), "deforming
the `w`-interval near `w₀` into the complex plane"; general).

Sketch. As `logInt`, from `cauchyEnd` and reflection, or directly:
`∫ f/(δ+u) = ∫ (f(u) - f(-δ))/(δ+u) + f(-δ)(Log(δ+w₂) - L⁺(δ+w₁))` with `L⁺(z) = Log(-z) + iπ` (the
continuation of `Log` from the upper half-plane across `(-∞,0)`); every term is holomorphic for
`|δ| < ρ`. -/
theorem cauchyInt {f : ℂ → ℂ} {ρ w₁ w₂ : ℝ} (hρ : 0 < ρ) (h₁ : w₁ < -ρ) (h₂ : ρ < w₂)
    {U : Set ℂ} (hU : IsOpen U) (hUc : Convex ℝ U) (hball : ball (0 : ℂ) ρ ⊆ U)
    (hseg : ∀ u ∈ Icc w₁ w₂, (u : ℂ) ∈ U) (hf : DifferentiableOn ℂ f U) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball 0 ρ) ∧ ∀ δ ∈ ball (0 : ℂ) ρ, 0 < δ.im →
      F δ = ∫ u in w₁..w₂, f u / (δ + u) := by
  have hw : w₁ ≤ w₂ := by linarith
  have hseg' : ∀ u ∈ [[w₁, w₂]], (u : ℂ) ∈ U := by
    rw [uIcc_of_le hw]; exact hseg
  have hdf : DifferentiableOn ℂ (deriv f) U := ((hf.analyticOnNhd hU).deriv).differentiableOn
  have hφ : DifferentiableOn ℂ (Function.uncurry fun (_ : ℂ) w => deriv f w)
      (ball (0 : ℂ) ρ ×ˢ U) := by
    intro p hp
    exact DifferentiableWithinAt.comp p (hdf p.2 hp.2) differentiableWithinAt_snd
      (fun q hq => hq.2)
  have hfneg : DifferentiableOn ℂ (fun ε => f (-ε)) (ball (0 : ℂ) ρ) :=
    hf.comp (differentiableOn_neg _) fun ε hε => hball (neg_mem_ball_zero hε)
  refine ⟨fun δ => (∫ u in w₁..w₂, segR (fun _ => deriv f) δ u) +
      f (-δ) * (Complex.log (δ + w₂) - (Complex.log (-δ - w₁) + (Real.pi : ℂ) * I)), ?_, ?_⟩
  · apply DifferentiableOn.analyticOnNhd _ isOpen_ball
    apply DifferentiableOn.add
    · exact differentiableOn_int_segR hU hUc hball hφ hseg'
    · refine hfneg.mul (DifferentiableOn.sub ?_ ?_)
      · refine DifferentiableOn.clog (by fun_prop) fun δ hδ => ?_
        exact Or.inl (re_add_pos hδ h₂)
      · refine DifferentiableOn.add ?_ (differentiableOn_const _)
        refine DifferentiableOn.clog (by fun_prop) fun δ hδ => ?_
        exact Or.inl (re_neg_sub_pos hδ h₁)
  · intro δ hδ him
    have h := cauchy_split hU hUc hf (hball (neg_mem_ball_zero hδ)) hseg'
      (fun u _ => add_mem_slitPlane_of_im_pos him u)
    have hlog : Complex.log (δ + w₁) = Complex.log (-δ - w₁) + (Real.pi : ℂ) * I := by
      rw [log_eq_log_neg_add (by simpa using him)]
      congr 2; ring
    rw [h, hlog]

end GoldbachBoundaries.ThmA
