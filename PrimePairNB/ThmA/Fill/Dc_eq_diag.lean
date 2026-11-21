import PrimePairNB.ThmA.G18_LocalAccess
import PrimePairNB.ThmA.Fill.FCommon
import PrimePairNB.ThmA.Fill.analyticOn_Dc

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
namespace GoldbachBoundaries.ThmA

/-- **`𝒟` in diagonal coordinates** (the access lemma(ii): `𝒟(s) = v∫_0^{2(1-b)} φ(w)/((s-2)/v + w) dw`).
No RH.

Sketch. Unfold `Dc`, `Yf` to `v² ∫∫_{[0,1-b]²} Γ(1-uv)Γ(1-u'v)/(s - 2 + (u+u')v)` (integrand
continuous since `s ∉ 𝒮 + 𝒮`), change variables `(u, u') ↦ (u, w = u + u')` (Fubini on the square,
`MeasureTheory.integral_prod`, then the triangle split at `w = 1-b`), and use
`v²/(s - 2 + wv) = v/((s-2)/v + w)`. -/
theorem Dc_eq_diag (κ : ℝ) {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) {s : ℂ} (hs : s ∉ segSS κ b) :
    Dc κ b s = slantDir κ * ∫ w in (0 : ℝ)..(2 * (1 - b)), phiD κ b w / ((s - 2) / slantDir κ + w) := by
  let f : ℝ × ℝ → ℂ := fun p =>
    Gamma (1 - (p.1 : ℂ) * slantDir κ) * Gamma (1 - (p.2 : ℂ) * slantDir κ) /
      (s - 2 + ((p.1 + p.2 : ℝ) : ℂ) * slantDir κ)
  have hc : ContinuousOn f (Icc (0 : ℝ) (1-b) ×ˢ Icc (0 : ℝ) (1-b)) := by
    apply ContinuousOn.div
    · exact ((F_gamma_segment_continuous κ hb.1).comp continuousOn_fst (fun _ hp => hp.1)).mul
        ((F_gamma_segment_continuous κ hb.1).comp continuousOn_snd (fun _ hp => hp.2))
    · fun_prop
    · rintro ⟨u,t⟩ ⟨hu,ht⟩ he
      apply hs
      exact ⟨u+t, ⟨by linarith [hu.1,ht.1], by linarith [hu.2,ht.2]⟩,
        by dsimp at he; linear_combination he⟩
  have hiter : Dc κ b s = slantDir κ * slantDir κ *
      ∫ u in (0 : ℝ)..(1-b), ∫ t in (0 : ℝ)..(1-b), f (u,t) := by
    unfold Dc Yf
    simp only [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [f]
    have he : s - 1 + (u : ℂ) * slantDir κ - 1 + (t : ℂ) * slantDir κ =
        s - 2 + ((u+t : ℝ) : ℂ) * slantDir κ := by push_cast; ring
    rw [he]
    ring
  rw [hiter, F_square_diagonal (by linarith [hb.2]) hc]
  have hslice : ∀ w : ℝ,
      (∫ u in (max 0 (w-(1-b)))..(min w (1-b)), f (u,w-u)) =
        phiD κ b w / (s - 2 + (w : ℂ) * slantDir κ) := by
    intro w
    unfold phiD
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp [f]
    rw [add_sub_cancel]
  simp_rw [hslice]
  simp only [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro w _
  have hden : (s - 2) / slantDir κ + (w : ℂ) =
      (s - 2 + (w : ℂ) * slantDir κ) / slantDir κ := by
    field_simp [slantDir_ne_zero κ]
  dsimp only
  rw [hden, div_div_eq_mul_div]
  ring

end GoldbachBoundaries.ThmA
