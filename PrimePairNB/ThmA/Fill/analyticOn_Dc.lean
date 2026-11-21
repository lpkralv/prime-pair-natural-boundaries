import PrimePairNB.ThmA.G15_Kernel
import PrimePairNB.ThmA.Fill.differentiableOn_intervalIntegral_of_continuousOn

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

lemma F_gamma_differentiableAt {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro n hn
  have := congrArg Complex.re hn
  simp only [neg_re, natCast_re] at this
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

lemma F_isCompact_Sseg (κ b : ℝ) : IsCompact (Sseg κ b) := by
  have he : Sseg κ b = (fun u : ℝ => (1 : ℂ) - (u : ℂ) * slantDir κ) ''
      Icc (0 : ℝ) (1 - b) := by
    ext z
    simp only [Sseg, mem_ofPred_eq, mem_image]
    constructor <;> rintro ⟨u, hu, he⟩ <;> exact ⟨u, hu, he.symm⟩
  rw [he]
  exact isCompact_Icc.image (by fun_prop)

lemma F_isCompact_segSS (κ b : ℝ) : IsCompact (segSS κ b) := by
  have he : segSS κ b = (fun u : ℝ => (2 : ℂ) - (u : ℂ) * slantDir κ) ''
      Icc (0 : ℝ) (2 * (1 - b)) := by
    ext z
    simp only [segSS, mem_ofPred_eq, mem_image]
    constructor <;> rintro ⟨u, hu, he⟩ <;> exact ⟨u, hu, he.symm⟩
  rw [he]
  exact isCompact_Icc.image (by fun_prop)

lemma F_gamma_segment_continuous (κ : ℝ) {b : ℝ} (hb : 0 < b) :
    ContinuousOn (fun u : ℝ => Gamma (1 - (u : ℂ) * slantDir κ))
      (Icc (0 : ℝ) (1 - b)) := by
  intro u hu
  have hz : 0 < (1 - (u : ℂ) * slantDir κ).re := by
    simp only [sub_re, one_re, mul_re, ofReal_re, slantDir, add_re,
      mul_re, I_re, ofReal_im, zero_mul, sub_zero, zero_add, mul_im,
      I_im, add_im, one_im, zero_mul, add_zero]
    linarith [hu.2]
  exact (F_gamma_differentiableAt hz).continuousAt.comp_continuousWithinAt
    (f := fun u : ℝ => 1 - (u : ℂ) * slantDir κ) (by fun_prop)

lemma F_Yf_analytic (κ : ℝ) {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    AnalyticOnNhd ℂ (Yf κ b) (Sseg κ b)ᶜ := by
  have hU : IsOpen (Sseg κ b)ᶜ := (F_isCompact_Sseg κ b).isClosed.isOpen_compl
  have hI : [[(0 : ℝ), 1 - b]] = Icc (0 : ℝ) (1 - b) := uIcc_of_le (by linarith [hb.2])
  have hn : ∀ p ∈ (Sseg κ b)ᶜ ×ˢ Icc (0 : ℝ) (1 - b),
      p.1 - 1 + (p.2 : ℂ) * slantDir κ ≠ 0 := by
    rintro ⟨z, u⟩ ⟨hz, hu⟩ he
    exact hz ⟨u, hu, by linear_combination he⟩
  have hc : ContinuousOn (fun p : ℂ × ℝ =>
      Gamma (1 - (p.2 : ℂ) * slantDir κ) /
        (p.1 - 1 + (p.2 : ℂ) * slantDir κ))
      ((Sseg κ b)ᶜ ×ˢ [[(0 : ℝ), 1 - b]]) := by
    rw [hI]
    apply ContinuousOn.div
    · exact (F_gamma_segment_continuous κ hb.1).comp continuousOn_snd (fun _ hp => hp.2)
    · fun_prop
    · exact hn
  have hd := differentiableOn_intervalIntegral_of_continuousOn
    (f := fun z u => Gamma (1 - (u : ℂ) * slantDir κ) / (z - 1 + (u : ℂ) * slantDir κ)) hU hc (by
    intro u hu z hz
    apply DifferentiableWithinAt.div (differentiableWithinAt_const _)
    · fun_prop
    · exact hn (z, u) ⟨hz, hI ▸ hu⟩)
  exact (hd.const_mul (slantDir κ)).analyticOnNhd hU

/-- **Holomorphy of `𝒟` off `𝒮 + 𝒮`** (the principal-sheet proposition, "`𝒟`"). No RH.

Sketch. `Dc(s) = v² ∫∫ Γ(1-uv)Γ(1-u'v)/(s - 2 + (u+u')v)`; for `s ∉ 𝒮 + 𝒮` the denominator is
non-zero on the compact square, uniformly near `s`; `Re(1 - uv) ≥ b > 0`. `differentiableOn_intervalIntegral_of_continuousOn` twice (inner
integral `Yf(s - 1 + uv)` jointly continuous). -/
theorem analyticOn_Dc (κ : ℝ) {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    AnalyticOnNhd ℂ (Dc κ b) (segSS κ b)ᶜ := by
  have hU : IsOpen (segSS κ b)ᶜ := (F_isCompact_segSS κ b).isClosed.isOpen_compl
  have hI : [[(0 : ℝ), 1 - b]] = Icc (0 : ℝ) (1 - b) := uIcc_of_le (by linarith [hb.2])
  have hm : ∀ p ∈ (segSS κ b)ᶜ ×ˢ Icc (0 : ℝ) (1 - b),
      p.1 - 1 + (p.2 : ℂ) * slantDir κ ∈ (Sseg κ b)ᶜ := by
    rintro ⟨s, u⟩ ⟨hs, hu⟩ ⟨u', hu', he⟩
    apply hs
    refine ⟨u + u', ⟨by linarith [hu.1, hu'.1], by linarith [hu.2, hu'.2]⟩, ?_⟩
    push_cast
    linear_combination he
  have hc : ContinuousOn (fun p : ℂ × ℝ =>
      Gamma (1 - (p.2 : ℂ) * slantDir κ) *
        Yf κ b (p.1 - 1 + (p.2 : ℂ) * slantDir κ))
      ((segSS κ b)ᶜ ×ˢ [[(0 : ℝ), 1 - b]]) := by
    rw [hI]
    apply ContinuousOn.mul
    · exact (F_gamma_segment_continuous κ hb.1).comp continuousOn_snd (fun _ hp => hp.2)
    · exact (F_Yf_analytic κ hb).continuousOn.comp (by fun_prop) hm
  have hd := differentiableOn_intervalIntegral_of_continuousOn
    (f := fun s u => Gamma (1 - (u : ℂ) * slantDir κ) * Yf κ b (s - 1 + (u : ℂ) * slantDir κ)) hU hc (by
    intro u hu s hs
    apply DifferentiableWithinAt.const_mul
    apply ((F_Yf_analytic κ hb) _ (hm (s, u) ⟨hs, hI ▸ hu⟩)).differentiableAt.comp_differentiableWithinAt s
      (f := fun s : ℂ => s - 1 + (u : ℂ) * slantDir κ) (by fun_prop))
  exact (hd.const_mul (slantDir κ)).analyticOnNhd hU

end GoldbachBoundaries.ThmA
