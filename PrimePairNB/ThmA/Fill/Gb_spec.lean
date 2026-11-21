import PrimePairNB.ThmA.G15_Kernel
import PrimePairNB.ThmA.Fill.FCommon
import PrimePairNB.ThmA.Fill.Pv_spec
import PrimePairNB.ThmA.Fill.analyticAt_N1A
import PrimePairNB.ThmA.Fill.analyticOn_Dc
import PrimePairNB.ThmA.Fill.decomp_exists

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

/-- **the principal-sheet proposition for one `b`.** `G^♮_b` is holomorphic on `Ω_ℍ ∩ R_b` and equals `G` on
`σ > 2`. Under RH, any slope.

Sketch. Anchor: for `s ∈ Ω_ℍ ∩ R_b`, `Re(s - w_b) = σ - b > 1/2`, and `(s - w_b - 1)/v ∈ slitPlane`
(else `s ∈ 2 - [1-b, ∞)v` with `σ > 2b`, i.e. `s ∈ cut_2`); so `Pv` is analytic there (`Pv_spec`).
Path: `s - 1 + uv = a ∈ Σ` would put `s ∈ cut_{1+a}` (`one_add_mem_catalogue_of_mem_poleSetQ`). So
`analyticAt_N1A` applies. `𝒟`: `segSS ∩ R_b ⊆ cut_2`, so `analyticOn_Dc`. `Htil_spec`; `Γ ≠ 0` on
`ℍ` (`Complex.Gamma_ne_zero_of_re_pos`). For `σ > 2`: `N1nat = N1ser` (anchor `Pv = P`, and
`v∫_u^{1-b} Q(s-1+u'v) du' = P(s-1+uv) - P(s - w_b)` by FTC with `hasDerivAt_P`), then
`decomp_exists`/`Htil_spec`. -/
theorem Gb_spec (hRH : RiemannHypothesis) (κ : ℝ) {b : ℝ} (hb : b ∈ Ioo (1 / 2 : ℝ) 1) :
    AnalyticOnNhd ℂ (Gb κ b) (Omega κ ∩ halfPlane (2 * b)) ∧ EqOn (Gb κ b) G (halfPlane 2) := by
  have hb0 : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1], hb.2⟩
  constructor
  · intro s hs
    have hs1 : 1 < s.re := hs.1.1
    have hs2 : 2 * b < s.re := hs.2
    have ha := (Pv_spec hRH κ).2.1 (s - wb κ b)
      (by simp only [sub_re, F_re_wb]; linarith [hb.1])
      (F_Omega_anchor_slit hb.2 hs.1)
    have hN := analyticAt_N1A hb0 hs1 ha.1 (fun u hu => F_Omega_no_pole hs.1 hu.1)
    have hD := analyticOn_Dc κ hb0 s (F_Omega_not_segSS hs.1)
    have hH := (Htil_spec hRH (κ := κ) hb).1.analyticOnNhd (isOpen_halfPlane _) s hs.2
    have hi := Complex.differentiable_one_div_Gamma.analyticAt s
    have hnum : AnalyticAt ℂ (fun z => 2 * N1nat κ b z - Dc κ b z + Htil κ b z) s :=
      ((analyticAt_const.mul hN).sub hD).add hH
    change AnalyticAt ℂ (fun z => (2 * N1nat κ b z - Dc κ b z + Htil κ b z) / Gamma z) s
    simp only [div_eq_mul_inv]
    change AnalyticAt ℂ ((fun z => 2 * N1nat κ b z - Dc κ b z + Htil κ b z) *
      (fun z => (Gamma z)⁻¹)) s
    exact hnum.mul (by simpa only [one_div] using hi)
  · intro s hs
    have hs2 : 2 < s.re := hs
    have hN : N1nat κ b s = N1ser κ b s := by
      unfold N1nat N1A N1ser
      congr 1
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (by linarith [hb.2])] at hu
      dsimp only
      rw [F_PsegA_eq_P hRH (κ := κ) hs2 hu]
    have he := (Htil_spec hRH (κ := κ) hb).2 s hs2
    rw [Gb, hN, ← he]
    exact mul_div_cancel_left₀ _ (Complex.Gamma_ne_zero_of_re_pos (by linarith))

end GoldbachBoundaries.ThmA
