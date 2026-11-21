import PrimePairNB.ThmA.Fill.verticalIntegral_CauchyS_shift
import PrimePairNB.ThmA.Fill.ECommonLines
import PrimePairNB.ThmA.Fill.ECommonCauchy
import PrimePairNB.ThmA.Fill.F0_mellin
import PrimePairNB.ThmA.Fill.Pv_eq_Eb_add
import PrimePairNB.ThmA.Fill.Pv_spec
import PrimePairNB.ThmA.Fill.verticalIntegral_Eb_shift

/-!
# `F0_split` (the `F₀` splitting)

`F₀ = L + h₀` on `t > 0` and `|h₀(t)| ≤ C t^{-b}`, under RH, any slope.

Chain (at `c = 2`): `F₀(t) = VI'(Γ P t^{-z}; 2)` (`F0_mellin`) `= VI'(Γ E_b t^{-z}; 2) +
VI'(Γ (∫_𝒮) t^{-z}; 2)` (`Pv_spec`, `Pv_eq_Eb_add`; on `Re z > 1`, `(z-1)/v ∈ slitPlane`)
`= VI'(Γ E_b; b) + L(t) + VI'(Γ (∫_𝒮); b)` (`verticalIntegral_Eb_shift`,
`verticalIntegral_CauchyS_shift`) `= L(t) + h₀(t)` (`Pv_eq_Eb_add` on `Re z = b` except at `w_b`).
The bound is the trivial estimate `|h₀(t)| ≤ (2π)⁻¹ t^{-b} ∫ |Γ P_v(b+iy)| dy` (as
`TIdentity.norm_verticalIntegral'_kernelQ_le`; it needs no integrability).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

namespace GroupE

/-- Linearity of `VerticalIntegral'` for integrable integrands. -/
theorem cauchy_VI_add {f g : ℂ → ℂ} {σ : ℝ} (hf : Integrable fun y : ℝ => f (σ + y * I))
    (hg : Integrable fun y : ℝ => g (σ + y * I)) :
    VerticalIntegral' f σ + VerticalIntegral' g σ = VerticalIntegral' (fun z => f z + g z) σ := by
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
  rw [integral_add hf hg]
  ring

/-- If `(z-1)/v ∉ slitPlane` then `z - 1 = r v` with `r = Re(z-1) ≤ 0`. -/
theorem cauchy_not_slit {κ : ℝ} {z : ℂ} (h : (z - 1) / slantDir κ ∉ slitPlane) :
    (z - 1).re ≤ 0 ∧ (z - 1).im = (z - 1).re * κ := by
  have hv : slantDir κ ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0
    simp [slantDir] at this
  set q := (z - 1) / slantDir κ with hq
  rw [mem_slitPlane_iff, not_or, not_lt, not_not] at h
  have hz : z - 1 = q * slantDir κ := by rw [hq, div_mul_cancel₀ _ hv]
  have hre : (z - 1).re = q.re := by rw [hz]; simp [slantDir, h.2]
  have him : (z - 1).im = q.re * κ := by rw [hz]; simp [slantDir, h.2]
  exact ⟨hre ▸ h.1, by rw [him, hre]⟩

theorem cauchy_slit_of_one_lt_re {κ : ℝ} {z : ℂ} (hz : 1 < z.re) :
    (z - 1) / slantDir κ ∈ slitPlane := by
  by_contra h
  have := (cauchy_not_slit h).1
  simp at this
  linarith

theorem cauchy_slit_line_b {κ b y : ℝ} (hy : y ≠ -((1 - b) * κ)) :
    (((b : ℂ) + y * I) - 1) / slantDir κ ∈ slitPlane := by
  by_contra h
  have := (cauchy_not_slit h).2
  simp at this
  exact hy (by linarith)

end GroupE

open GroupE in
/-- **the `F₀` splitting.** `F₀ = L + h₀` on `t > 0`, and `|h₀(t)| ≤ C t^{-b}`. Under RH, any slope.

Sketch. `F₀(t) = VI'(Γ P t^{-z}; 2)` (`F0_mellin`) `= VI'(Γ P_v t^{-z}; 2)` (`Pv_spec`)
`= VI'(Γ E_b t^{-z}; 2) + VI'(Γ (∫_𝒮) t^{-z}; 2)` (`Pv_eq_Eb_add`: on `Re z = 2`,
`(z-1)/v ∈ slitPlane`) `= VI'(Γ E_b; b) + L(t) + VI'(Γ (∫_𝒮); b)` `= L(t) + h₀(t)`
(`Pv_eq_Eb_add` on `Re z = b` off the single point `w_b`). The bound: `|t^{-z}| = t^{-b}` on the line
and `∫|Γ P_v(b+iy)| dy < ∞` (the decay of `Γ` with `norm_Eaux_le`, `|Log| ≪ log|y|`, `|∫_𝒮| ≪ 1/|y|`, and the
integrable log singularity at `w_b`). -/
theorem F0_split (hRH : RiemannHypothesis) {κ b : ℝ} (hb : b ∈ Ioo (1 / 2 : ℝ) 1) :
    (∀ t : ℝ, 0 < t → (F0 t : ℂ) = Lf κ b t + h0 κ b t) ∧
      ∃ C : ℝ, ∀ t : ℝ, 0 < t → ‖h0 κ b t‖ ≤ C * t ^ (-b) := by
  have hb0 : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1], hb.2⟩
  constructor
  · intro t ht
    have hc : (1 : ℝ) < 2 := one_lt_two
    rw [F0_mellin.2.2 2 t hc ht]
    have h1 : VerticalIntegral' (fun z => Gamma z * P z * (t : ℂ) ^ (-z)) 2 =
        VerticalIntegral' (fun z => Gamma z * Eb κ b z * (t : ℂ) ^ (-z)) 2 +
          VerticalIntegral' (fun z => Gamma z * CauchyS κ b z * (t : ℂ) ^ (-z)) 2 := by
      rw [cauchy_VI_add (integrable_Gamma_Eb_line hRH hb (by linarith [hb.2]) ht)
        (integrable_Gamma_CauchyS_line hb0 (Or.inr hc) ht)]
      simp only [VerticalIntegral', VerticalIntegral]
      congr 2
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      have hre : 1 < ((2 : ℝ) + y * I : ℂ).re := by simp
      beta_reduce
      rw [← (Pv_spec hRH κ).1 _ hre, Pv_eq_Eb_add hb.2 (cauchy_slit_of_one_lt_re hre)]
      ring
    rw [h1, verticalIntegral_Eb_shift hRH hb hc ht, verticalIntegral_CauchyS_shift hb0 hc ht,
      add_left_comm,
      cauchy_VI_add (integrable_Gamma_Eb_line hRH hb le_rfl ht)
        (integrable_Gamma_CauchyS_line hb0 (Or.inl rfl) ht)]
    congr 1
    simp only [h0, VerticalIntegral', VerticalIntegral]
    congr 2
    refine integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (-((1 - b) * κ))] with y hy
    rw [Pv_eq_Eb_add hb.2 (cauchy_slit_line_b hy)]
    ring
  · set g : ℝ → ℂ := fun y => Gamma (b + y * I) * Pv κ (b + y * I) with hg
    refine ⟨(1 / (2 * Real.pi)) * ∫ y, ‖g y‖, fun t ht => ?_⟩
    have hnorm : ∀ y : ℝ, ‖Gamma (b + y * I) * Pv κ (b + y * I) * (t : ℂ) ^ (-((b : ℂ) + y * I))‖ =
        t ^ (-b) * ‖g y‖ := by
      intro y
      simp only [norm_mul, hg]
      rw [norm_cpow_eq_rpow_re_of_pos ht]
      simp only [neg_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
        sub_self, add_zero]
      ring
    have hI : ‖(1 / (2 * (Real.pi : ℂ) * I))‖ * ‖I‖ = 1 / (2 * Real.pi) := by
      simp [abs_of_pos Real.pi_pos]
    calc ‖h0 κ b t‖
        = ‖(1 / (2 * (Real.pi : ℂ) * I))‖ * ‖I‖ *
            ‖∫ y : ℝ, Gamma (b + y * I) * Pv κ (b + y * I) * (t : ℂ) ^ (-((b : ℂ) + y * I))‖ := by
          simp only [h0, VerticalIntegral', VerticalIntegral, norm_smul]; ring
      _ ≤ 1 / (2 * Real.pi) *
            ∫ y : ℝ, ‖Gamma (b + y * I) * Pv κ (b + y * I) * (t : ℂ) ^ (-((b : ℂ) + y * I))‖ := by
          rw [hI]
          exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
      _ = 1 / (2 * Real.pi) * (t ^ (-b) * ∫ y : ℝ, ‖g y‖) := by
          rw [integral_congr_ae (Eventually.of_forall hnorm), integral_const_mul]
      _ = 1 / (2 * Real.pi) * (∫ y, ‖g y‖) * t ^ (-b) := by ring

end GoldbachBoundaries.ThmA
