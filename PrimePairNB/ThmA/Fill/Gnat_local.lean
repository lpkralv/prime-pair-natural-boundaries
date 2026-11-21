import PrimePairNB.ThmA.G18_LocalAccess
import PrimePairNB.ThmA.Fill.FCommon
import PrimePairNB.ThmA.Fill.Dc_local_two
import PrimePairNB.ThmA.Fill.Gnat_spec
import PrimePairNB.ThmA.Fill.N1A_local
import PrimePairNB.ThmA.Fill.Pv_spec
import PrimePairNB.ThmA.Fill.analyticOn_Dc
import PrimePairNB.ThmA.Fill.decomp_exists
import PrimePairNB.ThmA.Fill.exists_good_discs
import PrimePairNB.ThmA.Fill.slitDisc_facts

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory

namespace GoldbachBoundaries.ThmA

private lemma F_ball_subset_halfPlane {α : ℂ} {r c : ℝ} (hr : r ≤ α.re - c) :
    ball α r ⊆ halfPlane c := by
  intro s hs
  have h1 : |s.re - α.re| ≤ ‖s - α‖ := by
    rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
  have h2 : ‖s - α‖ < r := by rw [← dist_eq_norm]; exact mem_ball.mp hs
  have h3 := (abs_lt.mp (lt_of_le_of_lt h1 h2)).1
  change c < s.re
  linarith

/-- **the local model** for `G^♮`, in the form of `IsPrincipalSheet.local_form`. Under RH.

Sketch. Choose `b ∈ (1/2, Re α/2)` (`α = 2`: any `b ∈ (1/2,1)`). On `Ω_ℍ ∩ R_b`, `Gnat = Gb b`
(`Gnat_spec`). Anchor `α - w_b = a + (1-b)v` has real part `> 1/2` and is off the ray of `P_v`
(for `α ≠ 2` by the good slant, as `α ∉ 2 - ℝv`; for `α = 2` it is `1 + (1-b)v`), so `Pv` is analytic
there (`Pv_spec`); `a + uv ∉ Σ` for `u > 0` (good slant). `N1A_local` gives `N₁^♮ = c Γ J_{1a} Log_α +
H₁`. `𝒟`: holomorphic near `α ≠ 2` (`analyticOn_Dc`; `α ∉ segSS`), `Dc_local_two` at `2`. `Htil_spec`.
Divide by `Γ` (`≠ 0`): `X_α = 2cJ_{1a}` for `α ≠ 2`, `X_2 = 2J_{11} - J_{11}` (`sigmaRes 1 = 1`,
`hasResidue_Qcont_one`). Shrink `r` with `exists_good_discs` (`slitDisc ⊆ Ω_ℍ`), `r ≤ Re α - 1`,
`ball α r ⊆ R_b`; convert `s ∉ cut_α` to `(s-α)/v ∈ slitPlane` with `slitDisc_facts`. -/
theorem Gnat_local (hRH : RiemannHypothesis) {κ : ℝ} (hκ : IsGoodSlant κ) {α : ℂ}
    (hα : α ∈ catalogue) :
    ∃ r : ℝ, 0 < r ∧ r ≤ α.re - 1 ∧ slitDisc (slantDir κ) α r ⊆ Omega κ ∧
      ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball α r) ∧
        EqOn (Gnat κ) (fun s => X α s * logAt (slantDir κ) α s + H s)
          (slitDisc (slantDir κ) α r) := by
  have hα1 := one_lt_re_of_mem_catalogue hα
  have hmin : (1 / 2 : ℝ) < min 1 (α.re / 2) := lt_min (by norm_num) (by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_between hmin
  have hb : b ∈ Ioo (1 / 2 : ℝ) 1 := ⟨hb1, hb2.trans_le (min_le_left _ _)⟩
  have hb0 : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, hb.2⟩
  have hαb : 2 * b < α.re := by linarith [hb2.trans_le (min_le_right _ _)]
  have hlog : (α - wb κ b - 1) / slantDir κ ∈ slitPlane := by
    by_cases h2 : α = 2
    · have he : (α - wb κ b - 1) / slantDir κ = ((1 - b : ℝ) : ℂ) := by
        rw [h2, div_eq_iff (slantDir_ne_zero κ)]
        simp only [wb]; ring
      rw [he]
      exact ofReal_mem_slitPlane.mpr (by linarith [hb.2])
    · by_contra hn
      obtain ⟨-, he⟩ := F_of_not_slit hn
      apply F_goodSlant_off_two_line hκ hα h2
        (1 - b - ((α - wb κ b - 1) / slantDir κ).re)
      have he' := (div_eq_iff (slantDir_ne_zero κ)).mp he
      simp only [wb] at he' ⊢
      push_cast at he' ⊢
      linear_combination he'
  have hA := ((Pv_spec hRH κ).2.1 (α - wb κ b)
    (by simp only [sub_re, F_re_wb]; linarith) hlog).1
  obtain ⟨rN, hrN, HN, hHN, hN⟩ := N1A_local hRH hb0 hα1
    (sub_one_mem_poleSetQ_of_mem_catalogue hα) hA
    (fun u hu => F_goodSlant_segment hκ hα hu.1)
  have hD : ∃ rD : ℝ, 0 < rD ∧ ∃ HD : ℂ → ℂ,
      AnalyticOnNhd ℂ HD (ball α rD) ∧
      ∀ s ∈ ball α rD, (s - α) / slantDir κ ∈ slitPlane →
        Dc κ b s = (if α = 2 then Gamma s * J 1 1 s else 0) * logAt (slantDir κ) α s + HD s := by
    by_cases h2 : α = 2
    · subst α
      simpa using Dc_local_two κ hb0
    · have hαD : α ∉ segSS κ b := by
        rintro ⟨t, -, he⟩
        exact F_goodSlant_off_two_line hκ hα h2 t he
      obtain ⟨rD, hrD, hDc⟩ := (analyticOn_Dc κ hb0 α hαD).exists_ball_analyticOnNhd
      exact ⟨rD, hrD, Dc κ b, hDc, fun s _ _ => by simp [h2]⟩
  obtain ⟨rD, hrD, HD, hHD, hD⟩ := hD
  obtain ⟨rG, hrG, hrGα, hG⟩ := (exists_good_discs hκ hα).1
  let r := min rN (min rD (min rG (α.re - 2 * b)))
  have hr : 0 < r := lt_min hrN (lt_min hrD (lt_min hrG (by linarith)))
  have hrN' : r ≤ rN := min_le_left _ _
  have hrD' : r ≤ rD := (min_le_right _ _).trans (min_le_left _ _)
  have hrG' : r ≤ rG := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrb : r ≤ α.re - 2 * b :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrα : r ≤ α.re - 1 := hrG'.trans hrGα
  have hballb := F_ball_subset_halfPlane hrb
  let H : ℂ → ℂ := fun s => (2 * HN s - HD s + Htil κ b s) / Gamma s
  refine ⟨r, hr, hrα, (slitDisc_mono hrG').trans hG, H, ?_, ?_⟩
  · intro s hs
    have hn := hHN s (ball_subset_ball hrN' hs)
    have hd := hHD s (ball_subset_ball hrD' hs)
    have hh := (Htil_spec hRH (κ := κ) hb).1.analyticOnNhd (isOpen_halfPlane _) s (hballb hs)
    have hnum : AnalyticAt ℂ (fun z => 2 * HN z - HD z + Htil κ b z) s :=
      ((analyticAt_const.mul hn).sub hd).add hh
    simp only [H, div_eq_mul_inv]
    change AnalyticAt ℂ ((fun z => 2 * HN z - HD z + Htil κ b z) *
      (fun z => (Gamma z)⁻¹)) s
    exact hnum.mul (by simpa only [one_div] using
      Complex.differentiable_one_div_Gamma.analyticAt s)
  · intro s hs
    have hslog := ((slitDisc_facts κ hr hrα).2.2 s hs.1).mp hs.2
    have hsH : s ∈ HH := ball_subset_HH hrα hs.1
    have hs0 : 0 < s.re := by have : 1 < s.re := hsH; linarith
    have hΓ := Complex.Gamma_ne_zero_of_re_pos hs0
    have hcoef : 2 * (sigmaRes (α - 1) * Gamma s * J 1 (α - 1) s) -
        (if α = 2 then Gamma s * J 1 1 s else 0) = Gamma s * X α s := by
      by_cases h2 : α = 2
      · subst α
        have hres : sigmaRes (1 : ℂ) = 1 := sigmaRes_eq hasResidue_Qcont_one
        norm_num [X, hres]
        ring
      · simp only [X, h2, ↓reduceIte, sub_zero]
        ring
    rw [(Gnat_spec hRH κ).2.2 b hb ⟨(slitDisc_mono hrG' |>.trans hG) hs, hballb hs.1⟩]
    rw [Gb]
    change (2 * N1A κ b (Pv κ) s - Dc κ b s + Htil κ b s) / Gamma s = _
    rw [hN s (ball_subset_ball hrN' hs.1) hslog,
      hD s (ball_subset_ball hrD' hs.1) hslog]
    dsimp [H]
    field_simp
    linear_combination hcoef * logAt (slantDir κ) α s

end GoldbachBoundaries.ThmA
