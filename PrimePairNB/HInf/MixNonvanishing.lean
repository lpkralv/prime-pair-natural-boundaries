import PrimePairNB.HInf.MixDefs

/-! The full-disc bound follows from the Gamma recurrence, with Gamma factors
cancelled using Mathlib’s nonvanishing theorem away from its poles. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf

theorem betaMix_eq {u : ℂ} (hu : 0 < u.im) : betaMix u = 2 / u := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hGamma : Gamma u ≠ 0 := Complex.Gamma_ne_zero fun n h => by
    have hi := congrArg Complex.im h
    simp only [neg_im, natCast_im, neg_zero] at hi
    linarith
  have hrec : Gamma (1 + u) = u * Gamma u := by
    rw [add_comm, Complex.Gamma_add_one u hu0]
  simp only [betaMix, kerG, KerS, add_sub_cancel_left, add_sub_cancel_right,
    Gamma_one, one_mul, mul_one, hrec]
  field_simp
  ring

theorem betaMix_lower (y ε : ℝ) (hε : 0 < ε) (hεy : ε < y)
    {u : ℂ} (hu : u ∈ closedBall ((y : ℂ) * I) ε) :
    2 / (y + ε) ≤ ‖betaMix u‖ := by
  have hy : 0 < y := hε.trans hεy
  have hdist : ‖u - (y : ℂ) * I‖ ≤ ε := by simpa [dist_eq_norm] using hu
  have him : 0 < u.im := by
    have hh := (abs_le.mp ((Complex.abs_im_le_norm (u - (y : ℂ) * I)).trans hdist)).1
    simp only [sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re,
      mul_zero, add_zero] at hh
    linarith
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr (by intro h; simp [h] at him)
  have hnorm : ‖u‖ ≤ y + ε := by
    have hh := norm_add_le (u - (y : ℂ) * I) ((y : ℂ) * I)
    simp only [sub_add_cancel, norm_mul, norm_I, mul_one, norm_real,
      Real.norm_eq_abs, abs_of_pos hy] at hh
    linarith
  rw [betaMix_eq him, norm_div, norm_ofNat]
  exact div_le_div_of_nonneg_left (by norm_num) hu0 hnorm

theorem NV_mix : ∀ y ε : ℝ, 0 < ε → ε < y →
    ∃ κ : ℝ, 0 < κ ∧ ∀ u ∈ closedBall ((y : ℂ) * I) ε, κ ≤ ‖betaMix u‖ := by
  intro y ε hε hεy
  have hy : 0 < y := hε.trans hεy
  exact ⟨2 / (y + ε), by positivity, fun u hu => betaMix_lower y ε hε hεy hu⟩

end GoldbachBoundaries.HInf
