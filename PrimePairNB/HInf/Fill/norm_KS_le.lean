import PrimePairNB.HInf.Defs

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

lemma KS_reflection {w : ℂ} (hw : w ≠ 1) :
    KS w = (1 - w) * (Real.pi : ℂ) / Complex.sin (Real.pi * w) := by
  have h : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  rw [KS, show 2 - w = (1 - w) + 1 by ring, Complex.Gamma_add_one _ h]
  rw [mul_left_comm, Complex.Gamma_mul_Gamma_one_sub]
  ring

lemma sinh_abs_im_le_norm_sin (z : ℂ) : Real.sinh |z.im| ≤ ‖Complex.sin z‖ := by
  have hs : ‖Complex.sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.sin_eq]
    simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cosh, normSq_apply, add_re, add_im, mul_re, mul_im,
      ofReal_re, ofReal_im, I_re, I_im]
    nlinarith [Real.sin_sq_add_cos_sq z.re, Real.cosh_sq_sub_sinh_sq z.im]
  have he : Real.sinh |z.im| ^ 2 = Real.sinh z.im ^ 2 := by
    rcases le_total 0 z.im with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, Real.sinh_neg, neg_sq]
  have hpos := Real.sinh_nonneg_iff.mpr (abs_nonneg z.im)
  nlinarith [sq_nonneg (Real.sin z.re), norm_nonneg (Complex.sin z)]

/-- Reflection, the lower bound for sine, and an elementary exponential estimate. -/
theorem norm_KS_le {w : ℂ} (h0 : 0 ≤ w.re) (h2 : w.re ≤ 2) (him : 1 ≤ |w.im|) :
    ‖KS w‖ ≤ 7 * (1 + |w.im|) * Real.exp (-(Real.pi * |w.im|)) := by
  have hw : w ≠ 1 := by intro h; norm_num [h] at him
  let t := Real.pi * |w.im|
  have ht : 3 ≤ t := by dsimp [t]; nlinarith [Real.pi_gt_three]
  have he : 4 ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hinv : Real.exp (-t) ≤ Real.exp t / 16 := by
    have hmul := Real.exp_add t (-t)
    simp only [add_neg_cancel, Real.exp_zero] at hmul
    nlinarith [Real.exp_pos (-t), sq_nonneg (Real.exp t - 4)]
  have hsin : (15 / 32 : ℝ) * Real.exp t ≤ ‖Complex.sin (Real.pi * w)‖ := by
    have h := sinh_abs_im_le_norm_sin (Real.pi * w)
    have hi : |((Real.pi : ℂ) * w).im| = t := by
      simp [t, abs_mul, abs_of_pos Real.pi_pos]
    rw [hi, Real.sinh_eq] at h
    linarith
  have hspos : 0 < ‖Complex.sin (Real.pi * w)‖ :=
    lt_of_lt_of_le (by positivity) hsin
  have hnorm : ‖1 - w‖ ≤ 1 + |w.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im (1 - w)
    have hre : |1 - w.re| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    simp only [sub_re, one_re, sub_im, one_im, zero_sub, abs_neg] at h
    linarith
  rw [KS_reflection hw, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  apply (div_le_iff₀ hspos).mpr
  have hpi : Real.pi ≤ 7 * (15 / 32 : ℝ) := by linarith [Real.pi_lt_d2]
  have hexp : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  calc
    ‖1 - w‖ * Real.pi ≤ (1 + |w.im|) * Real.pi := by gcongr
    _ ≤ (1 + |w.im|) * (7 * (15 / 32)) := by gcongr
    _ = (7 * (1 + |w.im|) * Real.exp (-t)) * ((15 / 32) * Real.exp t) := by
      nlinarith [hexp]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsin (by positivity)

end GoldbachBoundaries.HInf.Fill
