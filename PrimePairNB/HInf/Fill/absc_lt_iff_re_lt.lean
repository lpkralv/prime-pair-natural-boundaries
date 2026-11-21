import PrimePairNB.HInf.Defs

/-! Coordinate helpers for separating graphs. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

lemma slantDir_ne_zero' (κ : ℝ) : slantDir κ ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [slantDir] at this

lemma hgt_sub (κ : ℝ) (v w : ℂ) : hgt κ (v - w) = hgt κ v - hgt κ w := by
  simp [hgt, sub_div]

lemma absc_sub (κ : ℝ) (v w : ℂ) : absc κ (v - w) = absc κ v - absc κ w := by
  simp [absc, sub_div]

/-- Moving along a `κ`-line keeps the height. -/
lemma hgt_sub_mul (κ : ℝ) (a : ℂ) (t : ℝ) : hgt κ (a - (t : ℂ) * slantDir κ) = hgt κ a := by
  have : (a - (t : ℂ) * slantDir κ) / slantDir κ = a / slantDir κ - t := by
    have := slantDir_ne_zero' κ
    field_simp
  simp [hgt, this]

/-- Moving along a `κ`-line shifts the abscissa by the parameter. -/
lemma absc_sub_mul (κ : ℝ) (a : ℂ) (t : ℝ) : absc κ (a - (t : ℂ) * slantDir κ) = absc κ a - t := by
  have : (a - (t : ℂ) * slantDir κ) / slantDir κ = a / slantDir κ - t := by
    have := slantDir_ne_zero' κ
    field_simp
  simp [absc, this]

lemma re_eq_absc (κ : ℝ) (w : ℂ) : w.re = absc κ w - κ * hgt κ w := by
  have h : w = slantDir κ * (w / slantDir κ) := (mul_div_cancel₀ w (slantDir_ne_zero' κ)).symm
  have hr := congrArg Complex.re h
  simpa [slantDir, absc, hgt] using hr

lemma im_eq_absc (κ : ℝ) (w : ℂ) : w.im = κ * absc κ w + hgt κ w := by
  have h : w = slantDir κ * (w / slantDir κ) := (mul_div_cancel₀ w (slantDir_ne_zero' κ)).symm
  have hr := congrArg Complex.im h
  simpa [slantDir, absc, hgt, add_comm] using hr

/-- Two points of one `κ`-line differ by the difference of real parts, along `slantDir κ`. -/
lemma eq_sub_of_hgt_eq {κ : ℝ} {w w' : ℂ} (hh : hgt κ w = hgt κ w') :
    w' = w - ((w.re - w'.re : ℝ) : ℂ) * slantDir κ := by
  have r1 := re_eq_absc κ w
  have r2 := re_eq_absc κ w'
  have i1 := im_eq_absc κ w
  have i2 := im_eq_absc κ w'
  apply Complex.ext
  · simp [slantDir]
  · simp only [slantDir, sub_im, mul_im, ofReal_re, ofReal_im, add_im, one_im, mul_re, I_re, I_im, add_re, one_re]
    rw [i1, i2, r1, r2, ← hh]
    ring

lemma pt_re {κ : ℝ} (Γ : SlantGraph κ) (h : ℝ) : (Γ.pt h).re = Γ.ξ h - κ * h := by
  simp [SlantGraph.pt, slantDir]

/-- `Σ` is finite on `{ε ≤ Re} ∩ {|hgt| ≤ H}`. -/
lemma finite_poleSetQ_height (κ : ℝ) {ε : ℝ} (hε : 0 < ε) (H : ℝ) :
    {a | a ∈ PoleSetQ ∧ ε ≤ a.re ∧ |hgt κ a| ≤ H}.Finite := by
  set R : ℝ := 1 + |κ| + (1 + κ ^ 2) * H with hR
  set K : Set ℂ := closedBall 0 R ∩ {w | ε ≤ w.re} with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_re)
  have hK0 : K ⊆ halfPlane 0 := fun w hw => by
    show 0 < w.re
    have : ε ≤ w.re := hw.2
    linarith
  refine (M6.finite_inter_poleSetQ_A hKc hK0).subset ?_
  rintro a ⟨ha, hre, hh⟩
  refine ⟨⟨?_, hre⟩, ha⟩
  have hb := M1.poleSetQ_re_bounds ha
  rw [mem_closedBall, dist_zero_right]
  refine (Complex.norm_le_abs_re_add_abs_im a).trans ?_
  rw [abs_of_pos hb.1]
  have r1 := re_eq_absc κ a
  have i1 := im_eq_absc κ a
  have hi : a.im = κ * a.re + (1 + κ ^ 2) * hgt κ a := by
    rw [i1, r1]; ring
  have h1 : |κ * a.re| ≤ |κ| := by
    rw [abs_mul, abs_of_pos hb.1]
    nlinarith [abs_nonneg κ, hb.2.1]
  have h2 : |(1 + κ ^ 2) * hgt κ a| ≤ (1 + κ ^ 2) * H := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 + κ ^ 2)]
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  have h3 : |a.im| ≤ |κ| + (1 + κ ^ 2) * H := by
    rw [hi]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  rw [hR]
  linarith [hb.2.1]

end GoldbachBoundaries.HInf.Fill

