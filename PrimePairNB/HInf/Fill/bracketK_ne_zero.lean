import PrimePairNB.HInf.Fill.norm_KS_le

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory ComplexConjugate
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

lemma sin_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : Complex.sin z ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  apply hz
  simp [hk]

private lemma cot_equation_real {v : ℂ}
    (h : Complex.cos (Real.pi * v) = 4 * v * Complex.sin (Real.pi * v)) : v.im = 0 := by
  have he (z : ℂ) : (Complex.cos z * conj (Complex.sin z)).im =
      -(Real.cosh z.im * Real.sinh z.im) := by
    rw [Complex.cos_eq z, Complex.sin_eq z]
    simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cosh, map_add, map_mul, conj_ofReal, conj_I,
      mul_im, mul_re, add_re, add_im, sub_re, sub_im, ofReal_re, ofReal_im, I_re, I_im,
      neg_re, neg_im]
    linear_combination -(Real.cosh z.im * Real.sinh z.im) * (Real.sin_sq_add_cos_sq z.re)
  have hi := congrArg Complex.im (congrArg (fun z : ℂ => z * conj (Complex.sin (Real.pi * v))) h)
  rw [he] at hi
  have hh : (4 * v * Complex.sin (Real.pi * v) * conj (Complex.sin (Real.pi * v))).im =
      4 * v.im * Complex.normSq (Complex.sin (Real.pi * v)) := by
    rw [mul_assoc, Complex.mul_conj]
    simp [mul_im]
  rw [hh] at hi
  have him : ((Real.pi : ℂ) * v).im = Real.pi * v.im := by simp
  rw [him] at hi
  rcases lt_trichotomy v.im 0 with hv | hv | hv
  · have hs : Real.sinh (Real.pi * v.im) < 0 := Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg Real.pi_pos hv)
    have hp := mul_neg_of_pos_of_neg (Real.cosh_pos (Real.pi * v.im)) hs
    have hn := mul_nonpos_of_nonpos_of_nonneg (show 4 * v.im ≤ 0 by linarith)
      (Complex.normSq_nonneg (Complex.sin (Real.pi * v)))
    linarith
  · exact hv
  · have hs : 0 < Real.sinh (Real.pi * v.im) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hv)
    have hp := mul_pos (Real.cosh_pos (Real.pi * v.im)) hs
    have hn := mul_nonneg (show 0 ≤ 4 * v.im by linarith)
      (Complex.normSq_nonneg (Complex.sin (Real.pi * v)))
    linarith

/-- The imaginary part of cotangent has the opposite sign to its argument. -/
theorem bracketK_ne_zero {u : ℂ} (hu : u.im ≠ 0) : KS (1 - u / 4) + KS (1 / 2 + u / 4) ≠ 0 := by
  let x : ℂ := u / 4
  have hx : x.im ≠ 0 := by simpa [x] using div_ne_zero hu (by norm_num : (4 : ℝ) ≠ 0)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs : Complex.sin (Real.pi * x) ≠ 0 :=
    sin_ne_zero_of_im_ne_zero (by simpa using mul_ne_zero Real.pi_ne_zero hx)
  have hc : Complex.cos (Real.pi * x) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h
    have hi := congrArg Complex.im hk
    simp at hi
    exact hx hi
  have h1 : (1 : ℂ) - x ≠ 1 := by
    intro h
    apply hx
    have he : x = 0 := by linear_combination -h
    simp [he]
  have h2 : (1 / 2 : ℂ) + x ≠ 1 := by
    intro h
    apply hx
    have : x = (1 / 2 : ℂ) := by linear_combination h
    simp [this]
  have es : Complex.sin (Real.pi * (1 - x)) = Complex.sin (Real.pi * x) := by
    rw [show (Real.pi : ℂ) * (1 - x) = Real.pi - Real.pi * x by ring, Complex.sin_pi_sub]
  have ec : Complex.sin (Real.pi * (1 / 2 + x)) = Complex.cos (Real.pi * x) := by
    rw [show (Real.pi : ℂ) * (1 / 2 + x) = Real.pi / 2 + Real.pi * x by ring, Complex.sin_add]
    simp
  intro hz
  change KS (1 - x) + KS (1 / 2 + x) = 0 at hz
  rw [KS_reflection h1, KS_reflection h2, es, ec] at hz
  have hn : x * Complex.cos (Real.pi * x) + (1 / 2 - x) * Complex.sin (Real.pi * x) = 0 := by
    rw [div_add_div _ _ hs hc] at hz
    have hznum : (1 - (1 - x)) * (Real.pi : ℂ) * Complex.cos (Real.pi * x) +
        (1 - (1 / 2 + x)) * (Real.pi : ℂ) * Complex.sin (Real.pi * x) = 0 := by
      rcases (div_eq_zero_iff).mp hz with hh | hh
      · linear_combination hh
      · exact False.elim ((mul_ne_zero hs hc) hh)
    apply (mul_eq_zero.mp (show (x * Complex.cos (Real.pi * x) +
      (1 / 2 - x) * Complex.sin (Real.pi * x)) * (Real.pi : ℂ) = 0 by
        linear_combination hznum)).resolve_right hpi
  let v : ℂ := x - 1 / 4
  have htrig : Complex.cos (Real.pi * v) = 4 * v * Complex.sin (Real.pi * v) := by
    have e : (Real.pi : ℂ) * v = Real.pi * x - (Real.pi / 4 : ℝ) := by dsimp [v]; push_cast; ring
    rw [e, Complex.cos_sub, Complex.sin_sub]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
    dsimp [v]
    linear_combination (4 * (Real.sqrt 2 / 2 : ℝ)) * hn
  have := cot_equation_real htrig
  apply hx
  simpa [v] using this

end GoldbachBoundaries.HInf.Fill
