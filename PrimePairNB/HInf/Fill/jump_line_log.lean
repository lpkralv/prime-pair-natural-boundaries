import PrimePairNB.HInf.Fill.Pth_local

/-! The two logarithms used when crossing a catalogue point. -/
noncomputable section
open Complex Filter Topology Set Metric
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

private lemma logK_right (σ : ℝ) {z : ℂ} (hz : 0 < z.re) : logK σ z = Complex.log z := by
  have hw : 0 < (slantDir σ).re := by simp [slantDir]
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hw0 := ThmA.slantDir_ne_zero σ
  have hzarg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  have hwarg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw))
  have hlog : Complex.log (z / slantDir σ) = Complex.log z - Complex.log (slantDir σ) := by
    have he : Complex.exp (Complex.log z - Complex.log (slantDir σ)) = z / slantDir σ := by
      rw [Complex.exp_sub, Complex.exp_log hz0, Complex.exp_log hw0]
    rw [← he]
    apply Complex.log_exp <;> simp only [Complex.sub_im, Complex.log_im] <;> linarith
  simp only [logK, hlog, sub_add_cancel]

private lemma log_neg_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.log (-z) = Complex.log z - (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp only [Complex.log_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero]
    exact Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz

private lemma log_neg_of_im_neg {z : ℂ} (hz : z.im < 0) :
    Complex.log (-z) = Complex.log z + (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp only [Complex.log_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero]
    exact Complex.arg_neg_eq_arg_add_pi_of_im_neg hz

lemma logK_east (σ κ : ℝ) {t : ℝ} (ht : 0 < t) :
    logK σ ((t : ℂ) * slantDir κ) = Complex.log ((t : ℂ) * slantDir κ) :=
  logK_right σ (by simpa [slantDir] using ht)

lemma logK_west {m κ p t : ℝ} (hm : m < κ) (hp : κ < p) (ht : 0 < t) :
    logK p (-((t : ℂ) * slantDir κ)) - logK m (-((t : ℂ) * slantDir κ)) =
      2 * (Real.pi : ℂ) * I := by
  have hs (σ : ℝ) : (((t : ℂ) * slantDir κ) / slantDir σ).im =
      t * (κ - σ) / (1 + σ ^ 2) := by
    simp [slantDir, Complex.div_im, Complex.normSq_apply]
    ring
  have hmpos : 0 < (((t : ℂ) * slantDir κ) / slantDir m).im := by
    rw [hs]; exact div_pos (mul_pos ht (sub_pos.mpr hm)) (by positivity)
  have hpneg : (((t : ℂ) * slantDir κ) / slantDir p).im < 0 := by
    rw [hs]; exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ht (sub_neg.mpr hp)) (by positivity)
  have hmL := logK_east m κ ht
  have hpL := logK_east p κ ht
  simp only [logK, neg_div, log_neg_of_im_pos hmpos, log_neg_of_im_neg hpneg]
  dsimp only [logK] at hmL hpL
  linear_combination hpL - hmL

/-- Equality of logarithmic derivatives upgrades a value to a germ. -/
lemma logK_germ {m p : ℝ} {x z c : ℂ} (hm : z ∉ rayW m x) (hp : z ∉ rayW p x)
    (he : logK p (z - x) = logK m (z - x) + c) :
    (fun v => logK p (v - x)) =ᶠ[𝓝 z] fun v => logK m (v - x) + c := by
  have ho (σ : ℝ) : IsOpen (rayW σ x)ᶜ := by
    rw [show (rayW σ x)ᶜ = (fun v : ℂ => (v - x) / slantDir σ) ⁻¹' slitPlane from
      Set.ext (fun v => not_mem_rayW_iff σ x v)]
    exact isOpen_slitPlane.preimage (by fun_prop)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ((ho m).inter (ho p)) z ⟨hm, hp⟩
  have heq : EqOn (fun v => logK p (v - x)) (fun v => logK m (v - x) + c) (ball z r) := by
    apply isOpen_ball.eqOn_of_deriv_eq (convex_ball z r).isPreconnected
    · exact fun v hv => (hasDerivAt_logK (hball hv).2).differentiableAt.differentiableWithinAt
    · exact fun v hv => ((hasDerivAt_logK (hball hv).1).add_const c).differentiableAt.differentiableWithinAt
    · intro v hv
      exact (hasDerivAt_logK (hball hv).2).deriv.trans
        ((hasDerivAt_logK (hball hv).1).add_const c).deriv.symm
    · exact mem_ball_self hr
    · exact he
  exact Filter.eventuallyEq_of_mem (ball_mem_nhds z hr) heq

end GoldbachBoundaries.HInf.Fill
