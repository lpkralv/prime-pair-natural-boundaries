import PrimePairNB.Paper2.M1.Kernel

/-!
# `mellin_one_add_cpow_neg`

The substitution `x = t/(1+t)` (`integral_image_eq_integral_abs_deriv_smul`) carries
`∫_0^∞ t^{w-1} (1+t)^{-s} dt` to `Complex.betaIntegral w (s - w)`, and
`Complex.Gamma_mul_Gamma_eq_betaIntegral` evaluates it.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The substitution `t ↦ t / (1 + t)`. -/
private def subst (t : ℝ) : ℝ := t / (1 + t)

private lemma hasDerivWithinAt_subst {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    HasDerivWithinAt subst (1 / (1 + t) ^ 2) (Ioi 0) t := by
  have ht' : (1 + t) ≠ 0 := by have := mem_Ioi.mp ht; positivity
  have h := (hasDerivAt_id t).div ((hasDerivAt_id t).const_add 1) ht'
  refine (h.congr_deriv ?_).hasDerivWithinAt
  simp only [id]
  field_simp
  ring

private lemma injOn_subst : InjOn subst (Ioi 0) := by
  intro t ht u hu h
  have ht' : 0 < 1 + t := by have := mem_Ioi.mp ht; linarith
  have hu' : 0 < 1 + u := by have := mem_Ioi.mp hu; linarith
  simp only [subst] at h
  rw [div_eq_div_iff ht'.ne' hu'.ne'] at h
  linarith

private lemma image_subst : subst '' Ioi 0 = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht0 : 0 < t := ht
    have ht' : 0 < 1 + t := by linarith
    refine ⟨div_pos ht0 ht', (div_lt_one ht').mpr (by linarith)⟩
  · rintro ⟨hx0, hx1⟩
    have h1x : 0 < 1 - x := by linarith
    refine ⟨x / (1 - x), div_pos hx0 h1x, ?_⟩
    simp only [subst]
    field_simp
    ring

/-- The pointwise identity behind the substitution. -/
private lemma subst_integrand {s w : ℂ} {t : ℝ} (ht : 0 < t) :
    (|1 / (1 + t) ^ 2| : ℝ) • ((subst t : ℂ) ^ (w - 1) * (1 - (subst t : ℂ)) ^ (s - w - 1)) =
      (t : ℂ) ^ (w - 1) * ((1 + t : ℝ) : ℂ) ^ (-s) := by
  have h1t : 0 < 1 + t := by linarith
  set a : ℂ := ((1 + t : ℝ) : ℂ) with ha
  have ha0 : a ≠ 0 := ofReal_ne_zero.mpr h1t.ne'
  have harg : a.arg ≠ Real.pi := by
    rw [ha, arg_ofReal_of_nonneg h1t.le]; exact Real.pi_pos.ne
  have hinv : ∀ r : ℂ, (((1 + t)⁻¹ : ℝ) : ℂ) ^ r = a ^ (-r) := fun r => by
    rw [ofReal_inv, ← ha, inv_cpow _ _ harg, cpow_neg]
  have hx : (subst t : ℂ) ^ (w - 1) = (t : ℂ) ^ (w - 1) * a ^ (-(w - 1)) := by
    rw [subst, div_eq_mul_inv, ofReal_mul,
      mul_cpow_ofReal_nonneg ht.le (inv_nonneg.mpr h1t.le), hinv]
  have h1x : (1 - (subst t : ℂ)) ^ (s - w - 1) = a ^ (-(s - w - 1)) := by
    have : (1 - (subst t : ℂ)) = (((1 + t)⁻¹ : ℝ) : ℂ) := by
      have h1t' : (1 : ℂ) + t ≠ 0 := by exact_mod_cast h1t.ne'
      rw [subst]; push_cast; field_simp; ring
    rw [this, hinv]
  have hd : ((|1 / (1 + t) ^ 2| : ℝ) : ℂ) = a ^ (-(2 : ℂ)) := by
    rw [abs_of_pos (by positivity), cpow_neg, ha, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num,
      cpow_natCast]
    push_cast
    ring
  rw [real_smul, hd, hx, h1x]
  calc a ^ (-(2 : ℂ)) * ((t : ℂ) ^ (w - 1) * a ^ (-(w - 1)) * a ^ (-(s - w - 1)))
      = (t : ℂ) ^ (w - 1) * (a ^ (-(w - 1)) * a ^ (-(s - w - 1)) * a ^ (-(2 : ℂ))) := by ring
    _ = (t : ℂ) ^ (w - 1) * a ^ (-s) := by
      rw [← cpow_add _ _ ha0, ← cpow_add _ _ ha0]
      congr 2
      ring

/-- **The Beta integral as a Mellin transform**: for `0 < Re w < Re s`,
`∫_0^∞ t^{w-1} (1+t)^{-s} dt = K_s(w)` (substitute `t = x/(1-x)` in `Complex.betaIntegral w (s - w)`, then
`Complex.Gamma_mul_Gamma_eq_betaIntegral`). The integral converges absolutely. -/
theorem mellin_one_add_cpow_neg {s w : ℂ} (hw : 0 < w.re) (hws : w.re < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * ((1 + t : ℝ) : ℂ) ^ (-s)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w - 1) * ((1 + t : ℝ) : ℂ) ^ (-s) = KerS s w := by
  have hsw : 0 < (s - w).re := by rw [sub_re]; linarith
  set B : ℝ → ℂ := fun x => (x : ℂ) ^ (w - 1) * (1 - (x : ℂ)) ^ (s - w - 1) with hB
  have hBint : IntegrableOn B (Ioo 0 1) := by
    have := (betaIntegral_convergent hw hsw).1
    exact this.mono_set Ioo_subset_Ioc_self
  have heq : EqOn (fun t : ℝ => |1 / (1 + t) ^ 2| • B (subst t))
      (fun t : ℝ => (t : ℂ) ^ (w - 1) * ((1 + t : ℝ) : ℂ) ^ (-s)) (Ioi 0) :=
    fun t ht => subst_integrand (mem_Ioi.mp ht)
  have hint : IntegrableOn (fun t : ℝ => |1 / (1 + t) ^ 2| • B (subst t)) (Ioi 0) := by
    rw [← integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (fun t ht => hasDerivWithinAt_subst ht) injOn_subst, image_subst]
    exact hBint
  refine ⟨hint.congr_fun heq measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi heq,
    ← integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun t ht => hasDerivWithinAt_subst ht) injOn_subst, image_subst,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have hbeta : ∫ x in (0 : ℝ)..1, B x = betaIntegral w (s - w) := rfl
  rw [hbeta, KerS]
  have hG := Gamma_mul_Gamma_eq_betaIntegral hw hsw
  rw [add_sub_cancel] at hG
  rw [hG, mul_div_cancel_left₀ _ (Gamma_ne_zero_of_re_pos (by linarith))]

end GoldbachBoundaries.Paper2.M1
