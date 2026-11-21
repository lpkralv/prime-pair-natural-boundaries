import PrimePairNB.ThmA.G15_Kernel

/-!
# `∫_𝒮 dx/(z-x)` on vertical lines

The main statement is `integrable_Gamma_CauchyS_line` (used by `F0_split`). Helpers live in the namespace `GoldbachBoundaries.ThmA.GroupE`.

## Helpers (prefix `cauchy_`)

Throughout `v = slantDir κ`, `x_u = 1 - u v`, and `cauchy_g κ t u z = Γ(z) t^{-z} / (z - x_u)`.

* `cauchy_Gamma_CauchyS_eq`: `Γ(z) (∫_𝒮 dx/(z-x)) t^{-z} = v ∫_{(0,1-b]} cauchy_g κ t u z du`.
* `cauchy_integrable_prod`: `(y, u) ↦ cauchy_g κ t u (σ + iy)` is integrable on
  `ℝ × (0, 1-b]` for `σ = b` and for `σ > 1`. At `σ = b`, with `s = 1 - b - u` and
  `η = y + (1-b)κ = y - Im w_b`, `|b + iy - x_u|² ≥ s|η|/(1+|κ|)`, so the integrand is dominated by the
  product `|Γ(b+iy)| t^{-b} √(1+|κ|) |η|^{-1/2} · s^{-1/2}` of two integrable functions.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

namespace GroupE

/-- `Γ(z) t^{-z} / (z - x_u)` with `x_u = 1 - u v`. -/
def cauchy_g (κ t u : ℝ) (z : ℂ) : ℂ :=
  Gamma z * (t : ℂ) ^ (-z) / (z - 1 + (u : ℂ) * slantDir κ)

theorem cauchy_Gamma_CauchyS_eq (κ : ℝ) {b : ℝ} (hb : b ≤ 1) (t : ℝ) (z : ℂ) :
    Gamma z * CauchyS κ b z * (t : ℂ) ^ (-z) =
      slantDir κ * ∫ u in Ioc (0 : ℝ) (1 - b), cauchy_g κ t u z := by
  have hfun : (fun u : ℝ => cauchy_g κ t u z) =
      fun u : ℝ => (Gamma z * (t : ℂ) ^ (-z)) * (1 / (z - 1 + (u : ℂ) * slantDir κ)) := by
    funext u; simp only [cauchy_g]; ring
  rw [hfun, integral_const_mul, CauchyS, intervalIntegral.integral_of_le (by linarith)]
  ring

/-- `Γ` is bounded on a vertical line `Re z = σ > 0` and `‖Γ(σ + iy)‖` is integrable. -/
theorem cauchy_integrable_norm_Gamma {σ : ℝ} (hσ : 0 < σ) :
    Integrable fun y : ℝ => ‖Gamma (σ + y * I)‖ := by
  have h := TIdentity.integrable_Gamma_mul_of_bound hσ (q := fun _ => (1 : ℂ)) continuous_const
    (K := 1) (fun y => by simp)
  simpa using h.norm

theorem cauchy_measurable_abs_rpow (y₀ : ℝ) :
    Measurable fun y : ℝ => |y - y₀| ^ (-(1 / 2 : ℝ)) :=
  ((continuous_abs.comp (continuous_id.sub continuous_const)).measurable).pow_const _

/-- `|y - y₀|^{-1/2}` is integrable on `[y₀ - 1, y₀ + 1]`. -/
theorem cauchy_integrableOn_abs_rpow (y₀ : ℝ) :
    IntegrableOn (fun y : ℝ => |y - y₀| ^ (-(1 / 2 : ℝ))) (Icc (y₀ - 1) (y₀ + 1)) := by
  have h1 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (((-(1 / 2 : ℝ)) : ℝ) : ℂ)) volume (-1) 1 :=
    intervalIntegral.intervalIntegrable_cpow' (by simp; norm_num)
  have h2 := (h1.comp_sub_right y₀).norm
  have h3 : (fun x : ℝ => ‖((x - y₀ : ℝ) : ℂ) ^ (((-(1 / 2 : ℝ)) : ℝ) : ℂ)‖) =
      fun y : ℝ => |y - y₀| ^ (-(1 / 2 : ℝ)) := by
    funext x
    rw [Complex.norm_cpow_real, Complex.norm_real, Real.norm_eq_abs]
  rw [h3] at h2
  have h4 : -1 + y₀ = y₀ - 1 := by ring
  have h5 : 1 + y₀ = y₀ + 1 := by ring
  rw [h4, h5] at h2
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp h2

/-- `‖Γ(σ + iy)‖ |y - y₀|^{-1/2}` is integrable for `σ > 0`. -/
theorem cauchy_integrable_Gamma_rpow {σ : ℝ} (hσ : 0 < σ) (y₀ : ℝ) :
    Integrable fun y : ℝ => ‖Gamma (σ + y * I)‖ * |y - y₀| ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨M, hM⟩ := TIdentity.norm_Gamma_mul_one_add_abs_im_pow_le (a := σ) (a' := σ) hσ 0
  have hint : Integrable fun y : ℝ => ‖Gamma (σ + y * I)‖ +
      M * (Icc (y₀ - 1) (y₀ + 1)).indicator (fun y : ℝ => |y - y₀| ^ (-(1 / 2 : ℝ))) y :=
    (cauchy_integrable_norm_Gamma hσ).add
      (((cauchy_integrableOn_abs_rpow y₀).integrable_indicator measurableSet_Icc).const_mul M)
  refine hint.mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact ((TIdentity.continuous_Gamma_line hσ).norm.measurable.mul
      (cauchy_measurable_abs_rpow y₀)).aestronglyMeasurable
  · have hG : ‖Gamma (σ + y * I)‖ ≤ M := by
      simpa using hM (σ + y * I) (by simp) (by simp)
    have hG0 : 0 ≤ ‖Gamma (σ + y * I)‖ := norm_nonneg _
    have hr0 : 0 ≤ |y - y₀| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hG0 hr0)]
    by_cases hy : y ∈ Icc (y₀ - 1) (y₀ + 1)
    · rw [indicator_of_mem hy]
      nlinarith
    · rw [indicator_of_notMem hy, mul_zero, add_zero]
      have h1 : 1 ≤ |y - y₀| := by
        simp only [mem_Icc, not_and_or, not_le] at hy
        rcases hy with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have : |y - y₀| ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
      nlinarith

/-- The key lower bound on the line `Re z = b`: with `s = 1 - b - u ≥ 0` and `η = y + (1-b)κ`,
`s |η| ≤ (1 + |κ|) |b + iy - x_u|²`. -/
theorem cauchy_den_sq_ge (κ b y u : ℝ) (hs : 0 ≤ 1 - b - u) :
    (1 - b - u) * |y + (1 - b) * κ| ≤
      (1 + |κ|) * ‖(b : ℂ) + y * I - 1 + (u : ℂ) * slantDir κ‖ ^ 2 := by
  set s := 1 - b - u with hsdef
  set η := y + (1 - b) * κ with hη
  have hnorm : ‖(b : ℂ) + y * I - 1 + (u : ℂ) * slantDir κ‖ ^ 2 = s ^ 2 + (η - s * κ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [slantDir, add_re, sub_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, one_re,
      add_im, sub_im, mul_im, one_im]
    rw [hsdef, hη]; ring
  rw [hnorm]
  set m := max s |η - s * κ| with hm
  have hm1 : s ≤ m := le_max_left _ _
  have hm2 : |η - s * κ| ≤ m := le_max_right _ _
  have hη1 : |η| ≤ |η - s * κ| + s * |κ| := by
    calc |η| = |(η - s * κ) + s * κ| := by ring_nf
      _ ≤ |η - s * κ| + |s * κ| := abs_add_le _ _
      _ = |η - s * κ| + s * |κ| := by rw [abs_mul, abs_of_nonneg hs]
  have hk : 0 ≤ |κ| := abs_nonneg _
  have hm0 : 0 ≤ m := le_trans hs hm1
  have hsq : m ^ 2 ≤ s ^ 2 + (η - s * κ) ^ 2 := by
    rcases le_total s |η - s * κ| with h | h
    · rw [hm, max_eq_right h, sq_abs]; nlinarith
    · rw [hm, max_eq_left h]; nlinarith [sq_nonneg (η - s * κ)]
  calc s * |η| ≤ s * (|η - s * κ| + s * |κ|) := mul_le_mul_of_nonneg_left hη1 hs
    _ ≤ m * (m + m * |κ|) := by
        apply mul_le_mul hm1 _ (by positivity) hm0
        nlinarith
    _ = (1 + |κ|) * m ^ 2 := by ring
    _ ≤ (1 + |κ|) * (s ^ 2 + (η - s * κ) ^ 2) := by gcongr

/-- `1/|b + iy - x_u| ≤ √(1+|κ|) |η|^{-1/2} s^{-1/2}` for `s > 0`, `η ≠ 0`. -/
theorem cauchy_inv_norm_den_le (κ b y u : ℝ) (hs : 0 < 1 - b - u) (hη : y + (1 - b) * κ ≠ 0) :
    ‖(b : ℂ) + y * I - 1 + (u : ℂ) * slantDir κ‖⁻¹ ≤
      Real.sqrt (1 + |κ|) * |y + (1 - b) * κ| ^ (-(1 / 2 : ℝ)) *
        (1 - b - u) ^ (-(1 / 2 : ℝ)) := by
  set s := 1 - b - u with hsdef
  set η := y + (1 - b) * κ with hηdef
  set w := (b : ℂ) + y * I - 1 + (u : ℂ) * slantDir κ with hw
  have h := cauchy_den_sq_ge κ b y u hs.le
  rw [← hsdef, ← hηdef, ← hw] at h
  have hηpos : 0 < |η| := abs_pos.mpr hη
  have hK : 0 < 1 + |κ| := by positivity
  have hwpos : 0 < ‖w‖ := by
    by_contra hcon
    have : ‖w‖ = 0 := le_antisymm (not_lt.mp hcon) (norm_nonneg _)
    rw [this] at h
    nlinarith [mul_pos hs hηpos]
  have hA : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  have hB : 0 < |η| ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hηpos _
  have hA2 : (s ^ (1 / 2 : ℝ)) ^ 2 = s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]; norm_num
  have hB2 : (|η| ^ (1 / 2 : ℝ)) ^ 2 = |η| := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hηpos.le]; norm_num
  have hS2 : Real.sqrt (1 + |κ|) ^ 2 = 1 + |κ| := Real.sq_sqrt hK.le
  have hS : 0 < Real.sqrt (1 + |κ|) := Real.sqrt_pos.mpr hK
  rw [Real.rpow_neg hs.le, Real.rpow_neg hηpos.le]
  -- `s^{1/2} |η|^{1/2} ≤ √K ‖w‖`
  have hkey : s ^ (1 / 2 : ℝ) * |η| ^ (1 / 2 : ℝ) ≤ Real.sqrt (1 + |κ|) * ‖w‖ := by
    have hsq : (s ^ (1 / 2 : ℝ) * |η| ^ (1 / 2 : ℝ)) ^ 2 ≤ (Real.sqrt (1 + |κ|) * ‖w‖) ^ 2 := by
      rw [mul_pow, mul_pow, hA2, hB2, hS2]; exact h
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  rw [inv_le_iff_one_le_mul₀ hwpos]
  calc (1 : ℝ) = (s ^ (1 / 2 : ℝ) * |η| ^ (1 / 2 : ℝ))⁻¹ * (s ^ (1 / 2 : ℝ) * |η| ^ (1 / 2 : ℝ)) := by
        rw [inv_mul_cancel₀ (by positivity)]
    _ ≤ (s ^ (1 / 2 : ℝ) * |η| ^ (1 / 2 : ℝ))⁻¹ * (Real.sqrt (1 + |κ|) * ‖w‖) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (Real.sqrt (1 + |κ|) * (|η| ^ (1 / 2 : ℝ))⁻¹ * (s ^ (1 / 2 : ℝ))⁻¹) * ‖w‖ := by
        rw [mul_inv]; ring

/-- The product measure `dy × du` on `ℝ × (0, 1-b]`. -/
abbrev cauchy_μ (b : ℝ) : Measure (ℝ × ℝ) := volume.prod (volume.restrict (Ioc (0 : ℝ) (1 - b)))

theorem cauchy_aestronglyMeasurable_prod {κ σ t : ℝ} (b : ℝ) (hσ : 0 < σ) (ht : 0 < t) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => cauchy_g κ t p.2 (σ + p.1 * I)) (cauchy_μ b) := by
  have hnum : Continuous fun p : ℝ × ℝ =>
      Gamma (σ + p.1 * I) * (t : ℂ) ^ (-((σ : ℂ) + p.1 * I)) :=
    ((TIdentity.continuous_Gamma_line hσ).comp continuous_fst).mul
      (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast ht.ne')))
  have hden : Continuous fun p : ℝ × ℝ => (σ : ℂ) + p.1 * I - 1 + (p.2 : ℂ) * slantDir κ := by
    fun_prop
  exact (hnum.measurable.div hden.measurable).aestronglyMeasurable

theorem cauchy_norm_g (κ σ t u y : ℝ) (ht : 0 < t) :
    ‖cauchy_g κ t u (σ + y * I)‖ =
      ‖Gamma (σ + y * I)‖ * t ^ (-σ) * ‖(σ : ℂ) + y * I - 1 + (u : ℂ) * slantDir κ‖⁻¹ := by
  simp only [cauchy_g, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, div_eq_mul_inv]
  simp

/-- Fubini integrability on the line `Re z = b`. -/
theorem cauchy_integrable_prod_b {κ b t : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) (ht : 0 < t) :
    Integrable (fun p : ℝ × ℝ => cauchy_g κ t p.2 (b + p.1 * I)) (cauchy_μ b) := by
  set y₀ : ℝ := -((1 - b) * κ) with hy₀
  have hf : Integrable fun y : ℝ =>
      t ^ (-b) * Real.sqrt (1 + |κ|) * (‖Gamma (b + y * I)‖ * |y - y₀| ^ (-(1 / 2 : ℝ))) :=
    (cauchy_integrable_Gamma_rpow hb.1 y₀).const_mul _
  have hg : Integrable (fun u : ℝ => (1 - b - u) ^ (-(1 / 2 : ℝ)))
      (volume.restrict (Ioc (0 : ℝ) (1 - b))) := by
    have h1 := (intervalIntegral.intervalIntegrable_rpow' (a := 1 - b) (b := 0)
      (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_left (1 - b)
    simp only [sub_self, sub_zero] at h1
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [hb.2])).mp h1
  refine (hf.mul_prod hg).mono' (cauchy_aestronglyMeasurable_prod b hb.1 ht) ?_
  have h1 : ∀ᵐ p : ℝ × ℝ ∂(cauchy_μ b), p.1 ≠ y₀ :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume y₀)
  have h2 : ∀ᵐ p : ℝ × ℝ ∂(cauchy_μ b), p.2 ∈ Ioo (0 : ℝ) (1 - b) := by
    refine Measure.quasiMeasurePreserving_snd.ae ?_
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [h1, h2] with p hp1 hp2
  obtain ⟨y, u⟩ := p
  simp only at hp1 hp2 ⊢
  have hs : 0 < 1 - b - u := by linarith [hp2.2]
  have hη : y + (1 - b) * κ ≠ 0 := fun h => hp1 (by rw [hy₀]; linarith)
  have hyη : y - y₀ = y + (1 - b) * κ := by rw [hy₀]; ring
  rw [cauchy_norm_g κ b t u y ht, hyη]
  have hbd := cauchy_inv_norm_den_le κ b y u hs hη
  have h0 : 0 ≤ ‖Gamma (b + y * I)‖ * t ^ (-b) := by positivity
  calc ‖Gamma (b + y * I)‖ * t ^ (-b) * ‖(b : ℂ) + y * I - 1 + (u : ℂ) * slantDir κ‖⁻¹
      ≤ ‖Gamma (b + y * I)‖ * t ^ (-b) * (Real.sqrt (1 + |κ|) * |y + (1 - b) * κ| ^ (-(1 / 2 : ℝ)) *
        (1 - b - u) ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hbd h0
    _ = _ := by ring

/-- Fubini integrability on a line `Re z = σ > 1`. -/
theorem cauchy_integrable_prod_gt {κ b σ t : ℝ} (hσ : 1 < σ) (ht : 0 < t) :
    Integrable (fun p : ℝ × ℝ => cauchy_g κ t p.2 (σ + p.1 * I)) (cauchy_μ b) := by
  have hf : Integrable fun y : ℝ => ‖Gamma (σ + y * I)‖ * t ^ (-σ) * (σ - 1)⁻¹ :=
    ((cauchy_integrable_norm_Gamma (by linarith)).mul_const _).mul_const _
  have hg : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc (0 : ℝ) (1 - b))) :=
    integrable_const _
  refine (hf.mul_prod hg).mono' (cauchy_aestronglyMeasurable_prod b (by linarith) ht) ?_
  have h2 : ∀ᵐ p : ℝ × ℝ ∂(cauchy_μ b), p.2 ∈ Ioc (0 : ℝ) (1 - b) :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [h2] with p hp2
  obtain ⟨y, u⟩ := p
  simp only at hp2 ⊢
  rw [cauchy_norm_g κ σ t u y ht, mul_one]
  have hre : σ - 1 ≤ ‖(σ : ℂ) + y * I - 1 + (u : ℂ) * slantDir κ‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp [slantDir]; linarith [hp2.1]
  have h0 : 0 ≤ ‖Gamma (σ + y * I)‖ * t ^ (-σ) := by positivity
  exact mul_le_mul_of_nonneg_left (inv_anti₀ (by linarith) hre) h0

theorem cauchy_integrable_prod {κ b σ t : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) (hσ : σ = b ∨ 1 < σ)
    (ht : 0 < t) :
    Integrable (fun p : ℝ × ℝ => cauchy_g κ t p.2 (σ + p.1 * I)) (cauchy_μ b) := by
  rcases hσ with rfl | hσ
  · exact cauchy_integrable_prod_b hb ht
  · exact cauchy_integrable_prod_gt hσ ht

/-- `Γ (∫_𝒮 dx/(z-x)) t^{-z}` is integrable on the lines `Re z = b` (where the kernel has the
integrable singularity at `w_b`) and `Re z = σ > 1`. -/
theorem integrable_Gamma_CauchyS_line {κ b σ t : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
    (hσ : σ = b ∨ 1 < σ) (ht : 0 < t) :
    Integrable fun y : ℝ =>
      Gamma (σ + y * I) * CauchyS κ b (σ + y * I) * (t : ℂ) ^ (-((σ : ℂ) + y * I)) := by
  have h := ((cauchy_integrable_prod (κ := κ) hb hσ ht).integral_prod_left).const_mul
    (slantDir κ)
  refine h.congr (Eventually.of_forall fun y => ?_)
  exact (cauchy_Gamma_CauchyS_eq κ hb.2.le t ((σ : ℂ) + y * I)).symm

end GroupE

end GoldbachBoundaries.ThmA
