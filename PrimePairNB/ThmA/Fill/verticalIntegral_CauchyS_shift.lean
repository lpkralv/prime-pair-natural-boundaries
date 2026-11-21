import PrimePairNB.ThmA.Fill.ECommonCauchy

/-!
# `verticalIntegral_CauchyS_shift`

`VI'(Γ (∫_𝒮 dx/(z-x)) t^{-z}; c) = L(t) + VI'(Γ (∫_𝒮 dx/(z-x)) t^{-z}; b)`, no RH.

Proof: Fubini on both lines (`cauchy_integrable_prod`, `ECommonCauchy.lean`) writes each side as
`v ∫_{(0,1-b]} VI'(Γ(z) t^{-z}/(z - x_u)) du`; for `u ∈ (0, 1-b)` the pole `x_u = 1 - uv` has
`b < Re x_u < c` and `verticalIntegral'_eq_add_of_simplePole` gives the residue
`Γ(x_u) t^{-x_u}`; the endpoint `u = 1-b` is null; `v ∫ Γ(x_u) t^{-x_u} du = L(t)`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries.ThmA

namespace GroupE

/-- Horizontal integrals tend to `0` under a uniform `K (1+|y|)⁻¹` bound (as
`TIdentity.tendsto_integral_kernelQ_horizontal`). -/
theorem cauchy_tendsto_horizontal {f : ℂ → ℂ} {σ σ' K Y : ℝ} (hσ : σ ≤ σ')
    (hK : ∀ y : ℝ, Y ≤ |y| → ∀ x ∈ Icc σ σ', ‖f (x + y * I)‖ ≤ K * (1 + |y|)⁻¹)
    {l : Filter ℝ} (hl : Tendsto (fun y : ℝ => |y|) l atTop) :
    Tendsto (fun y : ℝ => ∫ x in σ..σ', f (x + y * I)) l (𝓝 0) := by
  have hlim : Tendsto (fun y : ℝ => K * (1 + |y|)⁻¹ * |σ' - σ|) l (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => (1 + |y|)⁻¹) l (𝓝 0) :=
      (tendsto_atTop_add_const_left _ 1 hl).inv_tendsto_atTop
    simpa using (h1.const_mul K).mul_const |σ' - σ|
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hl.eventually (eventually_ge_atTop Y)] with y hy
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [uIoc_of_le hσ] at hx
  exact hK y hy x ⟨le_of_lt hx.1, hx.2⟩

/-- `|Γ(z) t^{-z}/(z - x_u)| ≤ K (1+|y|)⁻¹` on `b ≤ Re z ≤ c`, `|Im z| ≥ |uκ| + 1`. -/
theorem cauchy_g_bound (κ : ℝ) {b c t : ℝ} (u : ℝ) (hb : 0 < b) (ht : 0 < t) :
    ∃ K : ℝ, ∀ y : ℝ, |u * κ| + 1 ≤ |y| → ∀ x ∈ Icc b c,
      ‖cauchy_g κ t u (x + y * I)‖ ≤ K * (1 + |y|)⁻¹ := by
  obtain ⟨CΓ, hCΓ⟩ := TIdentity.norm_Gamma_mul_one_add_abs_im_pow_le (a := b) (a' := c) hb 1
  refine ⟨(t ^ (-b) + t ^ (-c)) * CΓ, fun y hy x hx => ?_⟩
  have hpos : 0 < 1 + |y| := by positivity
  rw [cauchy_norm_g κ x t u y ht]
  have hT : t ^ (-x) ≤ t ^ (-b) + t ^ (-c) := by
    have h1 : 0 ≤ t ^ (-b) := Real.rpow_nonneg ht.le _
    have h2 : 0 ≤ t ^ (-c) := Real.rpow_nonneg ht.le _
    rcases le_or_gt 1 t with h | h
    · have := Real.rpow_le_rpow_of_exponent_le h (show -x ≤ -b by linarith [hx.1])
      linarith
    · have := Real.rpow_le_rpow_of_exponent_ge ht h.le (show -c ≤ -x by linarith [hx.2])
      linarith
  have hG := hCΓ (x + y * I) (by simp [hx.1]) (by simp [hx.2])
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add, pow_one] at hG
  have hden : 1 ≤ ‖(x : ℂ) + y * I - 1 + (u : ℂ) * slantDir κ‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    have him : ((x : ℂ) + y * I - 1 + (u : ℂ) * slantDir κ).im = y + u * κ := by simp [slantDir]
    rw [him]
    have := abs_sub_abs_le_abs_sub y (-(u * κ))
    rw [abs_neg, sub_neg_eq_add] at this
    linarith
  have hinv : ‖(x : ℂ) + y * I - 1 + (u : ℂ) * slantDir κ‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hden
  have hG' : ‖Gamma (x + y * I)‖ ≤ CΓ * (1 + |y|)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact hG
  have h0 : 0 ≤ ‖Gamma (x + y * I)‖ := norm_nonneg _
  have hT0 : 0 ≤ t ^ (-x) := Real.rpow_nonneg ht.le _
  calc ‖Gamma (x + y * I)‖ * t ^ (-x) * ‖(x : ℂ) + y * I - 1 + (u : ℂ) * slantDir κ‖⁻¹
      ≤ ‖Gamma (x + y * I)‖ * t ^ (-x) * 1 := mul_le_mul_of_nonneg_left hinv (by positivity)
    _ ≤ (CΓ * (1 + |y|)⁻¹) * (t ^ (-b) + t ^ (-c)) := by
        rw [mul_one]; exact mul_le_mul hG' hT hT0 (le_trans h0 hG')
    _ = (t ^ (-b) + t ^ (-c)) * CΓ * (1 + |y|)⁻¹ := by ring

/-- The shift for one point `x_u` of `𝒮`, `0 ≤ u < 1 - b`: residue `Γ(x_u) t^{-x_u}`. -/
theorem cauchy_shift_single {κ b c t u : ℝ} (hb : 0 < b) (hc : 1 < c) (ht : 0 < t)
    (hu0 : 0 ≤ u) (hu : u < 1 - b)
    (hleft : Integrable fun y : ℝ => cauchy_g κ t u (b + y * I))
    (hright : Integrable fun y : ℝ => cauchy_g κ t u (c + y * I)) :
    VerticalIntegral' (cauchy_g κ t u) c =
      Gamma (1 - (u : ℂ) * slantDir κ) * (t : ℂ) ^ (-(1 - (u : ℂ) * slantDir κ)) +
        VerticalIntegral' (cauchy_g κ t u) b := by
  set p : ℂ := 1 - (u : ℂ) * slantDir κ with hp
  have hpre : p.re = 1 - u := by simp [hp, slantDir]
  have hden : ∀ z : ℂ, z - 1 + (u : ℂ) * slantDir κ = z - p := fun z => by rw [hp]; ring
  obtain ⟨K, hK⟩ := cauchy_g_bound κ (c := c) u hb ht
  refine TIdentity.verticalIntegral'_eq_add_of_simplePole (p := p)
    ⟨by rw [hpre]; linarith, by rw [hpre]; linarith⟩ ?_ ?_
    (cauchy_tendsto_horizontal (by linarith) hK tendsto_abs_atBot_atTop)
    (cauchy_tendsto_horizontal (by linarith) hK tendsto_abs_atTop_atTop) hleft hright
  · rintro z ⟨hz, hzp⟩
    have hzre : z.re ∈ Icc b c := (mem_reProdIm.mp hz).1
    refine DifferentiableAt.differentiableWithinAt ?_
    have hne : z - 1 + (u : ℂ) * slantDir κ ≠ 0 := by
      rw [hden]; exact sub_ne_zero.mpr hzp
    show DifferentiableAt ℂ (fun z : ℂ =>
      Gamma z * (t : ℂ) ^ (-z) / (z - 1 + (u : ℂ) * slantDir κ)) z
    exact ((TIdentity.differentiableAt_Gamma_of_re_pos (by linarith [hzre.1])).mul
      (TIdentity.differentiableAt_ofReal_cpow_neg ht z)).div (by fun_prop) hne
  · set ψ : ℂ → ℂ := fun z => Gamma z * (t : ℂ) ^ (-z) with hψ
    have hψd : DifferentiableAt ℂ ψ p :=
      (TIdentity.differentiableAt_Gamma_of_re_pos (by rw [hpre]; linarith)).mul
        (TIdentity.differentiableAt_ofReal_cpow_neg ht p)
    have hB : (dslope ψ p) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
      ((continuousAt_dslope_same.mpr hψd).tendsto.isBigO_one ℂ).mono nhdsWithin_le_nhds
    refine hB.congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzp : z - p ≠ 0 := sub_ne_zero.mpr hz
    rw [dslope_of_ne _ hz, slope_def_field]
    simp only [Pi.sub_apply, cauchy_g, hden, hψ]
    field_simp

/-- Fubini: `VI'(Γ (∫_𝒮) t^{-z}; σ) = v ∫_{(0,1-b]} VI'(Γ(z) t^{-z}/(z - x_u); σ) du`. -/
theorem cauchy_VI_eq {κ b σ t : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) (hσ : σ = b ∨ 1 < σ) (ht : 0 < t) :
    VerticalIntegral' (fun z => Gamma z * CauchyS κ b z * (t : ℂ) ^ (-z)) σ =
      slantDir κ * ∫ u in Ioc (0 : ℝ) (1 - b), VerticalIntegral' (cauchy_g κ t u) σ := by
  have hint := cauchy_integrable_prod (κ := κ) hb hσ ht
  have hswap := integral_integral_swap (f := fun (y u : ℝ) => cauchy_g κ t u (σ + y * I)) hint
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
  simp_rw [cauchy_Gamma_CauchyS_eq κ hb.2.le t]
  rw [integral_const_mul, hswap, integral_const_mul, integral_const_mul]
  ring

theorem cauchy_shift_main {κ b c t : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) (hc : 1 < c)
    (ht : 0 < t) :
    VerticalIntegral' (fun z => Gamma z * CauchyS κ b z * (t : ℂ) ^ (-z)) c =
      Lf κ b t + VerticalIntegral' (fun z => Gamma z * CauchyS κ b z * (t : ℂ) ^ (-z)) b := by
  rw [cauchy_VI_eq hb (Or.inr hc) ht, cauchy_VI_eq hb (Or.inl rfl) ht]
  have hpc := cauchy_integrable_prod (κ := κ) hb (Or.inr hc) ht
  have hpb := cauchy_integrable_prod (κ := κ) hb (Or.inl rfl) ht
  set A : ℝ → ℂ := fun u =>
    Gamma (1 - (u : ℂ) * slantDir κ) * (t : ℂ) ^ (-(1 - (u : ℂ) * slantDir κ)) with hA
  have hae : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) (1 - b))),
      VerticalIntegral' (cauchy_g κ t u) c = A u + VerticalIntegral' (cauchy_g κ t u) b := by
    have hIoo : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) (1 - b))), u ∈ Ioo (0 : ℝ) (1 - b) := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]; exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hpc.prod_left_ae, hpb.prod_left_ae, hIoo] with u hc' hb' hu
    exact cauchy_shift_single hb.1 hc ht hu.1.le hu.2 hb' hc'
  have hVIint : Integrable (fun u => VerticalIntegral' (cauchy_g κ t u) b)
      (volume.restrict (Ioc (0 : ℝ) (1 - b))) := by
    have := (hpb.integral_prod_right.const_mul I).const_mul (1 / (2 * Real.pi * I) : ℂ)
    simpa [VerticalIntegral', VerticalIntegral, smul_eq_mul] using this
  have hAint : Integrable A (volume.restrict (Ioc (0 : ℝ) (1 - b))) := by
    have hcont : ContinuousOn A (Icc 0 (1 - b)) := by
      intro u hu
      apply ContinuousAt.continuousWithinAt
      have hre : 0 < (1 - (u : ℂ) * slantDir κ).re := by
        simp [slantDir]; linarith [hu.2, hb.1]
      have h1 : ContinuousAt (fun u : ℝ => 1 - (u : ℂ) * slantDir κ) u := by fun_prop
      exact (ContinuousAt.comp (f := fun u : ℝ => 1 - (u : ℂ) * slantDir κ)
        (TIdentity.differentiableAt_Gamma_of_re_pos hre).continuousAt h1).mul
        (ContinuousAt.comp (f := fun u : ℝ => 1 - (u : ℂ) * slantDir κ)
          (TIdentity.differentiableAt_ofReal_cpow_neg ht _).continuousAt h1)
    exact (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [integral_congr_ae hae, integral_add hAint hVIint, Lf,
    intervalIntegral.integral_of_le (by linarith [hb.2])]
  ring

end GroupE

/-- **Shift of the Cauchy part** (`∫_𝒮 dx/(z-x)`): the residues at the points of `𝒮` sum
to `L(t)`. Unconditional.

Sketch. Fubini (absolute integrability on `{Re z = c} × [0,1-b]` and on `{Re z = b} × [0,1-b]`: on
`Re z = b` the kernel `1/|z - x|` is integrable in `(y, u)` near `w_b`) turns both sides into
`v ∫_0^{1-b} (…) du`. For fixed `u ∈ [0, 1-b)`, `x = 1 - uv` has `b < Re x ≤ 1 < c`, and
`verticalIntegral'_eq_add_of_simplePole` (`TIdentity/Basic.lean`) for `Γ(z)t^{-z}/(z-x)` gives the
residue `Γ(x)t^{-x}`; the endpoint `u = 1-b` is null. -/
theorem verticalIntegral_CauchyS_shift {κ b c t : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) (hc : 1 < c)
    (ht : 0 < t) :
    VerticalIntegral' (fun z => Gamma z * CauchyS κ b z * (t : ℂ) ^ (-z)) c =
      Lf κ b t + VerticalIntegral' (fun z => Gamma z * CauchyS κ b z * (t : ℂ) ^ (-z)) b :=
  GroupE.cauchy_shift_main hb hc ht

end GoldbachBoundaries.ThmA
