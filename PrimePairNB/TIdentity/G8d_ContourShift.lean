import PrimePairNB.TIdentity.G7d_QcontBound
import PrimePairNB.TIdentity.G8b_IntegrableOneLt
import PrimePairNB.TIdentity.G8c_IntegrableRH

/-!
# the contour shift of step (1)

`(2πi)⁻¹ ∫_{(c)} t^{-z} Γ(z) Q(z) dz = 1/t + (2πi)⁻¹ ∫_{(b)} t^{-z} Γ(z) Q(z) dz` under RH, for
`1/2 < b < 1 < c`, `t > 0`: `verticalIntegral'_eq_add_of_simplePole` with `p = 1`, `A = 1/t`.

`analyticAt_Qcont_of_RH` (shared with `G8c_IntegrableRH`) is in `Basic.lean`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries

namespace TIdentity

/-- `Γ` is differentiable on `Re z > 0`. -/
theorem differentiableAt_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ Gamma z :=
  differentiableAt_Gamma _ fun m h => by
    rw [h] at hz
    simp at hz
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- `z ↦ t^{-z}` is entire for `t > 0`. -/
theorem differentiableAt_ofReal_cpow_neg {t : ℝ} (ht : 0 < t) (z : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ => (t : ℂ) ^ (-z)) z :=
  differentiableAt_id.neg.const_cpow (Or.inl (by exact_mod_cast ht.ne'))

/-- `|t^{-z}| = t^{-Re z}` makes `kernelQ t` integrable on any line where `Γ Q` is. -/
theorem integrable_kernelQ {σ t : ℝ} (ht : 0 < t)
    (h : Integrable fun y : ℝ => Gamma (σ + y * I) * Qcont (σ + y * I)) :
    Integrable fun y : ℝ => kernelQ t (σ + y * I) := by
  refine Integrable.mono' (h.norm.const_mul (t ^ (-σ))) ?_ (Eventually.of_forall fun y => ?_)
  · have hc : Continuous fun y : ℝ => (t : ℂ) ^ (-((σ : ℂ) + y * I)) :=
      Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast ht.ne'))
    exact hc.aestronglyMeasurable.mul h.aestronglyMeasurable
  · simp only [kernelQ, norm_mul]
    rw [norm_cpow_eq_rpow_re_of_pos ht]
    simp

/-- Uniform bound on the horizontal segments: under RH, for `1/2 < b ≤ c`, `t > 0`,
`|kernelQ t (x + iy)| ≤ K (1 + |y|)⁻¹` for `x ∈ [b, c]`, `|y| ≥ 4`
(`norm_Qcont_le_log` and the decay of `Γ` with `n = 2`). -/
theorem norm_kernelQ_le (hRH : RiemannHypothesis) {b c t : ℝ} (hb : 1 / 2 < b) (ht : 0 < t) :
    ∃ K : ℝ, ∀ y : ℝ, 4 ≤ |y| → ∀ x ∈ Icc b c,
      ‖kernelQ t (x + y * I)‖ ≤ K * (1 + |y|)⁻¹ := by
  obtain ⟨CΓ, hCΓ⟩ := norm_Gamma_mul_one_add_abs_im_pow_le (a := b) (a' := c) (by linarith) 2
  obtain ⟨C, hC⟩ := norm_Qcont_le_log hRH (ε := b - 1 / 2) (by linarith)
  refine ⟨(t ^ (-b) + t ^ (-c)) * |C| * CΓ, fun y hy x hx => ?_⟩
  have hpos : 0 < 1 + |y| := by positivity
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have him : ((x : ℂ) + y * I).im = y := by simp
  -- the factor `t^{-z}`
  have hT : ‖(t : ℂ) ^ (-((x : ℂ) + y * I))‖ ≤ t ^ (-b) + t ^ (-c) := by
    rw [norm_cpow_eq_rpow_re_of_pos ht]
    simp only [neg_re, hre]
    have h1 : 0 ≤ t ^ (-b) := Real.rpow_nonneg ht.le _
    have h2 : 0 ≤ t ^ (-c) := Real.rpow_nonneg ht.le _
    rcases le_or_gt 1 t with h | h
    · have := Real.rpow_le_rpow_of_exponent_le h (show -x ≤ -b by linarith [hx.1])
      linarith
    · have := Real.rpow_le_rpow_of_exponent_ge ht h.le (show -c ≤ -x by linarith [hx.2])
      linarith
  -- the factor `Γ`
  have hG := hCΓ (x + y * I) (by rw [hre]; exact hx.1) (by rw [hre]; exact hx.2)
  rw [him] at hG
  -- the factor `Q`
  have hQ : ‖Qcont (x + y * I)‖ ≤ |C| * (1 + |y|) := by
    have h1 := hC (x + y * I) (by rw [hre]; linarith [hx.1]) (by rw [him]; exact hy)
    rw [him] at h1
    have hlog0 : 0 ≤ Real.log |y| := Real.log_nonneg (by linarith)
    have hlog1 : Real.log |y| ≤ 1 + |y| := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < |y|)
      linarith
    exact h1.trans (le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) hlog0)
      (mul_le_mul_of_nonneg_left hlog1 (abs_nonneg C)))
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  simp only [kernelQ, norm_mul]
  have hT0 : 0 ≤ t ^ (-b) + t ^ (-c) := by positivity
  calc ‖(t : ℂ) ^ (-((x : ℂ) + y * I))‖ * (‖Gamma (x + y * I)‖ * ‖Qcont (x + y * I)‖) * (1 + |y|)
      ≤ (t ^ (-b) + t ^ (-c)) * (‖Gamma (x + y * I)‖ * (|C| * (1 + |y|))) * (1 + |y|) := by
        gcongr
    _ = (t ^ (-b) + t ^ (-c)) * |C| * (‖Gamma (x + y * I)‖ * (1 + |y|) ^ 2) := by ring
    _ ≤ (t ^ (-b) + t ^ (-c)) * |C| * CΓ :=
        mul_le_mul_of_nonneg_left hG (mul_nonneg hT0 (abs_nonneg C))

/-- The horizontal integrals tend to `0` along any filter on which `|y| → ∞`. -/
theorem tendsto_integral_kernelQ_horizontal (hRH : RiemannHypothesis) {b c t : ℝ} (hb : 1 / 2 < b)
    (hbc : b ≤ c) (ht : 0 < t) {l : Filter ℝ} (hl : Tendsto (fun y : ℝ => |y|) l atTop) :
    Tendsto (fun y : ℝ => ∫ x in b..c, kernelQ t (x + y * I)) l (𝓝 0) := by
  obtain ⟨K, hK⟩ := norm_kernelQ_le hRH (c := c) hb ht
  have hlim : Tendsto (fun y : ℝ => K * (1 + |y|)⁻¹ * |c - b|) l (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => (1 + |y|)⁻¹) l (𝓝 0) :=
      (tendsto_atTop_add_const_left _ 1 hl).inv_tendsto_atTop
    simpa using (h1.const_mul K).mul_const |c - b|
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hl.eventually (eventually_ge_atTop 4)] with y hy
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [uIoc_of_le hbc] at hx
  exact hK y hy x ⟨le_of_lt hx.1, hx.2⟩

/-- Near `z = 1`, `kernelQ t - (1/t)/(z - 1)` is bounded: `Qcont = (z - 1)⁻¹ g` with `g` analytic,
`g(1) = 1` (`hasResidue_Qcont_one`), so the difference is the difference quotient of
`ψ(z) = t^{-z} Γ(z) g(z)` at `1`, and `ψ(1) = 1/t`. -/
theorem kernelQ_sub_pole_isBigO {t : ℝ} (ht : 0 < t) :
    (kernelQ t - fun s => 1 / (t : ℂ) / (s - 1)) =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
  have hm : MeromorphicAt Qcont 1 := meromorphicAt_Qcont (by norm_num)
  have hord := hasResidue_Qcont_one.meromorphicOrderAt_eq_neg_one hm one_ne_zero
  obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hm).mp hord
  -- `g 1 = 1`
  have hg1 : g 1 = 1 := by
    have h1 : Tendsto g (𝓝[≠] (1 : ℂ)) (𝓝 (g 1)) :=
      hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto g (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
      refine (hasResidue_Qcont_one : Tendsto _ _ _).congr' ?_
      filter_upwards [hfg, self_mem_nhdsWithin] with z hz hz1
      have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
      rw [hz, smul_eq_mul, zpow_neg_one, ← mul_assoc, mul_inv_cancel₀ hz1', one_mul]
    exact tendsto_nhds_unique h1 h2
  set ψ : ℂ → ℂ := fun z => (t : ℂ) ^ (-z) * Gamma z * g z with hψdef
  have hψd : DifferentiableAt ℂ ψ 1 :=
    ((differentiableAt_ofReal_cpow_neg ht 1).mul (differentiableAt_Gamma_of_re_pos (by norm_num))).mul
      hg.differentiableAt
  have hψ1 : ψ 1 = 1 / (t : ℂ) := by
    simp only [hψdef, cpow_neg_one, Gamma_one, hg1, mul_one, one_div]
  have hB : (dslope ψ 1) =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) :=
    ((continuousAt_dslope_same.mpr hψd).tendsto.isBigO_one ℂ).mono nhdsWithin_le_nhds
  refine hB.congr' ?_ EventuallyEq.rfl
  filter_upwards [hfg, self_mem_nhdsWithin] with z hz hz1
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  rw [dslope_of_ne _ hz1, slope_def_field, hψ1]
  simp only [Pi.sub_apply, kernelQ, hz, smul_eq_mul, zpow_neg_one, hψdef]
  field_simp

/-- **The shift of step (1):** under RH, for `1/2 < b < 1 < c` and `t > 0`,
`(2πi)⁻¹ ∫_{(c)} t^{-z} Γ(z) Q(z) dz = 1/t + (2πi)⁻¹ ∫_{(b)} t^{-z} Γ(z) Q(z) dz`.
(Between the lines, `ΓQ` has only the pole `z = 1`, with residue `t^{-1}`. The
horizontal connectors at `Im z = ±U` tend to `0` by the growth bound for `Q` and Stirling.)

Proof sketch. Apply `verticalIntegral'_eq_add_of_simplePole` with `p = 1`, `A = 1/t`.
* Holomorphy on `[b, c] × ℝ \ {1}`: `t^{-z}` entire, `Γ` holomorphic on `Re > 0`, `Qcont` analytic
  on `{Re > 0} \ Σ` and `Σ ∩ {Re > 1/2} = {1}` (`lem_Sigma_iv_proof`).
* Pole: `Qcont - 1/(z-1)` is analytic at `1` (`analyticAt_Qcont_sub_sum` with `S = {1}`, or the
  residue `hasResidue_Qcont_one` plus `meromorphicAt_Qcont`), and `t^{-z}Γ(z)` is analytic at `1`
  with value `1/t`, so `kernelQ t - (1/t)/(z-1)` is bounded near `1`.
* Horizontal integrals: for `|y| ≥ 4`, `|kernelQ t (x+iy)| ≤ max(t^{-b}, t^{-c}) · C log|y| ·
  C'(1+|y|)^{-2}` uniformly in `x ∈ [b, c]` (`norm_Qcont_le_log`, `ε = b - 1/2`;
  `norm_Gamma_mul_one_add_abs_im_pow_le`), which tends to `0`.
* Integrability on both lines: `integrable_Gamma_mul_Qcont_of_RH`, `..._of_one_lt`, times the
  constant-modulus factor `|t^{-z}| = t^{-Re z}`. -/
theorem verticalIntegral'_kernelQ_shift (hRH : RiemannHypothesis) {b c t : ℝ}
    (hb : 1 / 2 < b) (hb1 : b < 1) (hc : 1 < c) (ht : 0 < t) :
    VerticalIntegral' (kernelQ t) c = 1 / (t : ℂ) + VerticalIntegral' (kernelQ t) b := by
  have hbc : b ≤ c := by linarith
  refine verticalIntegral'_eq_add_of_simplePole (p := 1) (A := 1 / (t : ℂ))
    ⟨by simpa using hb1, by simpa using hc⟩ ?_ (kernelQ_sub_pole_isBigO ht)
    (tendsto_integral_kernelQ_horizontal hRH hb hbc ht tendsto_abs_atBot_atTop)
    (tendsto_integral_kernelQ_horizontal hRH hb hbc ht tendsto_abs_atTop_atTop)
    (integrable_kernelQ ht (integrable_Gamma_mul_Qcont_of_RH hRH hb hb1))
    (integrable_kernelQ ht (integrable_Gamma_mul_Qcont_of_one_lt hc))
  rintro z ⟨hz, hz1⟩
  have hzre : z.re ∈ Icc b c := (mem_reProdIm.mp hz).1
  have hz1' : z ≠ 1 := hz1
  have hre : 1 / 2 < z.re := by linarith [hzre.1]
  refine DifferentiableAt.differentiableWithinAt ?_
  show DifferentiableAt ℂ (fun z : ℂ => (t : ℂ) ^ (-z) * (Gamma z * Qcont z)) z
  exact (differentiableAt_ofReal_cpow_neg ht z).mul ((differentiableAt_Gamma_of_re_pos (by linarith)).mul
    (analyticAt_Qcont_of_RH hRH hre hz1').differentiableAt)

end TIdentity

end GoldbachBoundaries
