import PrimePairNB.ThmA.G15_Kernel

/-!
# general tools for vertical-line integrals

Namespace `GoldbachBoundaries.ThmA.GroupE`, names prefixed `dom_`.

* `dom_integrable_logDom`: `(1+|y|)^{-3} (1 + |y| + |log|y - y₀||)` is integrable on `ℝ` (the
  dominating function for `Γ × (linear growth + one logarithmic singularity)`).
* `dom_tendsto_verticalIntegral'`: dominated convergence for `VerticalIntegral'` in the abscissa.
* `dom_verticalIntegral'_eq_of_differentiableOn`: moving a vertical line across a strip on which
  `f` is holomorphic (the pole-shift lemma `verticalIntegral'_eq_add_of_simplePole` with no pole).
* `dom_tendsto_horizontal`: horizontal integrals tend to `0` under a `K (1+|y|)⁻¹` bound.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

namespace GroupE

/-- `(1+|y|)^{-2}` is integrable. -/
theorem dom_integrable_inv_sq :
    Integrable fun y : ℝ => ((1 + |y|) ^ 2)⁻¹ := by
  refine (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).congr
    (Eventually.of_forall fun y => ?_)
  have hpos : 0 < 1 + |y| := by positivity
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg hpos.le]
  norm_cast

theorem dom_integrable_logDom (y₀ : ℝ) :
    Integrable fun y : ℝ => ((1 + |y|) ^ 3)⁻¹ * (1 + |y| + |Real.log (y - y₀)|) := by
  have hloc : IntegrableOn (fun y : ℝ => |Real.log (y - y₀)|) (Icc (y₀ - 1) (y₀ + 1)) := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := -1) (b := 1)).comp_sub_right y₀
    have h' : IntervalIntegrable (fun y : ℝ => Real.log (y - y₀)) volume (y₀ - 1) (y₀ + 1) := by
      convert h using 1 <;> ring
    have h2 := ((intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp h').norm
    simp only [Real.norm_eq_abs] at h2
    exact h2
  have hdom : Integrable fun y : ℝ =>
      (2 + |y₀|) * ((1 + |y|) ^ 2)⁻¹ +
        (Icc (y₀ - 1) (y₀ + 1)).indicator (fun y : ℝ => |Real.log (y - y₀)|) y :=
    (dom_integrable_inv_sq.const_mul _).add ((integrable_indicator_iff measurableSet_Icc).mpr hloc)
  refine hdom.mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  have hpos : 0 < 1 + |y| := by positivity
  have hy0 : 0 ≤ |y| := abs_nonneg y
  have hL : 0 ≤ |Real.log (y - y₀)| := abs_nonneg _
  rw [Real.norm_of_nonneg (by positivity)]
  have hsplit : ((1 + |y|) ^ 3)⁻¹ * (1 + |y| + |Real.log (y - y₀)|) =
      ((1 + |y|) ^ 2)⁻¹ + ((1 + |y|) ^ 3)⁻¹ * |Real.log (y - y₀)| := by
    field_simp
  rw [hsplit]
  have hinv3 : ((1 + |y|) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hinv2 : 0 ≤ ((1 + |y|) ^ 2)⁻¹ := by positivity
  by_cases hy : y ∈ Icc (y₀ - 1) (y₀ + 1)
  · rw [indicator_of_mem hy]
    have : ((1 + |y|) ^ 3)⁻¹ * |Real.log (y - y₀)| ≤ |Real.log (y - y₀)| :=
      mul_le_of_le_one_left hL hinv3
    have h4 : 0 ≤ |y₀| * ((1 + |y|) ^ 2)⁻¹ := by positivity
    linarith
  · rw [indicator_of_notMem hy, add_zero]
    have hfar : 1 < |y - y₀| := by
      by_contra h
      push Not at h
      exact hy ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩
    have hlog : |Real.log (y - y₀)| ≤ |y - y₀| := by
      rw [← Real.log_abs, abs_of_nonneg (Real.log_nonneg hfar.le)]
      exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have htri : |y - y₀| ≤ (1 + |y₀|) * (1 + |y|) := by
      have := abs_sub y y₀
      nlinarith [abs_nonneg y₀]
    have h3 : ((1 + |y|) ^ 3)⁻¹ * |Real.log (y - y₀)| ≤ (1 + |y₀|) * ((1 + |y|) ^ 2)⁻¹ := by
      have he : ((1 + |y|) ^ 3)⁻¹ = ((1 + |y|) ^ 2)⁻¹ * (1 + |y|)⁻¹ := by
        rw [pow_succ, mul_inv]
      rw [he]
      calc ((1 + |y|) ^ 2)⁻¹ * (1 + |y|)⁻¹ * |Real.log (y - y₀)|
          ≤ ((1 + |y|) ^ 2)⁻¹ * (1 + |y|)⁻¹ * ((1 + |y₀|) * (1 + |y|)) := by gcongr; linarith
        _ = (1 + |y₀|) * ((1 + |y|) ^ 2)⁻¹ := by field_simp
    linarith

theorem dom_tendsto_verticalIntegral' {f : ℂ → ℂ} {σ₀ : ℝ} {l : Filter ℝ}
    [l.IsCountablyGenerated] {D : ℝ → ℝ} (hD : Integrable D)
    (hmeas : ∀ᶠ σ : ℝ in l, AEStronglyMeasurable (fun y : ℝ => f ((σ : ℂ) + y * I)))
    (hbound : ∀ᶠ σ : ℝ in l, ∀ᵐ y : ℝ, ‖f ((σ : ℂ) + y * I)‖ ≤ D y)
    (hlim : ∀ᵐ y : ℝ, Tendsto (fun σ : ℝ => f ((σ : ℂ) + y * I)) l (𝓝 (f ((σ₀ : ℂ) + y * I)))) :
    Tendsto (fun σ => VerticalIntegral' f σ) l (𝓝 (VerticalIntegral' f σ₀)) := by
  have h := tendsto_integral_filter_of_dominated_convergence D hmeas hbound hD hlim
  simpa only [VerticalIntegral', VerticalIntegral] using
    (h.const_smul I).const_smul (1 / (2 * Real.pi * I) : ℂ)

theorem dom_verticalIntegral'_eq_of_differentiableOn {σ σ' : ℝ} {f : ℂ → ℂ} (hσ : σ < σ')
    (hf : DifferentiableOn ℂ f (Icc σ σ' ×ℂ univ))
    (hbot : Tendsto (fun y : ℝ => ∫ x in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (htop : Tendsto (fun y : ℝ => ∫ x in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable fun y : ℝ => f (σ + y * I))
    (hright : Integrable fun y : ℝ => f (σ' + y * I)) :
    VerticalIntegral' f σ' = VerticalIntegral' f σ := by
  set p : ℂ := (((σ + σ') / 2 : ℝ) : ℂ) with hp
  have hpre : p.re = (σ + σ') / 2 := by simp [hp]
  have hopen : IsOpen (Ioo σ σ' ×ℂ (univ : Set ℝ)) := isOpen_Ioo.reProdIm isOpen_univ
  have hsub : Ioo σ σ' ×ℂ (univ : Set ℝ) ⊆ Icc σ σ' ×ℂ univ :=
    fun z hz => ⟨Ioo_subset_Icc_self hz.1, hz.2⟩
  have hmem : p ∈ Ioo σ σ' ×ℂ (univ : Set ℝ) :=
    ⟨show p.re ∈ Ioo σ σ' by rw [hpre]; constructor <;> linarith, mem_univ _⟩
  have hnhds : Icc σ σ' ×ℂ univ ∈ 𝓝 p := mem_of_superset (hopen.mem_nhds hmem) hsub
  have hcont : ContinuousAt f p := (hf.differentiableAt hnhds).continuousAt
  have h := TIdentity.verticalIntegral'_eq_add_of_simplePole (p := p) (A := 0)
    ⟨by rw [hpre]; linarith, by rw [hpre]; linarith⟩ (hf.mono sdiff_subset) ?_ hbot htop hleft hright
  · rw [h, zero_add]
  · have : (f - fun s => (0 : ℂ) / (s - p)) = f := by funext s; simp
    rw [this]
    exact (hcont.tendsto.isBigO_one ℂ).mono nhdsWithin_le_nhds

theorem dom_tendsto_horizontal {f : ℂ → ℂ} {σ σ' K Y : ℝ} (hσ : σ ≤ σ')
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

end GroupE

end GoldbachBoundaries.ThmA
